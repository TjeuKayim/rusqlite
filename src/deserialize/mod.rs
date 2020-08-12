//! `feature = "deserialize"` Serialize and deserialize interfaces.
//!
//! This API is only available when SQLite is compiled with `SQLITE_ENABLE_DESERIALIZE`.
//! These functions create and read a serialized file in-memory, useful on platforms without
//! a real file system like WebAssembly or Cloud Functions.
//!
//! For large in-memory database files, you probably don't want to copy or reallocate
//! because that would temporarily double the required memory.
//!
//! * While downloading a `.sqlite` file, write the buffers directly to [`Vec<u8>`]
//!   and pass that to [`Connection::deserialize`]
//!   (ownership is tranferred to SQLite without copying).
//! * Borrow the memory from SQLite using [`Connection::serialize_no_copy`].
//! * Let SQLite immutably borrow a large Rust-allocated vector using
//!   [`BorrowingConnection::deserialize_read_only`].
//! * Let SQLite mutably borrow a [`SetLenBytes`] using
//!   [`BorrowingConnection::deserialize_mut`].
//! * Let SQlite mutably borrow a SQLite owned memory using
//!   [`BorrowingConnection::deserialize_resizable`].
//! * Obtain a copy of the file using [`Connection::serialize`].
//!
//! ```
//! # use rusqlite::{Result, Connection, DatabaseName, NO_PARAMS};
//! # fn main() -> Result<()> {
//! let db = Connection::open_in_memory()?;
//! db.execute_batch("CREATE TABLE foo(x INTEGER);INSERT INTO foo VALUES(44)")?;
//! let serialized = db.serialize(DatabaseName::Main)?.unwrap();
//! let mut clone = Connection::open_in_memory()?;
//! clone.deserialize(DatabaseName::Main, serialized)?;
//! let row: u16 = clone.query_row("Select x FROM foo", NO_PARAMS, |r| r.get(0))?;
//! assert_eq!(44, row);
//! # Ok(())
//! # }
//! ```
//!
//! Alternatively, consider using the [Backup API](./backup/).

use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::os::raw::{c_char, c_int, c_void};
use std::{convert::TryInto, fmt, mem, ops, panic, ptr, rc::Rc, borrow::Cow};

use crate::ffi;
use crate::{
    inner_connection::InnerConnection, util::SmallCString, Connection, DatabaseName, Result, NO_PARAMS,
};
use mem_file::MemFile;
use ptr::NonNull;

mod mem_file;

impl Connection {
    /// Disconnect from database and reopen as an in-memory database based on [`Vec<u8>`].
    pub fn deserialize(&self, schema: DatabaseName<'_>, data: Vec<u8>) -> Result<()> {
        let schema = schema.to_cstring()?;
        self.db
            .borrow_mut()
            .deserialize_hook(&schema, FileType::Owned(data))
    }

    /// Return the serialization of a database, or `None` when [`DatabaseName`] does not exist.
    /// See the C Interface Specification [Serialize a database](https://www.sqlite.org/c3ref/serialize.html).
    pub fn serialize(&self, schema: DatabaseName<'_>) -> Result<Option<Vec<u8>>> {
        let schema = schema.to_cstring()?;
        let c = self.db.borrow();
        let file = file_ptr(&c, &schema);
        mem::drop(c);
        file.map(|file| unsafe {
            if file.pMethods == hooked_io_methods() {
                let hooked = &mut *(file as *mut _ as *mut HookedFile);
                return Ok(hooked.as_ref().as_slice().to_vec());
            }
            // TODO: Optimize sqlite_io_methods

            // pragma_query_value is not used because the PRAGMA function should be preferred.
            // escape_double_quote is only available with feature vtab.
            let schema_str = schema.as_str();
            let escaped = if schema_str.contains('\'') {
                Cow::Owned(schema_str.replace("'", "''"))
            } else {
                Cow::Borrowed(schema_str)
            };
            let sql = &format!(
                "SELECT * FROM '{}'.pragma_page_size JOIN pragma_page_count",
                escaped
            );
            let (page_size, page_count): (i64, i64) =
                self.query_row(sql, NO_PARAMS, |r| Ok((r.get(0)?, r.get(1)?)))?;
            let total_size = (page_size * page_count).try_into().unwrap();
            let mut vec = Vec::with_capacity(total_size);
            // Unfortunately, sqlite3PagerGet and sqlite3PagerGetData are private APIs
            let temp_db_name = "rusqlite_internal_deserialize";
            let temp_db_uri = &format!("file:{}?vfs=memdb&cache=shared", temp_db_name);
            self.execute_batch(&format!("ATTACH DATABASE '{}' AS {}", temp_db_uri, temp_db_name))?;
            let temp_file = file_ptr(&self.db.borrow(), &SmallCString::new(temp_db_name)?).unwrap();
            assert_eq!(temp_file.pMethods, sqlite_io_methods());
            // At this point, MemFile->aData is null
            let hooked = HookedFile {
                methods: hooked_io_methods(),
                data: Rc::new(FileType::Resizable(&mut vec)),
                memory_mapped: 0,
                size_max: total_size * 2,
            };
            let file = file as *mut _ as _;
            ptr::write(file, hooked);

            let sql = &format!(
                "VACUUM '{escaped}' INTO '{uri}';DETACH DATABASE {name};",
                escaped=escaped,
                name=temp_db_name,
                uri=temp_db_uri
            );
            dbg!("vacuum now");
            self.execute_batch(sql)?;
            assert_ne!(dbg!(vec.len()), 0);

            // TODO: hook and fill vec
            Ok(vec)
        })
        .transpose()
    }

    /// Wraps the `Connection` in `BorrowingConnection` to connect it to borrowed serialized memory
    /// using [`BorrowingConnection::deserialize_read_only`].
    pub fn into_borrowing(self) -> BorrowingConnection<'static> {
        BorrowingConnection::new(self)
    }
}

impl InnerConnection {
    /// Disconnect from database and reopen as an in-memory database based on a borrowed slice.
    /// If the `DatabaseName` does not exist, return
    /// `SqliteFailure(Error { code: Unknown, extended_code: 1 }, Some("not an error"))`.
    ///
    /// # Safety
    ///
    /// The reference `data` must last for the lifetime of this connection.
    /// `cap` must be the size of the allocation, and `cap >= data.len()`.
    ///
    /// If the data is not mutably borrowed, set [`DeserializeFlags::READ_ONLY`].
    /// If SQLite allocated the memory, consider setting [`DeserializeFlags::FREE_ON_CLOSE`]
    /// and/or [`DeserializeFlags::RESIZABLE`].
    ///
    /// See the C Interface Specification [Deserialize a database](https://www.sqlite.org/c3ref/deserialize.html).
    unsafe fn deserialize_with_flags(
        &mut self,
        schema: &SmallCString,
        data: &[u8],
        cap: usize,
        flags: c_int,
    ) -> Result<()> {
        let rc = ffi::sqlite3_deserialize(
            self.db(),
            schema.as_ptr(),
            data.as_ptr() as *mut _,
            data.len() as _,
            cap as _,
            flags as _,
        );
        self.decode_result(rc)
    }

    /// Store `data: FileType` in a new `HookedFile`, after moving
    /// the original file to a new allocation.
    fn deserialize_hook<'a>(&mut self, schema: &SmallCString, data: FileType<'a>) -> Result<()> {
        unsafe {
            self.deserialize_with_flags(schema, data.as_slice(), data.cap(), 0)?;
            let file = file_ptr(self, &schema).unwrap();
            assert_eq!(file.pMethods, sqlite_io_methods());
            let size_max = file_size_max(file);
            let hooked = HookedFile {
                methods: hooked_io_methods(),
                data: Rc::new(data),
                memory_mapped: 0,
                size_max,
            };
            let file = file as *mut _ as _;
            ptr::write(file, hooked);
            Ok(())
        }
    }
}

/// Wrap `Connection` with lifetime constraint to borrow from serialized memory.
/// Use [`Connection::into_borrowing`] to obtain one.
pub struct BorrowingConnection<'a> {
    conn: Connection,
    phantom: PhantomData<&'a [u8]>,
}

impl<'a> BorrowingConnection<'a> {
    fn new(conn: Connection) -> Self {
        BorrowingConnection {
            conn,
            phantom: PhantomData,
        }
    }

    /// Borrow the serialization of a database without copying the memory.
    /// This returns `Ok(None)` when [`DatabaseName`] does not exist or no in-memory serialization is present.
    pub fn serialize_no_copy(&self, schema: DatabaseName<'_>) -> Result<Option<Fetch<'a>>> {
        let schema = schema.to_cstring()?;
        let c = self.conn.db.borrow_mut();
        Ok(file_ptr(&c, &schema).and_then(|file| {
            let hooked = if file.pMethods == hooked_io_methods() {
                unsafe { &mut *(file as *mut _ as *mut _) }
            } else {
                return None;
            };
            Some(Fetch::new(hooked))
        }))
    }

    /// Disconnect from database and reopen as an read-only in-memory database based on a borrowed slice
    /// (using the flag [`ffi::SQLITE_DESERIALIZE_READONLY`]).
    pub fn deserialize_read_only(&self, schema: DatabaseName<'a>, data: &'a [u8]) -> Result<()> {
        let schema = schema.to_cstring()?;
        self.db
            .borrow_mut()
            .deserialize_hook(&schema, FileType::ReadOnly(data))
    }

    /// Disconnect from database and reopen as an in-memory database based on a borrowed vector
    /// (pass a `Vec<u8>`, `MemFile` or another type that implements `SetLenBytes`).
    /// If the capacity is reached, SQLite can't reallocate, so it throws [`crate::ErrorCode::DiskFull`].
    /// Before the connection drops, the slice length is updated.
    pub fn deserialize_mut<T>(&mut self, schema: DatabaseName<'a>, data: &'a mut T) -> Result<()>
    where
        T: SetLenBytes + Send,
    {
        let schema = schema.to_cstring()?;
        let mut c = self.conn.db.borrow_mut();
        c.deserialize_hook(&schema, FileType::SetLen(data))
    }

    /// Disconnect from database and reopen as an in-memory database based on a borrowed `MemFile`.
    /// If the capacity is reached, SQLite may reallocate the borrowed memory.
    /// Before the connection drops, the `&mut MemFile` pointer, length and capacity are updated.
    pub fn deserialize_resizable(
        &mut self,
        schema: DatabaseName<'a>,
        data: &'a mut Vec<u8>,
    ) -> Result<()> {
        let schema = schema.to_cstring()?;
        let mut c = self.conn.db.borrow_mut();
        c.deserialize_hook(&schema, FileType::Resizable(data))
    }
}

impl ops::Deref for BorrowingConnection<'_> {
    type Target = Connection;
    fn deref(&self) -> &Connection {
        &self.conn
    }
}

impl ops::DerefMut for BorrowingConnection<'_> {
    fn deref_mut(&mut self) -> &mut Connection {
        &mut self.conn
    }
}

impl fmt::Debug for BorrowingConnection<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BorrowingConnection")
            .field("conn", &self.conn)
            .finish()
    }
}

/// Reference counted slice of memory file with serialized database content
pub struct Fetch<'a>(pub &'a [u8], Rc<FileType<'a>>);

impl<'a> Fetch<'a> {
    fn new(hooked: &'a HookedFile<'a>) -> Self {
        Fetch(hooked.as_ref().as_slice(), Rc::clone(&hooked.data))
    }
}

impl ops::Deref for Fetch<'_> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.0
    }
}

/// Pointer that should be updated on close.
enum FileType<'a> {
    Owned(Vec<u8>),
    Resizable(&'a mut Vec<u8>),
    SetLen(&'a mut dyn SetLenBytes),
    ReadOnly(&'a [u8]),
}

impl FileType<'_> {
    fn as_slice(&self) -> &[u8] {
        match self {
            FileType::Owned(d) => d,
            FileType::Resizable(d) => d,
            FileType::SetLen(d) => d,
            FileType::ReadOnly(d) => d,
        }
    }

    fn as_ptr(&self) -> *const u8 {
        self.as_slice().as_ptr()
    }

    fn as_mut_slice(&mut self) -> &mut [u8] {
        match self {
            FileType::Owned(d) => &mut d[..],
            FileType::Resizable(d) => &mut d[..],
            FileType::SetLen(d) => &mut d[..],
            FileType::ReadOnly(_) => panic!("ReadOnly.as_mut_slice"),
        }
    }

    fn as_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_slice().as_mut_ptr()
    }

    fn len(&self) -> usize {
        self.as_slice().len()
    }

    fn set_len(&mut self, new_len: usize) {
        unsafe {
            match self {
                FileType::Owned(d) => d.set_len(new_len),
                FileType::Resizable(d) => d.set_len(new_len),
                FileType::SetLen(d) => d.set_len(new_len),
                FileType::ReadOnly(_) => panic!("ReadOnly.set_len"),
            }
        }
    }

    fn cap(&self) -> usize {
        match self {
            FileType::Owned(d) => d.capacity(),
            FileType::Resizable(d) => d.capacity(),
            FileType::SetLen(d) => d.capacity(),
            FileType::ReadOnly(d) => d.len(),
        }
    }

    fn reserve_additional(&mut self, additional: usize) -> bool {
        match self {
            FileType::Owned(d) => {
                d.reserve(additional);
                true
            }
            FileType::Resizable(d) => {
                d.reserve(additional);
                true
            }
            FileType::SetLen(_) => false,
            FileType::ReadOnly(_) => false,
        }
    }

    // Write-protected/read-only or not
    fn writable(&self) -> bool {
        match self {
            FileType::Owned(_) => true,
            FileType::Resizable(_) => true,
            FileType::SetLen(_) => true,
            FileType::ReadOnly(_) => false,
        }
    }
}

/// `sqlite3_file` subclass that delegates most methods
/// to the original/lower file defined in `memdb.c`.
/// On close, the `data` pointer gets updated.
#[repr(C)]
struct HookedFile<'a> {
    methods: *const ffi::sqlite3_io_methods,
    data: Rc<FileType<'a>>,
    size_max: usize,
    memory_mapped: u16,
}

impl<'a> HookedFile<'a> {
    fn get_mut(&mut self) -> Option<&mut FileType<'a>> {
        if !self.data.writable() {
            None
        } else {
            Rc::get_mut(&mut self.data)
        }
    }

    fn as_ref(&self) -> &FileType<'a> {
        Rc::as_ref(&self.data)
    }
}

fn hooked_io_methods() -> *const ffi::sqlite3_io_methods {
    const HOOKED_IO_METHODS: ffi::sqlite3_io_methods = ffi::sqlite3_io_methods {
        iVersion: 3,
        xClose: Some(c_close),
        xRead: Some(c_read),
        xWrite: Some(c_write),
        xTruncate: Some(c_truncate),
        xSync: Some(c_sync),
        xFileSize: Some(c_size),
        xLock: Some(c_lock),
        xUnlock: Some(c_lock),
        xCheckReservedLock: None,
        xFileControl: Some(c_file_control),
        xSectorSize: None,
        xDeviceCharacteristics: Some(c_device_characteristics),
        xShmMap: None,
        xShmLock: None,
        xShmBarrier: None,
        xShmUnmap: None,
        xFetch: Some(c_fetch),
        xUnfetch: Some(c_unfetch),
    };
    &HOOKED_IO_METHODS
}

lazy_static::lazy_static! {
    /// Get `memdb_io_methods` and `szOsFile` for the VFS defined in `memdb.c`
    static ref MEM_VFS: (&'static ffi::sqlite3_io_methods, i32) = unsafe {
        let vfs = &mut *ffi::sqlite3_vfs_find("memdb\0".as_ptr() as _);
        let sz = vfs.szOsFile;
        assert!(mem::size_of::<HookedFile>() <= sz as _);
        let file = ffi::sqlite3_malloc(sz) as *mut ffi::sqlite3_file;
        assert!(!file.is_null());
        let mut out_flags = 0;
        let rc = vfs.xOpen.unwrap()(vfs, ptr::null(), file, ffi::SQLITE_OPEN_MAIN_DB, &mut out_flags);
        assert_eq!(rc, ffi::SQLITE_OK);
        let methods = &*(*file).pMethods;
        ffi::sqlite3_free(file as _);
        (methods, sz)
    };
}

fn sqlite_io_methods() -> *const ffi::sqlite3_io_methods {
    MEM_VFS.0
}

fn file_ptr<'a>(c: &InnerConnection, schema: &SmallCString) -> Option<&'a mut ffi::sqlite3_file> {
    unsafe {
        let mut file = MaybeUninit::<&mut ffi::sqlite3_file>::zeroed();
        let rc = ffi::sqlite3_file_control(
            c.db(),
            schema.as_ptr(),
            ffi::SQLITE_FCNTL_FILE_POINTER,
            file.as_mut_ptr() as _,
        );
        if rc != ffi::SQLITE_OK || file.as_ptr().is_null() {
            None
        } else {
            Some(file.assume_init())
        }
    }
}

fn file_size_max(file: &mut ffi::sqlite3_file) -> usize {
    let mut size_max: ffi::sqlite3_int64 = -1;
    let rc = unsafe { (*file.pMethods).xFileControl.unwrap()(
        file,
        ffi::SQLITE_FCNTL_SIZE_LIMIT,
        &mut size_max as *mut _ as _,
    )};
    assert_eq!(rc, ffi::SQLITE_OK);
    size_max.try_into().unwrap()
}

fn file_length(file: &mut ffi::sqlite3_file) -> usize {
    unsafe {
        let mut size: i64 = 0;
        let rc = (*file.pMethods).xFileSize.map(|c| c(file, &mut size));
        debug_assert_eq!(rc, Some(ffi::SQLITE_OK));
        size as _
    }
}

fn file_buffer(file: &mut ffi::sqlite3_file) -> NonNull<u8> {
    let fetch: *mut u8 = unsafe {
        // Unfortunately, serialize_no_copy does not work here as the db is already
        // detached, but the sqlite3_file is not yet freed. Because the aData field
        // is private, this hack is needed to get the buffer.
        let mut fetch = MaybeUninit::zeroed();
        let rc = (*file.pMethods).xFetch.unwrap()(file, 0, 0, fetch.as_mut_ptr() as _);
        debug_assert_eq!(rc, ffi::SQLITE_OK);
        let rc = (*file.pMethods).xUnfetch.unwrap()(file, 0, ptr::null_mut());
        debug_assert_eq!(rc, ffi::SQLITE_OK);
        fetch.assume_init()
    };
    NonNull::new(fetch).unwrap()
}

/// This will be called when dropping the `Connection` or
/// when the database gets detached.
unsafe extern "C" fn c_close(file: *mut ffi::sqlite3_file) -> c_int {
    panic::catch_unwind(|| {
        dbg!("c_close");
        // This ptr::read is used so that the HookedFile is dropped at the end of scope.
        ptr::drop_in_place(file as *mut HookedFile);
        ffi::SQLITE_OK
    })
    .unwrap_or_else(|e| {
        dbg!(e); // TODO: Pass error message to caller
        ffi::SQLITE_ERROR
    })
}
/// Read data from a memory file.
unsafe extern "C" fn c_read(
    file: *mut ffi::sqlite3_file,
    buf: *mut c_void,
    amt: c_int,
    ofst: i64,
) -> c_int {
    panic::catch_unwind(|| {
        let file = &mut *(file as *mut HookedFile);
        let data = file.as_ref();
        let buf = buf as *mut u8;
        let amt: usize = amt.try_into().unwrap();
        let ofst: usize = ofst.try_into().unwrap();
        if ofst + amt > data.len() {
            ptr::write_bytes(buf, 0, amt);
            if ofst < data.len() {
                ptr::copy_nonoverlapping(data.as_ptr().add(ofst), buf, data.len() - ofst);
            }
            return ffi::SQLITE_IOERR_SHORT_READ;
        }
        ptr::copy_nonoverlapping(data.as_ptr().add(ofst), buf, amt);
        ffi::SQLITE_OK
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}
/// Write data to a memory file.
unsafe extern "C" fn c_write(
    file: *mut ffi::sqlite3_file,
    buf: *const c_void,
    amt: c_int,
    ofst: i64,
) -> c_int {
    dbg!("c_write");
    panic::catch_unwind(|| {
        let file = &mut *(file as *mut HookedFile);
        let data = if let Some(d) = Rc::get_mut(&mut file.data) {
            d
        } else {
            return ffi::SQLITE_READONLY;
        };
        let sz = data.len();
        let sz_alloc = data.cap();
        let amt = amt as usize;
        let ofst = ofst as usize;
        if ofst + amt > sz {
            if ofst + amt > sz_alloc {
                if file.memory_mapped > 0 {
                    return ffi::SQLITE_FULL;
                }
                if !data.reserve_additional(ofst + amt - sz_alloc) {
                    return ffi::SQLITE_FULL;
                }
                if data.cap() > file.size_max {
                    return ffi::SQLITE_FULL;
                }
            }
            if ofst > sz {
                ptr::write_bytes(data.as_mut_ptr().add(sz), 0, ofst - sz);
            }
            data.set_len(ofst + amt);
        }
        ptr::copy_nonoverlapping(buf, data.as_mut_ptr().add(ofst).cast(), amt);
        ffi::SQLITE_OK
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}
/// Truncate a memory file.
///
/// In rollback mode (which is always the case for memdb, as it does not
/// support WAL mode) the truncate() method is only used to reduce
/// the size of a file, never to increase the size.
unsafe extern "C" fn c_truncate(file: *mut ffi::sqlite3_file, size: i64) -> c_int {
    panic::catch_unwind(|| {
        if let Some(data) = (&mut *(file as *mut HookedFile)).get_mut() {
            let size = size.try_into().unwrap();
            if size > data.len() {
                ffi::SQLITE_FULL
            } else {
                data.set_len(size);
                ffi::SQLITE_OK
            }
        } else {
            ffi::SQLITE_FULL
        }
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}
/// Sync a memory file.
unsafe extern "C" fn c_sync(_file: *mut ffi::sqlite3_file, _flags: c_int) -> c_int {
    ffi::SQLITE_OK
}
/// Return the current file-size of a memory file.
unsafe extern "C" fn c_size(file: *mut ffi::sqlite3_file, size: *mut i64) -> c_int {
    panic::catch_unwind(|| {
        let data = (&*(file as *mut HookedFile)).as_ref();
        *size = data.len() as _;
        ffi::SQLITE_OK
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}
/// Lock a memory file.
unsafe extern "C" fn c_lock(file: *mut ffi::sqlite3_file, lock: c_int) -> c_int {
    let data = (&*(file as *mut HookedFile)).as_ref();
    if lock > ffi::SQLITE_LOCK_SHARED && !data.writable() {
        ffi::SQLITE_READONLY
    } else {
        // TODO: Why stores memdb.c the lock in the struct but never uses it
        ffi::SQLITE_OK
    }
}
/// File control method.
unsafe extern "C" fn c_file_control(
    file: *mut ffi::sqlite3_file,
    op: c_int,
    arg: *mut c_void,
) -> c_int {
    panic::catch_unwind(|| {
        let file = &mut *(file as *mut HookedFile);
        let data = file.as_ref();
        match op {
            ffi::SQLITE_FCNTL_VFSNAME => {
                *(arg as *mut *const c_char) = ffi::sqlite3_mprintf(
                    "rust_memdb(%p,%llu)".as_ptr() as _,
                    data.as_ptr(),
                    data.len() as ffi::sqlite3_uint64,
                );
                ffi::SQLITE_OK
            }
            ffi::SQLITE_FCNTL_SIZE_LIMIT => {
                let arg = arg as *mut ffi::sqlite3_int64;
                let mut limit = *arg;
                if limit < data.len() as _ {
                    if limit < 0 {
                        limit = file.size_max as _;
                    } else {
                        limit = data.len() as _;
                    }
                }
                file.size_max = limit.try_into().expect("overflow size_max");
                *arg = limit;
                ffi::SQLITE_OK
            }
            _ => ffi::SQLITE_NOTFOUND,
        }
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}
/// Return the device characteristic flags supported.
unsafe extern "C" fn c_device_characteristics(_file: *mut ffi::sqlite3_file) -> c_int {
    ffi::SQLITE_IOCAP_ATOMIC
        | ffi::SQLITE_IOCAP_POWERSAFE_OVERWRITE
        | ffi::SQLITE_IOCAP_SAFE_APPEND
        | ffi::SQLITE_IOCAP_SEQUENTIAL
}
/// Fetch a page of a memory-mapped file.
unsafe extern "C" fn c_fetch(
    file: *mut ffi::sqlite3_file,
    ofst: i64,
    amt: c_int,
    p: *mut *mut c_void,
) -> c_int {
    panic::catch_unwind(|| {
        let file = &mut *(file as *mut HookedFile);
        let data = file.as_ref();
        if ofst + amt as i64 > data.len() as _ {
            *p = ptr::null_mut();
        } else {
            // Safety: SQLite uses a read-only memory map <https://www.sqlite.org/mmap.html>,
            // so it is safe to cast this *const to *mut.
            *p = data.as_ptr() as *mut u8 as _;
            file.memory_mapped += 1;
        }
        ffi::SQLITE_OK
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}
/// Release a memory-mapped page.
unsafe extern "C" fn c_unfetch(file: *mut ffi::sqlite3_file, _ofst: i64, _p: *mut c_void) -> c_int {
    panic::catch_unwind(|| {
        let file = &mut *(file as *mut HookedFile);
        file.memory_mapped -= 1;
        ffi::SQLITE_OK
    })
    .unwrap_or_else(|e| {
        dbg!(e);
        ffi::SQLITE_ERROR
    })
}

/// Vector of bytes where the length can be modified.
/// [`BorrowingConnection`] functions use this to borrow memory from arbitrary allocators.
pub trait SetLenBytes: ops::Deref<Target = [u8]> + ops::DerefMut + fmt::Debug {
    /// Forces the length of the vector to new_len.
    ///
    /// # Safety
    /// - `new_len` must be less than or equal to `capacity()`.
    /// - The elements at `old_len..new_len` must be initialized.
    unsafe fn set_len(&mut self, new_len: usize);
    /// The size of the allocation.
    /// It must be safe to write this number of bytes at `as_ptr()`.
    fn capacity(&self) -> usize;
}
impl SetLenBytes for Vec<u8> {
    unsafe fn set_len(&mut self, new_len: usize) {
        self.set_len(new_len);
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
}
impl SetLenBytes for MemFile {
    unsafe fn set_len(&mut self, new_len: usize) {
        self.set_len(new_len);
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Connection, DatabaseName, Error, ErrorCode, Result, NO_PARAMS};

    #[test]
    pub fn test_serialize_deserialize() {
        let db = Connection::open_in_memory().unwrap().into_borrowing();
        let sql = "BEGIN;
            CREATE TABLE foo(x INTEGER);
            INSERT INTO foo VALUES(1);
            INSERT INTO foo VALUES(2);
            INSERT INTO foo VALUES(3);
            END;";
        db.execute_batch(sql).unwrap();
        let serialized = db.serialize(DatabaseName::Main).unwrap().unwrap();

        // create a new db and import the serialized data
        let db2 = Connection::open_in_memory().unwrap().into_borrowing();
        db2.deserialize(DatabaseName::Main, serialized).unwrap();
        let mut query = db2.prepare("SELECT x FROM foo").unwrap();
        let results: Result<Vec<u16>> = query
            .query_map(NO_PARAMS, |row| row.get(0))
            .unwrap()
            .collect();
        std::mem::drop(query);
        assert_eq!(vec![1, 2, 3], results.unwrap());
        // should not be read-only
        let sql = "INSERT INTO foo VALUES(4)";
        db2.execute_batch(sql).unwrap();

        // NO_COPY only works on db2
        assert!(db.serialize_no_copy(DatabaseName::Main).unwrap().is_none());
        let borrowed_serialized = db2.serialize_no_copy(DatabaseName::Main).unwrap().unwrap();
        let mut serialized = Vec::new();
        serialized.extend(borrowed_serialized.iter().cloned());

        // create a third db and import the serialized data
        let db3 = Connection::open_in_memory().unwrap();
        db3.deserialize(DatabaseName::Main, serialized).unwrap();
        let mut query = db3.prepare("SELECT x FROM foo").unwrap();
        let results: Result<Vec<u16>> = query
            .query_map(NO_PARAMS, |row| row.get(0))
            .unwrap()
            .collect();
        assert_eq!(vec![1, 2, 3, 4], results.unwrap());
    }

    #[test]
    pub fn test_serialize_no_copy() {
        // prepare two distinct files: a & b
        let db1 = Connection::open_in_memory().unwrap().into_borrowing();
        db1.execute_batch("CREATE TABLE a(x INTEGER);INSERT INTO a VALUES(1);")
            .unwrap();
        let file_a = db1.serialize(DatabaseName::Main).unwrap().unwrap();
        db1.execute_batch("INSERT INTO a VALUES(2);").unwrap();
        let file_b = db1.serialize(DatabaseName::Main).unwrap().unwrap();

        let db2 = Connection::open_in_memory().unwrap().into_borrowing();
        db2.deserialize(DatabaseName::Main, file_a.clone()).unwrap();
        let file_c = db2.serialize_no_copy(DatabaseName::Main).unwrap().unwrap();
        let sql = "INSERT INTO a VALUES(3)";
        db2.execute_batch(sql)
            .expect_err("should be write protected");
        mem::drop(file_c);
        db2.execute_batch(sql)
            .expect("should succeed after file_c is dropped");
        assert_eq!(
            2,
            db2.query_row("SELECT COUNT(x) FROM a", NO_PARAMS, |r| r.get::<_, i32>(0))
                .unwrap()
        );

        db2.execute_batch("ATTACH DATABASE ':memory:' AS d")
            .unwrap();
        let name_d = DatabaseName::Attached("d");
        db2.deserialize(name_d, file_a).unwrap();
        let file_d = db2.serialize_no_copy(name_d).unwrap().unwrap();
        // detach and attach other db, this should call xClose and decrease reference count
        assert_eq!(2, Rc::strong_count(&file_d.1));
        db2.deserialize(name_d, file_b).unwrap();
        assert_eq!(1, Rc::strong_count(&file_d.1));
        // test whether file_d stayed intact
        db2.deserialize_read_only(DatabaseName::Main, &file_d)
            .unwrap();
        assert_eq!(
            1,
            db2.query_row("SELECT MAX(x) FROM main.a", NO_PARAMS, |r| r
                .get::<_, i32>(0))
                .unwrap()
        );
        assert_eq!(
            2,
            db2.query_row("SELECT MAX(x) FROM d.a", NO_PARAMS, |r| r.get::<_, i32>(0))
                .unwrap()
        );
    }

    #[test]
    pub fn test_deserialize_with_flags() {
        let db = Connection::open_in_memory().unwrap();
        let sql = "BEGIN;
            CREATE TABLE foo(x INTEGER);
            INSERT INTO foo VALUES(1);
            INSERT INTO foo VALUES(2);
            INSERT INTO foo VALUES(3);
            END;";
        db.execute_batch(sql).unwrap();
        let serialized = db.serialize(DatabaseName::Main).unwrap().unwrap();
        // copy to Vec and create new Vec
        let serialized_vec = Vec::from(&serialized[..]);
        let mut serialized = Vec::new();
        serialized.extend(serialized_vec);

        // create a new db and import the serialized data
        let db2 = Connection::open_in_memory().unwrap();
        unsafe {
            db2.db
                .borrow_mut()
                .deserialize_with_flags(
                    &DatabaseName::Main.to_cstring().unwrap(),
                    &serialized,
                    serialized.capacity(),
                    ffi::SQLITE_DESERIALIZE_READONLY,
                )
                .unwrap()
        };
        let mut query = db2.prepare("SELECT x FROM foo").unwrap();
        let results: Result<Vec<u16>> = query
            .query_map(NO_PARAMS, |row| row.get(0))
            .unwrap()
            .collect();
        assert_eq!(vec![1, 2, 3], results.unwrap());
        // should be read-only
        let sql = "INSERT INTO foo VALUES(4)";
        db2.execute_batch(sql).unwrap_err();
    }

    #[test]
    pub fn test_deserialize_read_only() -> Result<()> {
        let sql = "BEGIN;
            CREATE TABLE hello(x INTEGER);
            INSERT INTO hello VALUES(1);
            INSERT INTO hello VALUES(2);
            INSERT INTO hello VALUES(3);
            END;";

        // prepare two named databases
        let one = Connection::open_in_memory()?;
        one.execute_batch(sql)?;
        let serialized_one = one.serialize(DatabaseName::Main)?.unwrap();

        let two = Connection::open_in_memory()?;
        two.execute_batch(sql)?;
        let serialized_two = two.serialize(DatabaseName::Main)?.unwrap();

        // create a new db and import the serialized data
        let db = Connection::open_in_memory()?.into_borrowing();
        db.execute_batch("ATTACH DATABASE ':memory:' AS foo; ATTACH DATABASE ':memory:' AS bar")?;
        db.deserialize_read_only(DatabaseName::Attached("foo"), &serialized_one)?;
        db.deserialize_read_only(DatabaseName::Attached("bar"), &serialized_two)?;
        let mut query = db.prepare("SELECT x FROM foo.hello")?;
        let results: Result<Vec<u16>> = query.query_map(NO_PARAMS, |row| row.get(0))?.collect();
        assert_eq!(vec![1, 2, 3], results?);
        let mut query = db.prepare("SELECT x FROM bar.hello")?;
        let results: Result<Vec<u16>> = query.query_map(NO_PARAMS, |row| row.get(0))?.collect();
        assert_eq!(vec![1, 2, 3], results?);
        // should be read-only
        let sql = "INSERT INTO foo VALUES(4)";
        db.execute_batch(sql).unwrap_err();
        Ok(())
    }

    #[test]
    pub fn test_deserialize_mutable() -> Result<()> {
        let sql = "BEGIN;
            CREATE TABLE hello(x INTEGER);
            INSERT INTO hello VALUES(1);
            INSERT INTO hello VALUES(2);
            INSERT INTO hello VALUES(3);
            END;";
        let db1 = Connection::open_in_memory()?;
        db1.execute_batch(sql)?;
        let mut serialized1 = db1.serialize(DatabaseName::Main)?.unwrap();
        let initial_len = serialized1.len();
        serialized1.reserve(8192);

        // create a new db and mutably borrow the serialized data
        let mut db3 = Connection::open_in_memory()?.into_borrowing();
        db3.deserialize_mut(DatabaseName::Main, &mut serialized1)?;
        // update should not affect length
        db3.execute_batch("UPDATE hello SET x = 44 WHERE x = 3")?;
        let mut query = db3.prepare("SELECT x FROM hello")?;
        let results: Result<Vec<u16>> = query.query_map(NO_PARAMS, |row| row.get(0))?.collect();
        assert_eq!(vec![1, 2, 44], results?);
        mem::drop(query);
        assert_eq!(initial_len, serialize_len(&mut db3));

        // insert data until the length needs to grow
        let count_until_resize = std::iter::repeat(())
            .take_while(|_| {
                db3.execute_batch("INSERT INTO hello VALUES(44);").unwrap();
                serialize_len(&mut db3) == initial_len
            })
            .count();
        assert_eq!(524, count_until_resize);

        // after some time, DiskFull is thrown
        let sql = "INSERT INTO hello VALUES(55);";
        for _i in 0..=509 {
            db3.execute_batch(sql)?;
        }
        if let Err(Error::SqliteFailure(
            ffi::Error {
                code: ErrorCode::DiskFull,
                extended_code: _,
            },
            _,
        )) = db3.execute_batch(sql)
        {
        } else {
            panic!("should return SqliteFailure");
        }
        // connection close should update length of serialized1
        let new_len = serialize_len(&mut db3);
        assert!(new_len > initial_len);
        mem::drop(db3);
        assert_eq!(new_len, serialized1.len());

        Ok(())
    }

    #[test]
    pub fn test_deserialize_resizable() -> Result<()> {
        let sql = "BEGIN;
            CREATE TABLE hello(x INTEGER);
            INSERT INTO hello VALUES(1);
            INSERT INTO hello VALUES(2);
            INSERT INTO hello VALUES(3);
            END;";
        let db1 = Connection::open_in_memory()?;
        db1.execute_batch(sql)?;
        let mut serialized1 = db1.serialize(DatabaseName::Main)?.unwrap();
        let initial_cap = serialized1.capacity();
        let initial_len = serialized1.len();

        // create a new db and mutably borrow the serialized data
        let mut db3 = Connection::open_in_memory()?.into_borrowing();
        db3.deserialize_resizable(DatabaseName::Main, &mut serialized1)?;
        // update should not affect length
        db3.execute_batch("UPDATE hello SET x = 44 WHERE x = 3")?;
        let mut query = db3.prepare("SELECT x FROM hello")?;
        let results: Result<Vec<u16>> = query.query_map(NO_PARAMS, |row| row.get(0))?.collect();
        assert_eq!(vec![1, 2, 44], results?);
        mem::drop(query);
        assert_eq!(initial_len, serialize_len(&mut db3));

        // insert data until the length needs to grow
        let count_until_resize = std::iter::repeat(())
            .take_while(|_| {
                db3.execute_batch("INSERT INTO hello VALUES(44);").unwrap();
                serialize_len(&mut db3) == initial_len
            })
            .count();
        assert_eq!(524, count_until_resize);

        // connection close should update ptr, capacity, length of serialized1
        let new_len = serialize_len(&mut db3);
        assert!(new_len > initial_len);
        mem::drop(db3);
        assert_eq!(new_len, serialized1.len());
        assert!(serialized1.capacity() > initial_cap);
        // serialized1.as_ptr() may differ, but it could also have grown in place
        let mut serialized2 = serialized1.clone();

        // serializing again should work
        db1.execute_batch("ATTACH DATABASE ':memory:' AS three;")?;
        let mut db1 = db1.into_borrowing();
        db1.deserialize_resizable(DatabaseName::Attached("three"), &mut serialized1)?;
        let count: u16 = db1.query_row("SELECT COUNT(*) FROM hello", NO_PARAMS, |r| r.get(0))?;
        assert_eq!(3, count);
        let count: u16 =
            db1.query_row("SELECT COUNT(*) FROM three.hello", NO_PARAMS, |r| r.get(0))?;
        assert_eq!(528, count);

        // test detach error handling for deserialize_resizable
        db1.execute_batch("DETACH DATABASE three")?;
        mem::drop(db1);
        assert_ne!(0, serialized1.capacity());
        assert_eq!(new_len, serialized1.len());

        // test detach error handling for deserialize_mut
        assert_ne!(0, serialized2.capacity());
        assert!(serialized1[..] == serialized2[..]);
        let mut db4 = Connection::open_in_memory()?.into_borrowing();
        db4.execute_batch("ATTACH DATABASE ':memory:' AS hello")?;
        db4.deserialize_mut(DatabaseName::Attached("hello"), &mut serialized2)?;
        db4.execute_batch("DETACH DATABASE hello")?;
        let debug = format!("{:?}", db4);
        mem::drop(db4);
        assert_ne!(0, serialized2.capacity());
        assert!(serialized1[..] == serialized2[..]);

        // Debug impl
        assert_eq!(
            &debug,
            "BorrowingConnection { conn: Connection { path: Some(\":memory:\") } }"
        );

        Ok(())
    }

    #[test]
    fn test_serialize_non_existing_db_name() {
        let db = Connection::open_in_memory().unwrap().into_borrowing();
        let sql = "BEGIN;
        CREATE TABLE hello(x INTEGER);
        INSERT INTO hello VALUES(1);
        INSERT INTO hello VALUES(2);
        INSERT INTO hello VALUES(3);
        END;";
        db.execute_batch(sql).unwrap();
        assert!(db
            .serialize_no_copy(DatabaseName::Attached("does not exist"))
            .unwrap()
            .is_none());
        assert!(db
            .serialize(DatabaseName::Attached("does not exist"))
            .unwrap()
            .is_none());
        let file = db.serialize(DatabaseName::Main).unwrap().unwrap();
        db.deserialize(DatabaseName::Attached("does not exist"), file)
            .unwrap_err();
    }

    fn serialize_len(conn: &mut BorrowingConnection) -> usize {
        conn.serialize_no_copy(DatabaseName::Main)
            .unwrap()
            .unwrap()
            .len()
    }
}
