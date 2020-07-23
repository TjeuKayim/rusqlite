//! `feature = "deserialize"` Serialize and deserialize interfaces.
//!
//! This API is only available when SQLite is compiled with `SQLITE_ENABLE_DESERIALIZE`.
//! These functions create and read a serialized file in-memory, useful on platforms without
//! a real file system like WebAssembly or Cloud Functions.
//!
//! For large in-memory database files, you probably don't want to copy or reallocate
//! because that would temporarily double the required memory. Possible solutions:
//!
//! * While downloading a `.sqlite` file, write the buffers directly to [`SerializedDb`]
//!   and pass that to [`Connection::deserialize`]
//!   (ownership is tranferred to SQLite without copying).
//! * Let SQLite borrow a large Rust-allocated vector using
//!   [`BorrowingConnection::deserialize_read_only`].
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

use std::collections::HashMap;
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::{alloc, fmt, iter, mem, ops, slice};

use crate::ffi;
use crate::{Connection, DatabaseName, Result};

impl Connection {
    /// Disconnect from database and reopen as an in-memory database based on [`SerializedDb`].
    pub fn deserialize(&mut self, db: DatabaseName<'_>, data: SerializedDb) -> Result<()> {
        let result = unsafe {
            self.deserialize_with_flags(
                db,
                &data,
                data.cap,
                DeserializeFlags::FREE_ON_CLOSE | DeserializeFlags::RESIZEABLE,
            )
        };
        mem::forget(data);
        result
    }

    /// Wraps the `Connection` in `BorrowingConnection` to connect it to borrowed serialized memory
    /// using [`BorrowingConnection::deserialize_read_only`].
    pub fn into_borrowing(self) -> BorrowingConnection<'static> {
        BorrowingConnection::new(self)
    }

    /// Disconnect from database and reopen as an in-memory database based on the serialization data.
    ///
    /// # Safety
    ///
    /// The reference `data` must last for the lifetime of this connection.
    /// `cap` must be the size of the allocation, and `cap >= data.len()`.
    ///
    /// If the data is not mutably borrowed, set [`DeserializeFlags::READ_ONLY`].
    /// If SQLite allocated the memory, consider setting [`DeserializeFlags::FREE_ON_CLOSE`]
    /// and/or [`DeserializeFlags::RESIZEABLE`].
    ///
    /// See the C Interface Specification [Deserialize a database](https://www.sqlite.org/c3ref/deserialize.html).
    pub unsafe fn deserialize_with_flags(
        &mut self,
        db: DatabaseName<'_>,
        data: &[u8],
        cap: usize,
        flags: DeserializeFlags,
    ) -> Result<()> {
        let path = &mut self.path;
        let mut c = self.db.borrow_mut();
        let db = db.to_cstring()?;
        let rc = ffi::sqlite3_deserialize(
            c.db(),
            db.as_ptr(),
            data.as_ptr() as *mut _,
            data.len() as _,
            cap as _,
            flags.bits() as _,
        );
        c.decode_result(rc).map(|_| {
            *path = Some(":memory:".into());
        })
    }

    /// Return the serialization of a database, or `None` when [`DatabaseName`] does not exist.
    pub fn serialize(&self, db: DatabaseName<'_>) -> Result<Option<SerializedDb>> {
        unsafe {
            self.serialize_with_flags(db, SerializeFlags::empty())
                .map(|r| {
                    r.map(|(data, len)| {
                        let cap = ffi::sqlite3_msize(data.as_ptr() as _) as _;
                        SerializedDb::from_raw(data, len, cap)
                    })
                })
        }
    }

    /// Borrow the serialization of a database using the flag [`ffi::SQLITE_SERIALIZE_NOCOPY`].
    /// This returns `Ok(None)` when [`DatabaseName`] does not exist or no in-memory serialization is present.
    pub fn serialize_no_copy(&mut self, db: DatabaseName<'_>) -> Result<Option<&mut [u8]>> {
        unsafe {
            self.serialize_with_flags(db, SerializeFlags::NO_COPY)
                .map(|r| r.map(|(data, len)| slice::from_raw_parts_mut(data.as_ptr(), len)))
        }
    }

    /// The serialization is the same sequence of bytes which would be written to disk
    /// if the database where backed up to disk.
    ///
    /// Returns `Ok(None)` when [`DatabaseName`] does not exist or malloc/prepare fails.
    ///
    /// # Safety
    ///
    /// If [`SerializeFlags::NO_COPY`] is set, this returns a pointer to memory that SQLite is currently using
    /// (or `Ok(None)` if this is not available).
    /// In that case, the returned `SerializedDb` mutably borrows `Connection`,
    /// [`std::mem::forget()`] one of them to prevent double free.
    ///
    /// See the C Interface Specification [Serialize a database](https://www.sqlite.org/c3ref/serialize.html).
    unsafe fn serialize_with_flags(
        &self,
        db: DatabaseName<'_>,
        flags: SerializeFlags,
    ) -> Result<Option<(NonNull<u8>, usize)>> {
        let c = self.db.borrow();
        let db = db.to_cstring()?;
        let mut len = 0;
        let data = ffi::sqlite3_serialize(
            c.db(),
            db.as_ptr(),
            &mut len as *mut _ as *mut _,
            flags.bits() as _,
        );
        Ok(NonNull::new(data).map(|d| (d, len)))
    }
}

/// Wrap `Connection` with lifetime constraint to borrow from serialized memory.
/// Use [`Connection::into_borrowing`] to obtain one.
#[derive(Debug)]
pub struct BorrowingConnection<'a> {
    conn: Connection,
    mut_slices: HashMap<DatabaseName<'a>, *mut Vec<u8>>,
    phantom: PhantomData<&'a [u8]>,
}

impl<'a> BorrowingConnection<'a> {
    fn new(conn: Connection) -> Self {
        BorrowingConnection {
            conn,
            mut_slices: HashMap::new(),
            phantom: PhantomData,
        }
    }

    /// Disconnect from database and reopen as an read-only in-memory database based on a borrowed slice
    /// (using the flag [`ffi::SQLITE_DESERIALIZE_READONLY`]).
    pub fn deserialize_read_only(&mut self, db: DatabaseName<'_>, data: &'a [u8]) -> Result<()> {
        unsafe { self.deserialize_with_flags(db, data, data.len(), DeserializeFlags::READ_ONLY) }
    }

    /// Disconnect from database and reopen as an in-memory database based on a borrowed vector.
    /// If the capacity is reached, SQLite can't reallocate, so it throws [`crate::ErrorCode::DiskFull`].
    /// Before the connection drops, the vector length is updated.
    pub fn deserialize_borrow(
        &mut self,
        db: DatabaseName<'a>,
        data: &'a mut Vec<u8>,
    ) -> Result<()> {
        if let Some(prev) = self.mut_slices.insert(db, data as *mut _) {
            Self::update_serialized_len(&mut self.conn, db, prev);
        }
        unsafe { self.deserialize_with_flags(db, data, data.len(), DeserializeFlags::empty()) }
    }

    fn update_serialized_len(conn: &mut Connection, db: DatabaseName<'a>, vec: *mut Vec<u8>) {
        // SQLite could have grown or shrunk the database length,
        // but could also have detached it.
        let new_len = if let Ok(Some(new)) = conn.serialize_no_copy(db) {
            new.len()
        } else {
            // On failure, the safest thing to do is setting the length to zero.
            // This way no uninitialized memory is exposed.
            0
        };
        unsafe {
            (*vec).set_len(new_len);
        }
    }
}

impl Drop for BorrowingConnection<'_> {
    fn drop(&mut self) {
        for (db, vec) in self.mut_slices.iter_mut() {
            Self::update_serialized_len(&mut self.conn, *db, *vec);
        }
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

/// Serialized database content (a growable vector of `u8`) owned by SQLite.
/// Used for [`Connection::serialize`] and [`Connection::deserialize`].
/// Memory allocation is handled by `sqlite3_malloc64`, `sqlite3_realloc64`, `sqlite3_msize` and `sqlite3_free`.
/// ```
/// # use rusqlite::deserialize::SerializedDb;
/// let mut serialized = SerializedDb::new();
/// serialized.extend(vec![1, 2, 3]);
/// assert_eq!(serialized[1], 2);
/// ```
pub struct SerializedDb {
    data: NonNull<u8>,
    len: usize,
    cap: usize,
}

impl Drop for SerializedDb {
    fn drop(&mut self) {
        if self.cap > 0 {
            unsafe { ffi::sqlite3_free(self.data.as_ptr() as *mut _) };
        }
    }
}

impl SerializedDb {
    /// Create a new, empty `SerializedDb`. It will not allocate until extended.
    pub fn new() -> Self {
        unsafe { Self::from_raw(NonNull::dangling(), 0, 0) }
    }

    /// Create a new `SerializedDb` from a raw pointer, length and capacity.
    /// # Safety
    /// The pointer must be allocated by `sqlite3_malloc64()` or `sqlite3_malloc()`
    /// for `cap` number of bytes.
    /// # Panics
    /// Panics if `len` overflows the allocation (`len > cap`).
    pub unsafe fn from_raw(data: NonNull<u8>, len: usize, cap: usize) -> Self {
        assert!(len <= cap);
        SerializedDb { data, len, cap }
    }

    /// Number of bytes in the deserialization.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns if `len()` equals zero.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Set `len`, the number of bytes in the deserialization.
    /// # Safety
    /// This can expose uninitialized memory when increasing the length.
    /// # Panics
    /// `len` must not overflows the allocation, panics if `len > capacity`.
    pub unsafe fn set_len(&mut self, len: usize) {
        assert!(len <= self.cap, "len overflows capacity");
        self.len = len;
    }

    /// The number of allocated bytes.
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Grow or shrink the allocation.
    /// `len` is capped if it would overflow.
    pub fn set_capacity(&mut self, cap: usize) {
        if self.len > self.cap {
            self.len = self.cap;
        }
        if cap == 0 {
            *self = Self::new();
            return;
        }
        unsafe {
            let p = if self.cap == 0 {
                ffi::sqlite3_malloc64(cap as _)
            } else {
                ffi::sqlite3_realloc64(self.data.as_ptr() as _, cap as _)
            };
            self.data = NonNull::new(p)
                .unwrap_or_else(|| {
                    alloc::handle_alloc_error(alloc::Layout::from_size_align_unchecked(cap, 1))
                })
                .cast();
            self.cap = ffi::sqlite3_msize(self.data.as_ptr() as _) as _;
            assert!(self.cap >= cap);
        };
    }
}

impl Default for SerializedDb {
    fn default() -> Self {
        Self::new()
    }
}

impl iter::Extend<u8> for SerializedDb {
    fn extend<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.set_capacity(iter.size_hint().0);
        let mut index = self.len();
        for byte in iter {
            let next = index + 1;
            if next > self.cap {
                self.set_capacity(next * 2);
            }
            unsafe { self.set_len(next) };
            self[index] = byte;
            index = next;
        }
    }
}

impl ops::Deref for SerializedDb {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.data.as_ptr(), self.len) }
    }
}

impl ops::DerefMut for SerializedDb {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.data.as_ptr(), self.len) }
    }
}

impl fmt::Debug for SerializedDb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SerializedDb")
            .field("len", &self.len)
            .field("cap", &self.cap)
            .finish()
    }
}

bitflags::bitflags! {
    /// Flags for [`Connection::deserialize_with_flags`].
    #[repr(C)]
    pub struct DeserializeFlags: ::std::os::raw::c_int {
        /// The deserialized database should be treated as read-only.
        const READ_ONLY = ffi::SQLITE_DESERIALIZE_READONLY;
        /// SQLite should take ownership of this memory and automatically free it when it has finished using it.
        const FREE_ON_CLOSE = ffi::SQLITE_DESERIALIZE_FREEONCLOSE;
        /// SQLite is allowed to grow the size of the database using `sqlite3_realloc64()`.
        const RESIZEABLE = ffi::SQLITE_DESERIALIZE_RESIZEABLE;
    }
}

bitflags::bitflags! {
    /// Flags for [`Connection::serialize_with_flags`].
    #[repr(C)]
    struct SerializeFlags: ::std::os::raw::c_int {
        /// Return a reference to the contiguous in-memory database that the connection
        /// currently uses instead of making a copy of the database.
        const NO_COPY = ffi::SQLITE_SERIALIZE_NOCOPY;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Connection, DatabaseName, Result, NO_PARAMS};

    #[test]
    pub fn test_serialize() {
        let mut db = Connection::open_in_memory().unwrap();
        let sql = "BEGIN;
            CREATE TABLE foo(x INTEGER);
            INSERT INTO foo VALUES(1);
            INSERT INTO foo VALUES(2);
            INSERT INTO foo VALUES(3);
            END;";
        db.execute_batch(sql).unwrap();
        let serialized = db.serialize(DatabaseName::Main).unwrap().unwrap();

        // create a new db and import the serialized data
        let mut db2 = Connection::open_in_memory().unwrap();
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
        let mut serialized = SerializedDb::new();
        serialized.extend(borrowed_serialized.iter().cloned());

        // create a third db and import the serialized data
        let mut db3 = Connection::open_in_memory().unwrap();
        db3.deserialize(DatabaseName::Main, serialized).unwrap();
        let mut query = db3.prepare("SELECT x FROM foo").unwrap();
        let results: Result<Vec<u16>> = query
            .query_map(NO_PARAMS, |row| row.get(0))
            .unwrap()
            .collect();
        assert_eq!(vec![1, 2, 3, 4], results.unwrap());
    }

    #[test]
    pub fn test_serialize_read_only() {
        let db = Connection::open_in_memory().unwrap();
        let sql = "BEGIN;
            CREATE TABLE foo(x INTEGER);
            INSERT INTO foo VALUES(1);
            INSERT INTO foo VALUES(2);
            INSERT INTO foo VALUES(3);
            END;";
        db.execute_batch(sql).unwrap();
        let serialized = db.serialize(DatabaseName::Main).unwrap().unwrap();
        // copy to Vec and create new SerializedDb
        let serialized_vec = Vec::from(&serialized[..]);
        let mut serialized = SerializedDb::new();
        serialized.extend(serialized_vec);

        // create a new db and import the serialized data
        let mut db2 = Connection::open_in_memory().unwrap();
        unsafe {
            db2.deserialize_with_flags(
                DatabaseName::Main,
                &serialized,
                serialized.cap,
                DeserializeFlags::READ_ONLY,
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
    pub fn test_serialized_db() {
        let s = SerializedDb::default();
        assert!(s.is_empty());
        let mut s = SerializedDb::new();
        assert_eq!(0, s.len());
        assert!(s.is_empty());
        assert_eq!(0, s.capacity());
        assert_eq!(&[] as &[u8], &s[..]);
        s.extend(vec![1u8, 2, 33]);
        assert_eq!(&[1u8, 2, 33], &s[..]);
        assert!(!s.is_empty());
        assert_eq!(
            format!("SerializedDb {{ len: 3, cap: {} }}", s.capacity()),
            format!("{:?}", &s)
        );
        s[2] = 3;
        s.extend(vec![4, 5, 6]);
        assert_eq!(&[1u8, 2, 3, 4, 5, 6], &s[..]);
        unsafe { s.set_len(3) };
        assert_eq!(&[1u8, 2, 3], &s[..]);
        unsafe { s.set_len(0) };
        assert_eq!(&[] as &[u8], &s[..]);
        assert!((6..300).contains(&s.capacity()));
        s.extend(iter::repeat(5).take(400));
        s.extend(iter::repeat(5).take(400));
        assert_eq!(s.len(), 800);
        s.set_capacity(0);
        assert_eq!(0, s.capacity());
    }

    #[test]
    #[should_panic]
    pub fn test_serialized_db_overflow_len() {
        let mut s = SerializedDb::new();
        unsafe { s.set_len(1) };
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
        let mut db = Connection::open_in_memory()?.into_borrowing();
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
}
