#include <stdlib.h>
#include <stdio.h>
#include "sqlite3.h"

int add(int a, int b) {
    float x = atof("5.0") / 3.0;
    printf("Hello World from C %f\n", x);
    // char * buffer = malloc(a);
    // return (int) buffer;
    printf("a\n");
    my_sqlite_test();
    printf("b\n");
    return a + b;
}

int* foo(int a) {
    return malloc(a);
}

int my_sqlite_test() {
    // long double x = rand();
    // long double x;
    // x = (long double) rand();

    // below fails if not compiled with LONGDOUBLE_TYPE=double

    sqlite3_str *acc;
    va_list ap;
    sqlite3_str_vappendf(acc, "hello", ap);

    sqlite3_log(1, "he");

    sqlite3_config(SQLITE_CONFIG_SINGLETHREAD);

    sqlite3_initialize();

    void *heap_thing = sqlite3_malloc(8);
    printf("heap_thing %p\n", heap_thing);
    sqlite3_free(heap_thing);

    // sqlite3_log(1, "log msg");

    char *str = sqlite3_mprintf("hello from sqlite3 mprintf\n");
    printf(str);
    sqlite3_free(str);

   sqlite3 *db;
   char *zErrMsg = 0;
   int rc;
   char *sql;

   /* Open database */
   rc = sqlite3_open(":memory:", &db);
   
   if( rc ) {
      fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
      return(0);
   } else {
      fprintf(stdout, "Opened database successfully\n");
   }

   sqlite3_close(db);
   return 0;
}
