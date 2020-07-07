#include <stdlib.h>

int add(int a, int b) {
    char * buffer = malloc(a);
    return (int) buffer;
}

int* foo(int a) {
    return malloc(a);
}
