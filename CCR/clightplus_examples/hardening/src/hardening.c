#include <stdint.h>

uintptr_t encode(uintptr_t key, void *ptr) {
  uintptr_t encoded;
  encoded = (uintptr_t)ptr ^ key;
  return encoded;
}

void *decode(uintptr_t key, uintptr_t ptr) {
  void *decoded;
  decoded = (void *)(ptr ^ key);
  return decoded;
}

// Function that uses encoded pointer
long bar(long k, uintptr_t ep, long x) {
    long *q = decode(k, ep);
    *q = x;
    return *q;                   
}

// Function that creates encoded pointer
long foo(long *p, long k, long x) {
    uintptr_t ep = encode(k, p);  // pointer encoding
    bar(k, ep, x);     // pass encoded pointer
    return *p;  // *p = x
}

/* long bar(uintptr_t key, uintptr_t ptr) { */
/*   long *q = decode(key, ptr); */
/*   return *q; */
/* } */

/* long foo(uintptr_t key, long *p) { */
/*   *p = 42; */
/*   uintptr_t qi = encode(key, p); */
/*   long ret = bar(key, qi); */
/*   return ret; */
/* } */
