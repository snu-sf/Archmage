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

long bar(uintptr_t key, uintptr_t ptr) {
  long *q = decode(key, ptr);
  return *q;
}

long foo(uintptr_t key, long *p) {
  *p = 42;
  uintptr_t qi = encode(key, p);
  long ret = bar(key, qi);
  return ret;
}
