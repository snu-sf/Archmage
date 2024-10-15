#ifndef _XORLIST_H_
#define _XORLIST_H_

#include <stdint.h>
#include <stdlib.h>

typedef struct _Node {
  long item;
  intptr_t link;
} node;

void add_hd(node **, node **, long);

void add_tl(node **, node **, long);

long delete_hd(node **, node **);

long delete_tl(node **, node **);

// long search_hd(node **, node **, size_t);
// long search_tl(node **, node **, size_t);

#endif /* _XORLIST_H_ */
