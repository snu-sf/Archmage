#include "xorlist.h"

#include <stdint.h>
#include <stdlib.h>

// Performs the xor operation of two pointers
//  static intptr_t encrypt(node* prev, node* next) {
//      return ((intptr_t) prev ^ (intptr_t) next);
//  }

// static node* decrypt(intptr_t key, node* ptr) {
//   return (node*)(key ^ (intptr_t)ptr);
// }

void add_hd(node** hd_handler, node** tl_handler, long item) {
  node* entry = (node*)malloc(sizeof(node));
  node* hd = *hd_handler;
  node* tl = *tl_handler;
  entry->item = item;

  if (hd == NULL) {
    entry->link = 0;
    *hd_handler = *tl_handler = entry;
  } else {
    entry->link = (intptr_t)hd;
    hd->link = hd->link ^ (intptr_t)entry;
    *hd_handler = entry;
  }
}

void add_tl(node** hd_handler, node** tl_handler, long item) {
  node* entry = (node*)malloc(sizeof(node));
  node* hd = *hd_handler;
  node* tl = *tl_handler;
  entry->item = item;

  if (tl == NULL) {
    entry->link = 0;
    *hd_handler = *tl_handler = entry;
  } else {
    entry->link = (intptr_t)tl;
    tl->link = tl->link ^ (intptr_t)entry;
    *tl_handler = entry;
  }
}

long delete_hd(node** hd_handler, node** tl_handler) {
  long item = 0;
  node* hd_old = *hd_handler;

  if (hd_old != NULL) {
    item = hd_old->item;
    node* hd_new = (node*)(hd_old->link);
    *hd_handler = hd_new;

    if (hd_new == NULL) {
      *tl_handler = NULL;
    } else {
      intptr_t link = hd_new->link;
      hd_new->link = link ^ (intptr_t)hd_old;
    }
    free(hd_old);
  }
  return item;
}

long delete_tl(node** hd_handler, node** tl_handler) {
  long item = 0;
  node* tl_old = *tl_handler;

  if (tl_old != NULL) {
    item = tl_old->item;
    node* tl_new = (node*)(tl_old->link);
    *tl_handler = tl_new;
    if (tl_new == NULL) {
      *hd_handler = NULL;
    } else {
      intptr_t link = tl_new->link;
      tl_new->link = link ^ (intptr_t)tl_old;
    }
    free(tl_old);
  }
  return item;
}

// long search_hd(node** hd_handler, node** tl_handler, size_t index) {
//   node* cur;
//   node* prev = NULL;

//   cur = *hd_handler;

//   while (index--) {
//     if (cur == NULL) {
//       return 0;
//     } else {
//       node* next = decrypt(cur->link, prev);
//       prev = cur;
//       cur = next;
//     }
//   }

//   return cur->item;
// }

// // return ith element from handler. to_right determines the 0th index and
// // searching direction
// long search_tl(node** hd_handler, node** tl_handler, size_t index) {
//   node* cur;
//   node* prev = NULL;

//   cur = *tl_handler;

//   while (index--) {
//     if (cur == NULL) {
//       return 0;
//     } else {
//       node* next = decrypt(cur->link, prev);
//       prev = cur;
//       cur = next;
//     }
//   }

//   return cur->item;
// }