#include "xorlist.h"

int main() {
  node *head = NULL, *tail = NULL;
  long item = 1;
  add_hd(&head, &tail, 3);
  add_tl(&head, &tail, 7);
  item = item * delete_hd(&head, &tail);
  item = item * delete_tl(&head, &tail);
  return item;
}