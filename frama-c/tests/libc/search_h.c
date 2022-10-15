// This code is the example from POSIX Programmer's Manual's TDELETE(3P) page.

#include <limits.h>
#include <search.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

struct element {      /* Pointers to these are stored in the tree. */
  int     count;
  char    string[];
};

void  *root = NULL;          /* This points to the root. */

int main(void) {
  char   str[_POSIX2_LINE_MAX+1];
  int    length = 0;
  struct element *elementptr;
  void   *node;
  void   print_node(const void *, VISIT, int);
  int    node_compare(const void *, const void *),
    delete_root(const void *, const void *);

  while (fgets(str, sizeof(str), stdin))  {
    /* Set element. */
    length = strlen(str);
    if (str[length-1] == '\n')
      str[--length] = '\0';
    elementptr = malloc(sizeof(struct element) + length + 1);
    strcpy(elementptr->string, str);
    elementptr->count = 1;
    /* Put element into the tree. */
    node = tsearch((void *)elementptr, &root, node_compare);
    if (node == NULL) {
      fprintf(stderr,
              "tsearch: Not enough space available\n");
      exit(EXIT_FAILURE);
    }
    else if (*(struct element **)node != elementptr) {
      /* A node containing the element already exists */
      (*(struct element **)node)->count++;
      free(elementptr);
    }
  }
  twalk(root, print_node);

  /* Delete all nodes in the tree */
  while (root != NULL) {
    elementptr = *(struct element **)root;
    printf("deleting node: string = %s,  count = %d\n",
           elementptr->string,
           elementptr->count);
    tdelete((void *)elementptr, &root, delete_root);
    free(elementptr);
  }

  return 0;
}

int node_compare(const void *node1, const void *node2) {
  return strcmp(((const struct element *) node1)->string,
                ((const struct element *) node2)->string);
}

int delete_root(const void *node1, const void *node2) {
  return 0;
}

void print_node(const void *ptr, VISIT order, int level) {
  const struct element *p = *(const struct element **) ptr;

  if (order == postorder || order == leaf)  {
    (void) printf("string = %s,  count = %d\n",
                  p->string, p->count);
  }
}
