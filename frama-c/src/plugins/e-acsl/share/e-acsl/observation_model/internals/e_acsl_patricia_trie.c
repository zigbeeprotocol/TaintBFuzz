/**************************************************************************/
/*                                                                        */
/*  This file is part of the Frama-C's E-ACSL plug-in.                    */
/*                                                                        */
/*  Copyright (C) 2012-2021                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

/*! ***********************************************************************
 * \file
 * \brief Patricia Trie API Implementation
***************************************************************************/

#include <stdint.h>

#include "../../internals/e_acsl_concurrency.h"
#include "../../internals/e_acsl_config.h"
#include "../../internals/e_acsl_malloc.h"
#include "../../internals/e_acsl_private_assert.h"

#include "e_acsl_patricia_trie.h"

#if E_ACSL_OS_IS_LINUX
#  define WORDBITS __WORDSIZE
#elif E_ACSL_OS_IS_WINDOWS
// On windows, __WORDSIZE is not available
#  ifdef _WIN64
#    define WORDBITS 64
#  else
#    define WORDBITS 32
#  endif
#else
#  error "Unsupported OS"
#endif

#if WORDBITS == 16

static const uintptr_t PT_MASKS[] = {
    0x0,    0x8000, 0xc000, 0xe000, 0xf000, 0xf800, 0xfc00, 0xfe00, 0xff00,
    0xff80, 0xffc0, 0xffe0, 0xfff0, 0xfff8, 0xfffc, 0xfffe, 0xffff};

static const int PT_EQ[] = {0,  -1, 3,   -3, 6,   -5, 7,  -7, 12,
                            -9, 11, -11, 14, -13, 15, 16, -16};
static const int PT_NEQ[] = {0,  0, 1,   -2, 2,   -4, 5,   -6, 4,
                             -8, 9, -10, 10, -12, 13, -14, -15};

#elif WORDBITS == 32

static const uintptr_t PT_MASKS[] = {
    0x0,        0x80000000, 0xc0000000, 0xe0000000, 0xf0000000, 0xf8000000,
    0xfc000000, 0xfe000000, 0xff000000, 0xff800000, 0xffc00000, 0xffe00000,
    0xfff00000, 0xfff80000, 0xfffc0000, 0xfffe0000, 0xffff0000, 0xffff8000,
    0xffffc000, 0xffffe000, 0xfffff000, 0xfffff800, 0xfffffc00, 0xfffffe00,
    0xffffff00, 0xffffff80, 0xffffffc0, 0xffffffe0, 0xfffffff0, 0xfffffff8,
    0xfffffffc, 0xfffffffe, 0xffffffff};

static const int PT_EQ[] = {0,   -1,  3,   -3,  6,   -5,  7,   -7,  12,
                            -9,  11,  -11, 14,  -13, 15,  -15, 24,  -17,
                            19,  -19, 22,  -21, 23,  -23, 28,  -25, 27,
                            -27, 30,  -29, 31,  32,  -32};

static const int PT_NEQ[] = {0,   0,   1,   -2,  2,   -4,  5,   -6,  4,
                             -8,  9,   -10, 10,  -12, 13,  -14, 8,   -16,
                             17,  -18, 18,  -20, 21,  -22, 20,  -24, 25,
                             -26, 26,  -28, 29,  -30, -31};

#else /* WORDBITS == 64 */

// clang-format off
static const size_t PT_MASKS[] = {
0x0,0x8000000000000000,0xc000000000000000,0xe000000000000000,0xf000000000000000,
0xf800000000000000,0xfc00000000000000,0xfe00000000000000,0xff00000000000000,
0xff80000000000000,0xffc0000000000000,0xffe0000000000000,0xfff0000000000000,
0xfff8000000000000,0xfffc000000000000,0xfffe000000000000,0xffff000000000000,
0xffff800000000000,0xffffc00000000000,0xffffe00000000000,0xfffff00000000000,
0xfffff80000000000,0xfffffc0000000000,0xfffffe0000000000,0xffffff0000000000,
0xffffff8000000000,0xffffffc000000000,0xffffffe000000000,0xfffffff000000000,
0xfffffff800000000,0xfffffffc00000000,0xfffffffe00000000,0xffffffff00000000,
0xffffffff80000000,0xffffffffc0000000,0xffffffffe0000000,0xfffffffff0000000,
0xfffffffff8000000,0xfffffffffc000000,0xfffffffffe000000,0xffffffffff000000,
0xffffffffff800000,0xffffffffffc00000,0xffffffffffe00000,0xfffffffffff00000,
0xfffffffffff80000,0xfffffffffffc0000,0xfffffffffffe0000,0xffffffffffff0000,
0xffffffffffff8000,0xffffffffffffc000,0xffffffffffffe000,0xfffffffffffff000,
0xfffffffffffff800,0xfffffffffffffc00,0xfffffffffffffe00,0xffffffffffffff00,
0xffffffffffffff80,0xffffffffffffffc0,0xffffffffffffffe0,0xfffffffffffffff0,
0xfffffffffffffff8,0xfffffffffffffffc,0xfffffffffffffffe,0xffffffffffffffff};
// clang-format on

static const int PT_EQ[] = {
    0,   -1,  3,   -3,  6,   -5,  7,   -7,  12,  -9,  11,  -11, 14,
    -13, 15,  -15, 24,  -17, 19,  -19, 22,  -21, 23,  -23, 28,  -25,
    27,  -27, 30,  -29, 31,  -31, 48,  -33, 35,  -35, 38,  -37, 39,
    -39, 44,  -41, 43,  -43, 46,  -45, 47,  -47, 56,  -49, 51,  -51,
    54,  -53, 55,  -55, 60,  -57, 59,  -59, 62,  -61, 63,  64,  -64};

static const int PT_NEQ[] = {
    0,   0,   1,   -2,  2,   -4,  5,   -6,  4,   -8,  9,   -10, 10,
    -12, 13,  -14, 8,   -16, 17,  -18, 18,  -20, 21,  -22, 20,  -24,
    25,  -26, 26,  -28, 29,  -30, 16,  -32, 33,  -34, 34,  -36, 37,
    -38, 36,  -40, 41,  -42, 42,  -44, 45,  -46, 40,  -48, 49,  -50,
    50,  -52, 53,  -54, 52,  -56, 57,  -58, 58,  -60, 61,  -62, -63};

#endif

typedef struct pt_node {
  uintptr_t addr, mask;
  struct pt_node *left, *right, *parent;
  pt_leaf_t leaf;
  int is_leaf;
} pt_node_t;

typedef struct pt_struct {
  /*! \brief Root node of the trie. */
  pt_node_t *root;
  /*! \brief Function to extract the pointer of a leaf. */
  get_ptr_fct_t get_ptr_fct;
  /*! \brief Function to test if a leaf contains a pointer. */
  contains_ptr_fct_t contains_ptr_fct;
  /*! \brief Function to clean the content of a leaf. */
  clean_leaf_fct_t clean_leaf_fct;
  /*! \brief Function to print the content of a leaf. */
  print_leaf_fct_t print_leaf_fct;
  /*! \brief Read-write lock to concurrently access the trie. */
  E_ACSL_RWLOCK_DECL(lock);
} pt_struct_t;

/* common prefix of two addresses */
/*@ assigns \nothing;
  @ ensures \forall int i;
     0 <= i <= WORDBITS
     ==> (PT_MASKS[i] & a) == (PT_MASKS[i] & b)
     ==> \result >= PT_MASKS[i];
  @ ensures (a & \result) == (b & \result);
  @ ensures \exists int i; 0 <= i <= WORDBITS && \result == PT_MASKS[i];
  @*/
static uintptr_t pt_mask(uintptr_t a, uintptr_t b) {
  uintptr_t nxor = ~(a ^ b), ret;
  int i = WORDBITS / 2; /* dichotomic search, starting in the middle */

  /* if the current mask matches we use transition from PT_EQ, else from PT_NEQ
     we stop as soon as i is negative, meaning that we found the mask
     a negative element i from PT_EQ or PT_NEQ means stop and return PT_MASKS[-i] */
  /*@ loop invariant -WORDBITS <= i <= WORDBITS;
    @ loop assigns i;
    @*/
  while (i > 0) {
    //@ assert 0 < i <= WORDBITS;
    //@ assert \valid(PT_MASKS+i);
    if (nxor >= PT_MASKS[i])
      //@ assert \valid(PT_EQ+i);
      i = PT_EQ[i];
    else
      //@ assert \valid(PT_NEQ+i);
      i = PT_NEQ[i];
  }

  //@ assert -WORDBITS <= i <= 0;
  ret = PT_MASKS[-i];
  DASSERT((a & ret) == (b & ret));
  return ret;
}

pt_struct_t *pt_create(get_ptr_fct_t get_ptr_fct,
                       contains_ptr_fct_t contains_ptr_fct,
                       clean_leaf_fct_t clean_leaf_fct,
                       print_leaf_fct_t print_leaf_fct) {
  DASSERT(get_ptr_fct != NULL);
  DASSERT(contains_ptr_fct != NULL);
  DASSERT(clean_leaf_fct != NULL);
  DASSERT(print_leaf_fct != NULL);

  pt_struct_t *pt = private_malloc(sizeof(pt_struct_t));
  DASSERT(pt != NULL);
  pt->root = NULL;
  pt->get_ptr_fct = get_ptr_fct;
  pt->contains_ptr_fct = contains_ptr_fct;
  pt->clean_leaf_fct = clean_leaf_fct;
  pt->print_leaf_fct = print_leaf_fct;

  E_ACSL_RWINIT(pt->lock, NULL);
  return pt;
}

void pt_destroy(pt_struct_t *pt) {
  DASSERT(pt != NULL);
  pt_clean(pt);
  E_ACSL_RWDESTROY(pt->lock);
  private_free(pt);
}

/* called from pt_insert */
/* the returned node will be the sibling of the soon to be added node */
/*@ requires \valid_read(pt);
  @ requires \valid_read(pt->root);
  @ requires \valid_read(leaf);
  @ assigns \nothing;
  @ ensures \valid(\result); */
static pt_node_t *pt_most_similar_node(const pt_struct_t *pt, pt_leaf_t leaf) {
  DASSERT(pt != NULL);
  DASSERT(pt->root != NULL);
  DASSERT(leaf != NULL);
  pt_node_t *curr = pt->root;
  uintptr_t left_prefix, right_prefix;

  uintptr_t ptr = (uintptr_t)pt->get_ptr_fct(leaf);

  while (1) {
    if (curr->is_leaf) {
      return curr;
    }
    DASSERT(curr->left != NULL && curr->right != NULL);
    left_prefix = pt_mask(curr->left->addr & curr->left->mask, ptr);
    right_prefix = pt_mask(curr->right->addr & curr->right->mask, ptr);
    if (left_prefix > right_prefix) {
      curr = curr->left;
    } else if (right_prefix > left_prefix) {
      curr = curr->right;
    } else {
      return curr;
    }
  }
}

void pt_insert(pt_struct_t *pt, pt_leaf_t leaf) {
  DASSERT(pt != NULL);
  DASSERT(leaf != NULL);
  pt_node_t *new_leaf_node;

  E_ACSL_WLOCK(pt->lock);

  uintptr_t ptr = (uintptr_t)pt->get_ptr_fct(leaf);

  new_leaf_node = private_malloc(sizeof(pt_node_t));
  DASSERT(new_leaf_node != NULL);
  new_leaf_node->is_leaf = 1;
  new_leaf_node->addr = ptr;
  new_leaf_node->mask = PT_MASKS[WORDBITS]; /* ~0ul */
  new_leaf_node->left = NULL;
  new_leaf_node->right = NULL;
  new_leaf_node->parent = NULL;
  new_leaf_node->leaf = leaf;

  if (pt->root == NULL) {
    pt->root = new_leaf_node;
  } else {
    pt_node_t *sibling = pt_most_similar_node(pt, leaf), *parent, *aux;

    DASSERT(sibling != NULL);
    parent = private_malloc(sizeof(pt_node_t));
    DASSERT(parent != NULL);
    parent->is_leaf = 0;
    parent->addr = sibling->addr & new_leaf_node->addr;
    /*parent->mask = pt_mask(sibling->addr & sibling->mask, ptr);*/
    parent->leaf = NULL;
    if (new_leaf_node->addr <= sibling->addr) {
      parent->left = new_leaf_node;
      parent->right = sibling;
    } else {
      parent->left = sibling;
      parent->right = new_leaf_node;
    }
    new_leaf_node->parent = parent;

    if (sibling == pt->root) {
      parent->parent = NULL;
      parent->mask = pt_mask(sibling->addr & sibling->mask, ptr);
      pt->root = parent;
    } else {
      if (sibling->parent->left == sibling) {
        sibling->parent->left = parent;
      } else {
        sibling->parent->right = parent;
      }
      parent->parent = sibling->parent;

      /* necessary ? -- begin */
      aux = parent;
      aux->mask = pt_mask(aux->left->addr & aux->left->mask,
                          aux->right->addr & aux->right->mask);
      /* necessary ? -- end */
    }
    sibling->parent = parent;
    if (!sibling->is_leaf) {
      sibling->mask = pt_mask(sibling->left->addr & sibling->left->mask,
                              sibling->right->addr & sibling->right->mask);
    }

    DASSERT((parent->left == sibling && parent->right == new_leaf_node)
            || (parent->left == new_leaf_node && parent->right == sibling));
  }

  E_ACSL_RWUNLOCK(pt->lock);
}

/* called from pt_remove */
/* the leaf we are looking for has to be in the tree */
/*@ requires \valid_read(pt);
  @ requires \valid_read(pt->root);
  @ requires \valid_read(leaf);
  @ assigns \nothing;
  @ ensures \valid(\result);
  @ ensures \result->leaf == ptr; */
static pt_node_t *pt_get_leaf_node_from_leaf(const pt_struct_t *pt,
                                             pt_leaf_t leaf) {
  DASSERT(pt != NULL);
  DASSERT(pt->root != NULL);
  DASSERT(leaf != NULL);
  pt_node_t *curr = pt->root;

  uintptr_t ptr = (uintptr_t)pt->get_ptr_fct(leaf);

  /*@ loop assigns curr; */
  while (!curr->is_leaf) {
    // the prefix is consistent
    DASSERT((curr->addr & curr->mask) == (ptr & curr->mask));
    // two children
    DASSERT(curr->left != NULL && curr->right != NULL);
    // the prefix of one child is consistent
    if ((curr->right->addr & curr->right->mask) == (ptr & curr->right->mask)) {
      curr = curr->right;
    } else if ((curr->left->addr & curr->left->mask)
               == (ptr & curr->left->mask)) {
      curr = curr->left;
    } else {
      private_abort("Unreachable\n");
    }
  }
  DASSERT(curr->is_leaf);
  DASSERT(curr->leaf == leaf);
  return curr;
}

/** Remove the given leaf node from the patricia trie.
 *
 * Internal function for `pt_remove()` and `pt_remove_if()`. The function will
 * delete the given leaf node and copy its sibling if it exists to the parent
 * node.
 */
static void pt_remove_leaf_node(pt_struct_t *pt,
                                pt_node_t *leaf_node_to_delete) {
  DASSERT(leaf_node_to_delete != NULL);
  DASSERT(leaf_node_to_delete->is_leaf);

  if (leaf_node_to_delete->parent == NULL) {
    // the leaf is the root
    pt->root = NULL;
  } else {
    pt_node_t *sibling, *parent;
    parent = leaf_node_to_delete->parent;
    sibling =
        (leaf_node_to_delete == parent->left) ? parent->right : parent->left;
    DASSERT(sibling != NULL);
    // copying all sibling's fields into the parent's
    parent->is_leaf = sibling->is_leaf;
    parent->addr = sibling->addr;
    parent->mask = sibling->mask;
    parent->left = sibling->left;
    parent->right = sibling->right;
    parent->leaf = sibling->leaf;
    if (!sibling->is_leaf) {
      sibling->left->parent = parent;
      sibling->right->parent = parent;
    }
    private_free(sibling);
    /* necessary ? -- begin */
    if (parent->parent != NULL) {
      parent->parent->mask =
          pt_mask(parent->parent->left->addr & parent->parent->left->mask,
                  parent->parent->right->addr & parent->parent->right->mask);
    }
    /* necessary ? -- end */
  }
  pt->clean_leaf_fct(leaf_node_to_delete->leaf);
  private_free(leaf_node_to_delete);
}

void pt_remove(pt_struct_t *pt, pt_leaf_t leaf) {
  DASSERT(pt != NULL);

  E_ACSL_WLOCK(pt->lock);

  pt_node_t *leaf_node_to_delete = pt_get_leaf_node_from_leaf(pt, leaf);
  DASSERT(leaf_node_to_delete->leaf == leaf);

  pt_remove_leaf_node(pt, leaf_node_to_delete);

  E_ACSL_RWUNLOCK(pt->lock);
}

/** Starting at `node`, remove all leaves that satisfy the given predicate from
 * the patricia trie. Return 1 if `node` is a leaf that is removed, 0
 * otherwise.
 * Internal function for `pt_remove_if()`. */
int pt_remove_node_if(pt_struct_t *pt, pt_node_t *node,
                      pt_predicate_t predicate) {
  DASSERT(pt != NULL);
  if (node != NULL) {
    if (node->is_leaf) {
      if (predicate(node->leaf)) {
        pt_remove_leaf_node(pt, node);
        return 1;
      }
    } else {
      // If `node->left` is a leaf that is removed, then `node->right` is
      // copied to node and we have `node->left == \old(node->right->left)`
      // (see `pt_remove_leaf_node()̀).
      // We need to call `pt_remove_node_if()` on `node->left` until it is not
      // a removed leaf.
      while (pt_remove_node_if(pt, node->left, predicate)) {}
      pt_remove_node_if(pt, node->right, predicate);
    }
  }
  return 0;
}

void pt_remove_if(pt_struct_t *pt, pt_predicate_t predicate) {
  DASSERT(pt != NULL);
  E_ACSL_WLOCK(pt->lock);
  pt_remove_node_if(pt, pt->root, predicate);
  E_ACSL_RWUNLOCK(pt->lock);
}

pt_leaf_t pt_lookup(const pt_struct_t *pt, void *ptr) {
  DASSERT(pt != NULL);
  DASSERT(ptr != NULL);

  E_ACSL_RLOCK(pt->lock);
  DASSERT(pt->root != NULL);

  pt_leaf_t res;
  pt_node_t *tmp = pt->root;

  /*@ loop assigns tmp;
    @*/
  while (!tmp->is_leaf) {
    // if the ptr we are looking for does not share the prefix of tmp
    if ((tmp->addr & tmp->mask) != ((uintptr_t)ptr & tmp->mask)) {
      res = NULL;
      goto end;
    }

    // two children
    DASSERT(tmp->left != NULL && tmp->right != NULL);
    // the prefix of one child is consistent
    if ((tmp->right->addr & tmp->right->mask)
        == ((uintptr_t)ptr & tmp->right->mask)) {
      tmp = tmp->right;
    } else if ((tmp->left->addr & tmp->left->mask)
               == ((uintptr_t)ptr & tmp->left->mask)) {
      tmp = tmp->left;
    } else {
      res = NULL;
      goto end;
    }
  }

  if (pt->get_ptr_fct(tmp->leaf) != ptr) {
    res = NULL;
  }

end:
  E_ACSL_RWUNLOCK(pt->lock);
  return res;
}

pt_leaf_t pt_find(const pt_struct_t *pt, void *ptr) {
  DASSERT(pt != NULL);
  E_ACSL_RLOCK(pt->lock);

  pt_leaf_t res;
  if (pt->root == NULL || ptr == NULL) {
    res = NULL;
    goto end;
  }

  pt_node_t *tmp = pt->root;
  pt_node_t *other_choice = NULL;

  while (1) {
    if (tmp->is_leaf) {
      /* tmp cannot contain ptr because its begin addr is higher */
      if (tmp->addr > (uintptr_t)ptr) {
        res = NULL;
        goto end;
      }

      /* tmp->addr <= ptr, tmp may contain ptr */
      else if (pt->contains_ptr_fct(tmp->leaf, ptr)) {
        res = tmp->leaf;
        goto end;
      }
      /* tmp->addr <= ptr, but tmp does not contain ptr */
      else {
        res = NULL;
        goto end;
      }
    }

    DASSERT(tmp->left != NULL && tmp->right != NULL);

    /* the right child has the highest address, so we test it first */
    if ((tmp->right->addr & tmp->right->mask)
        <= ((uintptr_t)ptr & tmp->right->mask)) {
      other_choice = tmp->left;
      tmp = tmp->right;
    } else if ((tmp->left->addr & tmp->left->mask)
               <= ((uintptr_t)ptr & tmp->left->mask)) {
      tmp = tmp->left;
    } else {
      if (other_choice == NULL) {
        res = NULL;
        goto end;
      } else {
        tmp = other_choice;
        other_choice = NULL;
      }
    }
  }

end:
  E_ACSL_RWUNLOCK(pt->lock);
  return res;
}

static pt_leaf_t pt_find_if_rec(pt_node_t *node, pt_predicate_t predicate) {
  DASSERT(node != NULL);
  if (node->is_leaf) {
    return predicate(node->leaf) ? node->leaf : NULL;
  } else {
    pt_node_t *result = pt_find_if_rec(node->left, predicate);
    if (result == NULL) {
      result = pt_find_if_rec(node->right, predicate);
    }
    return result;
  }
}

pt_leaf_t pt_find_if(const pt_struct_t *pt, pt_predicate_t predicate) {
  DASSERT(pt != NULL);
  E_ACSL_RLOCK(pt->lock);

  pt_leaf_t res;
  if (pt->root == NULL) {
    res = NULL;
  } else {
    res = pt_find_if_rec(pt->root, predicate);
  }

  E_ACSL_RWUNLOCK(pt->lock);
  return res;
}

static void pt_clean_rec(const pt_struct_t *pt, pt_node_t *ptr) {
  if (ptr == NULL) {
    return;
  } else if (ptr->is_leaf) {
    pt->clean_leaf_fct(ptr->leaf);
    ptr->leaf = NULL;
  } else {
    pt_clean_rec(pt, ptr->left);
    pt_clean_rec(pt, ptr->right);
    ptr->left = ptr->right = NULL;
  }
  private_free(ptr);
}

void pt_clean(pt_struct_t *pt) {
  DASSERT(pt != NULL);
  E_ACSL_WLOCK(pt->lock);
  pt_clean_rec(pt, pt->root);
  pt->root = NULL;
  E_ACSL_RWUNLOCK(pt->lock);
}

#ifdef E_ACSL_DEBUG
static void pt_print_node(const pt_struct_t *pt, pt_node_t *node, int depth) {
  if (node == NULL) {
    return;
  }
  // Indentation
  for (int i = 0; i < depth; ++i) {
    DLOG("  ");
  }
  // Print node
  if (node->is_leaf) {
    pt->print_leaf_fct(node->leaf);
  } else {
    DLOG("%p -- %p\n", (void *)node->mask, (void *)node->addr);
    pt_print_node(pt, node->left, depth + 1);
    pt_print_node(pt, node->right, depth + 1);
  }
}

void pt_print(const pt_struct_t *pt) {
  RTL_IO_LOCK();
  DLOG("------------DEBUG\n");
  if (pt != NULL) {
    E_ACSL_RLOCK(pt->lock);
    pt_print_node(pt, pt->root, 0);
    E_ACSL_RWUNLOCK(pt->lock);
  } else {
    DLOG("Patricia trie is NULL\n");
  }
  DLOG("-----------------\n");
  RTL_IO_UNLOCK();
}
#endif // E_ACSL_DEBUG
