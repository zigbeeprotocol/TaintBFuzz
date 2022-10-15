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
 * \brief Bittree implemented with a patricia trie.
 **************************************************************************/

#include "../../internals/e_acsl_private_assert.h"
#include "../internals/e_acsl_patricia_trie.h"

#include "e_acsl_bittree.h"

static pt_struct_t *bittree = NULL;

static void *bt_get_ptr(pt_leaf_t block) {
  return (void *)((bt_block *)block)->ptr;
}

static int bt_contains_ptr(pt_leaf_t block, void *ptr) {
  uintptr_t ptr_ui = (uintptr_t)ptr;
  bt_block *b = (bt_block *)block;
  return ptr_ui >= b->ptr
         && (ptr_ui < b->ptr + b->size || (b->size == 0 && ptr_ui == b->ptr));
}

/* erase information about initialization of a block */
void bt_clean_block_init(bt_block *ptr) {
  if (ptr->init_ptr != NULL) {
    private_free(ptr->init_ptr);
    ptr->init_ptr = NULL;
  }
  ptr->init_bytes = 0;
}

bt_block *bt_alloc_block(uintptr_t ptr, size_t size) {
  bt_block *res = private_malloc(sizeof(bt_block));
  res->ptr = (uintptr_t)ptr;
  res->size = size;
  res->init_ptr = NULL;
  res->init_bytes = 0;
  res->is_readonly = 0;
  res->is_freeable = 0;
#ifdef E_ACSL_DEBUG
  res->line = 0;
  res->file = "undefined";
#endif
#ifdef E_ACSL_TEMPORAL
  res->timestamp = NEW_TEMPORAL_TIMESTAMP();
  res->temporal_shadow = (size >= sizeof(void *)) ? private_malloc(size) : NULL;
#endif
  return res;
}

void bt_clean_and_free_block(bt_block *blk, int deallocate) {
  if (blk) {
    bt_clean_block_init(blk);
    if (deallocate) {
#ifdef E_ACSL_TEMPORAL
      private_free(blk->temporal_shadow);
#endif
      private_free(blk);
    }
  }
}

void bt_free_block(bt_block *blk) {
  bt_clean_and_free_block(blk, 1);
}

/* erase all information about a block */
static int bt_clean_with_deallocation = 0;
static void bt_clean_block(pt_leaf_t ptr) {
  bt_clean_and_free_block((bt_block *)ptr, bt_clean_with_deallocation);
}

static void bt_print_block(pt_leaf_t block) {
  if (block != NULL) {
    bt_block *b = (bt_block *)block;
    DLOG("%a; %lu Bytes; %slitteral; [init] : %d ", (char *)b->ptr, b->size,
         b->is_readonly ? "" : "not ", b->init_bytes);
    if (b->init_ptr != NULL) {
      unsigned i;
      for (i = 0; i < b->size / 8; i++)
        DLOG("%b ", b->init_ptr[i]);
    }
    DLOG("\n");
  }
}

void bt_insert(bt_block *b) {
  if (bittree == NULL) {
    bittree =
        pt_create(bt_get_ptr, bt_contains_ptr, bt_clean_block, bt_print_block);
  }
  pt_insert(bittree, (pt_leaf_t)b);
}

void bt_remove(bt_block *b) {
  DASSERT(bittree != NULL);
  pt_remove(bittree, (pt_leaf_t)b);
}

bt_block *bt_lookup(void *ptr) {
  if (bittree == NULL) {
    return NULL;
  } else {
    return pt_lookup(bittree, ptr);
  }
}

bt_block *bt_find(void *ptr) {
  if (bittree == NULL) {
    return NULL;
  } else {
    return pt_find(bittree, ptr);
  }
}

void bt_clean() {
  DASSERT(bittree != NULL);
  // Indicates to `bt_clean` (called by `pt_destroy`) that it should deallocate
  // the leaves of the tree
  bt_clean_with_deallocation = 1;
  pt_destroy(bittree);
  bt_clean_with_deallocation = 0;
  bittree = NULL;
}

/*********************/
/* DEBUG             */
/*********************/
#ifdef E_ACSL_DEBUG
void eacsl_bt_print_block(bt_block *ptr) {
  bt_print_block((pt_leaf_t)ptr);
}

void eacsl_bt_print_tree() {
  pt_print(bittree);
}
#endif
