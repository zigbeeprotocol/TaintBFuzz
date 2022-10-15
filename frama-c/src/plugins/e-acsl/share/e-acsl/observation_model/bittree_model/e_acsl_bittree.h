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
 * \brief Bittree API
***************************************************************************/

#ifndef E_ACSL_BITTREE
#define E_ACSL_BITTREE

#include <stddef.h>
#include <stdint.h>

/* Public API {{{ */
/* Debug */
#ifdef E_ACSL_DEBUG
#  define eacsl_bt_print_block export_alias(bt_print_block)
#  define eacsl_bt_print_tree  export_alias(bt_print_tree)
#endif
/* }}} */

/*! \brief Structure representing an allocated memory block */
struct bt_block {
  uintptr_t ptr;           //!< Base address
  size_t size;             //!< Block length (in bytes)
  unsigned char *init_ptr; //!< Per-bit initialization
  size_t init_bytes;       //!< Number of initialized bytes within a block
  int is_readonly;         //!< True if a block is marked read-only
  int is_freeable;         //!< True if a block can be de-allocated using `free`
#ifdef E_ACSL_DEBUG
  size_t line; //!< Line number where this block was recorded
  char *file;  //!< File name where this block was recorded
#endif
#ifdef E_ACSL_TEMPORAL
  uint32_t timestamp;    //!< Temporal timestamp of a block's creation
  void *temporal_shadow; //!< Temporal shadow for storing referent numbers
#endif
};

typedef struct bt_block bt_block;

/*! \brief Remove a block from the structure */
void bt_remove(bt_block *b);

/*! \brief Add a block to the structure */
void bt_insert(bt_block *b);

/*! \brief Look-up a memory block by its base address
  NB: The function assumes that such a block exists. */
bt_block *bt_lookup(void *ptr);

/*! \brief Find a memory block containing a given memory address
 *
 * Return block B such that:
 *  `\base_addr(B->ptr) <= ptr < (\base_addr(B->ptr) + size)`
 *  or NULL if such a block does not exist. */
bt_block *bt_find(void *ptr);

/*! \brief Erase the contents of the structure */
void bt_clean(void);

/*! \brief Erase information about a block's initialization */
void bt_clean_block_init(bt_block *b);

/*! \brief Allocates a `bt_block` for a block of memory at address `ptr` and
    with the given size. */
bt_block *bt_alloc_block(uintptr_t ptr, size_t size);

/*! \brief Frees the given `bt_block`. */
void bt_free_block(bt_block *blk);

#ifdef E_ACSL_DEBUG
/*! \brief Print information about a given block */
void eacsl_bt_print_block(bt_block *b);

/*! \brief Print the contents of the entire bittree */
/*@ assigns \nothing; */
void eacsl_bt_print_tree();
#endif

#endif // E_ACSL_BITTREE
