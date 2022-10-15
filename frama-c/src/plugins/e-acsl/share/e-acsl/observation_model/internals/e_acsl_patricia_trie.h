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
 * \brief Patricia Trie API
***************************************************************************/

#ifndef E_ACSL_PATRICIA_TRIE
#define E_ACSL_PATRICIA_TRIE

#ifdef __FC_FEATURES_H
#  include <__fc_alloc_axiomatic.h>
#else
/*@ ghost extern int __fc_heap_status; */
#endif

/*! \brief Opaque pointer representing a leaf on the patricia trie. */
typedef void *pt_leaf_t;
/*! \brief Function pointer to a function that retrieves the pointer of a
    leaf. */
typedef void *(*get_ptr_fct_t)(pt_leaf_t);
/*! \brief Function pointer to a function that tests whether a leaf contains the
    given pointer. */
typedef int (*contains_ptr_fct_t)(pt_leaf_t, void *);
/*! \brief Function pointer to a function that cleans (i.e. free memory) the
    content of a leaf. */
typedef void (*clean_leaf_fct_t)(pt_leaf_t);
/*! \brief Function pointer to a function that prints the content of a leaf. */
typedef void (*print_leaf_fct_t)(pt_leaf_t);
/*! \brief Function pointer to a predicate function that returns true (!= 0) or
    false (== 0) for a given leaf. */
typedef int (*pt_predicate_t)(pt_leaf_t leaf);

/*! \brief Opaque structure of a patricia trie. */
typedef struct pt_struct pt_struct_t;

/*! \brief Create a patricia trie.
    \param get_ptr_fct Function to extract the pointer of a leaf.
    \param contains_ptr_fct Function to test if a leaf contains a pointer.
    \param clean_leaf_fct Function to clean the content of a leaf.
    \param print_leaf_fct Function to print the content of a leaf.
    \return The newly created patricia trie. */
/*@ requires \valid_function(get_ptr_fct_t get_ptr_fct);
  @ requires \valid_function(contains_ptr_fct_t contains_ptr_fct);
  @ requires \valid_function(clean_leaf_fct_t clean_leaf_fct);
  @ requires \valid_function(print_leaf_fct_t print_leaf_fct);
  @ allocates \result;
  @ assigns *\result \from get_ptr_fct, contains_ptr_fct, clean_leaf_fct,
                           print_leaf_fct;
  @ admit ensures \valid(\result); */
pt_struct_t *pt_create(get_ptr_fct_t get_ptr_fct,
                       contains_ptr_fct_t contains_ptr_fct,
                       clean_leaf_fct_t clean_leaf_fct,
                       print_leaf_fct_t print_leaf_fct);

/*! \brief Clean and destroy the patricia trie.
    \param pt The patricia trie to destroy. */
/*@ requires \valid(pt);
  @ frees pt; */
void pt_destroy(pt_struct_t *pt);

/*! \brief Insert a new leaf to the patricia trie.
    \param pt Patricia trie to update.
    \param leaf Leaf to add to the trie. */
/*@ requires \valid(pt);
  @ assigns __fc_heap_status \from __fc_heap_status;
  @ assigns *pt \from *pt, leaf, indirect:__fc_heap_status; */
void pt_insert(pt_struct_t *pt, pt_leaf_t leaf);

/*! \brief Remove an existing leaf from the patricia trie.
    \param pt Patricia trie to update.
    \param leaf Leaf to remove from the trie. */
/*@ requires \valid(pt);
  @ assigns __fc_heap_status \from __fc_heap_status;
  @ assigns *pt \from *pt, leaf, indirect:__fc_heap_status; */
void pt_remove(pt_struct_t *pt, pt_leaf_t leaf);

/*! \brief Remove all leaves that satisfy the given predicate from the patricia
    trie.
    \param pt Patricia trie to update.
    \param predicate Predicate to test the leaves of the trie. */
/*@ requires \valid(pt);
  @ requires \valid_function(pt_predicate_t predicate);
  @ assigns __fc_heap_status \from __fc_heap_status;
  @ assigns *pt \from *pt, indirect:predicate, indirect:__fc_heap_status; */
void pt_remove_if(pt_struct_t *pt, pt_predicate_t predicate);

/*! \brief Look for the leaf representing exactly the given pointer.

    Given the function `get_fct_ptr` provided at the trie creation and a leaf
    `l`, the leaf representing exactly the given pointer `ptr` is the leaf such
    that `get_fct_ptr(l) == ptr`.

    \param pt Patricia trie where to look for.
    \param ptr Pointer to look for in the leaves of the patricia trie.
    \return The leaf representing exactly the given pointer. */
/*@ requires \valid_read(pt);
  @ requires ptr != \null;
  @ assigns \result \from *pt, indirect:ptr; */
pt_leaf_t pt_lookup(const pt_struct_t *pt, void *ptr);

/*! \brief Look for the leaf containing the given pointer.

    Given the function `contains_ptr_fct` provided at the trie creation and a
    leaf `l`, the leaf containing the given pointer is the leaf such that
    `contains_ptr_fct(l, ptr) != 0`.

    \param pt Patricia trie where to look for.
    \param ptr Pointer to look for in the leaves of the patricia trie.
    \return The leaf containing the given pointer. */
/*@ requires \valid_read(pt);
  @ assigns \result \from *pt, indirect:ptr; */
pt_leaf_t pt_find(const pt_struct_t *pt, void *ptr);

/*! \brief Look for the first leaf that satisfies the given predicate.
    \param pt Patricia trie where to look for.
    \param predicate Predicate to test the leaves of the trie.
    \return The first leaf satisfying the given predicate. */
/*@ requires \valid_read(pt);
  @ requires \valid_function(pt_predicate_t predicate);
  @ assigns \result \from *pt, indirect:predicate; */
pt_leaf_t pt_find_if(const pt_struct_t *pt, pt_predicate_t predicate);

/*! \brief Clean the content of the given patricia trie.

    Contrary to `pt_destroy()`, this function removes all leaves of the trie but
    does not destroy the trie. The function `pt_insert()` can still be called on
    the trie afterward.

    \param pt Patricia trie to update. */
/*@ requires \valid(pt);
  @ assigns __fc_heap_status \from __fc_heap_status;
  @ assigns *pt \from *pt, indirect:__fc_heap_status; */
void pt_clean(pt_struct_t *pt);

#ifdef E_ACSL_DEBUG

/*! \brief Print the content of the given patricia trie.

    The function `print_leaf_fct` provided at the trie creation is used to print
    the leaves.

    \param pt The patricia trie to print. */
/*@ requires pt == \null || \valid_read(pt);
  @ assigns \nothing; */
void pt_print(const pt_struct_t *pt);

#endif // E_ACSL_DEBUG

#endif // E_ACSL_PATRICIA_TRIE
