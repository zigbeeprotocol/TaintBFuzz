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
 * \brief  Observation model API
 *
 * Functions and variables with non-static linkage used for memory
 * observation.
 **************************************************************************/

#ifndef E_ACSL_OBSERVATION_MODEL_H
#define E_ACSL_OBSERVATION_MODEL_H

#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>

#include "../internals/e_acsl_alias.h"
#include "e_acsl_heap.h"

#ifdef __FC_FEATURES_H
#  include <__fc_alloc_axiomatic.h>
#else
/*@ ghost extern int __fc_heap_status; */

/*@ axiomatic dynamic_allocation {
  @   predicate is_allocable{L}(integer n) // Can a block of n bytes be allocated?
  @     reads __fc_heap_status;
  @   // The logic label L is not used, but it must be present because the
  @   // predicate depends on the memory state
  @   axiom never_allocable{L}:
  @     \forall integer i;
  @        i < 0 || i > SIZE_MAX ==> !is_allocable(i);
  @ }
*/
#endif

/************************************************************************/
/*** API Prefixes {{{ ***/
/************************************************************************/

/* Memory state initialization */
#define eacsl_memory_init  export_alias(memory_init)
#define eacsl_memory_clean export_alias(memory_clean)

/* Tracking */
#define eacsl_store_block           export_alias(store_block)
#define eacsl_store_block_duplicate export_alias(store_block_duplicate)
#define eacsl_delete_block          export_alias(delete_block)

/* Predicates */
#define eacsl_offset       export_alias(offset)
#define eacsl_base_addr    export_alias(base_addr)
#define eacsl_block_length export_alias(block_length)
#define eacsl_valid_read   export_alias(valid_read)
#define eacsl_valid        export_alias(valid)
#define eacsl_initialized  export_alias(initialized)
#define eacsl_freeable     export_alias(freeable)
#define eacsl_separated    export_alias(separated)

/* Block initialization  */
#define eacsl_mark_readonly export_alias(mark_readonly)
#define eacsl_initialize    export_alias(initialize)
#define eacsl_full_init     export_alias(full_init)

/* Concurrency */
#define eacsl_pthread_create export_alias(pthread_create)

/* }}} */

/************************************************************************/
/*** Dynamic memory allocation {{{ ***/
/************************************************************************/

/*! \brief Drop-in replacement for \p malloc with memory tracking enabled.
 * For further information, see \p malloc(3).
 *
 * NOTE: This malloc returns a `NULL` pointer if the requested size is `0`.
 * Such behaviour is compliant with the C99 standard, however it differs from
 * the behaviour of the GLIBC malloc, which returns a zero-size block instead.
 * The standard indicates that a return value for a zero-sized allocation
 * is implementation specific:
 *    "If the size of the space requested is zero, the behaviour is
 *    implementation-defined: either a null pointer is returned, or the
 *    behaviour is as if the size were some non-zero value, except that the
 *    returned pointer shall not be used to access an object." */
/*@
  assigns __e_acsl_heap_allocation_size \from indirect:size, __e_acsl_heap_allocation_size;
  assigns __e_acsl_heap_allocated_blocks \from indirect:size, __e_acsl_heap_allocated_blocks;
  behavior allocation:
    assumes can_allocate: is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from indirect:size, __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from indirect:size, __e_acsl_heap_allocated_blocks;
  behavior no_allocation:
    assumes cannot_allocate: !is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from indirect:size, __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from size, __e_acsl_heap_allocated_blocks;
 */
void *malloc(size_t size) __attribute__((FC_BUILTIN));

/*! \brief Drop-in replacement for \p calloc with memory tracking enabled.
 * For further information, see \p calloc(3). */
/*@
  assigns __e_acsl_heap_allocation_size \from indirect:nbr_elt, indirect:size_elt, __e_acsl_heap_allocation_size;
  assigns __e_acsl_heap_allocated_blocks \from indirect:nbr_elt, indirect:size_elt, __e_acsl_heap_allocated_blocks;
  behavior allocation:
    assumes can_allocate: is_allocable(nbr_elt * size_elt);
    assigns __e_acsl_heap_allocation_size \from indirect:nbr_elt, indirect:size_elt, __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from indirect:nbr_elt, indirect:size_elt, __e_acsl_heap_allocated_blocks;
  behavior no_allocation:
    assumes cannot_allocate: !is_allocable(nbr_elt * size_elt);
    assigns __e_acsl_heap_allocation_size \from indirect:nbr_elt, indirect:size_elt, __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from indirect:nbr_elt, indirect:size_elt, __e_acsl_heap_allocated_blocks;
 */
void *calloc(size_t nbr_elt, size_t size_elt) __attribute__((FC_BUILTIN));

/*! \brief Drop-in replacement for \p realloc with memory tracking enabled.
 * For further information, see realloc(3) */
/*@
  assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
  assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
  behavior allocation:
    assumes   can_allocate: is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
  behavior deallocation:
    assumes   nonnull_ptr: ptr != \null;
    assumes   can_allocate: is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
  behavior fail:
    assumes cannot_allocate: !is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
 */
void *realloc(void *ptr, size_t size) __attribute__((FC_BUILTIN));

/*! \brief Drop-in replacement for \p free with memory tracking enabled.
 * For further information, see \p free(3). */
/*@
  assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
  assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
  behavior deallocation:
    assumes  nonnull_p: ptr != \null;
    assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
  behavior no_deallocation:
    assumes  null_p: ptr == \null;
    assigns __e_acsl_heap_allocation_size \from __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from __e_acsl_heap_allocated_blocks;
 */
void free(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Allocate `size` bytes of memory such that the allocation's base
 * address is an even multiple of alignment.
 *
 * \param alignment - should be the power of two
 * \param size - should be the multiple of alignment
 * \return - pointer to the allocated memory if the restrictions placed on size
 *   and alignment parameters hold. NULL is returned otherwise. */
/*@
  assigns __e_acsl_heap_allocation_size \from indirect:alignment, size, __e_acsl_heap_allocation_size;
  assigns __e_acsl_heap_allocated_blocks \from indirect:alignment, size, __e_acsl_heap_allocated_blocks;
 */
void *aligned_alloc(size_t alignment, size_t size) __attribute__((FC_BUILTIN));

/*! \brief Allocate size bytes and place the address of the allocated memory in
 * `*memptr`.  The address of the allocated memory will be a multiple of
 * `alignment`, which must be a power of two and a multiple of `sizeof(void*)`.
 * If size  is  0, then the value placed in *memptr is NULL. */
/*@
  assigns __e_acsl_heap_allocation_size \from indirect:alignment, size, __e_acsl_heap_allocation_size;
  assigns __e_acsl_heap_allocated_blocks \from indirect:alignment, size, __e_acsl_heap_allocated_blocks;
  behavior allocation:
    assumes can_allocate: is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from indirect:alignment, size, __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from indirect:alignment, size, __e_acsl_heap_allocated_blocks;
  behavior no_allocation:
    assumes cannot_allocate: !is_allocable(size);
    assigns __e_acsl_heap_allocation_size \from indirect:alignment, size, __e_acsl_heap_allocation_size;
    assigns __e_acsl_heap_allocated_blocks \from indirect:alignment, size, __e_acsl_heap_allocated_blocks;
 */
int posix_memalign(void **memptr, size_t alignment, size_t size)
    __attribute__((FC_BUILTIN));
/* }}} */

/************************************************************************/
/*** Memory tracking {{{ ***/
/************************************************************************/

/*! \brief Initialize memory tracking state.
 * Called before any other statement in \p main */
/*@ assigns \nothing; */
void eacsl_memory_init(int *argc_ref, char ***argv, size_t ptr_size)
    __attribute__((FC_BUILTIN));

/*! \brief Clean-up memory tracking state before a program's termination. */
/*@ assigns \nothing; */
void eacsl_memory_clean(void) __attribute__((FC_BUILTIN));

/*! \brief Store stack or globally-allocated memory block
 * starting at an address given by \p ptr.
 *
 * \param ptr base address of the tracked memory block
 * \param size size of the tracked block in bytes */
/*@ ensures \result == ptr;
  @ assigns \result \from *(((char*)ptr)+(0..size-1)), ptr, size; */
void *eacsl_store_block(void *ptr, size_t size) __attribute__((FC_BUILTIN));

/*! \brief Same as `eacsl_store_block`, but first check
 * checks whether a block with a base address given by `ptr` exists in the
 * tracked allocation and remove it before storing a new block.
 *
 * \param ptr base address of the tracked memory block
 * \param size size of the tracked block in bytes */
/*@ ensures \result == ptr;
  @ assigns \result \from *(((char*)ptr)+(0..size-1)), ptr, size; */
void *eacsl_store_block_duplicate(void *ptr, size_t size)
    __attribute__((FC_BUILTIN));

/*! \brief Remove a memory block which base address is \p ptr from tracking. */
/*@ assigns \nothing; */
void eacsl_delete_block(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Mark the \p size bytes starting at an address given by \p ptr as
 * initialized. */
/*@ assigns \nothing; */
void eacsl_initialize(void *ptr, size_t size) __attribute__((FC_BUILTIN));

/*! \brief Mark all bytes belonging to a memory block which start address is
 * given by \p ptr as initialized. */
/*@ assigns \nothing; */
void eacsl_full_init(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Mark a memory block which start address is given by \p ptr as
 * read-only. */
/*@ assigns \nothing; */
void eacsl_mark_readonly(void *ptr) __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** E-ACSL predicates {{{ ***/
/************************************************************************/

/*!\brief Implementation of the \b \\freeable predicate of E-ACSL.
 *
 * Evaluate to a non-zero value if \p ptr points to a start address of
 * a block allocated via \p malloc, \p calloc or \p realloc. */
/*@ assigns \result \from ptr; */
int eacsl_freeable(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\valid predicate of E-ACSL.
 *
 * \\valid evaluates an expression of the form `p+i`, where `p` is a pointer
 * and `i` is an integer offset and returns `true` if both `p` and `p+i` belong
 * to the same allocated memory block.
 *
 * @param ptr - memory address under question
 * @param size - the byte-length (starting from `ptr`) of the memory area which
 *  needs to be valid
 * @param base - if `ptr` can be represented by the expression `p+i` then
 *  `base` refers to `p`
 * @param addrof_base - if `ptr` can be represented by the expression `p+i`
 * then `addrof_base` refers to `&p`. For the cases when the address of `p`
 * cannot be taken (e.g., address of a static array or a constant value
 * casted to a pointer) then `addrof_base` is zero.
 *
 * @returns
 *  `true` if regions `[ptr, ptr + size]` and `[base, base + size]` are
 *  writable and lie within the same memory block and `false` otherwise.
 *  If `weak validity` is used (see macro `E_ACSL_WEAK_VALIDITY`)
 *  then only region `[ptr, ptr + size]` should lie within the same block
 *  and be writable.
 */
/*@ assigns \result \from *(((char*)ptr)+(0..size-1)), ptr, size;
  @ behavior valid:
  @   assumes \valid(((char *)ptr)+(0..size-1));
  @   assumes
  @     size <= 0 ||
  @     ! \separated(((char *)ptr)+(0..size-1),
  @                  ((char *)\base_addr(base))+(0..\block_length(base)-1));
  @   ensures \result == 1;
  @ behavior invalid_ptr:
  @   assumes ! \valid(((char *)ptr)+(0..size-1));
  @   ensures \result == 0;
  @ behavior separated_ptr:
  @   assumes size > 0;
  @   assumes \separated(((char *)ptr)+(0..size-1),
  @                      ((char *)\base_addr(base))+(0..\block_length(base)-1));
  @   ensures \result == 0;
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int eacsl_valid(void *ptr, size_t size, void *base, void *addrof_base)
    __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\valid_read predicate of E-ACSL.
 *
 * Same as ::eacsl_valid except the checked memory locations are only
 * required to be allocated.  */
/*@ assigns \result \from *(((char*)ptr)+(0..size-1)), ptr, size;
  @ behavior valid:
  @   assumes \valid_read(((char *)ptr)+(0..size-1));
  @   assumes
  @     size <= 0 ||
  @     ! \separated(((char *)ptr)+(0..size-1),
  @                  ((char *)\base_addr(base))+(0..\block_length(base)-1));
  @   ensures \result == 1;
  @ behavior invalid_ptr:
  @   assumes ! \valid_read(((char *)ptr)+(0..size-1));
  @   ensures \result == 0;
  @ behavior separated_ptr:
  @   assumes size > 0;
  @   assumes \separated(((char *)ptr)+(0..size-1),
  @                      ((char *)\base_addr(base))+(0..\block_length(base)-1));
  @   ensures \result == 0;
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int eacsl_valid_read(void *ptr, size_t size, void *base, void *addrof_base)
    __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\base_addr predicate of E-ACSL.
 * Return the base address of the memory block containing an address given
 * by \p ptr */
/*@ ensures \result == \base_addr(ptr);
  @ assigns \result \from ptr; */
void *eacsl_base_addr(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\block_length predicate of E-ACSL.
 * Return the byte length of the memory block of the block containing a memory
 * address given by \p ptr */
/*@ ensures \result == \block_length(ptr);
  @ assigns \result \from ptr; */
size_t eacsl_block_length(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\offset predicate of E-ACSL.
 * Return the byte offset of address given by \p ptr within a memory blocks
 * it belongs to */
/*@ ensures \result == \offset(ptr);
  @ assigns \result \from ptr; */
size_t eacsl_offset(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\initialized predicate of E-ACSL.
 * Return a non-zero value if \p size bytes starting from an address given by
 * \p ptr are initialized and zero otherwise. */
/*@ assigns \result \from *(((char*)ptr)+(0..size-1)), ptr, size;
  @ behavior initialized:
  @   assumes \initialized(((char *)ptr)+(0..size-1));
  @   ensures \result == 1;
  @ behavior uninitialized:
  @   assumes ! \initialized(((char *)ptr)+(0..size-1));
  @   ensures \result == 0;
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int eacsl_initialized(void *ptr, size_t size) __attribute__((FC_BUILTIN));

/*! \brief Implementation of the \b \\separated predicate of E-ACSL.
 *
 * The function should be called with `count` being the number of pointers to
 * check, and the variadic arguments filled with `count` successions of pointers
 * and sizes of the memory location.
 *
 * For instance, the ACSL notation `\separated(a[0..3], b[0..4])` could
 * correspond to the following call: `separated(2, a, 4, b, 5)`.
 *
 * \param count Number of couple (ptr, size) that are to be checked for
 * separation.
 * \param ... Pointer and size in succession that are to be checked for
 * separation.
 * \return A non-zero value if the memory locations given as parameters are
 * separated.
 */
/*@ assigns \result \from indirect:count;
  @ ensures \result == 0 || \result == 1; */
int eacsl_separated(size_t count, ...) __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** E-ACSL concurrency primitives {{{ ***/
/************************************************************************/

/*! \brief Function pointer to a function given to \p pthread_create. */
typedef void *(*pthread_routine_t)(void *);

/*! \brief Drop-in replacement for \p pthread_create with memory tracking
 *  enabled.
 *
 *  For further information, see \p pthread_create(3).
 */
// Specification extracted from share/libc/pthread.h in Frama-C
/*@ requires valid_thread: \valid(thread);
    requires valid_null_attr: attr == \null || \valid_read(attr);
    requires valid_routine: \valid_function(start_routine);
    requires valid_null_arg: arg == \null || \valid((char*)arg);
    assigns *thread \from *attr;
    assigns \result \from indirect:*attr;
    ensures success_or_error:
      \result == 0 ||
      \result == EAGAIN || \result == EINVAL || \result == EPERM;
 */
int eacsl_pthread_create(pthread_t *restrict thread,
                         const pthread_attr_t *restrict attr,
                         pthread_routine_t start_routine, void *restrict arg)
    __attribute__((FC_BUILTIN));

/* }}} */

#endif // E_ACSL_OBSERVATION_MODEL_H
