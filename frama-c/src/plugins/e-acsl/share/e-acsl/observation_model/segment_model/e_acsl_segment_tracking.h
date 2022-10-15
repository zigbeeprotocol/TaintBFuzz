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
 * \file  e_acsl_segment_tracking.h
 * \brief Core functionality of the segment-based memory model
 **************************************************************************/

#ifndef E_ACSL_SEGMENT_TRACKING_H
#define E_ACSL_SEGMENT_TRACKING_H

#include <stddef.h>
#include <stdint.h>

#include "e_acsl_shadow_layout.h"

/* Segment settings and shadow values interpretation {{{ */

/* This file implements segment-based and offset-based shadow memory models
 * (shadow encodings) (see draft of the ISMM'17 paper).
 *
 * IMPORTANT: While the implementation of the offset-based encoding mostly
 * follows the description given by the paper, there are differences in the
 * segment-based encoding for tracking heap memory. Some of these differences
 * are as follows:
 *  1) Size of a heap segment is increased to 32 bytes
 *  2) Heap meta-segments are no longer used, segment-based representation of
 *    a heap block considers only block segments, such that:
 *    - Lowest `intptr_t` bytes of each shadow segment tracking an application
 *      block store the base address of that block;
 *    - `intptr_t` bytes of the first segment following the initial `intptr_t`
 *      bytes store the length of the block. Note, the length is only stored
 *      by the first segment.
 *  3) Per-byte initialization of application bytes is tracked via a disjoint
 *    shadow region, which maps one bit of shadow memory to a byte of
 *    application memory. Comments within this file often refer to a shadow
 *    region tracking application blocks by segments as to `block shadow`,
 *    and to the region tracking initialization as to `init shadow`.
*/

/*! @brief Byte size of a heap segment.
 * This size is potentially used as an argument to `memalign`.
 * It SHOULD be a multiple of 2 and a multiple of a pointer size.
 *
 * \b FIXME: in the current implementation there might be issues with segment
 * size greater than 64 bytes. This is because presently some initialization
 * functionality relies on the fact that initialization per segment can be set
 * and/or evaluated using an 8-byte bitmask. */
#define HEAP_SEGMENT 32

/*! \brief Size (in bytes) of a long block on the stack. */
#define LONG_BLOCK 8

/*! \brief Bit offset in a primary shadow byte that represents initialization. */
#define INIT_BIT 0

/*! \brief Bit offset in a primary shadow byte that represents read-only or
 * read-write access.
 *
 * This is such that the value of 1 is read-only, and 0 is read/write */
#define READONLY_BIT 1

/*! \brief Evaluate to a non-zero value if the size of a memory
 * block indicates that it is a long one */
#define IS_LONG_BLOCK(_size) (_size > LONG_BLOCK)

/*! \brief Offset within a long block that identifies the portion of the block
 * that does not have a corresponding shadow and reuse the shadow of a previous
 * segment.
 * E.g., given a long block of 11 bytes the boundary is 8. Then, bytes [0,7] of
 * the block are shadowed (storing block offset and size) and bytes 8-10 are
 * not. This is because 3 bytes are not sufficient to store size and offset.
 * These remaining bytes reuse the shadow of [0,7]. */
#define LONG_BLOCK_BOUNDARY(_size) (_size - _size % LONG_BLOCK)

/*! \brief Primary shadow of a long block consists of a 8-byte segment + a
 * remainder. For instance, a 18-byte block is represented by two 8-byte
 * segments + 2 bytes.  Each byte of a segment stores an offset in the secondary
 * shadow. The offsets for each such segment can be expressed using the
 * following number obtained by compressing all eight bytes with offsets set
 * into a single block. */
#define LONG_BLOCK_MASK 15913703276567643328UL

/*! \brief 6 higher bytes of a memory cell on stack that belongs to a long
 * memory block store offsets relative to meta-data in the secondary shadow. The
 * offsets start with the below number. E.g., if the bits store 51, then the
 * offset at which to read meta-data is (51 - 48). */
#define LONG_BLOCK_INDEX_START 48

/* }}} */

/* Runtime assertions (debug mode) {{{ */
#ifdef E_ACSL_DEBUG
#  define DVALIDATE_ALIGNMENT(_addr)                                           \
    DVASSERT(((uintptr_t)_addr) % HEAP_SEGMENT == 0,                           \
             "Heap base address %a is unaligned\n", _addr)

#  define DVALIDATE_MEMORY_PRE_MAIN_INIT                                       \
    DVASSERT(mem_layout.is_initialized_pre_main != 0,                          \
             "Un-initialized pre-main shadow layout\n", NULL)

#  define DVALIDATE_MEMORY_MAIN_INIT                                           \
    DVASSERT(mem_layout.is_initialized_main != 0,                              \
             "Un-initialized main shadow layout\n", NULL)

#  define DVALIDATE_MEMORY_INIT                                                \
    DVASSERT(mem_layout.is_initialized_pre_main != 0                           \
                 && mem_layout.is_initialized_main != 0,                       \
             "Un-initialized shadow layout\n", NULL)

/* Debug function making sure that the order of program segments is as expected
 * and that the program and the shadow segments used do not overlap. */
void validate_shadow_layout();

/* Assert that memory layout has been initialized and all segments appear
 * in the expected order */
#  define DVALIDATE_SHADOW_LAYOUT validate_shadow_layout()

/* Assert that boundaries of a block [_addr, _addr+_size] are within a segment
 * given by `_s`. `_s` is either HEAP, STACK, TLS, GLOBAL or STATIC. */
#  define DVALIDATE_IS_ON(_addr, _size, _s)                                    \
    DVASSERT(IS_ON_##_s(_addr), "Address %a not on %s\n", _addr, #_s);         \
    DVASSERT(IS_ON_##_s(_addr + _size), "Address %a not on %s\n",              \
             _addr + _size, #_s)

/* Assert that [_addr, _addr+_size] are within heap segment */
#  define DVALIDATE_IS_ON_HEAP(_addr, _size) DVALIDATE_IS_ON(_addr, _size, HEAP)
/* Assert that [_addr, _addr+_size] are within stack segment */
#  define DVALIDATE_IS_ON_STACK(_addr, _size)                                  \
    DVALIDATE_IS_ON(_addr, _size, STACK)
#  if E_ACSL_OS_IS_LINUX
/* Assert that [_addr, _addr+_size] are within global segment */
#    define DVALIDATE_IS_ON_GLOBAL(_addr, _size)                               \
      DVALIDATE_IS_ON(_addr, _size, GLOBAL)
/* Assert that [_addr, _addr+_size] are within TLS segment */
#    define DVALIDATE_IS_ON_TLS(_addr, _size) DVALIDATE_IS_ON(_addr, _size, TLS)
#  elif E_ACSL_OS_IS_WINDOWS
/* Assert that [_addr, _addr+_size] are within text segment */
#    define DVALIDATE_IS_ON_TEXT(_addr, _size)                                 \
      DVALIDATE_IS_ON(_addr, _size, TEXT)
/* Assert that [_addr, _addr+_size] are within bss segment */
#    define DVALIDATE_IS_ON_BSS(_addr, _size) DVALIDATE_IS_ON(_addr, _size, BSS)
/* Assert that [_addr, _addr+_size] are within idata segment */
#    define DVALIDATE_IS_ON_IDATA(_addr, _size)                                \
      DVALIDATE_IS_ON(_addr, _size, IDATA)
#  endif
/* Assert that [_addr, _addr+_size] are within stack, global or TLS segments */
#  define DVALIDATE_IS_ON_STATIC(_addr, _size)                                 \
    DVALIDATE_IS_ON(_addr, _size, STATIC)

/* Assert that `_addr` is on heap and it is the base address of an allocated
 * heap memory block */
#  define DVALIDATE_FREEABLE(_addr)                                            \
    DVASSERT(IS_ON_HEAP(_addr), "Expected heap location: %a\n", _addr);        \
    DVASSERT(_addr == _base_addr(_addr),                                       \
             "Expected base address, i.e., %a, not %a\n", _base_addr(_addr),   \
             _addr);

/* Assert that a memory block [_addr, _addr + _size] is allocated on a
 * program's heap */
#  define DVALIDATE_HEAP_ACCESS(_addr, _size)                                  \
    DVASSERT(IS_ON_HEAP(_addr), "Expected heap location: %a\n", _addr);        \
    DVASSERT(heap_allocated((uintptr_t)_addr, _size, (uintptr_t)_addr),        \
             "Operation on unallocated heap block [%a + %lu]\n", _addr, _size)

/* Assert that every location belonging to the range [_addr, _addr + _size] is
 * - belongs to a tracked static region (i.e., stack, TLS or global)
 * - not allocated */
#  define DVALIDATE_HEAP_FREE(_addr, _size)                                    \
    {                                                                          \
      uintptr_t i, a = (uintptr_t)_addr;                                       \
      for (i = 0; i < _size; i++) {                                            \
        DVASSERT(IS_ON_HEAP(a + i), "Expected heap location: %a\n", a + i);    \
        DVASSERT(!heap_allocated(a + i, 1, a + i),                             \
                 "Expected heap unallocated location: [%a + %lu]\n", a, i);    \
      }                                                                        \
    }

/* Assert that memory block [_addr, _addr + _size] is allocated on stack, TLS
 * or globally */
#  define DVALIDATE_STATIC_ACCESS(_addr, _size)                                \
    DVASSERT(IS_ON_STATIC(_addr), "Expected static location: [%a + %lu], \n",  \
             _addr, _size);                                                    \
    DVASSERT(static_allocated((uintptr_t)_addr, _size, (uintptr_t)_addr),      \
             "Operation on unallocated static block [%a + %lu]\n", _addr,      \
             _size)

/* Same as ::DVALIDATE_STATIC_LOCATION but for a single memory location */
#  define DVALIDATE_STATIC_LOCATION(_addr)                                     \
    DVASSERT(IS_ON_STATIC(_addr), "Expected static location: %a\n", _addr);    \
    DVASSERT(static_allocated_one((uintptr_t)_addr),                           \
             "Operation on unallocated static block [%a]\n", _addr)

/* Assert that every location belonging to the range [_addr, _addr + _size] is
 * - belongs to a tracked static region (i.e., stack, TLS or global)
 * - not allocated */
#  define DVALIDATE_STATIC_FREE(_addr, _size)                                  \
    {                                                                          \
      uintptr_t i, a = (uintptr_t)_addr;                                       \
      for (i = 0; i < _size; i++) {                                            \
        DVASSERT(IS_ON_STATIC(a + i),                                          \
                 "Expected static location in freea: %a\n", a + i);            \
        DVASSERT(                                                              \
            !static_allocated_one(a + i),                                      \
            "Expected static unallocated location in freea: [%a + %lu]\n", a,  \
            i);                                                                \
      }                                                                        \
    }

/* Assert that neither of `_len - 1` addresses immediately preceding `_addr`
 * are base addresses of some other block and that `_len` addresses past
 * `_addr` are free */
#  define DVALIDATE_STATIC_SUFFICIENTLY_ALIGNED(_addr, _len)                   \
    {                                                                          \
      int _i;                                                                  \
      for (_i = 0; _i < _len; _i++) {                                          \
        uintptr_t _prev = _addr - _i;                                          \
        if (static_allocated_one(_prev)) {                                     \
          private_assert(                                                      \
              _base_addr(_prev) != _prev,                                      \
              "Potential backward overlap of: \n  previous block [%a]\n"       \
              "  with allocated block [%a]\n",                                 \
              _prev, _addr);                                                   \
        }                                                                      \
        uintptr_t _next = _addr + _i;                                          \
        private_assert(                                                        \
            !static_allocated_one(_next),                                      \
            "Potential forward overlap of:\n  following block location [%a]\n" \
            "  with allocated block [%a]\n",                                   \
            _next, _addr);                                                     \
      }                                                                        \
    }

#else
/*! \cond exclude from doxygen */
#  define DVALIDATE_MEMORY_PRE_MAIN_INIT
#  define DVALIDATE_MEMORY_MAIN_INIT
#  define DVALIDATE_MEMORY_INIT
#  define DVALIDATE_SHADOW_LAYOUT
#  define DVALIDATE_HEAP_ACCESS
#  define DVALIDATE_STATIC_ACCESS
#  define DVALIDATE_STATIC_LOCATION
#  define DVALIDATE_ALIGNMENT
#  define DVALIDATE_IS_ON
#  define DVALIDATE_IS_ON_HEAP
#  define DVALIDATE_IS_ON_STACK
#  if E_ACSL_OS_IS_LINUX
#    define DVALIDATE_IS_ON_GLOBAL
#    define DVALIDATE_IS_ON_TLS
#  elif E_ACSL_OS_IS_WINDOWS
#    define DVALIDATE_IS_ON_TEXT
#    define DVALIDATE_IS_ON_BSS
#    define DVALIDATE_IS_ON_IDATA
#  endif
#  define DVALIDATE_IS_ON_STATIC
#  define DVALIDATE_FREEABLE
#  define DVALIDATE_STATIC_FREE
#  define DVALIDATE_HEAP_FREE
#  define DVALIDATE_STATIC_SUFFICIENTLY_ALIGNED
/*! \endcond */
#endif
/* }}} */

/* E-ACSL predicates {{{ */

/*! \brief Quick test to check if a static location belongs to allocation.
 * This macro really belongs where static_allocated is defined, but
 * since it is used across this whole file it needs to be defined here. */
#define static_allocated_one(_addr) (*((unsigned char *)PRIMARY_SHADOW(_addr)))

/*! \brief Shortcut for executing statements based on the segment a given
 * address belongs to.
 * \param intptr_t _addr - a memory address
 * \param code_block _heap_stmt - code executed if `_addr` is a heap address
 * \param code_block _static_stmt - code executed if `_addr` is a static address */
#define TRY_SEGMENT_WEAK(_addr, _heap_stmt, _static_stmt)                      \
  if (IS_ON_HEAP(_addr)) {                                                     \
    _heap_stmt;                                                                \
  } else if (IS_ON_STATIC(_addr)) {                                            \
    _static_stmt;                                                              \
  }

/*! \brief Same as TRY_SEGMENT but performs additional checks aborting the
 * execution if the given address is `NULL` or does not belong to known
 * segments. Note that `NULL` also does not belong to any of the tracked
 * segments but it is treated separately for debugging purposes.
 *
 * The \b WEAK notion refers to the behaviour where no action is performed if
 * the given address does not belong to any of the known segments. */
#define TRY_SEGMENT(_addr, _heap_stmt, _static_stmt)                           \
  {                                                                            \
    TRY_SEGMENT_WEAK(_addr, _heap_stmt, _static_stmt)                          \
    else {                                                                     \
      private_assert(0, "Use of invalid address %a in %s\n", _addr, __func__); \
    }                                                                          \
  }

/*! \brief Wrapper around ::heap_info and ::static_info functions that
 * dispatches one of the above functions based on the type of supplied memory
 * address (`addr`) (static, global, tls or heap). For the case when the
 * supplied address does not belong to the track segments 0 is returned.
 *
 * \param uintptr_t addr - a memory address
 * \param char p - predicate type. See ::static_info for further details. */
uintptr_t predicate(uintptr_t addr, char p);

/*! \brief Return the byte length of the memory block containing `_addr` */
#define _block_length(_addr) predicate((uintptr_t)_addr, 'L')
/*! \brief Return the base address of the memory block containing `_addr` */
#define _base_addr(_addr) predicate((uintptr_t)_addr, 'B')
/* }}} */

/* Static allocation {{{ */
/*! \brief Record allocation of a given memory block and update shadows
 *  using offset-based encoding.
 *
 * \param ptr - pointer to a base memory address of the stack memory block.
 * \param size - size of the stack memory block. */
void shadow_alloca(void *ptr, size_t size);
/* }}} */

/* Deletion of static blocks {{{ */

/*! \brief Nullifies shadow regions of a memory block given by its address.
 * \param ptr - base memory address of the stack memory block. */
void shadow_freea(void *ptr);
/* }}} */

/* Static querying {{{ */

/*! \brief Checking whether a globally allocated memory block containing an
 * address _addr has read-only access. Note, this is light checking that
 * relies on the fact that a single block cannot contain read/write and
 * read-only parts, that is to check whether the block has read-only access it
 * is sufficient to check any of its bytes. */
#define global_readonly(_addr)                                                 \
  checkbit(READONLY_BIT, (*(char *)PRIMARY_GLOBAL_SHADOW(_addr)))

/*! \brief Return a non-zero value if a memory region of length `size`
 * starting at address `addr` belongs to a tracked stack, tls or
 * global memory block and 0 otherwise.
 * This function is only safe if applied to a tls, stack or global address.
 * Explanations regarding the third argument - `base_ptr` - are given
 * via inline documentation of function ::heap_allocated */
int static_allocated(uintptr_t addr, long size, uintptr_t base_ptr);

/*! \brief Return a non-zero value if a statically allocated memory block
 * starting at `addr` of length `size` is fully initialized (i.e., each of
 * its cells is initialized). */
int static_initialized(uintptr_t addr, long size);

/*! \brief Querying information about a specific global or stack memory address
 * (based on the value of parameter `global'). The return value is interpreted
 * based on the second argument that specifies parameters of the query:
 *
 * - 'B' - return the base address of the memory block `addr` belongs to or `0`
 *     if `addr` lies outside of tracked allocation.
 * - 'O' - return the offset of `addr` within its memory block or `0`
 *     if `addr` lies outside of tracked allocation.
 * - 'L' - return the size in bytes of the memory block `addr` belongs to or `0`
 *     if `addr` lies outside of tracked allocation.
 *
 * NB: One should make sure that a given address is allocated before querying.
 * That is, for the cases when addr does not refer to an allocated memory
 * address belonging to static allocation the return value for this function is
 * unspecified. */
uintptr_t static_info(uintptr_t addr, char type);

#ifdef E_ACSL_TEMPORAL /*{{{*/
/*! Return either an origin (if `origin` is non-zero) or referent timestamp
 *  associated with a static address `addr` */
uint32_t static_temporal_info(uintptr_t addr, int origin);

#  define static_origin_timestamp(_ptr)                                        \
    static_temporal_info((uintptr_t)(_ptr), 1)
#  define static_referent_timestamp(_ptr)                                      \
    static_temporal_info((uintptr_t)(_ptr), 0)

/*! Store a referent time stamp associated with a static pointer.
 *  Origin timestamps are generated via `shadow_alloca` */
void static_store_temporal_referent(uintptr_t addr, uint32_t ref);
#endif /*}}} E_ACSL_TEMPORAL*/
/* }}} */

/* Initialization {{{ */

/*! \brief Unsafe version of `eacsl_initialize()` that does not lock the memory
    model. */
void unsafe_initialize(void *ptr, size_t n);

/*! \brief The following function marks n bytes on a static region starting from
 * the address given by addr as initialized. `size` equating to zero indicates
 * that the whole block should be marked as initialized.  */
void initialize_static_region(uintptr_t addr, long size);

/*! \brief Mark n bytes on the heap starting from address addr as initialized */
void initialize_heap_region(uintptr_t addr, long len);
/* }}} */

/* Read-only {{{ */
/*! \brief Mark n bytes starting from the address given by `ptr` as initialized.
 * NOTE: This function has many similarities with ::initialize_static_region
 * The functionality, however is preferred to be kept separate
 * because the ::eacsl_mark_readonly should operate only on the global shadow.
 */
void mark_readonly_region(uintptr_t addr, long size);
/* }}} */

/* Heap allocation {{{ (malloc/calloc) */

/*! \brief Unsafe version of `malloc()` that does not lock the memory model. */
void *unsafe_malloc(size_t size);

/*! \brief Unsafe version of `calloc()` that does not lock the memory model. */
void *unsafe_calloc(size_t nbr_elt, size_t size_elt);

/*! \brief Unsafe version of `realloc()` that does not lock the memory model. */
void *unsafe_realloc(void *ptr, size_t size);

/*! \brief Unsafe version of `free()` that does not lock the memory model. */
void unsafe_free(void *ptr);

/*! \brief Unsafe version of `aligned_alloc()` that does not lock the memory
    model. */
void *unsafe_aligned_alloc(size_t alignment, size_t size);

/*! \brief Unsafe version of `posix_memalign()` that does not lock the memory
    model. */
int unsafe_posix_memalign(void **memptr, size_t alignment, size_t size);

/** \brief Return shadowed copy of a memory chunk on a program's heap using.
 * If `init` parameter is set to a non-zero value the memory occupied by the
 * resulting block is set to be initialized and uninitialized otherwise. */
void *shadow_copy(const void *ptr, size_t size, int init);
/* }}} */

/* Heap querying {{{ */
/*! \brief Return a non-zero value if a memory region of length `size`
 * starting at address `addr` belongs to an allocated (tracked) heap memory
 * block and a 0 otherwise. Note, this function is only safe if applied to a
 * heap address.
 *
 * Note the third argument `base_ptr` that represents the base of a pointer, i.e.,
 * `addr` of the form `base_ptr + i`, where `i` is some integer index.
 * ::heap_allocated also returns zero if `base_ptr` and `addr` belong to different
 * memory blocks, or if `base_ptr` lies within unallocated region. The intention
 * here is to be able to detect dereferencing of an allocated memory block through
 * a pointer to a different block. Consider, for instance, some pointer `p` that
 * points to a memory block `B`, and an index `i`, such that `p+i` references a
 * memory location belonging to a different memory block (say `C`). From a
 * low-level viewpoint, dereferencing `p+i` is safe (since it belongs to a properly
 * allocated block). From our perspective, however, dereference of `p+i` is
 * only legal if both `p` and `p+i` point to the same block. */
int heap_allocated(uintptr_t addr, size_t size, uintptr_t base_ptr);

/*! \brief Unsafe version of `eacsl_freeable()` that does not lock the memory
 * model.
 *
 * Return a non-zero value if a given address is a base address of a
 * heap-allocated memory block that `addr` belongs to.
 *
 * As some of the other functions, \b \\freeable can be expressed using
 * ::IS_ON_HEAP, ::heap_allocated and ::_base_addr. Here direct
 * implementation is preferred for performance reasons. */
int unsafe_freeable(void *ptr);

/*! \brief Querying information about a specific heap memory address.
 * This function is similar to ::static_info except it returns data
 * associated with dynamically allocated memory.
 * See in-line documentation for ::static_info for further details. */
uintptr_t heap_info(uintptr_t addr, char type);

/*! \brief Implementation of the \b \\initialized predicate for heap-allocated
 * memory. NB: If `addr` does not belong to an allocated heap block this
 * function returns 0. */
int heap_initialized(uintptr_t addr, long len);

/* }}} */

/* Heap temporal querying {{{*/
#ifdef E_ACSL_TEMPORAL
uint32_t heap_temporal_info(uintptr_t addr, int origin);

#  define heap_origin_timestamp(_ptr)   heap_temporal_info((uintptr_t)(_ptr), 1)
#  define heap_referent_timestamp(_ptr) heap_temporal_info((uintptr_t)(_ptr), 0)

void heap_store_temporal_referent(uintptr_t addr, uint32_t ref);
#endif /*}}} E_ACSL_TEMPORAL*/

/* Internal state print (debug mode) {{{ */
#ifdef E_ACSL_DEBUG
/* ! \brief Print human-readable representation of a byte in a primary
 * shadow */
void printbyte(unsigned char c, char buf[], size_t bufsize);

/*! \brief Print human-readable (well, ish) representation of a memory block
 * using primary and secondary shadows. */
void print_static_shadows(uintptr_t addr, size_t size);

/*! \brief Print human-readable representation of a heap shadow region for a
 * memory block of length `size` starting at address `addr`. This function
 * assumes that `addr` is the base address of the memory block. */
void print_heap_shadows(uintptr_t addr);

void print_shadows(uintptr_t addr, size_t size);

void print_memory_segment(struct memory_segment *p, char *lab, int off);

void print_memory_partition(struct memory_partition *p);

void print_shadow_layout();

/*! \brief Output the shadow segment the address belongs to */
const char *which_segment(uintptr_t addr);

/* NOTE: Above functions are designed to be used only through the following
 * macros or debug functions included/defined based on the value of the
 * E_ACSL_DEBUG macro. */

/*! \brief Print program layout. This function outputs start/end addresses of
 * various program segments, their shadow counterparts and sizes of shadow
 * regions used. */
#  define DEBUG_PRINT_LAYOUT print_shadow_layout()
void ___e_acsl_debug_print_layout() {
  DEBUG_PRINT_LAYOUT;
}

/*! \brief Print the shadow segment address addr belongs to */
#  define DEBUG_PRINT_SEGMENT(_addr) which_segment(_addr)
void ___e_acsl_debug_print_segment(uintptr_t addr) {
  DEBUG_PRINT_SEGMENT(addr);
}

/*! \brief Print human-readable representation of a shadow region corresponding
 * to a memory address addr. The second argument (size) if the size of the
 * shadow region to be printed. Normally addr argument is a base address of a
 * memory block and size is its length. */
#  define DEBUG_PRINT_SHADOW(addr, size)                                       \
    print_shadows((uintptr_t)addr, (size_t)size)
void ___e_acsl_debug_print_shadow(uintptr_t addr, size_t size) {
  DEBUG_PRINT_SHADOW(addr, size);
}

#else
/* \cond exclude from doxygen */
#  define DEBUG_PRINT_SHADOW(addr, size)
#  define DEBUG_PRINT_LAYOUT
#  define DEBUG_PRINT_SEGMENT(addr)
/* \endcond */
#endif
/* }}} */

#endif // E_ACSL_SEGMENT_TRACKING_H
