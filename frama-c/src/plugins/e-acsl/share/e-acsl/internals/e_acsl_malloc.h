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
 * \brief E-ACSL memory allocation bindings.
 *
 * Memory allocated for internal use of RTL and for the use by the application
 * is split into two mspaces (memory spaces). Memory allocation itself is
 * delegated to a slightly customised version of dlmalloc shipped with the
 * RTL. The overall pattern is as follows:
 *    mspace space = eacsl_create_locked_mspace(capacity);
 *    char *p = eacsl_mspace_malloc(space, size);
 **************************************************************************/

#ifndef E_ACSL_MALLOC_H
#define E_ACSL_MALLOC_H

#include <stddef.h>
#include <stdint.h>

#include "e_acsl_alias.h"

/* Block size units in bytes */
#define KB        (1024)      //!< Bytes in a kilobyte
#define MB        (1024 * KB) //!< Bytes in a megabyte
#define GB        (1024 * MB) //!< Bytes in a gigabyte
#define KB_SZ(_s) ((_s) / KB) //!< Convert bytes to kilobytes
#define MB_SZ(_s) ((_s) / MB) //!< Convert bytes to megabytes
#define GB_SZ(_s) ((_s) / GB) //!< Convert bytes to gigabytes

/************************************************************************/
/*** Mspace initialization {{{ ***/
/************************************************************************/

#define eacsl_make_memory_spaces    export_alias(make_memory_spaces)
#define eacsl_destroy_memory_spaces export_alias(destroy_memory_spaces)

/*! \brief Create two memory spaces, one for RTL and the other for application
    memory. This function *SHOULD* be called before any allocations are made
    otherwise execution fails */
void eacsl_make_memory_spaces(size_t rtl_size, size_t heap_size);

/*! \brief Destroy the memory spaces created with
    `eacsl_make_memory_spaces()`. */
void eacsl_destroy_memory_spaces();

/* }}} */

/************************************************************************/
/*** Mspace allocators (from dlmalloc) {{{ ***/
/************************************************************************/

#define eacsl_create_locked_mspace  export_alias(create_locked_mspace)
#define eacsl_destroy_mspace        export_alias(destroy_mspace)
#define eacsl_mspace_least_addr     export_alias(mspace_least_addr)
#define eacsl_mspace_malloc         export_alias(mspace_malloc)
#define eacsl_mspace_free           export_alias(mspace_free)
#define eacsl_mspace_calloc         export_alias(mspace_calloc)
#define eacsl_mspace_realloc        export_alias(mspace_realloc)
#define eacsl_mspace_posix_memalign export_alias(mspace_posix_memalign)
#define eacsl_mspace_aligned_alloc  export_alias(mspace_aligned_alloc)

typedef void *mspace;

struct memory_spaces {
  mspace rtl_mspace;           /* `private` (RTL) mspace */
  mspace heap_mspace;          /* `public` (application) mspace */
  uintptr_t rtl_start;         /* least address in RTL mspace */
  uintptr_t rtl_end;           /* greatest address in RTL mspace */
  uintptr_t heap_start;        /* least address in application mspace */
  uintptr_t heap_end;          /* greatest address in application mspace */
  uintptr_t heap_mspace_least; /* Initial least address in heap mspace */
};
extern struct memory_spaces mem_spaces;

/* Original functions from dlmalloc */
extern size_t eacsl_destroy_mspace(mspace);
extern void *eacsl_mspace_malloc(mspace, size_t);
extern void eacsl_mspace_free(mspace, void *);
extern void *eacsl_mspace_calloc(mspace msp, size_t, size_t);
extern void *eacsl_mspace_realloc(mspace msp, void *, size_t);
extern void *eacsl_mspace_aligned_alloc(mspace, size_t, size_t);
extern int eacsl_mspace_posix_memalign(mspace, void **, size_t, size_t);
extern void *eacsl_mspace_least_addr(mspace);

/*! \brief Wrapper around `eacsl_create_mspace` to always create a thread-safe
 *  mspace. */
mspace eacsl_create_locked_mspace(size_t size);

/* }}} */

/************************************************************************/
/*** Public allocators {{{ ***/
/************************************************************************/

/* Used within RTL to override standard allocation */
/* Shortcuts for public allocation functions */

#define public_malloc(...)                                                     \
  eacsl_mspace_malloc(mem_spaces.heap_mspace, __VA_ARGS__)
#define public_realloc(...)                                                    \
  eacsl_mspace_realloc(mem_spaces.heap_mspace, __VA_ARGS__)
#define public_calloc(...)                                                     \
  eacsl_mspace_calloc(mem_spaces.heap_mspace, __VA_ARGS__)
#define public_free(...) eacsl_mspace_free(mem_spaces.heap_mspace, __VA_ARGS__)
#define public_aligned_alloc(...)                                              \
  eacsl_mspace_aligned_alloc(mem_spaces.heap_mspace, __VA_ARGS__)
#define public_posix_memalign(...)                                             \
  eacsl_mspace_posix_memalign(mem_spaces.heap_mspace, __VA_ARGS__)

/* }}} */

/************************************************************************/
/*** Private allocators usable within RTL and GMP {{{ ***/
/************************************************************************/

#define private_malloc(...)                                                    \
  eacsl_mspace_malloc(mem_spaces.rtl_mspace, __VA_ARGS__)
#define private_calloc(...)                                                    \
  eacsl_mspace_calloc(mem_spaces.rtl_mspace, __VA_ARGS__)
#define private_realloc(...)                                                   \
  eacsl_mspace_realloc(mem_spaces.rtl_mspace, __VA_ARGS__)
#define private_free(...) eacsl_mspace_free(mem_spaces.rtl_mspace, __VA_ARGS__)

/* }}} */

/************************************************************************/
/*** Useful functions {{{ ***/
/************************************************************************/

/* \return a true value if x is a power of 2 and false otherwise */
int is_pow_of_2(size_t x);

/* }}} */

#endif // E_ACSL_MALLOC_H
