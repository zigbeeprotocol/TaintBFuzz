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

#ifndef E_ACSL_OMODEL_DEBUG_H
#define E_ACSL_OMODEL_DEBUG_H

#include "../../internals/e_acsl_rtl_string.h"
#include <stdint.h>

/* Assertions in debug mode */
#ifdef E_ACSL_DEBUG

/* Assert that a memory block [_addr, _addr + _size] is nullified */
#  define DVALIDATE_NULLIFIED(_addr, _size)                                    \
    DVASSERT(zeroed_out((void *)_addr, _size),                                 \
             "Block [%a, %a+%lu] not nullified\n", _addr, _addr, _size)

/* Assert that memory block [_addr, _addr + _size] is allocated */
#  define DVALIDATE_ALLOCATED(_addr, _size, _base)                             \
    private_assert(allocated((uintptr_t)_addr, _size, (uintptr_t)_base),       \
                   "Operation on unallocated block [%a + %lu] with base %a\n", \
                   _addr, _size, _base);

/* Assert that memory block [_addr, _addr + _size] is allocated
 * and can be written to */
#  define DVALIDATE_WRITEABLE(_addr, _size, _base)                             \
    private_assert(writeable((uintptr_t)_addr, _size, (uintptr_t)_base),       \
                   "Operation on unallocated block [%a + %lu] with base %a\n", \
                   _addr, _size, _base);

#else
#  define DVALIDATE_NULLIFIED(_addr, _size)
#  define DVALIDATE_ALLOCATED(_ptr, _size, _base)
#  define DVALIDATE_WRITEABLE(_ptr, _size, _base)
#endif

/*! Print to stdout the parameters of the model */
void describe_observation_model();

/*! \brief Return a non-zero value if a memory region of length `size`
 * starting at address `addr` belongs to an allocated (tracked) memory
 * block and a 0 otherwise.
 *
 * Note the third argument `base_ptr` that represents the base of a pointer,
 * i.e., `addr` of the form `base_ptr + i`, where `i` is some integer index.
 */
int allocated(uintptr_t addr, long size, uintptr_t base_ptr);

/** \brief Return 1 if a given memory location is read-only and 0 otherwise */
int readonly(void *ptr);

/** \brief Return 1 if a given memory location is writable and 0 otherwise */
int writeable(uintptr_t addr, long size, uintptr_t base_ptr);

#endif // E_ACSL_OMODEL_DEBUG_H
