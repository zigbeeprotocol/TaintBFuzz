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
 * \brief  User API to query E-ACSL about the state of heap allocation.
 **************************************************************************/

#ifndef E_ACSL_HEAP
#define E_ACSL_HEAP

#include <stddef.h>

#include "../internals/e_acsl_alias.h"

#define eacsl_heap_allocation_size      export_alias(heap_allocation_size)
#define eacsl_heap_allocated_blocks     export_alias(heap_allocated_blocks)
#define eacsl_get_heap_allocation_size  export_alias(get_heap_allocation_size)
#define eacsl_get_heap_allocated_blocks export_alias(get_heap_allocated_blocks)

/*! \brief A variable holding the number of bytes in heap application allocation. */
extern size_t eacsl_heap_allocation_size;
/*! \brief A variable holding the number of blocks in heap application allocation. */
extern size_t eacsl_heap_allocated_blocks;

/*! Return the number of bytes in heap application allocation. */
size_t eacsl_get_heap_allocation_size() __attribute__((FC_BUILTIN));

/*! Return the number of blocks in heap application allocation. */
size_t eacsl_get_heap_allocated_blocks() __attribute__((FC_BUILTIN));

#endif // E_ACSL_HEAP
