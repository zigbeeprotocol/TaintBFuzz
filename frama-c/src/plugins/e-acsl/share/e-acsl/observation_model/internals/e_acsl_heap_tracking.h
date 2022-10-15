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
 * \brief Functionality to report/track memory leaks. Shared between models
 **************************************************************************/

#ifndef E_ACSL_HEAP_TRACKING
#define E_ACSL_HEAP_TRACKING

#include <stddef.h>

/* Return the number of bytes in heap application allocation */
size_t get_heap_internal_allocation_size(void);

/* Return the number of blocks in heap application allocation */
size_t get_heap_internal_allocated_blocks(void);

/* Update heap allocation stats */
void update_heap_allocation(long size);

/* If E_ACSL_VERBOSE or E_ACSL_DEBUG are set, print a message if there is still
 * some allocated memory on the heap. */
void report_heap_leacks();

#endif // E_ACSL_HEAP_TRACKING
