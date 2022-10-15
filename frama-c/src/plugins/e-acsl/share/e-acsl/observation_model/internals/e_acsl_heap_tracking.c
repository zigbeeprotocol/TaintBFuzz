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

#include "e_acsl_heap_tracking.h"
#include "../../internals/e_acsl_rtl_io.h"

/* Variable tracking byte-count of user-allocated heap memory. */
static size_t heap_internal_allocation_size = 0;
/* Read-only version of the variable above exposed to the user in
 * `e_acsl_heap.h` */
size_t __e_acsl_heap_allocation_size = 0;

/* Variable tracking count of heap memory blocks */
static size_t heap_internal_allocated_blocks = 0;
/* Read-only version of the variable above exposed to the user in
 * `e_acsl_heap.h` */
size_t __e_acsl_heap_allocated_blocks = 0;

size_t get_heap_internal_allocation_size(void) {
  return heap_internal_allocation_size;
}

size_t get_heap_internal_allocated_blocks(void) {
  return heap_internal_allocated_blocks;
}

void update_heap_allocation(long size) {
  heap_internal_allocation_size += size;
  if (size > 0)
    ++heap_internal_allocated_blocks;
  else if (size < 0)
    --heap_internal_allocated_blocks;

  // Update read-only versions of the variables
  __e_acsl_heap_allocation_size = heap_internal_allocation_size;
  __e_acsl_heap_allocated_blocks = heap_internal_allocated_blocks;
}

void report_heap_leaks() {
#if defined(E_ACSL_VERBOSE) || defined(E_ACSL_DEBUG)
  size_t size = eacsl_get_heap_allocation_size();
  size_t blocks = eacsl_get_heap_allocated_blocks();
  if (size) {
    rtl_eprintf(
        " *** WARNING: Leaked %lu bytes of heap memory in %ld block%s\n", size,
        blocks, (blocks == 1) ? "" : "s");
  }
#endif
}
