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

#include "../../internals/e_acsl_private_assert.h"
#include "e_acsl_bittree.h"

#include "../internals/e_acsl_omodel_debug.h"

#define E_ACSL_MMODEL_DESC "patricia trie"

void describe_observation_model() {
  rtl_printf(" * Memory tracking: %s\n", E_ACSL_MMODEL_DESC);
}

/** \brief same as ::lookup_allocated but return either `1` or `0` depending
    on whether the memory block described by this function's arguments is
    allocated or not.
    NOTE: Should have same signature in all models. */
int allocated(uintptr_t addr, long size, uintptr_t base) {
  return lookup_allocated((void *)addr, size, (void *)base) == NULL ? 0 : 1;
}

int readonly(void *ptr) {
  bt_block *blk = bt_find(ptr);
  private_assert(blk != NULL, "Readonly on unallocated memory\n", NULL);
  return blk->is_readonly;
}

int writeable(uintptr_t addr, long size, uintptr_t base_ptr) {
  return allocated(addr, size, base_ptr) && !readonly((void *)addr);
}
