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

#include "../../internals/e_acsl_bits.h"
#include "../../internals/e_acsl_rtl_io.h"
#include "e_acsl_segment_tracking.h"
#include "e_acsl_shadow_layout.h"

#include "../internals/e_acsl_omodel_debug.h"

#define E_ACSL_MMODEL_DESC "shadow memory"

void describe_observation_model() {
  rtl_printf(" * Memory tracking: %s\n", E_ACSL_MMODEL_DESC);
  rtl_printf(" *           Heap %d MB\n", E_ACSL_HEAP_SIZE);
  rtl_printf(" *          Stack %d MB\n", E_ACSL_STACK_SIZE);
  rtl_printf(" *            TLS %d MB\n", E_ACSL_TLS_SIZE);
  rtl_printf(" *   Thread stack %d MB\n", E_ACSL_THREAD_STACK_SIZE);
}

int allocated(uintptr_t addr, long size, uintptr_t base) {
  TRY_SEGMENT_WEAK(addr, return heap_allocated(addr, size, base),
                   return static_allocated(addr, size, base));
  if (!IS_ON_VALID(addr))
    return 0;
  return 0;
}

int readonly(void *ptr) {
  uintptr_t addr = (uintptr_t)ptr;
  return IS_ON_GLOBAL(addr) && global_readonly(addr) ? 1 : 0;
}

int writeable(uintptr_t addr, long size, uintptr_t base_ptr) {
  return allocated(addr, size, base_ptr) && !readonly((void *)addr);
}
