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
#ifdef E_ACSL_TEMPORAL
#  include "../../instrumentation_model/e_acsl_temporal_timestamp.h"
#endif

#include "../internals/e_acsl_timestamp_retrieval.h"

/* Local operations on temporal timestamps {{{ */
/* Remaining functionality (shared between all models) is located in e_acsl_temporal.h */
#ifdef E_ACSL_TEMPORAL
uint32_t origin_timestamp(void *ptr) {
  bt_block *blk = bt_find(ptr);
  return blk != NULL ? blk->timestamp : INVALID_TEMPORAL_TIMESTAMP;
}

uintptr_t temporal_referent_shadow(void *ptr) {
  bt_block *blk = bt_find(ptr);
  private_assert(blk != NULL,
                 "referent timestamp on unallocated memory address %a\n",
                 (uintptr_t)ptr);
  private_assert(blk->temporal_shadow != NULL,
                 "no temporal shadow of block with base address\n",
                 (uintptr_t)blk->ptr);
  return (uintptr_t)blk->temporal_shadow + eacsl_offset(ptr);
}

uint32_t referent_timestamp(void *ptr) {
  bt_block *blk = bt_find(ptr);
  if (blk != NULL)
    return *((uint32_t *)temporal_referent_shadow(ptr));
  else
    return INVALID_TEMPORAL_TIMESTAMP;
}

void store_temporal_referent(void *ptr, uint32_t ref) {
  uint32_t *shadow = (uint32_t *)temporal_referent_shadow(ptr);
  *shadow = ref;
}
#endif
/* }}} */
