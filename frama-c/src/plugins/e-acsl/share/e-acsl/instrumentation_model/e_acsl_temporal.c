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

#ifdef E_ACSL_TEMPORAL

#  include <stddef.h>

#  include "../internals/e_acsl_private_assert.h"
#  include "../observation_model/internals/e_acsl_omodel_debug.h"
#  include "../observation_model/internals/e_acsl_timestamp_retrieval.h"
#  include "e_acsl_temporal_timestamp.h"

#  include "e_acsl_temporal.h"

/* Temporal store {{{ */
void eacsl_temporal_store_nblock(void *lhs, void *rhs) {
  store_temporal_referent(lhs, origin_timestamp(rhs));
}

void eacsl_temporal_store_nreferent(void *lhs, void *rhs) {
  store_temporal_referent(lhs, referent_timestamp(rhs));
}
/* }}} */

/* Memcpy/memset {{{ */
void eacsl_temporal_memcpy(void *dest, void *src, size_t size) {
  /* Memcpy is only relevant for pointers here, so if there is a
   * copy under a pointer's size then there no point in copying memory*/
  if (size >= sizeof(void *)) {
    DVALIDATE_ALLOCATED(src, size, src);
    DVALIDATE_WRITEABLE(dest, size, dest);
    void *dest_shadow = (void *)temporal_referent_shadow(dest);
    void *src_shadow = (void *)temporal_referent_shadow(src);
    memcpy(dest_shadow, src_shadow, size);
  }
}

void eacsl_temporal_memset(void *dest, int c, size_t size) {
  DVALIDATE_WRITEABLE(dest, size, dest);
  void *dest_shadow = (void *)temporal_referent_shadow(dest);
  memset(dest_shadow, 0, size);
}
/* }}} */

/* Function parameters {{{ */
void eacsl_temporal_save_nblock_parameter(void *ptr, unsigned int param) {
  parameter_referents[param].ptr = ptr;
  parameter_referents[param].temporal_flow = TBlockN;
}

void eacsl_temporal_save_nreferent_parameter(void *ptr, unsigned int param) {
  parameter_referents[param].ptr = ptr;
  parameter_referents[param].temporal_flow = TReferentN;
}

void eacsl_temporal_save_copy_parameter(void *ptr, unsigned int param) {
  parameter_referents[param].ptr = ptr;
  parameter_referents[param].temporal_flow = TCopy;
}

void eacsl_temporal_pull_parameter(void *ptr, unsigned int param, size_t size) {
  struct temporal_parameter *tpar = &parameter_referents[param];
  switch (tpar->temporal_flow) {
  case TBlockN:
    store_temporal_referent(ptr, origin_timestamp(tpar->ptr));
    break;
  case TReferentN:
    store_temporal_referent(ptr, referent_timestamp(tpar->ptr));
    break;
  case TCopy:
    eacsl_temporal_memcpy(ptr, tpar->ptr, size);
    break;
  default:
    private_abort("Unreachable\n");
  }
}

void eacsl_temporal_reset_parameters() {
  reset_parameter_referents();
}
/* }}} */

/* Return values {{{ */
void eacsl_temporal_save_return(void *ptr) {
  return_referent = (ptr, sizeof(void *)) ? referent_timestamp(ptr) : 0;
}

void eacsl_temporal_pull_return(void *ptr) {
  store_temporal_referent(ptr, return_referent);
}

void eacsl_temporal_reset_return() {
  return_referent = 0;
}
/* }}} */

/* Temporal valid {{{ */
int temporal_valid(void *ptr, void *addr_of_ptr) {
  /* Could check for NULL, but since temporal_valid if ran by `eacsl_valid`,
   * this has been already checked.
   * FIXME: If the address of pointer and the pointer itself reference the same
   * address the access is deemed temporally valid by default.
   * One issue associated  with such checking is the case when a pointer points
   * to itself. One way to address such issue is to mark pointers, arrays and
   * integers differently. Here one can use the "readonly" bit to mark
   * something which does not need to be checked (e.g. arrays) and then
   * recognise this mark. Blocks can be recognised as readonly by using range
   * checking. For instance if some existing block belongs to a text segment
   * then it is readonly. */
  if (addr_of_ptr && (uintptr_t)ptr != (uintptr_t)addr_of_ptr) {
    /* The case where there is an actual pointer pointing to some memory
     * chunk, otherwise temporal valid holds trivially since the block points
     * to itself */
    uint32_t stored_referent = referent_timestamp(addr_of_ptr);
    uint32_t actual_referent = origin_timestamp(ptr);
    return stored_referent == actual_referent;
  }
  return 1;
}
/* }}} */

#endif // E_ACSL_TEMPORAL
