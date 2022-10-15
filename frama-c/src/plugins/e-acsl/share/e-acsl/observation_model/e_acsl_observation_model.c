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

/************************************************************************/
/*** Common functions between all memory models {{{ ***/
/************************************************************************/

#include <stdarg.h>
#include <stddef.h>

#include "../internals/e_acsl_debug.h"

#include "e_acsl_observation_model.h"

/**
 * Check if the memory location represented by `ptr1..ptr1+size1` is separated
 * with the memory locatin represented by `ptr2..ptr2+size2`.
 *
 * \return A non-zero value if the two memory locations are separated, zero
 * otherwise.
 */
int separated2(void *ptr1, size_t size1, void *ptr2, size_t size2) {
  DASSERT(eacsl_valid_read(ptr1, size1, eacsl_base_addr(ptr1), NULL)
          && eacsl_valid_read(ptr2, size2, eacsl_base_addr(ptr2), NULL));

  // Cast pointers to char* to be able to do pointer arithmetic without
  // triggering undefined behavior
  char *cptr1 = ptr1;
  char *cptr2 = ptr2;

  // If at least one of the memory location is an empty set (size == 0), then
  // the memory is separated.
  // Otherwise the memory is separated if `cptr1 + size1 <= cptr2` or
  // `cptr2 + size2 <= cptr1`
  int sep = size1 == 0 || size2 == 0 || (cptr1 + size1) <= cptr2
            || (cptr2 + size2) <= cptr1;

  return sep;
}

int eacsl_separated(size_t count, ...) {
  void *ptrs[count];
  size_t sizes[count];

  // Extract arguments in an array to be able to iterate over them several times
  va_list args;
  va_start(args, count);
  for (size_t i = 0; i < count; ++i) {
    ptrs[i] = va_arg(args, void *);
    sizes[i] = va_arg(args, size_t);
  }
  va_end(args);

  int result = 1;

  // Check that every pointer is separated with any other pointer
  void *ptr1;
  size_t size1;
  for (size_t i = 0; result && i < count - 1; ++i) {
    ptr1 = ptrs[i];
    size1 = sizes[i];
    for (size_t j = i + 1; result && j < count; ++j) {
      result = separated2(ptr1, size1, ptrs[j], sizes[j]);
    }
  }

  return result;
}

/* }}} */

/************************************************************************/
/*** Implementation of the memory model {{{ ***/
/************************************************************************/

#include "internals/e_acsl_heap_tracking.c"
#include "internals/e_acsl_patricia_trie.c"
#include "internals/e_acsl_safe_locations.c"

/* Select memory model, either segment-based or bittree-based model should
   be defined */
#if defined E_ACSL_SEGMENT_MMODEL
#  include "segment_model/e_acsl_segment_observation_model.c"
#  include "segment_model/e_acsl_segment_omodel_debug.c"
#  include "segment_model/e_acsl_segment_timestamp_retrieval.c"
#  include "segment_model/e_acsl_segment_tracking.c"
#  include "segment_model/e_acsl_shadow_concurrency.c"
#  include "segment_model/e_acsl_shadow_layout.c"
#elif defined E_ACSL_BITTREE_MMODEL
#  include "bittree_model/e_acsl_bittree.c"
#  include "bittree_model/e_acsl_bittree_observation_model.c"
#  include "bittree_model/e_acsl_bittree_omodel_debug.c"
#  include "bittree_model/e_acsl_bittree_timestamp_retrieval.c"
#else
#  error "No E-ACSL memory model defined. Aborting compilation"
#endif

/* }}} */
