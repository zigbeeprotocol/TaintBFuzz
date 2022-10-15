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
 * \brief Implementation of E-ACSL API for contracts.
 **************************************************************************/

#include <limits.h>
#include <stdarg.h>

#include "../internals/e_acsl_debug.h"

#include "e_acsl_contract.h"

/*! \brief Return the index of the `char` where the bit number
    `global_bit_index` is located. */
static inline size_t find_char_index(size_t global_bit_index) {
  return global_bit_index / CHAR_BIT;
}

/*! \brief Return the index of the bit in the `char` given by
    \ref find_char_index for the bit number `global_bit_index`. */
static inline size_t find_bit_index(size_t global_bit_index) {
  return global_bit_index % CHAR_BIT;
}

/*! \brief Return the number of `char` to allocate to store `bit_count` bits. */
static inline size_t find_char_count(size_t bit_count) {
  size_t char_count = bit_count / CHAR_BIT;
  if (bit_count % CHAR_BIT > 0) {
    ++char_count;
  }
  return char_count;
}

/*! \brief Normalize the boolean parameter `value` to 0 or 1 */
static inline int normalize_to_boolean(int value) {
  return value ? 1 : 0;
}

/* Documented in e_acsl.h */
struct contract_t {
  /*! \brief Number of cells in the char array used to store the results of
     * the assumes clauses.
     */
  size_t char_count;

  /*! \brief Char array to store the results of the assumes clauses. One bit
     * per behavior.
     *
     * The functions \ref find_char_index() and \ref find_bit_index() can be
     * used to find the location of the bit for a specific behavior. */
  char *assumes;
};

/* Documented in e_acsl.h */
contract_t *contract_init(size_t size) {
  // Allocate memory for the structure
  contract_t *c = malloc(sizeof(contract_t));
  DVASSERT(c != NULL, "Unable to allocate %d bytes of memory for contract_t\n",
           sizeof(contract_t));

  // Compute the number of char needed to store `size` behaviors, assuming
  // that one behavior is stored in one bit.
  c->char_count = find_char_count(size);

  // Allocate an array of char of the computed count
  if (c->char_count > 0) {
    c->assumes = calloc(c->char_count, sizeof(char));
    DVASSERT(c->assumes != NULL,
             "Unable to allocate %d cells of %d bytes of memory for "
             "contract_t::assumes\n",
             c->char_count, sizeof(char));
  } else {
    c->assumes = NULL;
  }

  return c;
}

/* Documented in e_acsl.h */
void contract_clean(contract_t *c) {
  // Free array of char
  free(c->assumes);
  // Free structure
  free(c);
}

/* Documented in e_acsl.h */
void contract_set_behavior_assumes(contract_t *c, size_t i, int assumes) {
  size_t char_idx = find_char_index(i);
  DVASSERT(char_idx < c->char_count,
           "Out of bound char index %d (char_count: %d)\n", char_idx,
           c->char_count);
  size_t bit_idx = find_bit_index(i);
  assumes = normalize_to_boolean(assumes);
  c->assumes[char_idx] |= (assumes << bit_idx);
}

/* Documented in e_acsl.h */
int contract_get_behavior_assumes(const contract_t *c, size_t i) {
  size_t char_idx = find_char_index(i);
  DVASSERT(char_idx < c->char_count,
           "Out of bound char index %d (char_count: %d)\n", char_idx,
           c->char_count);
  size_t bit_idx = find_bit_index(i);
  int result = c->assumes[char_idx] & (1 << bit_idx);
  return normalize_to_boolean(result);
}

/* Documented in e_acsl.h */
int contract_partial_count_behaviors(const contract_t *c, size_t count, ...) {
  va_list args;
  va_start(args, count);

  int result = 0;
  for (size_t i = 0; i < 2 && i < count; ++i) {
    result += contract_get_behavior_assumes(c, va_arg(args, int));
  }

  va_end(args);
  return result;
}

/* Documented in e_acsl.h */
int contract_partial_count_all_behaviors(const contract_t *c) {
  int result = 0;
  for (int i = 0; i < c->char_count && result < 2; ++i) {
    // Counting bits set with Kernighan's algorithm, but stopping at two
    // bits set.
    // cf. <https://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetKernighan>
    unsigned char assumes_cell = c->assumes[i];
    for (; assumes_cell && result < 2; ++result) {
      assumes_cell &= assumes_cell - 1;
    }
  }
  return result;
}
