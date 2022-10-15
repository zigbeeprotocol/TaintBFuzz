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
 * \brief E-ACSL support of function and statement contracts.
 **************************************************************************/

#ifndef E_ACSL_CONTRACT_H
#define E_ACSL_CONTRACT_H

#include <stddef.h>

#include "../internals/e_acsl_alias.h"

#ifdef __FC_FEATURES_H
#  include <__fc_alloc_axiomatic.h>
#else
/*@ ghost extern int __fc_heap_status; */
#endif

#define contract_t     export_alias(contract_t)
#define contract_init  export_alias(contract_init)
#define contract_clean export_alias(contract_clean)
#define contract_set_behavior_assumes                                          \
  export_alias(contract_set_behavior_assumes)
#define contract_get_behavior_assumes                                          \
  export_alias(contract_get_behavior_assumes)
#define contract_partial_count_behaviors                                       \
  export_alias(contract_partial_count_behaviors)
#define contract_partial_count_all_behaviors                                   \
  export_alias(contract_partial_count_all_behaviors)

/*! \brief Structure to hold pieces of information about function and statement
 * contracts at runtime. */
typedef struct contract_t __attribute__((FC_BUILTIN)) contract_t;

/*! \brief Allocate and initialize a structure to hold pieces of information
 * about `size` behaviors.
 *
 * \param size Number of behaviors that the structure should support.
 * \return A structure to hold pieces of information about contracts at runtime.
 */
/*@ assigns \result \from indirect:__fc_heap_status, indirect:size;
  @ admit ensures \valid(\result); */
contract_t *contract_init(size_t size) __attribute__((FC_BUILTIN));

/*! \brief Cleanup the structure `c` previously allocated by
 * \ref contract_init.
 *
 * \param c The structure to deallocate.
 */
/*@ requires \valid(c);
  @ assigns \nothing; */
void contract_clean(contract_t *c) __attribute__((FC_BUILTIN));

/*! \brief Set the result of the assumes clauses for the behavior `i` in the
 * structure.
 *
 * \param c Valid pointer to the structure to update.
 * \param i Index of the behavior. The index must be valid.
 * \param assumes Boolean result of the assumes clauses for the behavior.
 * \see \ref contract_get_behavior_assumes to retrieve the value.
 */
/*@ requires \valid(c);
  @ assigns *c \from indirect:c, indirect:i, assumes; */
void contract_set_behavior_assumes(contract_t *c, size_t i, int assumes)
    __attribute__((FC_BUILTIN));

/*! \brief Retrieve the result of the assumes clauses for the behavior `i` from
 * the structure.
 *
 * \param c Valid pointer to the structure to read.
 * \param i Index of the behavior. The index must be valid.
 * \return The result of the assumes clauses for the behavior `i` (1 for true,
 *         0 for false).
 * \see \ref contract_set_behavior_assumes to set the value.
 */
/*@ requires \valid_read(c);
  @ assigns \result \from indirect:c, indirect:i;
  @ ensures \result == 0 || \result == 1; */
int contract_get_behavior_assumes(const contract_t *c, size_t i)
    __attribute__((FC_BUILTIN));

/*! \brief Count the number of active behaviors among the `count` given
 * behaviors.
 *
 * \param c Valid pointer to the structure to read.
 * \param count Number of behaviors to test. There must be `count` values in
 *              `indexes`.
 * \param ... Indexes of the behaviors to test. The indexes must be valid
 *                and there must be `count` indexes.
 * \return 0 if no behaviors are active, 1 if exactly one behavior is active,
 *         and 2 if more than one behavior is active.
 */
int contract_partial_count_behaviors(const contract_t *c, size_t count, ...)
    __attribute__((FC_BUILTIN));

/*! \brief Count the number of active behaviors among all the behaviors of the
 * contract.
 *
 * \param c Valid pointer to the structure to read.
 * \return 0 if no behaviors are active, 1 if exactly one behavior is active,
 *         and 2 if more than one behavior is active.
 */
int contract_partial_count_all_behaviors(const contract_t *c)
    __attribute__((FC_BUILTIN));

#endif
