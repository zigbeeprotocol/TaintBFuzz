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
 * \file  e_acsl_temporal.h
 * \brief Implementation of the tenporal API shared by all models
 **************************************************************************/
#ifndef E_ACSL_TEMPORAL_H
#define E_ACSL_TEMPORAL_H

#include <stddef.h>

#include "../internals/e_acsl_alias.h"

/* No need to encapsulate via ifdef: using these extra definitions does
   not hurt, otherwise need to pass additional parameters to frama-c */
// clang-format off
#define eacsl_temporal_store_nblock             export_alias(temporal_store_nblock)
#define eacsl_temporal_store_nreferent          export_alias(temporal_store_nreferent)
#define eacsl_temporal_save_nblock_parameter    export_alias(temporal_save_nblock_parameter)
#define eacsl_temporal_save_nreferent_parameter export_alias(temporal_save_nreferent_parameter)
#define eacsl_temporal_save_copy_parameter      export_alias(temporal_save_copy_parameter)
#define eacsl_temporal_pull_parameter           export_alias(temporal_pull_parameter)
#define eacsl_temporal_save_return              export_alias(temporal_save_return)
#define eacsl_temporal_reset_parameters         export_alias(temporal_reset_parameters)
#define eacsl_temporal_pull_return              export_alias(temporal_pull_return)
#define eacsl_temporal_reset_return             export_alias(temporal_reset_return)
#define eacsl_temporal_memcpy                   export_alias(temporal_memcpy)
#define eacsl_temporal_memset                   export_alias(temporal_memset)
// clang-format on

/* Temporal store {{{ */

/*! \brief Take origin number of a memory block containing `block_addr` and
 * store it as a referent number of a pointer given by `ptr_addr`. */
/*@ assigns \nothing; */
void eacsl_temporal_store_nblock(void *lhs, void *rhs)
    __attribute__((FC_BUILTIN));

/*! \brief Same as `eacsl_temporal_store_nblock` but take a referent
 * number of `block_addr` instead */
/*@ assigns \nothing; */
void eacsl_temporal_store_nreferent(void *lhs, void *rhs)
    __attribute__((FC_BUILTIN));

/* }}} */

/* Memcpy/memset {{{ */

/*! \brief Copy temporal shadow data from [src, src + size] to
 * [dest, dest + size]. Counterpart of the memcpy function */
/*@ assigns \nothing; */
void eacsl_temporal_memcpy(void *dest, void *src, size_t size)
    __attribute__((FC_BUILTIN));

/*! \brief Set temporal shadow data from [src, src + size] to 0.
 * Counterpart of memset the function */
/*@ assigns \nothing; */
void eacsl_temporal_memset(void *dest, int c, size_t size)
    __attribute__((FC_BUILTIN));
/* }}} */

/* Function parameters {{{ */

/*! \brief store struct { .ptr = ptr, .temporal_flow = TBlockN }
 *  in the global parameter array. */
/*@ assigns \nothing; */
void eacsl_temporal_save_nblock_parameter(void *ptr, unsigned int param)
    __attribute__((FC_BUILTIN));

/*! \brief store struct { .ptr = ptr, .temporal_flow = TReferentN }
 *  in the global parameter array. */
/*@ assigns \nothing; */
void eacsl_temporal_save_nreferent_parameter(void *ptr, unsigned int param)
    __attribute__((FC_BUILTIN));

/*! \brief store struct { .ptr = ptr, .temporal_flow = TCopy } in the global
 *  parameter array. */
/*@ assigns \nothing; */
void eacsl_temporal_save_copy_parameter(void *ptr, unsigned int param)
    __attribute__((FC_BUILTIN));

/*! \brief Assign a referent number of `ptr` based on the record in the global
 * parameter array at index `param`. */
/*@ assigns \nothing; */
void eacsl_temporal_pull_parameter(void *ptr, unsigned int param, size_t size)
    __attribute__((FC_BUILTIN));

/*! \brief Nullify global parameter array  */
/*@ assigns \nothing; */
void eacsl_temporal_reset_parameters() __attribute__((FC_BUILTIN));
/* }}} */

/* Return values {{{ */

/*! \brief Save temporal referent number of `ptr` in a placeholder variable
 * tracking the referent number of a function's return. */
/*@ assigns \nothing; */
void eacsl_temporal_save_return(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Take a temporal referent stored in the placeholder tracking return
 * values  as a temporal referent number of `ptr`. */
/*@ assigns \nothing; */
void eacsl_temporal_pull_return(void *ptr) __attribute__((FC_BUILTIN));

/*! \brief Nullify a placeholder variable tracking the referent number of a
 * function's return. */
/*@ assigns \nothing; */
void eacsl_temporal_reset_return() __attribute__((FC_BUILTIN));
/* }}} */

/* Temporal valid {{{ */
int temporal_valid(void *ptr, void *addr_of_ptr);
/* }}} */

#endif // E_ACSL_TEMPORAL_H
