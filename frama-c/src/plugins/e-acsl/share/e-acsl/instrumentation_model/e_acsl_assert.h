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
 * \brief E-ACSL assertions and abort statements.
 **************************************************************************/

#ifndef E_ACSL_ASSERT_H
#define E_ACSL_ASSERT_H

#include "../internals/e_acsl_alias.h"
#include "e_acsl_assert_data.h"

#define eacsl_runtime_sound_verdict export_alias(sound_verdict)
#define eacsl_runtime_assert        export_alias(assert)
#define eacsl_print_value           export_alias(print_value)
#define eacsl_print_value_content   export_alias(print_value_content)

/*! E-ACSL instrumentation automatically sets this global to 0 if its verdict
    becomes unsound.
    TODO: may only happen for annotations containing memory-related properties.
    For arithmetic properties, the verdict is always sound (?). */
extern int __attribute__((FC_BUILTIN)) eacsl_runtime_sound_verdict;

/*! \brief Runtime assertion verifying a given predicate
 *  \param predicate integer code of a predicate
 *  \param data context data for the predicate. */
/*@ requires \valid_read(data) && \initialized(data);
  @ assigns \nothing;
  @ behavior blocking:
  @   assumes data->blocking != 0;
  @   requires predicate != 0;
  @ behavior non_blocking:
  @   assumes data->blocking == 0;
  @   check requires predicate != 0;
  @ complete behaviors;
  @ disjoint behaviors; */
void eacsl_runtime_assert(int predicate, eacsl_assert_data_t *data)
    __attribute__((FC_BUILTIN));

/*@ requires \valid_read(value) && \initialized(value);
  @ assigns \nothing; */
void eacsl_print_value(eacsl_assert_data_value_t *value)
    __attribute__((FC_BUILTIN));

/*! \brief Utility function that prints the content of the given data value in
 *  the given stream.
 *  \param stream Stream where to print the value content.
 *  \param value Value to print to the stream.
 */
/*@ requires \valid_read(value) && \initialized(value);
  @ assigns \nothing; */
void eacsl_print_value_content(FILE *stream, eacsl_assert_data_value_t *value)
    __attribute__((FC_BUILTIN));

#endif // E_ACSL_ASSERT_H
