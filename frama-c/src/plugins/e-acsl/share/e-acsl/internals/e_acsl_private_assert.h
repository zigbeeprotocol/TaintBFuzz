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
 * \brief E-ACSL assertions and abort statements implementation.
 **************************************************************************/

#ifndef E_ACSL_PRIVATE_ASSERT
#define E_ACSL_PRIVATE_ASSERT

/*! \brief Assert with printf-like error message support */
#define private_assert(expr, fmt_and_args...)                                  \
  private_assert_fail(expr, __FILE__, __LINE__, fmt_and_args)

/*! \brief Output a message to error stream using printf-like format string
 * and abort the execution.
 *
 * This is a wrapper for \p eprintf combined with \p abort */
#define private_abort(fmt_and_args...)                                         \
  private_abort_fail(__FILE__, __LINE__, fmt_and_args)

void private_assert_fail(int expr, const char *file, int line, char *fmt, ...);
void private_abort_fail(const char *file, int line, char *fmt, ...);
void raise_abort(const char *file, int line);

/* Instances of assertions shared accross different memory models */

/*! \brief Abort the execution if the size of the pointer computed during
 * instrumentation (\p _ptr_sz) does not match the size of the pointer used
 * by a compiler (\p void*) */
#define arch_assert(_ptr_sz)                                                   \
  private_assert(                                                              \
      _ptr_sz == sizeof(void *),                                               \
      "Mismatch of instrumentation- and compile-time pointer sizes: "          \
      "%lu vs %lu\n",                                                          \
      _ptr_sz, sizeof(void *))

#endif // E_ACSL_PRIVATE_ASSERT
