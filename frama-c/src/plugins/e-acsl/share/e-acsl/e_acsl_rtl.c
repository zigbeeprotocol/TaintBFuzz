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

/* Get default definitions and macros e.g., PATH_MAX */
#ifndef _DEFAULT_SOURCE
#  define _DEFAULT_SOURCE 1
#endif

/* On Windows, setup minimum version to Windows 8 (or Server 2012) to be able to
   use some specific API functions.
   Check directly for windows instead of using E_ACSL_OS_IS_WINDOWS so that it
   can be done without including anything. */
#if defined(WIN32) || defined(_WIN32) || defined(__WIN32)
#  define _WIN32_WINNT 0x0602
#endif

// Internals
#include "internals/e_acsl_bits.c"
#include "internals/e_acsl_debug.c"
#include "internals/e_acsl_malloc.c"
#include "internals/e_acsl_private_assert.c"
#include "internals/e_acsl_rtl_error.c"
#include "internals/e_acsl_rtl_io.c"
#include "internals/e_acsl_rtl_string.c"
#include "internals/e_acsl_shexec.c"
#include "internals/e_acsl_trace.c"

// Instrumentation model
#include "instrumentation_model/e_acsl_assert.c"
#include "instrumentation_model/e_acsl_assert_data_api.c"
#include "instrumentation_model/e_acsl_contract.c"
#include "instrumentation_model/e_acsl_temporal.c"

// Observation model
#include "observation_model/e_acsl_heap.c"
#include "observation_model/e_acsl_observation_model.c"

// Numerical model
#include "numerical_model/e_acsl_floating_point.c"

// Libc replacements
#include "libc_replacements/e_acsl_stdio.c"
#include "libc_replacements/e_acsl_string.c"
