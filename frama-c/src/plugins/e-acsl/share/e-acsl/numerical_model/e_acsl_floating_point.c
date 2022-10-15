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

#include <fenv.h>
#include <math.h>
#include <stddef.h>

#include "../internals/e_acsl_rtl_io.h"

#include "e_acsl_floating_point.h"

// Initialization
double eacsl_math_HUGE_VAL = 0.0;
float eacsl_math_HUGE_VALF = 0.0;
double eacsl_math_INFINITY = 0.0;

void init_infinity_values() {
  /* Initialize E-ACSL infinity values */
  eacsl_math_HUGE_VAL = HUGE_VAL;
  eacsl_math_HUGE_VALF = HUGE_VALF;
  eacsl_math_INFINITY = INFINITY;
  /* Clear exceptions buffers */
  feclearexcept(FE_ALL_EXCEPT);
}

void eacsl_floating_point_exception(const char *exp) {
  int except = fetestexcept(FE_ALL_EXCEPT);
  char *resp = NULL;
  if (except) {
    if (fetestexcept(FE_DIVBYZERO))
      resp = "Division by zero";
    else if (fetestexcept(FE_INEXACT))
      resp = "Rounded result of an operation is not equal to the infinite "
             "precision result";
    else if (fetestexcept(FE_INVALID))
      resp = "Result of a floating-point operation is not well-defined";
    else if (fetestexcept(FE_OVERFLOW))
      resp = "Floating-point overflow";
    else if (fetestexcept(FE_UNDERFLOW))
      resp = "Floating-point underflow";
  }
  if (resp) {
    rtl_eprintf(
        "Execution of the statement `%s` leads to a floating point exception\n",
        exp);
    rtl_eprintf("Exception:  %s\n", resp);
  }
  feclearexcept(FE_ALL_EXCEPT);
}
