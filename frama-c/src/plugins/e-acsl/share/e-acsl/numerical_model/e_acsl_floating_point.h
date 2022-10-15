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
 * \brief  Functionality related to processing of floating point values
 **************************************************************************/

#ifndef E_ACSL_FLOATING_POINT_H
#define E_ACSL_FLOATING_POINT_H

#include "../internals/e_acsl_alias.h"

#define eacsl_math_HUGE_VAL            export_alias(math_HUGE_VAL)
#define eacsl_math_HUGE_VALF           export_alias(math_HUGE_VALF)
#define eacsl_math_INFINITY            export_alias(math_INFINITY)
#define eacsl_floating_point_exception export_alias(floating_point_exception)

/* Below variables hold infinity values for floating points defined in math.h.
   Most of them are defined as macros that expand to built-in function calls.
   As such, they cannot be used in E-ACSL specifications directly. To solve
   the issue this header provides alternative definitions prefixed
   __e_acsl_math_. For instance, if a call to `pow` overflows it
   returns `HUGE_VAL`. To make sure that the result of pow does not overflow
   one can use the following contract:

   extern double __e_acsl_math_HUGE_VAL;

   //@ ensures \result != __e_acsl_math_HUGE_VAL;
   double pow(double, double);
*/

/** \brief Positive infinity for doubles: same as HUGE_VAL */
extern double eacsl_math_HUGE_VAL __attribute__((FC_BUILTIN));
/** \brief Positive infinity for floats: same as HUGE_VALF */
extern float eacsl_math_HUGE_VALF __attribute__((FC_BUILTIN));
/** \brief Representation of infinity value for doubles: same as INFINITY */
extern double eacsl_math_INFINITY __attribute__((FC_BUILTIN));

/* FIXME: An additional variable that should be added to this list is
     long double math_HUGE_VALL;
   That represents positive infinity for long doubles. However, long doubles
   are unsupported Value plug-in analysis who start throwing errors once
   test suite is ran. */

void init_infinity_values();

void eacsl_floating_point_exception(const char *exp)
    __attribute__((FC_BUILTIN));

#endif // E_ACSL_FLOATING_POINT_H
