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
 * \brief Internal defines for E-ACSL set according to the current environment.
 *
 * Instead of using complicated logic with predefined macros in the RTL, the
 * logic should be done in this file and an E-ACSL specific define set to record
 * the result of the logic.
 */

#ifndef E_ACSL_CONFIG_H
#define E_ACSL_CONFIG_H

// OS detection
//  - Assign values to specific OSes
#define E_ACSL_OS_LINUX_VALUE   1
#define E_ACSL_OS_WINDOWS_VALUE 2
#define E_ACSL_OS_OTHER_VALUE   999
//  - Declare defines to test for a specific OS
/*!
 * \brief True if the target OS is linux, false otherwise
 */
#define E_ACSL_OS_IS_LINUX E_ACSL_OS == E_ACSL_OS_LINUX_VALUE
/*!
 * \brief True if the target OS is windows, false otherwise
 */
#define E_ACSL_OS_IS_WINDOWS E_ACSL_OS == E_ACSL_OS_WINDOWS_VALUE
/*!
 * \brief True if the target OS is unknown, false otherwise
 */
#define E_ACSL_OS_IS_OTHER E_ACSL_OS == E_ACSL_OS_OTHER_VALUE
//  - Check current OS
#ifdef __linux__
// Linux compilation
#  define E_ACSL_OS E_ACSL_OS_LINUX_VALUE
#elif defined(WIN32) || defined(_WIN32) || defined(__WIN32)
// Windows compilation
#  define E_ACSL_OS E_ACSL_OS_WINDOWS_VALUE
#else
// Other
#  define E_ACSL_OS E_ACSL_OS_OTHER_VALUE
#  error "Unsupported OS for E-ACSL RTL"
#endif

#endif // E_ACSL_CONFIG_H
