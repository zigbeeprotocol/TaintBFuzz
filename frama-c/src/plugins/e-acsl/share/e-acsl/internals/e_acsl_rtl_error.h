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
 * \brief Provide malloc-free replacements for some error formatting
 *        functions.
 **************************************************************************/

#ifndef E_ACSL_RTL_ERROR
#define E_ACSL_RTL_ERROR

#include <errno.h>

/*! \brief `strerror()` replacement without dynamic allocation. */
char *rtl_strerror(int errnum);

/*! \brief `strerror_r()` replacement without dynamic allocation.

    The error message will be copied into `buf` up to `bufsize`. The address of
    the buffer is also returned by the function. */
char *rtl_strerror_r(int errnum, char *buf, size_t bufsize);

#endif // E_ACSL_RTL_ERROR
