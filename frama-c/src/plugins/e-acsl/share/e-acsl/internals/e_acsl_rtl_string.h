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
 * \brief Replacement of system-wide \p <string.h> header for use with E-ACSL
 * runtime library.
 *
 * Intended use:
 *  - For the case when the sources are compiled using GCC prefer \p __builtin_
 *    versions of some of the string.h functions (e.g., \p memset). This is
 *    mostly because the GCC builtins are on average faster.
 *  - For the case it is not GCC system-wide versions should be used. This
 *    and the above options require \p E_ACSL_BUILTINS macro to be defined
 *    at compile-time.
 *  - For the case when the analysed program contains customised definitions
 *    of string.h functions use GLIBC-based implementations.
 **************************************************************************/

#ifndef E_ACSL_RTL_STRING_H
#define E_ACSL_RTL_STRING_H

#ifndef E_ACSL_NO_COMPILER_BUILTINS
#  define memset  __builtin_memset
#  define memcmp  __builtin_memcmp
#  define memcpy  __builtin_memcpy
#  define memmove __builtin_memmove
#  define strncat __builtin_strncat
#  define strcat  __builtin_strcat
#  define strlen  __builtin_strlen
#  define strcmp  __builtin_strcmp
#  define strncmp __builtin_strncmp
#  define strcpy  __builtin_strcpy
#  define strncpy __builtin_strncpy
#  define strchr  __builtin_strchr
#else
#  include <string.h>
#endif

#include <stddef.h>

/* \brief Local version of `strcat` */
char *nstrcat(char *dest, const char *src);

/* \brief Local version of `strdup` */
char *nstrdup(const char *s);

/* \brief Append `src` to `dest` by re-allocating `dest`.
 *
 * `sappend` assumes that `dest` is either NULL (in which case it is
 * allocated on the heap) or a heap-allocated C string that can be passed
 * as an input to realloc.  If `delim` and `dest` are not NULLs them string
 * `delim` is appended to `dest` before `src`
 *
 * \return Result of concatenation of `dest` and `src` */
char *sappend(char *dest, const char *src, const char *delim);

/** \brief Return 0 if C string `str` ends with string `pat` and a non-zero
 * value otherwise. The function assumes that both, `str` and `path` are valid,
 * NUL-terminated C strings. If any of the input strings are NULLs, a non-zero
 * value is returned. */
int endswith(char *str, char *pat);

/** \brief Return a non-zero value if `size` bytes past address `p` are
 * nullified and zero otherwise. */
int zeroed_out(const void *p, size_t size);

/** \brief Count the number of occurrences of char `c` in a string `s` */
int charcount(const char *s, char c);

#endif // E_ACSL_RTL_STRING_H
