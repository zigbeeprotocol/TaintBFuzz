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
 * \brief Validating format strings with respect to arguments and their types
 *
 * Detection of format string vulnerabilities and other violations
 * related to improper use of formats in printf-like functions are addressed
 * as follows. Each call to a format function `f` (e.g. printf)
 * is replaced by a call to an analysis function `f'`. The signature of `f'` is
 * similar to that of `f'` except it has an additional argument. This argument
 * is a literal string where each character describes the type of a variadic
 * argument in the original call to `f`.
 *
 * For instance:
 *  `printf("Str=%s, Int=%d ", str, num);`
 * is replaced by
 *  `__e_acsl_builtin_printf("sd", "Str=%s, Int=%d", str, num);`
 * Note the first argument "sd". It indicates that `printf` was invoked
 * with two variadic arguments of types `char*` (specified via 's')
 * and `int` (`d`). Such single-character types are further called
 * |abbreviated| types. See ::abbr2str function for details.
 *
 * Execution of __e_acsl_builtin_printf checks that
 *  - format string is a NUL-terminated C string
 *  - all directives in the format string are well-formed (as per C99 standard)
 *  - each formatting directive has a corresponding variadic argument.
 *    Excessive arguments (for which there are no directives) are allowed
 *    but otherwise ignored.
 *  - the types of variadic arguments provided via a call match the types
 *    expected by the respective format directives. This check includes checking
 *    for signedness. For instance,
 *      __e_acsl_builtin_printf("d", "%u", n);
 *    will abort because the formatting directive expects its argument to be an
 *    unsigned integer, whereas `n` is a signed integer (indicated by "d") in
 *    the first argument to `__e_acsl_builtin_printf`. Bear in mind though that
 *    char, short, and float types are the subjects to default promotions. That
 *    is, `char` and `short` are promoted to `int` and `float` is promoted to
 *    double. Frama-C enforces such promotions by adding explicit casts.
 *  - variadic arguments corresponding to `%s` conversion specifiers describe
 *    valid C strings (NUL-terminated arrays of characters belonging to program
 *    allocation)
 *  - variadic arguments corresponding to `%n` conversion specifiers describe
 *    valid integer pointers
 * Execution of __e_acsl_builtin_dprintf additionally checks that
 *  - the file descriptor designated for writing is open
 * Execution of __e_acsl_builtin_fprintf additionally checks that
 *  - the stream designated for writing is valid
 * Execution of __e_acsl_builtin_sprintf and  __e_acsl_builtin_sprintf
 * additionally check that
 *  - memory buffers designated for writing are allocated, writable and provide
 *    sufficient space for storing the results
 **************************************************************************/

#ifndef E_ACSL_STDIO_H
#define E_ACSL_STDIO_H

#include <stddef.h>
#include <stdio.h>

#include "../internals/e_acsl_alias.h"

/* No need to encapsulate via ifdef: using these extra definitions does
   not hurt, otherwise need to pass additional parameters to frama-c */
#define eacsl_builtin_printf   export_alias(builtin_printf)
#define eacsl_builtin_fprintf  export_alias(builtin_fprintf)
#define eacsl_builtin_dprintf  export_alias(builtin_dprintf)
#define eacsl_builtin_sprintf  export_alias(builtin_sprintf)
#define eacsl_builtin_snprintf export_alias(builtin_snprintf)
#define eacsl_builtin_syslog   export_alias(builtin_syslog)

/* Printf and friends {{{ */

/** \brief `printf` with error checking. */
int eacsl_builtin_printf(const char *fmtdesc, const char *fmt, ...)
    __attribute__((FC_BUILTIN));

/** \brief `fprintf` with error checking. */
int eacsl_builtin_fprintf(const char *fmtdesc, FILE *stream, const char *fmt,
                          ...) __attribute__((FC_BUILTIN));

/** \brief `dprintf` with error checking. */
int eacsl_builtin_dprintf(const char *fmtdesc, int fd, const char *fmt, ...)
    __attribute__((FC_BUILTIN));

/** \brief `sprintf` with error checking. */
int eacsl_builtin_sprintf(const char *fmtdesc, char *buffer, const char *fmt,
                          ...) __attribute__((FC_BUILTIN));

/** \brief `snprintf` with error checking. */
int eacsl_builtin_snprintf(const char *fmtdesc, char *buffer, size_t size,
                           const char *fmt, ...) __attribute__((FC_BUILTIN));

/** \brief `syslog` with error checking. */
int eacsl_builtin_syslog(const char *fmtdesc, int priority, const char *fmt,
                         ...) __attribute__((FC_BUILTIN));

/* }}} */

#endif // E_ACSL_STDIO_H
