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

#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stddef.h>

#include "e_acsl_config.h"
#include "e_acsl_rtl_io.h"
#include "e_acsl_trace.h"

#include "e_acsl_private_assert.h"

void raise_abort(const char *file, int line) {
#ifdef E_ACSL_DEBUG
#  ifndef E_ACSL_NO_TRACE
  trace();
#  endif
#endif
  raise(SIGABRT);
}

void private_abort_fail(const char *file, int line, char *fmt, ...) {
  va_list va;
#if E_ACSL_OS_IS_LINUX
  sigset_t defer_abrt;
  sigemptyset(&defer_abrt);
  sigaddset(&defer_abrt, SIGABRT);
  sigprocmask(SIG_BLOCK, &defer_abrt, NULL);
#endif // E_ACSL_OS_IS_LINUX
  va_start(va, fmt);
  rtl_veprintf(fmt, va);
  va_end(va);
#if E_ACSL_OS_IS_LINUX
  sigprocmask(SIG_UNBLOCK, &defer_abrt, NULL);
#endif // E_ACSL_OS_IS_LINUX
  raise_abort(file, line);
}

void private_assert_fail(int expr, const char *file, int line, char *fmt, ...) {
  if (!expr) {
    char *afmt = "%s:%d: %s";
    char buf[strlen(fmt) + strlen(afmt) + PATH_MAX + 11];
    rtl_snprintf(buf, sizeof(buf), afmt, file, line, fmt);
    fmt = buf;

    va_list va;
    va_start(va, fmt);
    rtl_veprintf(fmt, va);
    va_end(va);
    raise_abort(file, line);
  }
}
