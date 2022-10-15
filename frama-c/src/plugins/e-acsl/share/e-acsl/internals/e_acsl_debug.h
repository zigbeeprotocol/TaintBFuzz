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
 * \brief  Debug-level functions and macros
 **************************************************************************/

#ifndef E_ACSL_DEBUG_H
#define E_ACSL_DEBUG_H

/* Stringification macros {{{ */
#ifndef E_ACSL_STRINGIFICATION
// clang-format off
#  define E_ACSL_STRINGIFICATION
#  define STRINGIFY(x) #x
#  define TOSTRING(x)  STRINGIFY(x)
#  define __AT__       __FILE__ ":" TOSTRING(__LINE__)
// clang-format on
#endif
/* }}} */

/** Debugging support {{{
 * Enabled in the presence of the E_ACSL_DEBUG macro */
#ifdef E_ACSL_DEBUG

#  define E_ACSL_DEBUG_DESC "debug"

#  include "e_acsl_private_assert.h"
#  include "e_acsl_rtl_io.h"

#  include <stdio.h>

/* Default location of the E_ACSL log file */
#  ifndef E_ACSL_DEBUG_LOG
#    define E_ACSL_DEBUG_LOG -
#  endif

/*! \brief File descriptor associated with the debug log file */
int dlog_fd;

/*! \brief Output a message to a log file */
#  define DLOG(...) rtl_dprintf(dlog_fd, __VA_ARGS__)

#  ifdef E_ACSL_DEBUG_VERBOSE
#    define DVLOG(...) rtl_dprintf(dlog_fd, __VA_ARGS__)
#  else
#    define DVLOG(...)
#  endif

/*! \brief Debug-time assertion based on assert (see e_acsl_assert.h) */
#  define DASSERT(_e) private_assert(_e, TOSTRING(_e), NULL)

/*! \brief Debug-time assertion based on vassert (see e_acsl_assert.h) */
#  define DVASSERT(_expr, _fmt_and_args...) private_assert(_expr, _fmt_and_args)

#  define DVABORT(_fmt_and_args...) private_abort(_fmt_and_args)

/*! \brief Initialize debug report file:
 *  - open file descriptor
 *  - add program arguments to the log */
void initialize_report_file(int *argc, char ***argv);

int debug_stop_number;
#  define DSTOP                                                                \
    {                                                                          \
      DLOG(" << ***** "                                                        \
           "Debug Stop %d in '%s' at %s:%d"                                    \
           " ***** >> ",                                                       \
           ++debug_stop_number, __func__, __FILE__, __LINE__);                 \
      getchar();                                                               \
    }

#else
#  define E_ACSL_DEBUG_DESC "production"
#  define DSTOP
#  define initialize_report_file(...)
#  define DLOG(...)
#  define DVLOG(...)
#  define DASSERT(_e)
#  define DVASSERT(_expr, _fmt, ...)
#  define DVABORT(_fmt, ...)
#endif // E_ACSL_DEBUG
// }}}

/*! Print a header indicating current configuration of a run to STDIN. */
void describe_run();

#endif // E_ACSL_DEBUG_H
