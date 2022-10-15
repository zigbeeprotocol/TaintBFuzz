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

#include <fcntl.h>
#include <sys/stat.h>

#include "../observation_model/internals/e_acsl_omodel_debug.h"
#include "e_acsl_config.h"
#include "e_acsl_private_assert.h"
#include "e_acsl_rtl_io.h"

#include "e_acsl_debug.h"

/** Debugging support {{{
 * Enabled in the presence of the E_ACSL_DEBUG macro */
#ifdef E_ACSL_DEBUG

/*! \brief Name of the debug log file */
static const char *dlog_name = TOSTRING(E_ACSL_DEBUG_LOG);

// Global vars initialization
int dlog_fd = -1;
int debug_stop_number = 0;

void initialize_report_file(int *argc, char ***argv) {
  /* Redirect the log to stderr is just set to be defined or set to '-' */
  if (!strcmp(dlog_name, "-") || !strcmp(dlog_name, "1")) {
    dlog_fd = 2;
  } else {
#  if E_ACSL_OS_IS_LINUX
    dlog_fd =
        open(dlog_name, O_WRONLY | O_CREAT | O_TRUNC | O_NONBLOCK | O_NOCTTY,
             S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH);
#  elif E_ACSL_OS_IS_WINDOWS
    dlog_fd =
        _open(dlog_name, _O_WRONLY | _O_CREAT | _O_TRUNC, _S_IREAD | _S_IWRITE);
#  endif
  }
  if (dlog_fd == -1)
    private_abort("Cannot open file descriptor for %s\n", dlog_name);
}

#endif // E_ACSL_DEBUG
// }}}

#ifdef E_ACSL_WEAK_VALIDITY
#  define E_ACSL_VALIDITY_DESC "weak"
#else
#  define E_ACSL_VALIDITY_DESC "strong"
#endif

#ifdef E_ACSL_NO_ASSERT_FAIL
#  define E_ACSL_ASSERT_NO_FAIL_DESC "pass through"
#else
#  define E_ACSL_ASSERT_NO_FAIL_DESC "abort"
#endif

#ifdef E_ACSL_TEMPORAL
#  define E_ACSL_TEMPORAL_DESC "enabled"
#else
#  define E_ACSL_TEMPORAL_DESC "disabled"
#endif // E_ACSL_TEMPORAL

#ifndef E_ACSL_VALIDATE_FORMAT_STRINGS
#  define E_ACSL_FORMAT_VALIDITY_DESC "disabled"
#else
#  define E_ACSL_FORMAT_VALIDITY_DESC "enabled"
#endif // E_ACSL_VALIDATE_FORMAT_STRINGS

void describe_run() {
#if defined(E_ACSL_VERBOSE)
  RTL_IO_LOCK();
  rtl_printf(
      "/* ========================================================= */\n");
  rtl_printf(" * E-ACSL instrumented run\n");
  rtl_printf(" * Execution mode:  %s\n", E_ACSL_DEBUG_DESC);
  describe_observation_model();
  rtl_printf(" * Assertions mode: %s\n", E_ACSL_ASSERT_NO_FAIL_DESC);
  rtl_printf(" * Validity notion: %s\n", E_ACSL_VALIDITY_DESC);
  rtl_printf(" * Temporal checks: %s\n", E_ACSL_TEMPORAL_DESC);
  rtl_printf(" * Format Checks:   %s\n", E_ACSL_FORMAT_VALIDITY_DESC);
  rtl_printf(
      "/* ========================================================= */\n");
  RTL_IO_UNLOCK();
#endif
}
