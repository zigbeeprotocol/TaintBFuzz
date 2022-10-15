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
 * \brief E-ACSL assertions and abort statements implementation.
 **************************************************************************/

#include <stdlib.h>

#include "../internals/e_acsl_private_assert.h"
#include "../internals/e_acsl_rtl_io.h"

#include "e_acsl_assert.h"

int eacsl_runtime_sound_verdict = 1;

void eacsl_print_values(eacsl_assert_data_t *data) {
  eacsl_assert_data_value_t *value = data->values;
  if (value != NULL) {
    STDERR("\tWith values at failure point:\n");
  }
  while (value != NULL) {
    eacsl_print_value(value);
    value = value->next;
  }
}

/*! Print the given integer to `stream` */
void eacsl_print_int_content(FILE *stream,
                             eacsl_assert_data_int_content_t *int_content) {
  if (int_content->is_enum) {
    fprintf(stream, "<enum> ");
  }
  switch (int_content->kind) {
  case E_ACSL_IBOOL:
    fprintf(stream, "%d", int_content->value.value_bool);
    break;
  case E_ACSL_ICHAR:
    fprintf(stream, "%d", int_content->value.value_char);
    break;
  case E_ACSL_ISCHAR:
    fprintf(stream, "%hhd", int_content->value.value_schar);
    break;
  case E_ACSL_IUCHAR:
    fprintf(stream, "%hhu", int_content->value.value_uchar);
    break;
  case E_ACSL_IINT:
    fprintf(stream, "%d", int_content->value.value_int);
    break;
  case E_ACSL_IUINT:
    fprintf(stream, "%u", int_content->value.value_uint);
    break;
  case E_ACSL_ISHORT:
    fprintf(stream, "%hd", int_content->value.value_short);
    break;
  case E_ACSL_IUSHORT:
    fprintf(stream, "%hu", int_content->value.value_ushort);
    break;
  case E_ACSL_ILONG:
    fprintf(stream, "%ld", int_content->value.value_long);
    break;
  case E_ACSL_IULONG:
    fprintf(stream, "%lu", int_content->value.value_ulong);
    break;
  case E_ACSL_ILONGLONG:
    fprintf(stream, "%lld", int_content->value.value_llong);
    break;
  case E_ACSL_IULONGLONG:
    fprintf(stream, "%llu", int_content->value.value_ullong);
    break;
  case E_ACSL_IMPZ:
    __gmp_fprintf(stream, "%Zd", int_content->value.value_mpz);
    break;
  }
}

/*! Print the given real to `stream`. */
void eacsl_print_real_content(FILE *stream,
                              eacsl_assert_data_real_content_t *real_content) {
  switch (real_content->kind) {
  case E_ACSL_RFLOAT:
    fprintf(stream, "%e", real_content->value.value_float);
    break;
  case E_ACSL_RDOUBLE:
    fprintf(stream, "%le", real_content->value.value_double);
    break;
  case E_ACSL_RLONGDOUBLE:
    fprintf(stream, "%Le", real_content->value.value_ldouble);
    break;
  case E_ACSL_RMPQ:
    __gmp_fprintf(stream, "%Qd", real_content->value.value_mpq);
    break;
  }
}

void eacsl_print_value_content(FILE *stream, eacsl_assert_data_value_t *value) {
  switch (value->type) {
  case E_ACSL_INT:
    eacsl_print_int_content(stream, &value->content.int_content);
    break;
  case E_ACSL_REAL:
    eacsl_print_real_content(stream, &value->content.real_content);
    break;
  case E_ACSL_PTR:
    fprintf(stream, "%p", value->content.value_ptr);
    break;
  case E_ACSL_ARRAY:
    fprintf(stream, "<array>, address: %p", value->content.value_array);
    break;
  case E_ACSL_FUN:
    fprintf(stream, "<function>");
    break;
  case E_ACSL_STRUCT:
    fprintf(stream, "<struct>");
    break;
  case E_ACSL_UNION:
    fprintf(stream, "<union>");
    break;
  case E_ACSL_OTHER:
    fprintf(stream, "<other>");
    break;
  default:
    fprintf(stream, "<unknown>");
  }
}

#ifndef E_ACSL_EXTERNAL_ASSERT

/*! \brief Return `str` id `cond` is true, an empty string otherwise. */
#  define STR_IF(cond, str) ((cond) ? (str) : "")
/*! \brief Return `str` if the string is not null, an empty string otherwise. */
#  define STR_IF_NOT_NULL(str) STR_IF(str, str)

/*! \brief Default implementation of E-ACSL runtime assertions */
void eacsl_runtime_assert(int predicate, eacsl_assert_data_t *data) {
  if (eacsl_runtime_sound_verdict) {
    if (!predicate) {
      RTL_IO_LOCK();
      // clang-format off
      STDERR("%s: In function '%s'\n"
             "%s:%d: Error: %s failed:\n"
             "\tThe failing predicate is:\n"
             "\t%s%s%s.\n",
             data->file, data->fct,
             data->file, data->line, data->kind,
             STR_IF_NOT_NULL(data->name),
             STR_IF(data->name, ":\n\t\t"),
             data->pred_txt);
      // clang-format on
      eacsl_print_values(data);
      RTL_IO_UNLOCK();
      if (data->blocking) {
#  ifndef E_ACSL_NO_ASSERT_FAIL /* Do fail on assertions */
#    ifdef E_ACSL_FAIL_EXITCODE /* Fail by exit with a given code */
        exit(E_ACSL_FAIL_EXITCODE);
#    else
        raise_abort(data->file, data->line); /* Raise abort signal */
#    endif
#  endif
      }
    }
#  ifdef E_ACSL_DEBUG_ASSERT
    else {
      RTL_IO_LOCK();
      // clang-format off
      STDERR("%s: In function '%s'\n"
             "%s:%d: %s valid:\n"
             "\t%s%s%s.\n",
             data->file, data->fct,
             data->file, data->line, data->kind,
             STR_IF_NOT_NULL(data->name),
             STR_IF(data->name, ":\n\t\t"),
             data->pred_txt);
      // clang-format on
      eacsl_print_values(data);
      RTL_IO_UNLOCK();
    }
#  endif
  } else {
    RTL_IO_LOCK();
    // clang-format off
    STDERR("%s: In function '%s'\n"
           "%s:%d: Warning: no sound verdict for %s (guess: %s).\n"
           "\tthe considered predicate is:\n"
           "\t%s%s%s\n",
           data->file, data->fct,
           data->file, data->line, data->kind, predicate ? "ok" : "FAIL",
           STR_IF_NOT_NULL(data->name),
           STR_IF(data->name, ":\n\t\t"),
           data->pred_txt);
    // clang-format on
    eacsl_print_values(data);
    RTL_IO_UNLOCK();
  }
}
#endif

#ifndef E_ACSL_EXTERNAL_PRINT_VALUE
void eacsl_print_value(eacsl_assert_data_value_t *value) {
  fprintf(stderr, "\t- %s: ", value->name);
  if (value->type == E_ACSL_ARRAY) {
    // The function `eacsl_print_value_content()` prints the content of an array
    // on one line to be more generic towards alternative implementation.
    // For the default implementation we can override it to print something more
    // consistent with the way the name of the value is printed.
    fprintf(stderr, "<array>\n\t\t- address: %p", value->content.value_array);
  } else {
    eacsl_print_value_content(stderr, value);
  }
  fprintf(stderr, "\n");
}
#endif
