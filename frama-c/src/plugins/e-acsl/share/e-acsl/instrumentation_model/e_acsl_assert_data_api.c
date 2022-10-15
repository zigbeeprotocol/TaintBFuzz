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
 * \brief E-ACSL utility functions for assertions.
 **************************************************************************/

#include <stdlib.h>
#include <string.h>

#include "../internals/e_acsl_debug.h"
#include "../internals/e_acsl_malloc.h"

#include "e_acsl_assert_data_api.h"

/**
 * Test for equality between the integer values `lhs` and `rhs`
 */
int eacsl_assert_data_int_equal(eacsl_assert_data_int_content_t *lhs,
                                eacsl_assert_data_int_content_t *rhs) {
  if (lhs->kind != rhs->kind) {
    return 0;
  } else if (lhs->is_enum != rhs->is_enum) {
    return 0;
  } else {
    switch (lhs->kind) {
    case E_ACSL_IBOOL:
      return lhs->value.value_bool == rhs->value.value_bool;
    case E_ACSL_ICHAR:
      return lhs->value.value_char == rhs->value.value_char;
    case E_ACSL_ISCHAR:
      return lhs->value.value_schar == rhs->value.value_schar;
    case E_ACSL_IUCHAR:
      return lhs->value.value_uchar == rhs->value.value_uchar;
    case E_ACSL_IINT:
      return lhs->value.value_int == rhs->value.value_int;
    case E_ACSL_IUINT:
      return lhs->value.value_uint == rhs->value.value_uint;
    case E_ACSL_ISHORT:
      return lhs->value.value_short == rhs->value.value_short;
    case E_ACSL_IUSHORT:
      return lhs->value.value_ushort == rhs->value.value_ushort;
    case E_ACSL_ILONG:
      return lhs->value.value_long == rhs->value.value_long;
    case E_ACSL_IULONG:
      return lhs->value.value_ulong == rhs->value.value_ulong;
    case E_ACSL_ILONGLONG:
      return lhs->value.value_llong == rhs->value.value_llong;
    case E_ACSL_IULONGLONG:
      return lhs->value.value_ullong == rhs->value.value_ullong;
    case E_ACSL_IMPZ:
      return __gmpz_cmp(lhs->value.value_mpz, rhs->value.value_mpz) == 0;
    }
    private_abort("Unsupported integer kind: %d\n", lhs->kind);
    return 1;
  }
}

/**
 * Test for equality between the real values `lhs` and `rhs`
 */
int eacsl_assert_data_real_equal(eacsl_assert_data_real_content_t *lhs,
                                 eacsl_assert_data_real_content_t *rhs) {
  if (lhs->kind != rhs->kind) {
    return 0;
  } else {
    switch (lhs->kind) {
    case E_ACSL_RFLOAT:
      return lhs->value.value_float == rhs->value.value_float;
    case E_ACSL_RDOUBLE:
      return lhs->value.value_double == rhs->value.value_double;
    case E_ACSL_RLONGDOUBLE:
      return lhs->value.value_ldouble == rhs->value.value_ldouble;
    case E_ACSL_RMPQ:
      return __gmpq_cmp(lhs->value.value_mpq, rhs->value.value_mpq) == 0;
    }
    private_abort("Unsupported real kind: %d\n", lhs->kind);
    return 1;
  }
}

/** Test for equality between the value `lhs` and the value represented by
 * `rhs_name`, `rhs_type` and `rhs_content`.
 */
int eacsl_assert_data_equal(eacsl_assert_data_value_t *lhs,
                            const char *rhs_name,
                            eacsl_assert_data_type_t rhs_type,
                            eacsl_assert_data_content_t *rhs_content) {
  if (lhs->type != rhs_type) {
    return 0;
  }
  if (strcmp(lhs->name, rhs_name) != 0) {
    return 0;
  }
  switch (lhs->type) {
  case E_ACSL_INT:
    return eacsl_assert_data_int_equal(&lhs->content.int_content,
                                       &rhs_content->int_content);
  case E_ACSL_REAL:
    return eacsl_assert_data_real_equal(&lhs->content.real_content,
                                        &rhs_content->real_content);
  case E_ACSL_PTR:
    return lhs->content.value_ptr == rhs_content->value_ptr;
  case E_ACSL_ARRAY:
    return lhs->content.value_array == rhs_content->value_array;
  case E_ACSL_FUN:
  case E_ACSL_STRUCT:
  case E_ACSL_UNION:
  case E_ACSL_OTHER:
    // No data for those cases so two values with the same names and types are
    // considered equal.
    return 1;
  }
  private_abort("Unsupported data type: %d\n", lhs->type);
  return 1;
}

void eacsl_assert_register_data(eacsl_assert_data_t *data, const char *name,
                                eacsl_assert_data_type_t type,
                                eacsl_assert_data_content_t content) {
  // Check if the value has already been registered
  eacsl_assert_data_value_t *value = data->values;
  while (value != NULL) {
    if (eacsl_assert_data_equal(value, name, type, &content)) {
      // The value has already been registered, return immediately
      return;
    }
    value = value->next;
  }

  // This is a new value, we need to add it to the context
  value = private_malloc(sizeof(eacsl_assert_data_value_t));
  DVASSERT(value != NULL,
           "Unable to allocate %d bytes of memory for assert_register_data_t",
           sizeof(eacsl_assert_data_value_t));
  value->name = name;
  value->type = type;
  value->content = content;
  value->next = data->values;
  data->values = value;
}

void eacsl_assert_register_generic_int(eacsl_assert_data_t *data,
                                       const char *name, int is_enum,
                                       eacsl_assert_data_ikind_t kind,
                                       eacsl_assert_data_int_value_t value) {
  eacsl_assert_register_data(
      data, name, E_ACSL_INT,
      (eacsl_assert_data_content_t){
          .int_content = {.kind = kind, .value = value, .is_enum = is_enum}});
}

void eacsl_assert_register_bool(eacsl_assert_data_t *data, const char *name,
                                int is_enum, _Bool value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IBOOL,
      (eacsl_assert_data_int_value_t){.value_bool = value});
}

void eacsl_assert_register_char(eacsl_assert_data_t *data, const char *name,
                                int is_enum, char value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_ICHAR,
      (eacsl_assert_data_int_value_t){.value_char = value});
}

void eacsl_assert_register_schar(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, signed char value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_ISCHAR,
      (eacsl_assert_data_int_value_t){.value_schar = value});
}

void eacsl_assert_register_uchar(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, unsigned char value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IUCHAR,
      (eacsl_assert_data_int_value_t){.value_uchar = value});
}

void eacsl_assert_register_int(eacsl_assert_data_t *data, const char *name,
                               int is_enum, int value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IINT,
      (eacsl_assert_data_int_value_t){.value_int = value});
}

void eacsl_assert_register_uint(eacsl_assert_data_t *data, const char *name,
                                int is_enum, unsigned int value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IUINT,
      (eacsl_assert_data_int_value_t){.value_uint = value});
}

void eacsl_assert_register_short(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, short value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_ISHORT,
      (eacsl_assert_data_int_value_t){.value_short = value});
}

void eacsl_assert_register_ushort(eacsl_assert_data_t *data, const char *name,
                                  int is_enum, unsigned short value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IUSHORT,
      (eacsl_assert_data_int_value_t){.value_ushort = value});
}

void eacsl_assert_register_long(eacsl_assert_data_t *data, const char *name,
                                int is_enum, long value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_ILONG,
      (eacsl_assert_data_int_value_t){.value_long = value});
}

void eacsl_assert_register_ulong(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, unsigned long value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IULONG,
      (eacsl_assert_data_int_value_t){.value_ulong = value});
}

void eacsl_assert_register_longlong(eacsl_assert_data_t *data, const char *name,
                                    int is_enum, long long value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_ILONGLONG,
      (eacsl_assert_data_int_value_t){.value_llong = value});
}

void eacsl_assert_register_ulonglong(eacsl_assert_data_t *data,
                                     const char *name, int is_enum,
                                     unsigned long long value) {
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IULONGLONG,
      (eacsl_assert_data_int_value_t){.value_ullong = value});
}

void eacsl_assert_register_mpz(eacsl_assert_data_t *data, const char *name,
                               int is_enum, const eacsl_mpz_t value) {
  struct eacsl_mpz_struct *new_value =
      private_malloc(sizeof(struct eacsl_mpz_struct));
  __gmpz_init_set(new_value, value);
  eacsl_assert_register_generic_int(
      data, name, is_enum, E_ACSL_IMPZ,
      (eacsl_assert_data_int_value_t){.value_mpz = new_value});
}

void eacsl_assert_register_generic_real(eacsl_assert_data_t *data,
                                        const char *name,
                                        eacsl_assert_data_rkind_t kind,
                                        eacsl_assert_data_real_value_t value) {
  eacsl_assert_register_data(
      data, name, E_ACSL_REAL,
      (eacsl_assert_data_content_t){
          .real_content = {.kind = kind, .value = value}});
}

void eacsl_assert_register_float(eacsl_assert_data_t *data, const char *name,
                                 float value) {
  eacsl_assert_register_generic_real(
      data, name, E_ACSL_RFLOAT,
      (eacsl_assert_data_real_value_t){.value_float = value});
}

void eacsl_assert_register_double(eacsl_assert_data_t *data, const char *name,
                                  double value) {
  eacsl_assert_register_generic_real(
      data, name, E_ACSL_RDOUBLE,
      (eacsl_assert_data_real_value_t){.value_double = value});
}

void eacsl_assert_register_longdouble(eacsl_assert_data_t *data,
                                      const char *name, long double value) {
  eacsl_assert_register_generic_real(
      data, name, E_ACSL_RLONGDOUBLE,
      (eacsl_assert_data_real_value_t){.value_ldouble = value});
}

void eacsl_assert_register_mpq(eacsl_assert_data_t *data, const char *name,
                               const eacsl_mpq_t value) {
  struct eacsl_mpq_struct *new_value =
      private_malloc(sizeof(struct eacsl_mpq_struct));
  __gmpq_init(new_value);
  __gmpq_set(new_value, value);
  eacsl_assert_register_generic_real(
      data, name, E_ACSL_RMPQ,
      (eacsl_assert_data_real_value_t){.value_mpq = new_value});
}

void eacsl_assert_register_ptr(eacsl_assert_data_t *data, const char *name,
                               void *ptr) {
  eacsl_assert_register_data(
      data, name, E_ACSL_PTR,
      (eacsl_assert_data_content_t){.value_ptr = (uintptr_t)ptr});
}

void eacsl_assert_register_array(eacsl_assert_data_t *data, const char *name,
                                 void *array) {
  eacsl_assert_register_data(
      data, name, E_ACSL_ARRAY,
      (eacsl_assert_data_content_t){.value_array = (uintptr_t)array});
}

void eacsl_assert_register_fun(eacsl_assert_data_t *data, const char *name) {
  eacsl_assert_register_data(data, name, E_ACSL_FUN,
                             (eacsl_assert_data_content_t){});
}

void eacsl_assert_register_struct(eacsl_assert_data_t *data, const char *name) {
  eacsl_assert_register_data(data, name, E_ACSL_STRUCT,
                             (eacsl_assert_data_content_t){});
}

void eacsl_assert_register_union(eacsl_assert_data_t *data, const char *name) {
  eacsl_assert_register_data(data, name, E_ACSL_UNION,
                             (eacsl_assert_data_content_t){});
}

void eacsl_assert_register_other(eacsl_assert_data_t *data, const char *name) {
  eacsl_assert_register_data(data, name, E_ACSL_OTHER,
                             (eacsl_assert_data_content_t){});
}

void eacsl_assert_free_value(eacsl_assert_data_value_t *value) {
  if (value != NULL) {
    switch (value->type) {
    case E_ACSL_INT:
      if (value->content.int_content.kind == E_ACSL_IMPZ) {
        __gmpz_clear(value->content.int_content.value.value_mpz);
        private_free(value->content.int_content.value.value_mpz);
      }
      break;
    case E_ACSL_REAL:
      if (value->content.real_content.kind == E_ACSL_RMPQ) {
        __gmpq_clear(value->content.real_content.value.value_mpq);
        private_free(value->content.real_content.value.value_mpq);
      }
      break;
    case E_ACSL_PTR:
    case E_ACSL_ARRAY:
    case E_ACSL_FUN:
    case E_ACSL_STRUCT:
    case E_ACSL_UNION:
    case E_ACSL_OTHER:
      // No allocated memory in value content
      break;
    }
    eacsl_assert_free_value(value->next);
    private_free(value);
  }
}

void eacsl_assert_copy_value(eacsl_assert_data_t *dest,
                             eacsl_assert_data_value_t *value) {
  if (value != NULL) {
    switch (value->type) {
    case E_ACSL_INT: {
      eacsl_assert_data_int_content_t content = value->content.int_content;
      if (content.kind == E_ACSL_IMPZ) {
        eacsl_assert_register_mpz(dest, value->name, content.is_enum,
                                  content.value.value_mpz);
      } else {
        eacsl_assert_register_generic_int(dest, value->name, content.is_enum,
                                          content.kind, content.value);
      }
      break;
    }
    case E_ACSL_REAL: {
      eacsl_assert_data_real_content_t content = value->content.real_content;
      if (content.kind == E_ACSL_RMPQ) {
        eacsl_assert_register_mpq(dest, value->name, content.value.value_mpq);
      } else {
        eacsl_assert_register_generic_real(dest, value->name, content.kind,
                                           content.value);
      }
      break;
    }
    case E_ACSL_PTR: {
      eacsl_assert_register_ptr(dest, value->name,
                                (void *)value->content.value_ptr);
      break;
    }
    case E_ACSL_ARRAY: {
      eacsl_assert_register_array(dest, value->name,
                                  (void *)value->content.value_array);
      break;
    }
    case E_ACSL_FUN: {
      eacsl_assert_register_fun(dest, value->name);
      break;
    }
    case E_ACSL_STRUCT: {
      eacsl_assert_register_struct(dest, value->name);
      break;
    }
    case E_ACSL_UNION: {
      eacsl_assert_register_union(dest, value->name);
      break;
    }
    case E_ACSL_OTHER: {
      eacsl_assert_register_other(dest, value->name);
      break;
    }
    }
  }
}

void eacsl_assert_copy_values(eacsl_assert_data_t *dest,
                              eacsl_assert_data_t *src) {
  eacsl_assert_copy_value(dest, src->values);
}

void eacsl_assert_clean(eacsl_assert_data_t *data) {
  eacsl_assert_free_value(data->values);
  data->values = NULL; // Protect against successive calls to clean.
}
