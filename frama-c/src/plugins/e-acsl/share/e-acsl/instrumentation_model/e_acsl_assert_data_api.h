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

#ifndef E_ACSL_ASSERT_DATA_API_H
#define E_ACSL_ASSERT_DATA_API_H

#include "../internals/e_acsl_alias.h"
#include "../numerical_model/e_acsl_gmp_api.h"
#include "e_acsl_assert_data.h"

#ifdef __FC_FEATURES_H
#  include <__fc_alloc_axiomatic.h>
#else
/*@ ghost extern int __fc_heap_status; */
#endif

#define eacsl_assert_register_bool      export_alias(assert_register_bool)
#define eacsl_assert_register_char      export_alias(assert_register_char)
#define eacsl_assert_register_schar     export_alias(assert_register_schar)
#define eacsl_assert_register_uchar     export_alias(assert_register_uchar)
#define eacsl_assert_register_int       export_alias(assert_register_int)
#define eacsl_assert_register_uint      export_alias(assert_register_uint)
#define eacsl_assert_register_short     export_alias(assert_register_short)
#define eacsl_assert_register_ushort    export_alias(assert_register_ushort)
#define eacsl_assert_register_long      export_alias(assert_register_long)
#define eacsl_assert_register_ulong     export_alias(assert_register_ulong)
#define eacsl_assert_register_longlong  export_alias(assert_register_longlong)
#define eacsl_assert_register_ulonglong export_alias(assert_register_ulonglong)
#define eacsl_assert_register_mpz       export_alias(assert_register_mpz)
#define eacsl_assert_register_float     export_alias(assert_register_float)
#define eacsl_assert_register_double    export_alias(assert_register_double)
#define eacsl_assert_register_longdouble                                       \
  export_alias(assert_register_longdouble)
#define eacsl_assert_register_mpq    export_alias(assert_register_mpq)
#define eacsl_assert_register_ptr    export_alias(assert_register_ptr)
#define eacsl_assert_register_array  export_alias(assert_register_array)
#define eacsl_assert_register_fun    export_alias(assert_register_fun)
#define eacsl_assert_register_struct export_alias(assert_register_struct)
#define eacsl_assert_register_union  export_alias(assert_register_union)
#define eacsl_assert_register_other  export_alias(assert_register_other)
#define eacsl_assert_copy_values     export_alias(assert_copy_values)
#define eacsl_assert_clean           export_alias(assert_clean)

/************************************************************************/
/*** Register integers {{{ ***/
/************************************************************************/

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_bool(eacsl_assert_data_t *data, const char *name,
                                int is_enum, _Bool value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_char(eacsl_assert_data_t *data, const char *name,
                                int is_enum, char value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_schar(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, signed char value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_uchar(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, unsigned char value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value; */
/* @ // admit ensures \valid(data->values); */
void eacsl_assert_register_int(eacsl_assert_data_t *data, const char *name,
                               int is_enum, int value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_uint(eacsl_assert_data_t *data, const char *name,
                                int is_enum, unsigned int value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_short(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, short value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_ushort(eacsl_assert_data_t *data, const char *name,
                                  int is_enum, unsigned short value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_long(eacsl_assert_data_t *data, const char *name,
                                int is_enum, long value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_ulong(eacsl_assert_data_t *data, const char *name,
                                 int is_enum, unsigned long value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_longlong(eacsl_assert_data_t *data, const char *name,
                                    int is_enum, long long value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_ulonglong(eacsl_assert_data_t *data,
                                     const char *name, int is_enum,
                                     unsigned long long value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_mpz(eacsl_assert_data_t *data, const char *name,
                               int is_enum, const eacsl_mpz_t value)
    __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** Register reals {{{ ***/
/************************************************************************/

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_float(eacsl_assert_data_t *data, const char *name,
                                 float value) __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_double(eacsl_assert_data_t *data, const char *name,
                                  double value) __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_longdouble(eacsl_assert_data_t *data,
                                      const char *name, long double value)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, value;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_mpq(eacsl_assert_data_t *data, const char *name,
                               const eacsl_mpq_t value)
    __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** Register pointers {{{ ***/
/************************************************************************/

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, ptr;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_ptr(eacsl_assert_data_t *data, const char *name,
                               void *ptr) __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status, array;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_array(eacsl_assert_data_t *data, const char *name,
                                 void *array) __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** Register composite {{{ ***/
/************************************************************************/

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_fun(eacsl_assert_data_t *data, const char *name)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_struct(eacsl_assert_data_t *data, const char *name)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_union(eacsl_assert_data_t *data, const char *name)
    __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** Register other types {{{ ***/
/************************************************************************/

/*@ requires \valid(data);
  @ requires data->values == \null || \valid(data->values);
  @ assigns data->values \from indirect:__fc_heap_status;
  @ // admit ensures \valid(data->values); */
void eacsl_assert_register_other(eacsl_assert_data_t *data, const char *name)
    __attribute__((FC_BUILTIN));

/* }}} */

/************************************************************************/
/*** Miscellaneous functions {{{ ***/
/************************************************************************/

/*@ requires \valid(dest) && \valid(src);
  @ requires dest->values == \null || \valid(dest->values);
  @ requires src->values == \null || \valid(src->values);
  @ assigns dest->values \from indirect:__fc_heap_status, indirect:src->values;
  @ // admit ensures dest->values == \null || \valid(dest->values); */
void eacsl_assert_copy_values(eacsl_assert_data_t *dest,
                              eacsl_assert_data_t *src)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(data);
  @ assigns \nothing; */
void eacsl_assert_clean(eacsl_assert_data_t *data) __attribute__((FC_BUILTIN));

/* }}} */

#endif // E_ACSL_ASSERT_DATA_API_H
