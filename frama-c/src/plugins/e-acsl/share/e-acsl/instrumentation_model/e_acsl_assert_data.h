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
 * \brief E-ACSL data for assertions.
 **************************************************************************/

#ifndef E_ACSL_ASSERT_DATA_H
#define E_ACSL_ASSERT_DATA_H

#include <stdint.h>

#include "../internals/e_acsl_alias.h"
#include "../numerical_model/e_acsl_gmp_api.h"

#define eacsl_assert_data_type_t        export_alias(assert_data_type_t)
#define eacsl_assert_data_ikind_t       export_alias(assert_data_ikind_t)
#define eacsl_assert_data_rkind_t       export_alias(assert_data_rkind_t)
#define eacsl_assert_data_int_value_t   export_alias(assert_data_int_value_t)
#define eacsl_assert_data_real_value_t  export_alias(assert_data_real_value_t)
#define eacsl_assert_data_int_content_t export_alias(assert_data_int_content_t)
#define eacsl_assert_data_real_content_t                                       \
  export_alias(assert_data_real_content_t)
#define eacsl_assert_data_content_t export_alias(assert_data_content_t)
#define eacsl_assert_data_value_t   export_alias(assert_data_value_t)
#define eacsl_assert_data_t         export_alias(assert_data_t)

/*! Type of data contributing to an assertion. */
typedef enum eacsl_assert_data_type_t {
  /*! Integer data. */
  E_ACSL_INT = 0,

  /*! Real data. */
  E_ACSL_REAL,

  /*! Pointer data. */
  E_ACSL_PTR,
  /*! Array data. */
  E_ACSL_ARRAY,
  /*! Function data. */
  E_ACSL_FUN,

  /*! Structure data. */
  E_ACSL_STRUCT,
  /*! Union data. */
  E_ACSL_UNION,

  /*! Other type of data. */
  E_ACSL_OTHER = 1000
} __attribute__((FC_BUILTIN)) eacsl_assert_data_type_t;

/*! Kind of integer */
typedef enum eacsl_assert_data_ikind_t {
  E_ACSL_IBOOL,
  E_ACSL_ICHAR,
  E_ACSL_ISCHAR,
  E_ACSL_IUCHAR,
  E_ACSL_IINT,
  E_ACSL_IUINT,
  E_ACSL_ISHORT,
  E_ACSL_IUSHORT,
  E_ACSL_ILONG,
  E_ACSL_IULONG,
  E_ACSL_ILONGLONG,
  E_ACSL_IULONGLONG,
  E_ACSL_IMPZ,
} __attribute__((FC_BUILTIN)) eacsl_assert_data_ikind_t;

/*! Kind of real */
typedef enum eacsl_assert_data_rkind_t {
  /*! Floating point data of type float. */
  E_ACSL_RFLOAT,
  /*! Floating point data of type double. */
  E_ACSL_RDOUBLE,
  /*! Floating point data of type long double. */
  E_ACSL_RLONGDOUBLE,
  /*! Rational data of type mpq_t. */
  E_ACSL_RMPQ,
} __attribute__((FC_BUILTIN)) eacsl_assert_data_rkind_t;

/*! Union type holding the value of an integer. */
typedef union eacsl_assert_data_int_value_t {
  _Bool value_bool;
  char value_char;
  signed char value_schar;
  unsigned char value_uchar;
  int value_int;
  unsigned int value_uint;
  short value_short;
  unsigned short value_ushort;
  long value_long;
  unsigned long value_ulong;
  long long value_llong;
  unsigned long long value_ullong;
  /* Store a pointer to `struct eacsl_mpz_struct` instead of a `mpz_t` value to
     optimize the size of the union. With this optimization the size of the
     union is `sizeof(unsigned long long)` whereas, without the optimization, it
     is at least `sizeof(int) + sizeof(int) + sizeof(unsigned long *)`.
     In return, we need to manually allocate the memory for
     `struct eacsl_mpz_struct` before calling `__gmpz_init_set()`. */
  struct eacsl_mpz_struct *value_mpz;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_int_value_t;

/*! Union type holding the value of a real. */
typedef union eacsl_assert_data_real_value_t {
  float value_float;
  double value_double;
  long double value_ldouble;
  /* Store a pointer to `struct eacsl_mpq_struct` instead of a `mpq_t` value to
     optimize the size of the union. With this optimization the size of the
     union is `sizeof(unsigned long long)` whereas, without the optimization, it
     is at least `2*sizeof(int) + 2*sizeof(int) + 2*sizeof(unsigned long *)`.
     In return, we need to manually allocate the memory for
     `struct eacsl_mpq_struct` before calling `__gmpq_init_set()`. */
  struct eacsl_mpq_struct *value_mpq;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_real_value_t;

/*! Value of an integer. */
typedef struct eacsl_assert_data_int_content_t {
  /*! True if the integer is an enum value, false otherwise */
  int is_enum;
  /*! Kind of integer. */
  eacsl_assert_data_ikind_t kind;
  /*! Value of the integer.
      The active member of the union is identified with the field `kind`. */
  eacsl_assert_data_int_value_t value;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_int_content_t;

/*! Value of a real. */
typedef struct eacsl_assert_data_real_content_t {
  /*! Kind of real. */
  eacsl_assert_data_rkind_t kind;
  /*! Value of the real.
      The active member of the union is identified with the field `kind`. */
  eacsl_assert_data_real_value_t value;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_real_content_t;

/*! Union type holding the value of a piece of data. */
typedef union eacsl_assert_data_content_t {
  eacsl_assert_data_int_content_t int_content;

  eacsl_assert_data_real_content_t real_content;

  uintptr_t value_ptr;
  uintptr_t value_array;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_content_t;

/*! Piece of data contributing to an assertion.

  The structure is a single linked list that will hold all data that contributed
  to the assertion. */
typedef struct eacsl_assert_data_value_t {
  /*! Name of the piece of data */
  const char *name;
  /*! Type of the piece of data */
  eacsl_assert_data_type_t type;
  /*! Value of the piece of data.
      The active member of the union is identified with the field `type`. */
  eacsl_assert_data_content_t content;
  /*! Pointer to the next value in the list, or NULL if this is the last
      value.
      We can use a list here because the number of data in an assertion is
      small enough. */
  struct eacsl_assert_data_value_t *next;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_value_t;

/*! Data holding context information for E-ACSL assertions. */
typedef struct eacsl_assert_data_t {
  /*! integer representing if the assertion is blocking or not */
  int blocking;
  /*! C string representing a kind of annotation (e.g., "Assertion") */
  const char *kind;
  /*! name identifying the predicate */
  const char *name;
  /*! stringified predicate */
  const char *pred_txt;
  /*! un-instrumented file of predicate placement */
  const char *file;
  /*! function of predicate placement in the un-instrumented file */
  const char *fct;
  /*! line of predicate placement in the un-instrumented file */
  int line;
  /*! values contributing to the predicate */
  eacsl_assert_data_value_t *values;
} __attribute__((FC_BUILTIN)) eacsl_assert_data_t;

#endif // E_ACSL_ASSERT_DATA_H
