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
 * \brief Prototypes of functions belonging to GNU Multiple
 * Precision Arithmetic Library (GMP) used within E-ACSL
 **************************************************************************/

/******************/
/* GMP prototypes */
/******************/

#ifndef E_ACSL_GMP_API_H
#define E_ACSL_GMP_API_H

#include "../internals/e_acsl_alias.h"
#include <stddef.h>
#include <stdio.h>

#define eacsl_mpz_struct  export_alias(mpz_struct)
#define eacsl_mpz_t       export_alias(mpz_t)
#define eacsl_mpq_struct  export_alias(mpq_struct)
#define eacsl_mpq_t       export_alias(mpq_t)
#define eacsl_mp_bitcnt_t export_alias(mp_bitcnt_t)

struct eacsl_mpz_struct {
  int _mp_alloc;
  int _mp_size;
  unsigned long *_mp_d;
};

typedef struct eacsl_mpz_struct eacsl_mpz_struct;
typedef eacsl_mpz_struct(__attribute__((FC_BUILTIN)) eacsl_mpz_t)[1];

struct eacsl_mpq_struct {
  eacsl_mpz_struct _mp_num;
  eacsl_mpz_struct _mp_den;
};

typedef struct eacsl_mpq_struct eacsl_mpq_struct;
typedef eacsl_mpq_struct(__attribute__((FC_BUILTIN)) eacsl_mpq_t)[1];

/**
 * Counts of bits of a multi-precision number are represented in the C type
 * eacsl_mp_bitcnt_t. Currently this is always an unsigned long, but on some
 * systems it will be an unsigned long long in the future.
 * @see https://gmplib.org/manual/Nomenclature-and-Types#Nomenclature-and-Types
 */
typedef unsigned long int eacsl_mp_bitcnt_t;

/****************/
/* Initializers */
/****************/

/*@ ghost extern int __e_acsl_init; */

/*@ requires ! \initialized(z);
  @ ensures \valid(z);
  @ allocates z;
  @ assigns *z \from __e_acsl_init; */
extern void __gmpz_init(eacsl_mpz_t z) __attribute__((FC_BUILTIN));

/*@ requires ! \initialized(q);
  @ ensures \valid(q);
  @ allocates q;
  @ assigns *q \from __e_acsl_init; */
extern void __gmpq_init(eacsl_mpq_t q) __attribute__((FC_BUILTIN));

/*@ requires \valid_read(z_orig);
  @ requires ! \initialized(z);
  @ allocates z;
  @ ensures \valid(z);
//  @ ensures z->n == z_orig->n;
  @ assigns *z \from *z_orig; */
extern void __gmpz_init_set(eacsl_mpz_t z, const eacsl_mpz_t z_orig)
    __attribute__((FC_BUILTIN));

/*@ requires ! \initialized(z);
  @ allocates z;
  @ ensures \valid(z);
  @ ensures \initialized(z);
//  @ ensures z->n == n;
  @ assigns *z \from n; */
extern void __gmpz_init_set_ui(eacsl_mpz_t z, unsigned long int n)
    __attribute__((FC_BUILTIN));

/*@ requires ! \initialized(z);
  @ allocates z;
  @ ensures \valid(z);
  @ ensures \initialized(z);
//  @ ensures z->n == n;
  @ assigns *z \from n; */
extern void __gmpz_init_set_si(eacsl_mpz_t z, signed long int n)
    __attribute__((FC_BUILTIN));

/*@ requires ! \initialized(z);
  @ allocates z;
  @ ensures \valid(z);
  @ ensures \initialized(z);
  @ assigns *z \from str[0..],base;
  @ assigns \result \from str[0..],base; */
extern int __gmpz_init_set_str(eacsl_mpz_t z, const char *str, int base)
    __attribute__((FC_BUILTIN));

/*@ requires ! \initialized(z);
  @ allocates z;
  @ ensures \valid(z);
  @ ensures \initialized(z);
  @ assigns *z \from base; */
extern void __gmpz_import(eacsl_mpz_t z, size_t, int, size_t, int, size_t,
                          const void *base) __attribute__((FC_BUILTIN));

/***************/
/* Assignments */
/***************/

/*@ requires \valid_read(z_orig);
  @ requires \valid(z);
//  @ ensures z->n == z_orig->n;
  @ assigns *z \from *z_orig; */
extern void __gmpz_set(eacsl_mpz_t z, const eacsl_mpz_t z_orig)
    __attribute__((FC_BUILTIN));

/*@ requires \valid_read(q_orig);
  @ requires \valid(q);
  @ assigns *q \from *q_orig; */
extern void __gmpq_set(eacsl_mpq_t q, const eacsl_mpq_t q_orig)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(q);
  @ assigns *q \from d; */
extern void __gmpq_set_d(eacsl_mpq_t q, double d) __attribute__((FC_BUILTIN));

/*@ requires \valid(q);
  @ assigns *q \from n,d; */
extern void __gmpq_set_ui(eacsl_mpq_t q, unsigned long int n,
                          unsigned long int d) __attribute__((FC_BUILTIN));

/*@ requires \valid(q);
  @ assigns *q \from n,d; */
extern void __gmpq_set_si(eacsl_mpq_t q, signed long int n, unsigned long int d)
    __attribute__((FC_BUILTIN));

/*@ requires \valid_read(z_orig);
  @ requires \valid(q);
  @ assigns *q \from *z_orig; */
extern void __gmpq_set_z(eacsl_mpq_t q, const eacsl_mpz_t z_orig)
    __attribute__((FC_BUILTIN));

/*@ allocates q;
  @ ensures \valid(q);
  @ ensures \initialized(q);
  @ assigns *q \from str[0..],base;
  @ assigns \result \from str[0..],base; */
extern int __gmpq_set_str(eacsl_mpq_t q, const char *str, int base)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(z);
  @ assigns *z \from n; */
extern void __gmpz_set_ui(eacsl_mpz_t z, unsigned long int n)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(z);
//  @ ensures z->n == n;
  @ assigns *z \from n; */
extern void __gmpz_set_si(eacsl_mpz_t z, signed long int n)
    __attribute__((FC_BUILTIN));

/*@ requires \valid_read(q_orig);
  @ requires \valid(z);
  @ assigns *z \from *q_orig; */
extern void __gmpz_set_q(eacsl_mpz_t z, const eacsl_mpq_t q_orig)
    __attribute__((FC_BUILTIN));

/*************/
/* Finalizer */
/*************/

/*@ requires \valid(x);
//  @ frees x;
  @ assigns *x \from *x; */
extern void __gmpz_clear(eacsl_mpz_t x) __attribute__((FC_BUILTIN));

/*@ requires \valid(x);
//  @ frees x;
  @ assigns *x \from *x; */
extern void __gmpq_clear(eacsl_mpq_t x) __attribute__((FC_BUILTIN));

/********************/
/* Logical operator */
/********************/

/*@ requires \valid_read(z1);
  @ requires \valid_read(z2);
  @ assigns \result \from *z1, *z2; */
extern int __gmpz_cmp(const eacsl_mpz_t z1, const eacsl_mpz_t z2)
    __attribute__((FC_BUILTIN));

/*@ requires \valid_read(q1);
  @ requires \valid_read(q2);
  @ assigns \result \from *q1, *q2; */
extern int __gmpq_cmp(const eacsl_mpq_t q1, const eacsl_mpq_t q2)
    __attribute__((FC_BUILTIN));

/************************/
/* Arithmetic operators */
/************************/

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ assigns *z1 \from *z2; */
extern void __gmpz_neg(eacsl_mpz_t z1, const eacsl_mpz_t z2)
    __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_add(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                       const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(q1);
  @ requires \valid_read(q2);
  @ requires \valid_read(q3);
  @ assigns *q1 \from *q2, *q3; */
extern void __gmpq_add(eacsl_mpq_t q1, const eacsl_mpq_t q2,
                       const eacsl_mpq_t q3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_sub(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                       const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(q1);
  @ requires \valid_read(q2);
  @ requires \valid_read(q3);
  @ assigns *q1 \from *q2, *q3; */
extern void __gmpq_sub(eacsl_mpq_t q1, const eacsl_mpq_t q2,
                       const eacsl_mpq_t q3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_mul(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                       const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ assigns *z1 \from *z2, n; */
extern void __gmpz_mul_2exp(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                            eacsl_mp_bitcnt_t n) __attribute__((FC_BUILTIN));

/*@ requires \valid(q1);
  @ requires \valid_read(q2);
  @ requires \valid_read(q3);
  @ assigns *q1 \from *q2, *q3; */
extern void __gmpq_mul(eacsl_mpq_t q1, const eacsl_mpq_t q2,
                       const eacsl_mpq_t q3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_tdiv_q(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                          const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_tdiv_r(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                          const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ assigns *z1 \from *z2, n; */
extern void __gmpz_tdiv_q_2exp(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                               eacsl_mp_bitcnt_t n) __attribute__((FC_BUILTIN));

/*@ requires \valid(q1);
  @ requires \valid_read(q2);
  @ requires \valid_read(q3);
  @ assigns *q1 \from *q2, *q3; */
extern void __gmpq_div(eacsl_mpq_t q1, const eacsl_mpq_t q2,
                       const eacsl_mpq_t q3) __attribute__((FC_BUILTIN));

/*********************/
/* Bitwise operators */
/*********************/

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_and(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                       const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_ior(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                       const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ requires \valid_read(z3);
  @ assigns *z1 \from *z2, *z3; */
extern void __gmpz_xor(eacsl_mpz_t z1, const eacsl_mpz_t z2,
                       const eacsl_mpz_t z3) __attribute__((FC_BUILTIN));

/*@ requires \valid(z1);
  @ requires \valid_read(z2);
  @ assigns *z1 \from *z2;
  @ assigns \result \from *z1,*z2; */
extern int __gmpz_com(eacsl_mpz_t z1, const eacsl_mpz_t z2)
    __attribute__((FC_BUILTIN));

/************************/
/* Coercions to C types */
/************************/

/** Return non-zero iff the value of z fits in an unsigned long */
/*@ requires \valid_read(z);
  @ assigns \result \from *z; */
extern int __gmpz_fits_ulong_p(const eacsl_mpz_t z) __attribute__((FC_BUILTIN));

/** Return non-zero iff the value of z fits in a signed long */
/*@ requires \valid_read(z);
  @ assigns \result \from *z; */
extern int __gmpz_fits_slong_p(const eacsl_mpz_t z) __attribute__((FC_BUILTIN));

/*@ requires \valid_read(z);
  @ assigns \result \from *z; */
extern long __gmpz_get_si(const eacsl_mpz_t z) __attribute__((FC_BUILTIN));

/*@ requires \valid_read(q);
  @ assigns \result \from *q; */
extern double __gmpq_get_d(const eacsl_mpq_t q) __attribute__((FC_BUILTIN));

/*@ requires \valid_read(z);
  @ assigns \result \from *z; */
extern unsigned long __gmpz_get_ui(const eacsl_mpz_t z)
    __attribute__((FC_BUILTIN));

/************************/
/* Output functions     */
/************************/

extern int __gmp_fprintf(FILE *fp, const char *fmt, ...)
    __attribute__((FC_BUILTIN));

#endif
