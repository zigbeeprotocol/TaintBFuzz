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
 * \brief  Drop-in replacements for C library functions from string.h
 **************************************************************************/

#ifndef E_ACSL_STRING_H
#define E_ACSL_STRING_H

#include <stddef.h>
#include <stdint.h>

#include "../internals/e_acsl_alias.h"

#define eacsl_builtin_strlen  export_alias(builtin_strlen)
#define eacsl_builtin_strcpy  export_alias(builtin_strcpy)
#define eacsl_builtin_strncpy export_alias(builtin_strncpy)
#define eacsl_builtin_strcat  export_alias(builtin_strcat)
#define eacsl_builtin_strncat export_alias(builtin_strncat)
#define eacsl_builtin_strcmp  export_alias(builtin_strcmp)
#define eacsl_builtin_strncmp export_alias(builtin_strncmp)
#define eacsl_builtin_memcpy  export_alias(builtin_memcpy)
#define eacsl_builtin_memset  export_alias(builtin_memset)
#define eacsl_builtin_memcmp  export_alias(builtin_memcmp)
#define eacsl_builtin_memmove export_alias(builtin_memmove)

/************************************************************************/
/*** Support functionality {{{ ***/
/************************************************************************/

/* *** String validation {{{ */

/*! \brief Determine if `s` describes a C string up to length `n`.

   @return the index of `\0` character (i.e., the length of the string)
     if `s` is a valid pointer of byte-size `len`, and
       - `n` is negative and there is `\0` between `s` and the end of
       the block `s` points to.
       - `n` is positive and there is `\0` at index `i` (`i` < `n`)
       and `s+i` belongs to the same block as `s`.
    @return `n` if there is no `\0` between `s` and `s+n-1` but both
       `s` and `s+n-1` belong to the same block.

   @return -1 if `s` does not belong to tracked allocation
   @return -2 if `wrtbl` is set to a non-zero value and `s` is read-only
   @return -3 if there is no `\0` between `s` and the end of its block and
    `s+n-1` is unallocated or belongs to a different block.
   @return -4 if `n` is negative and `s` is not NUL-terminated */
long valid_nstring(char *s, long n, int wrtbl);

/*!\brief Same as ::valid_nstring but for wide characters.

   This function is very similar to ::valid_nstring. It is possible make it
   more concise (say define it as a macro with types provided explicitly) yet
   it is left this way for readibility reasons. */
long valid_nwstring(wchar_t *s, long n, int wrtbl);

/*! \brief Same as ::valid_nstring but check a NUL-terminated string */
long inline valid_string(char *s, int wrtbl) {
  return valid_nstring(s, -1, wrtbl);
}

/*! \brief same as ::valid_string but for wide characters */
long inline valid_wstring(wchar_t *s, int wrtbl) {
  return valid_nwstring(s, -1, wrtbl);
}
/* }}} */

/* *** Memory spaces {{{ */
/** \brief Return a true value if memory spaces given by intervals
    [s1, s1 + s1_sz] and [s2, s2 + s2_sz] are disjoint */
int disjoint_spaces(uintptr_t s1, size_t s1_sz, uintptr_t s2, size_t s2_sz);
/* }}} */
/* }}} */

/************************************************************************/
/*** strlen/strcpy/strcat/strcmp {{{ ***/
/************************************************************************/

/* drop-in replacement for `strlen` */
/*@ assigns \result \from s[0..]; */
size_t eacsl_builtin_strlen(const char *s) __attribute__((FC_BUILTIN));

/* drop-in replacement for `strcpy` */
/*@ assigns dest[0..] \from src[0..];
  @ assigns \result \from dest;
  @ ensures \result == dest; */
char *eacsl_builtin_strcpy(char *dest, const char *src)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `strncpy` */
/*@ assigns dest[0..n - 1] \from src[0..n-1];
  @ assigns \result \from dest;
  @ ensures \result == dest; */
char *eacsl_builtin_strncpy(char *dest, const char *src, size_t n)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `strcmp` */
/*@ assigns \result \from s1[0..], s2[0..]; */
int eacsl_builtin_strcmp(const char *s1, const char *s2)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `strncmp` */
/*@ assigns \result \from s1[0..n-1], s2[0..n-1]; */
int eacsl_builtin_strncmp(const char *s1, const char *s2, size_t n)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `strcat` */
/*@ assigns dest[..] \from src[0..];
  @ assigns \result \from dest;
  @ ensures \result == dest; */
char *eacsl_builtin_strcat(char *dest, const char *src)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `strncat` */
/*@ assigns dest[..] \from src[0..n];
  @ assigns \result \from dest;
  @ ensures \result == dest; */
char *eacsl_builtin_strncat(char *dest, const char *src, size_t n)
    __attribute__((FC_BUILTIN));
/* }}} */

/************************************************************************/
/*** memcpy/memcmp/memset/memmove {{{ ***/
/************************************************************************/

/* drop-in replacement for `memcpy` */
/*@ assigns ((char*)dest)[0..n-1] \from ((char*)src)[0..n-1];
  @ assigns \result \from dest;
  @ ensures \result == dest; */
void *eacsl_builtin_memcpy(void *dest, const void *src, size_t n)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `memset` */
/*@ assigns ((char*)s)[0..n-1] \from c;
  @ assigns \result \from s;
  @ ensures \result == s; */
void *eacsl_builtin_memset(void *s, int c, size_t n)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `memcmp` */
/*@ assigns \result \from ((char*)s1)[0..n-1], ((char*)s2)[0..n-1]; */
int eacsl_builtin_memcmp(const void *s1, const void *s2, size_t n)
    __attribute__((FC_BUILTIN));

/* drop-in replacement for `memmove` */
/*@ assigns ((char*)dest)[0..n-1] \from ((char*)src)[0..n-1];
  @ assigns \result \from dest;
  @ ensures \result == dest; */
void *eacsl_builtin_memmove(void *dest, const void *src, size_t n)
    __attribute__((FC_BUILTIN));

/* }}} */

#endif // E_ACSL_STRING_H
