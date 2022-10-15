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

#include "../internals/e_acsl_private_assert.h"
#include "../internals/e_acsl_rtl_string.h"
#include "../observation_model/e_acsl_observation_model.h"

#include "e_acsl_string.h"

/* *** String validation {{{ */

long valid_nstring(char *s, long n, int wrtbl) {
  if (n == 0)
    return n;

  int alc = allocated((uintptr_t)s, 1, (uintptr_t)s);
  if (alc) {
    if (wrtbl && readonly(s))
      return -2; /* Not writeable */
    long size = eacsl_block_length(s) - eacsl_offset(s);
    long i;
    for (i = 0; i < size; i++) {
      if (s[i] == '\0' || n == i)
        return i;
    }
    if (n == size)
      return n;
    if (n > size)
      return -3; /* Insufficient length */
    return -4;   /* Not NUL-terminated */
  }
  return -1 /* Not allocated */;
}

long valid_nwstring(wchar_t *s, long n, int wrtbl) {
  if (n == 0)
    return n;

  int alc = allocated((uintptr_t)s, 1, (uintptr_t)s);
  if (alc) {
    if (wrtbl && readonly(s))
      return -2; /* Not writeable */
    long size = (eacsl_block_length(s) - eacsl_offset(s)) / sizeof(wchar_t);
    long i;
    for (i = 0; i < size; i++) {
      if (s[i] == L'\0' || n == i)
        return i;
    }
    if (n == size)
      return n;
    if (n > size)
      return -3; /* Insufficient length */
    return -4;   /* Not NUL-terminated */
  }
  return -1 /* Not allocated */;
}

static long validate_string(char *s, long n, int wrtbl, const char *fun,
                            const char *desc) {
  long size = valid_nstring(s, n, wrtbl);

  switch (size) {
  case -1:
    private_abort("%s: %sstring unallocated\n", fun, desc);
  case -2:
    private_abort("%s: %sstring is not writable\n", fun, desc);
  case -3:
    private_abort("%s: %sstring has insufficient length\n", fun, desc);
  case -4:
    private_abort("%s: %sstring not NUL-terminated\n", fun, desc);
  }
  /* at this point negative return values should have been handled */
  private_assert(size >= 0, "unexpected return value of %d\n", size);
  return size;
}

static inline long validate_writeable_string(char *s, long n, const char *fun,
                                             const char *desc) {
  return validate_string(s, n, 1, fun, desc);
}

static inline long validate_allocated_string(char *s, long n, const char *fun,
                                             const char *desc) {
  return validate_string(s, n, 0, fun, desc);
}
/* }}} */

/* *** Memory spaces {{{ */
int disjoint_spaces(uintptr_t s1, size_t s1_sz, uintptr_t s2, size_t s2_sz) {
  return s1 + s1_sz <= s2 || s2 + s2_sz <= s1;
}

static inline void validate_allocated_space(void *p, size_t sz,
                                            const char *func,
                                            const char *space) {
  if (!allocated((uintptr_t)p, sz, (uintptr_t)p)) {
    private_abort("%s: unallocated (or insufficient) space in %s\n", func,
                  space);
  }
}

static inline void validate_writeable_space(void *p, size_t sz,
                                            const char *func,
                                            const char *space) {
  if (!writeable((uintptr_t)p, sz, (uintptr_t)p)) {
    if (writeable((uintptr_t)p, 1, (uintptr_t)p)) {
      private_abort("%s: insufficient space in %s, "
                    "at least %lu bytes required\n",
                    func, space, sz);
    } else {
      private_abort("%s: %s space unallocated or cannot be written\n", func,
                    space);
    }
  }
}

static inline void validate_overlapping_spaces(uintptr_t s1, size_t s1_sz,
                                               uintptr_t s2, size_t s2_sz,
                                               const char *func) {
  if (!disjoint_spaces(s1, s1_sz, s2, s2_sz))
    private_abort("%s: overlapping memory areas\n", func);
}
/* }}} */
/* }}} */

/************************************************************************/
/*** strlen/strcpy/strcat/strcmp {{{ ***/
/************************************************************************/

size_t eacsl_builtin_strlen(const char *s) {
  return validate_allocated_string((char *)s, -1, "strlen", "input ");
}

char *eacsl_builtin_strcpy(char *dest, const char *src) {
  // `src` string should be a valid NUL-terminated C string
  size_t size =
      validate_allocated_string((char *)src, -1, "strlen", "source string ");
  /* `dest` should be writable and at least `size + 1` bytes long to
     accommodate the NUL-terminator */
  validate_writeable_space(dest, size + 1, "strlen", "destination string");
  /* source and destination strings should not overlap */
  validate_overlapping_spaces((uintptr_t)dest, size + 1, (uintptr_t)src,
                              size + 1, "strcpy");
  char *res = strcpy(dest, src);
  eacsl_initialize(dest, size + 1);
  return res;
}

char *eacsl_builtin_strncpy(char *dest, const char *src, size_t n) {
  /* `src` should be a valid string up to `nth` character */
  validate_allocated_string((char *)src, n, "strncpy", "source string ");
  /* `dest` should be allocated and writeable up to `nth` character */
  validate_writeable_space(dest, n, "strncpy", "destination string ");
  /* source and destination strings should not overlap */
  validate_overlapping_spaces((uintptr_t)dest, n, (uintptr_t)src, n, "strncpy");
  char *res = strncpy(dest, src, n);
  eacsl_initialize(dest, n);
  return res;
}

int eacsl_builtin_strcmp(const char *s1, const char *s2) {
  /* both strings should be valid NUL-terminated strings */
  validate_allocated_string((char *)s1, -1, "strcmp", "string 1 ");
  validate_allocated_string((char *)s2, -1, "strcmp", "string 2 ");
  return strcmp(s1, s2);
}

int eacsl_builtin_strncmp(const char *s1, const char *s2, size_t n) {
  /* both strings should be valid up to nth character */
  validate_allocated_string((char *)s1, n, "strncmp", "string 1 ");
  validate_allocated_string((char *)s2, n, "strncmp", "string 2 ");
  return strncmp(s1, s2, n);
}

char *eacsl_builtin_strcat(char *dest, const char *src) {
  long src_sz =
      validate_allocated_string((char *)src, -1, "strcat", "source string ");
  long dest_sz = validate_writeable_string((char *)dest, -1, "strcat",
                                           "destination string ");
  size_t avail_sz = eacsl_block_length(dest) - eacsl_offset(dest);
  if (!(avail_sz >= src_sz + dest_sz + 1)) {
    private_abort("strcat: insufficient space in destination string, "
                  "available: %lu bytes, requires at least %lu bytes\n",
                  avail_sz, src_sz + dest_sz + 1);
  }
  validate_overlapping_spaces((uintptr_t)src, src_sz + 1, (uintptr_t)dest,
                              dest_sz + 1, "strcat");
  char *res = strcat(dest, src);
  eacsl_initialize(&dest[dest_sz], src_sz + 1);
  return res;
}

char *eacsl_builtin_strncat(char *dest, const char *src, size_t n) {
  long src_sz =
      validate_allocated_string((char *)src, n, "strncat", "source string ");
  long dest_sz = validate_writeable_string((char *)dest, -1, "strcat",
                                           "destination string ");
  size_t avail_sz = eacsl_block_length(dest) - eacsl_offset(dest);
  if (!(avail_sz >= n + dest_sz + 1)) {
    private_abort("strncat: insufficient space in destination string, "
                  "available: %lu bytes, requires at least %lu bytes\n",
                  avail_sz, n + dest_sz + 1);
  }
  validate_overlapping_spaces((uintptr_t)src, n, (uintptr_t)dest, dest_sz,
                              "strcat");
  char *res = strncat(dest, src, n);
  eacsl_initialize(&dest[dest_sz], src_sz + 1);
  return res;
}
/* }}} */

/************************************************************************/
/*** memcpy/memcmp/memset/memmove {{{ ***/
/************************************************************************/

void *eacsl_builtin_memcpy(void *dest, const void *src, size_t n) {
  validate_allocated_space((void *)src, n, "memcpy", "source space ");
  validate_writeable_space((void *)dest, n, "memcpy", "destination space ");
  validate_overlapping_spaces((uintptr_t)src, n, (uintptr_t)dest, n, "memcpy");
  void *res = memcpy(dest, src, n);
  eacsl_initialize(dest, n);
  return res;
}

void *eacsl_builtin_memset(void *s, int c, size_t n) {
  validate_writeable_space((void *)s, n, "memset", "space ");
  void *res = memset(s, c, n);
  eacsl_initialize(s, n);
  return res;
}

int eacsl_builtin_memcmp(const void *s1, const void *s2, size_t n) {
  validate_allocated_space((void *)s1, n, "memcmp", "space 1 ");
  validate_allocated_space((void *)s2, n, "memcmp", "space 1 ");
  validate_overlapping_spaces((uintptr_t)s1, n, (uintptr_t)s2, n, "memcpy");
  return memcmp(s1, s2, n);
}

void *eacsl_builtin_memmove(void *dest, const void *src, size_t n) {
  validate_allocated_space((void *)src, n, "memcmp", "source space ");
  validate_writeable_space((void *)dest, n, "memcmp", "destination space ");
  void *res = memmove(dest, src, n);
  eacsl_initialize(dest, n);
  return res;
}

/* }}} */
