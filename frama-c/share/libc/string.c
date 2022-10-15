/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
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

#include "__fc_builtin.h"
#include "string.h"
#include "stdint.h" // for uintptr_t
#include "stdlib.h" // for malloc()
#include "errno.h"
__PUSH_FC_STDLIB

void* memcpy(void* restrict dest, const void* restrict src, size_t n)
{
  /*@
    loop invariant no_eva: 0 <= i <= n;
    loop invariant no_eva: \forall ℤ k; 0 <= k < i ==> ((char*)dest)[k] == ((char*)src)[k];
    loop assigns i, ((char*)dest)[0 .. n-1];
    loop variant n - i;
   */
  for (size_t i = 0; i < n; i++) {
    ((char*)dest)[i] = ((char*)src)[i];
  }
  return dest;
}

// Non-POSIX; GNU extension
void* mempcpy(void* restrict dest, const void* restrict src, size_t n)
{
  size_t i;
  /*@
    loop invariant no_eva: 0 <= i <= n;
    loop invariant no_eva: \forall ℤ k; 0 <= k < i ==> ((char*)dest)[k] == ((char*)src)[k];
    loop assigns i, ((char*)dest)[0 .. n-1];
    loop variant n - i;
   */
  for (i = 0; i < n; i++) {
    ((char*)dest)[i] = ((char*)src)[i];
  }
  return (char*)dest + i;
}

// memoverlap: auxiliary function that returns
//   0 if p[0..n-1] and q[0..n-1] do not overlap;
//   -1/+1 otherwise, according to whether p is before or after q in the memory
/*@
  assigns \result \from indirect:p, indirect:q, indirect:n;
  behavior separated:
    assumes separation:no_overlap: \separated(p + (0 .. n-1), q + (0 .. n-1));
    ensures result_no_overlap: \result == 0;
  behavior not_separated_lt:
    assumes separation:overlap: !\separated(p + (0 .. n-1), q + (0 .. n-1));
    assumes p_before_q: p <= q <  p + n;
    ensures result_p_before_q: \result == -1;
  behavior not_separated_gt:
    assumes separation:overlap: !\separated(p + (0 .. n-1), q + (0 .. n-1));
    assumes p_after_q: q <  p <= q + n;
    ensures result_p_after_q: \result == 1;
  complete behaviors;
  disjoint behaviors;
*/
static int memoverlap(char const *p, char const *q, size_t n) {
  uintptr_t
    p1 = (uintptr_t)p, p2 = (uintptr_t)(p+n),
    q1 = (uintptr_t)q, q2 = (uintptr_t)(q+n);
  if (p1 <= q1 && p2 > q1) return -1;
  else if (q1 <= p1 && q2 > p1) return 1;
  else return 0;
}

void* memmove(void* dest, const void* src, size_t n)
{
  if (n == 0) return dest;
  char *s = (char*)src;
  char *d = (char*)dest;
  if (memoverlap(dest, src, n) <= 0) { /* default: copy up */
    /*@
      loop invariant no_eva: 0 <= i <= n;
      loop invariant no_eva: \forall ℤ k; 0 <= k < i ==> ((char*)dest)[k] == \at(((char*)src)[k],LoopEntry);
      loop invariant no_eva: \forall ℤ k; i <= k < n ==> ((char*)src)[k] == \at(((char*)src)[k],LoopEntry);
      loop assigns i, ((char*)dest)[0 .. n-1];
      loop variant n - i;
    */
    for (size_t i = 0; i < n; i++)
      d[i] = s[i];
  } else { // beginning of dest overlaps with src: copy down
    // to avoid unsigned overflow in the loop below, the '0' case is
    // done outside the loop (note: n == 0 has already been tested)
    /*@
      loop invariant no_eva: 0 <= i < n;
      loop invariant no_eva: \forall ℤ k; i < k < n ==> ((char*)dest)[k] == \at(((char*)src)[k],LoopEntry);
      loop invariant no_eva: \forall ℤ k; 0 <= k <= i ==> ((char*)src)[k] == \at(((char*)src)[k],LoopEntry);
      loop assigns i, ((char*)dest)[0 .. n-1];
      loop variant i;
    */
    for (size_t i = n-1; i > 0; i--)
      d[i] = s[i];
    d[0] = s[0];
  }
  return dest;
}

size_t strlen(const char *s)
{
  size_t i;
  for (i = 0; s[i] != 0; i++);
  return i;
}

size_t strnlen(const char *s, size_t maxlen)
{
  size_t i;
  for (i = 0; i < maxlen && s[i] != 0; i++);
  return i;
}

void* memset (void* s, int c, size_t n)
{
  unsigned char *p = (unsigned char*)s;
  for (size_t i = 0; i < n; i++) {
    p[i] = c;
  }
  return s;
}

int strcmp(const char *s1, const char *s2)
{
  size_t i;
  for (i = 0; s1[i] == s2[i]; i++) {
    if (s1[i] == 0) return 0;
  }
  return (((unsigned char *)s1)[i] - ((unsigned char *)s2)[i]);
}

int strncmp(const char *s1, const char *s2, size_t n)
{
  for (size_t i = 0; i < n; i++) {
    if (s1[i] != s2[i])
      return ((unsigned char *)s1)[i] - ((unsigned char *)s2)[i];
    /* stop comparison when strings end */
    if (s1[i] == 0) return 0;
  }
  return 0;
}

int memcmp(const void *s1, const void *s2, size_t n)
{
  const unsigned char *p1, *p2;
  p1 = (const unsigned char *)s1;
  p2 = (const unsigned char *)s2;
  for (size_t i = 0; i < n; i++)
    if (p1[i] != p2[i]) return p1[i] - p2[i];
  return 0;
}

// NOTE: strcasecmp is in POSIX's strings.h but not in C99
// auxiliary function for strcasecmp
static int char_equal_ignore_case(char c1, char c2)
{
  if (c1 >= 'A' && c1 <= 'Z') c1 -= ('A' - 'a');
  if (c2 >= 'A' && c2 <= 'Z') c2 -= ('A' - 'a');
  if (c1 == c2) return 0;
  else return (int) ((unsigned char)c2 - (unsigned char)c1);
}

int strcasecmp(const char *s1, const char *s2)
{
  size_t i;
  for (i = 0; s1[i] != 0 && s2[i] != 0; i++) {
    int res = char_equal_ignore_case(s1[i], s2[i]);
    if (res != 0) return res;
  }
  if (s1[i] == 0 && s2[i] == 0) return 0;
  else if (s1[i] == 0) return -1;
  else return 1;
}

char* strcat(char *dest, const char *src)
{
  size_t i;
  size_t n = strlen(dest);
  for (i = 0; src[i] != 0; i++) {
    dest[n+i] = src[i];
  }
  dest[n+i] = 0;
  return dest;
}

/* From the strncat man page */
char* strncat(char *dest, const char *src, size_t n)
{
  size_t dest_len = strlen(dest);
  size_t i;
  for (i = 0; i < n; i++) {
    if (src[i] == 0) break;
    dest[dest_len + i] = src[i];
  }
  dest[dest_len + i] = 0;

  return dest;
}

char* strcpy(char *dest, const char *src)
{
  size_t i;
  for (i = 0; src[i] != 0; i++)
    dest[i] = src[i];
  dest[i] = 0;
  return dest;
}

// POSIX.1-2008
char* stpcpy(char *dest, const char *src)
{
  size_t i;
  for (i = 0; src[i] != 0; i++)
    dest[i] = src[i];
  dest[i] = 0;
  return dest + i;
}

char *strncpy(char *dest, const char *src, size_t n)
{
  size_t i;
  for (i = 0; i < n; i++) {
    dest[i] = src[i];
    if (src[i] == 0) break;
  }
  for (; i < n; i++)
    dest[i] = 0;
  return dest;
}

char *strchr(const char *s, int c)
{
  const char ch = c;
  size_t i;
  for (i = 0; s[i] != ch; i++)
    if (s[i] == 0) return NULL;
  return (char*)&s[i];
}

char *strrchr(const char *s, int c)
{
  const char ch = c;
  for (size_t i = strlen(s)+1; i > 0; i--)
    if (s[i-1] == ch) return (char *)&s[i-1];
  return NULL;
}

void *memchr(const void *s, int c, size_t n)
{
  const unsigned char ch = c;
  const unsigned char *ss = (const unsigned char *)s;
  for (size_t i = 0; i < n; i++)
    if (ss[i] == ch) return (void *)&ss[i];
  return NULL;
}

void *memrchr(const void *s, int c, size_t n)
{
  const unsigned char ch = c;
  const unsigned char *ss = (const unsigned char *)s;
  for (size_t i = n; i > 0; i--)
    if (ss[i-1] == ch) return (void *)&ss[i-1];
  return NULL;
}

char *strstr(const char *haystack, const char *needle)
{
  // special case: empty string starts everywhere
  if (needle[0] == 0) return (char*)haystack;
  for (size_t i = 0; haystack[i] != 0; i++) {
    size_t j;
    for (j = 0; haystack[i+j] != 0; j++) {
      if (haystack[i+j] != needle[j]) break;
    }
    if (needle[j] == 0) return (char*)&haystack[i];
  }
  return NULL;
}

char __fc_strerror[64];

char *strerror(int errnum)
{
#ifdef __FRAMAC__
  static int __fc_strerror_init;
  if (!__fc_strerror_init) {
    Frama_C_make_unknown(__fc_strerror, 63);
    __fc_strerror[63] = 0;
    __fc_strerror_init = 1;
  }
#endif
  return __fc_strerror;
}

/* Warning: read considerations about malloc() in Frama-C */
char *strdup(const char *s)
{
  size_t l = strlen(s) + 1;
  char *p = malloc(l);
  if (!p) {
    errno = ENOMEM;
    return 0;
  }
  memcpy(p, s, l);
  return p;
}

/* Warning: read considerations about malloc() in Frama-C */
char *strndup(const char *s, size_t n)
{
  /* find length up to n bytes */
  size_t l;
  for (l = 0; l < n; l++) {
    if (s[l] == 0) break;
  }
  char *p = malloc(l+1); /* include terminating '\0' */
  if (!p) {
    errno = ENOMEM;
    return 0;
  }
  memcpy(p, s, l);
  p[l] = 0;
  return p;
}

char __fc_strsignal[64];

char *strsignal(int signum)
{
#ifdef __FRAMAC__
  static int __fc_strsignal_init;
  if (!__fc_strsignal_init) {
    Frama_C_make_unknown(__fc_strsignal, 63);
    __fc_strsignal[63] = 0;
    __fc_strsignal_init = 1;
  }
#endif
  return __fc_strsignal;
}

__POP_FC_STDLIB
