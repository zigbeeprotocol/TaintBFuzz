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

#include "e_acsl_malloc.h"

#include "e_acsl_rtl_string.h"

char *nstrcat(char *dest, const char *src) {
  memcpy(dest + strlen(dest), src, strlen(src) + 1);
  return dest;
}

char *nstrdup(const char *s) {
  if (s) {
    size_t len = strlen(s) + 1;
    void *n = private_malloc(len);
    return (n == NULL) ? NULL : (char *)memcpy(n, s, len);
  }
  return NULL;
}

char *sappend(char *dest, const char *src, const char *delim) {
  if (!dest && src)
    dest = nstrdup(src);
  else if (src && dest) {
    size_t ldelim = delim ? strlen(delim) : 0;
    size_t len = strlen(src) + strlen(dest) + 1;
    if (ldelim)
      len += ldelim;
    dest = private_realloc(dest, len);
    if (ldelim)
      dest = nstrcat(dest, delim);
    dest = nstrcat(dest, src);
  }
  return dest;
}

int endswith(char *str, char *pat) {
  if (str && pat) {
    size_t slen = strlen(str);
    size_t plen = strlen(pat);
    if (slen >= plen) {
      str += slen - plen;
      return strncmp(str, pat, plen);
    }
  }
  return 1;
}

#define ZERO_BLOCK_SIZE 1024
static unsigned char zeroblock[ZERO_BLOCK_SIZE];

int zeroed_out(const void *p, size_t size) {
  size_t lim = size / ZERO_BLOCK_SIZE, rem = size % ZERO_BLOCK_SIZE;
  unsigned char *pc = (unsigned char *)p;

  size_t i;
  for (i = 0; i < lim; i++) {
    if (memcmp(pc, &zeroblock, ZERO_BLOCK_SIZE))
      return 0;
    pc += ZERO_BLOCK_SIZE;
  }
  return !memcmp(pc, &zeroblock, rem);
}

int charcount(const char *s, char c) {
  int count = 0;
  while ((s = strchr(s, c)) != NULL) {
    count++;
    s++;
  }
  return count;
}
