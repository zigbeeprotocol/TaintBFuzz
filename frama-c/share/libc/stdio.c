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
#include "stdbool.h"
#include "stdio.h"
#include "stdlib.h"
#include "stdint.h" // for SIZE_MAX
#include "sys/types.h" // for ssize_t
#include "errno.h"
__PUSH_FC_STDLIB

FILE __fc_initial_stdout = {.__fc_FILE_id=1}; 
FILE * __fc_stdout = &__fc_initial_stdout;

FILE __fc_initial_stderr = {.__fc_FILE_id=2}; 
FILE * __fc_stderr = &__fc_initial_stderr;

FILE __fc_initial_stdin = {.__fc_FILE_id=0}; 
FILE * __fc_stdin = &__fc_initial_stdin;

// Returns 1 iff mode contains a valid mode string for fopen() and
// related functions; that is, one of the following:
// "r","w","a","rb","wb","ab","r+","w+","a+",
// "rb+","r+b","wb+","w+b","ab+","a+b".
/*@
  requires valid_mode: valid_read_string(mode);
 */
static bool is_valid_mode(char const *mode) {
  if (!(mode[0] != 'r' || mode[0] != 'w' || mode[0] != 'a')) return false;
  // single-char mode string; ok
  if (!mode[1]) return true;
  // two- or three-char mode string
  if (!(mode[1] != 'b' || mode[1] != '+')) return false;
  // two-char mode string; ok
  if (!mode[2]) return true;
  if (mode[2] == mode[1] || !(mode[2] != 'b' || mode[2] != '+')) return false;
  // a three-char mode string is ok; everything else is not
  return !mode[3];
}

// inefficient but POSIX-conforming implementation of getline
ssize_t getline(char **lineptr, size_t *n, FILE *stream) {
  if (!lineptr || !n || !stream) {
    errno = EINVAL;
    //TODO: set error indicator for stream
    return -1;
  }
  if (ferror(stream) || feof(stream)) {
    //TODO: set error indicator for stream
    return -1;
  }
  if (!*lineptr || *n == 0) {
    *lineptr = malloc(2);
    if (!lineptr) {
      errno = ENOMEM;
      //TODO: set error indicator for stream
      return -1;
    }
    *n = 2;
  }
  size_t cur = 0;
  while (!ferror(stream) && !feof(stream)) {
    while (cur < *n-1) {
      char c = fgetc(stream);
      if (c == EOF && cur == 0) {
        // no characters were read
        //TODO: set error indicator for stream
        return -1;
      }
      if (c != EOF) (*lineptr)[cur++] = c;
      if (c == '\n' || c == EOF) {
        // finished reading a line or the file
        (*lineptr)[cur] = '\0';
        return cur;
      }
    }
    // try to realloc larger buffer
    if (*n == SSIZE_MAX) {
      errno = EOVERFLOW;
      //TODO: set error indicator for stream
      return -1;
    }
    size_t new_size = *n+1;
    *lineptr = realloc(*lineptr, new_size);
    if (!*lineptr) {
      // failed to realloc larger line
      errno = ENOMEM;
      //TODO: set error indicator for stream
      return -1;
    }
    *n = new_size;
  }
  //TODO: set error indicator for stream
  return -1;
}

// Non-POSIX; arbitrarily allocates between 1 and 256 bytes.
// This stub is unsound in the general case, but enough for
// many test cases.
int asprintf(char **strp, const char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  size_t len = Frama_C_interval(1, 256);
  *strp = malloc(len);
  if (!*strp) {
    va_end(args);
    return -1;
  }
  // Emulate writing to the string
  Frama_C_make_unknown(*strp, len - 1U);
  (*strp)[len - 1U] = 0;
  return len;
}

// TODO: this stub does not ensure that, when fclose is called on the
// stream, the memory allocated here will be freed.
// (there is currently no metadata field in FILE for this information).
FILE *fmemopen(void *restrict buf, size_t size,
               const char *restrict mode) {
  if (!is_valid_mode(mode)) {
    errno = EINVAL;
    return NULL;
  }
  if (!buf) {
    if (size == 0) {
      // Some implementations may not support this; non-deterministically
      // return an error
      if (Frama_C_interval(0, 1)) {
        errno = EINVAL;
        return NULL;
      }
    }
    if (mode[1] != '+' && (mode[1] && mode[2] != '+')) {
      // null buffer requires an update ('+') mode
      errno = EINVAL;
      return NULL;
    }
    buf = malloc(size);
    if (!buf) {
      errno = ENOMEM;
      return NULL;
    }
  }
  // Code to emulate a possible exhaustion of open streams; there is currently
  // no metadata in the FILE structure to indicate when a stream is available.
  if (Frama_C_interval(0, 1)) {
    // emulate 'too many open streams'
    errno = EMFILE;
    return NULL;
  }
  return &__fc_fopen[Frama_C_interval(0, __FC_FOPEN_MAX-1)];
}

__POP_FC_STDLIB
