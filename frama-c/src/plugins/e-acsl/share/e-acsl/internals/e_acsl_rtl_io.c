/****************************************************************************/
/*                                                                          */
/*  Copyright (c) 2004,2012 Kustaa Nyholm / SpareTimeLabs                   */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*                                                                          */
/*  Redistributions of source code must retain the above copyright          */
/*  notice, this list of conditions and the following disclaimer.           */
/*                                                                          */
/*  Redistributions in binary form must reproduce the above copyright       */
/*  notice, this list of conditions and the following disclaimer in the     */
/*  documentation and/or other materials provided with the distribution.    */
/*                                                                          */
/*  Neither the name of the Kustaa Nyholm or SpareTimeLabs nor the names    */
/*  of its contributors may be used to endorse or promote products derived  */
/*  from this software without specific prior written permission.           */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS     */
/*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT       */
/*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR   */
/*  A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT   */
/*  HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,  */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,   */
/*  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY   */
/*  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT     */
/*  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   */
/*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.    */
/*                                                                          */
/*  File modified by CEA (Commissariat à l'énergie atomique et aux          */
/*                        énergies alternatives).                           */
/*                                                                          */
/****************************************************************************/

/*! ***********************************************************************
 * \file
 * \brief Malloc and stdio free implementation printf.
 **************************************************************************/

#include <stdarg.h>
#include <stdint.h>
#include <unistd.h>

#include "e_acsl_concurrency.h"
#include "e_acsl_rtl_io.h"

/*! \brief Test if we can still write `n + 1` characters to the buffer according
    to the `count` variable. */
#define TEST_COUNT_N(count, n) ((count) == NULL || *(count) > (n))

/*! \brief Test if we can still write a character to the buffer according to
    the `count` variable. */
#define TEST_COUNT(count) TEST_COUNT_N(count, 0)

/*! \brief Decrease the value of `*count` by `n` if `count` is not `NULL`. */
#define DEC_COUNT_N(count, n)                                                  \
  do {                                                                         \
    if ((count) != NULL) {                                                     \
      *(count) -= (n);                                                         \
    }                                                                          \
  } while (0)

/*! \brief Decrease the value of `*count` by 1 if `count` is not `NULL`. */
#define DEC_COUNT(count) DEC_COUNT_N(count, 1)

typedef void (*putcf)(void *, size_t *, char);

#ifdef E_ACSL_CONCURRENCY_PTHREAD
static pthread_mutex_t rtl_io_global_mutex_value;

static void rtl_io_initialize_global_mutex() {
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&rtl_io_global_mutex_value, &attr);
  pthread_mutexattr_destroy(&attr);
}

pthread_mutex_t *rtl_io_global_mutex() {
  E_ACSL_RUN_ONCE(rtl_io_initialize_global_mutex);
  return &rtl_io_global_mutex_value;
}
#endif

/* Unsigned long integers to string conversion (%u) */
static void uli2a(unsigned long int num, unsigned int base, int uc, char *bf) {
  int n = 0;
  unsigned long int d = 1;
  while (num / d >= base)
    d *= base;
  while (d != 0) {
    int dgt = num / d;
    num %= d;
    d /= base;
    if (n || dgt > 0 || d == 0) {
      *bf++ = dgt + (dgt < 10 ? '0' : (uc ? 'A' : 'a') - 10);
      ++n;
    }
  }
  *bf = 0;
}

/* Unsigned pointer-wide integers to memory address conversion (%a) */
static void addr2a(uintptr_t addr, char *bf) {
  *bf++ = '0';
  *bf++ = 'x';

  int base = 16;
  int group = 4;
  char sep = '-';

  unsigned int digits = 1;
  int n = 0;
  unsigned long int d = 1;
  while (addr / d >= base) {
    d *= base;
    digits++;
  }

  unsigned int ctr = 0;
  while (d != 0) {
    ctr++;
    int dgt = addr / d;
    addr %= d;
    d /= base;
    if (n || dgt > 0 || d == 0) {
      *bf++ = dgt + (dgt < 10 ? '0' : 'a' - 10);
      ++n;
    }
    if (--digits % group == 0 && d != 0)
      *bf++ = sep;
  }
  *bf = 0;
}

/* Pointer to string conversion (%p) */
static void ptr2a(void *p, char *bf) {
  *bf++ = '0';
  *bf++ = 'x';
  uli2a((uintptr_t)p, 16, 0, bf);
}

/* Signed long integer to string conversion (%ld) */
static void li2a(long num, char *bf) {
  if (num < 0) {
    num = -num;
    *bf++ = '-';
  }
  uli2a(num, 10, 0, bf);
}

/* Signed integer to string conversion (%d) */
static void ui2a(unsigned int num, unsigned int base, int uc, char *bf) {
  int n = 0;
  unsigned int d = 1;
  while (num / d >= base)
    d *= base;
  while (d != 0) {
    int dgt = num / d;
    num %= d;
    d /= base;
    if (n || dgt > 0 || d == 0) {
      *bf++ = dgt + (dgt < 10 ? '0' : (uc ? 'A' : 'a') - 10);
      ++n;
    }
  }
  *bf = 0;
}

/* Integer bit-fields to string conversion (%b, %B) */
static void bits2a(long int v, int size, char *bf, int l2r) {
  int i;
  if (l2r) {
    for (i = 0; i < size; i++) {
      *bf++ = '0' + ((v >> i) & 1);
      if (i && i + 1 < size && (i + 1) % 8 == 0)
        *bf++ = ' ';
    }
  } else {
    for (i = size - 1; i >= 0; i--) {
      *bf++ = '0' + ((v >> i) & 1);
      if (i && i + 1 < size && i % 4 == 0)
        *bf++ = ' ';
    }
  }
  *bf = 0;
}

/* Pointer bit-fields to string conversion (%v, %V) */
static void pbits2a(void *p, int size, char *bf, int l2r) {
  char *v = (char *)p;
  int i;
  if (l2r) {
    for (i = 0; i < size; i++) {
      *bf++ = '0' + ((v[i / 8] >> i % 8) & 1);
      if (i && i + 1 < size && (i + 1) % 4 == 0)
        *bf++ = ' ';
    }
  } else {
    for (i = size - 1; i >= 0; i--) {
      *bf++ = '0' + ((v[i / 8] >> i % 8) & 1);
      if (i && i + 1 < size && i % 4 == 0)
        *bf++ = ' ';
    }
  }
  *bf = 0;
}

/* Signed integer to string (%d) */
static void i2a(int num, char *bf) {
  if (num < 0) {
    num = -num;
    *bf++ = '-';
  }
  ui2a(num, 10, 0, bf);
}

/* Char to int conversion  */
static int a2d(char ch) {
  if (ch >= '0' && ch <= '9')
    return ch - '0';
  else if (ch >= 'a' && ch <= 'f')
    return ch - 'a' + 10;
  else if (ch >= 'A' && ch <= 'F')
    return ch - 'A' + 10;
  else
    return -1;
}

static char a2i(char ch, char **src, int base, int *nump) {
  char *p = *src;
  int num = 0;
  int digit;
  while ((digit = a2d(ch)) >= 0) {
    if (digit > base)
      break;
    num = num * base + digit;
    ch = *p++;
  }
  *src = p;
  *nump = num;
  return ch;
}

static void putchw(void *putp, size_t *count, putcf putf, int n, char z,
                   char *bf) {
  char fc = z ? '0' : ' ';
  char ch;
  char *p = bf;
  while (*p++ && n > 0)
    n--;
  while (n-- > 0)
    putf(putp, count, fc);
  while ((ch = *bf++))
    putf(putp, count, ch);
}

static void putcp(void *p, size_t *count, char c) {
  if (TEST_COUNT(count)) {
    *(*((char **)p))++ = c;
    DEC_COUNT(count);
  }
}

/** Load the data from the format string `fmt` and the variadic arguments `va`,
 * convert them to character string equivalents and write the result to the
 * stream `putp` with the function `putf` up to `count` characters.
 * \param putp Pointer to a stream where the formatted string will be outputted.
 * \param count Pointer to an integer representing the number of characters that
 *        can still be written to `putp`, or `NULL` if there are no limits.
 * \param putf Function pointer to write a character to a given stream.
 * \param fmt Formatting string.
 * \param va Arguments for the formatting string.
 */
static void _format(void *putp, size_t *count, putcf putf, char *fmt,
                    va_list va) {
  char bf[256];
  char ch;
  while ((ch = *(fmt++)) && TEST_COUNT(count)) {
    if (ch != '%') // if not '%' print character as is
      putf(putp, count, ch);
    else { // otherwise do the print based on the format following '%'
      char lz = 0;
      char lng = 0; // long (i.e., 'l' specifier)
      int w = 0;
      ch = *(fmt++);
      if (ch == '0') { // '0' specifier - padding with zeroes
        ch = *(fmt++);
        lz = 1;
      }
      if (ch >= '0' && ch <= '9') {
        ch = a2i(ch, &fmt, 10, &w);
      }
      if (ch == 'l') {
        ch = *(fmt++);
        lng = 1;
      }
      switch (ch) {
      case 0:
        break;
      case 'u': {
        if (lng)
          uli2a(va_arg(va, unsigned long int), 10, 0, bf);
        else
          ui2a(va_arg(va, unsigned int), 10, 0, bf);
        putchw(putp, count, putf, w, lz, bf);
        break;
      }
      case 'd': {
        if (lng)
          li2a(va_arg(va, unsigned long int), bf);
        else
          i2a(va_arg(va, int), bf);
        putchw(putp, count, putf, w, lz, bf);
        break;
      }
      case 'p':
        ptr2a(va_arg(va, void *), bf);
        putchw(putp, count, putf, w, lz, bf);
        break;
      case 'a':
        addr2a(va_arg(va, uintptr_t), bf);
        putchw(putp, count, putf, w, lz, bf);
        break;
      case 'b':
        bits2a(va_arg(va, long), w > 64 ? 64 : w ? w : 8, bf, 1);
        putchw(putp, count, putf, 0, 0, bf);
        break;
      case 'B':
        bits2a(va_arg(va, long), w > 64 ? 64 : w ? w : 8, bf, 0);
        putchw(putp, count, putf, 0, 0, bf);
        break;
      case 'v':
        pbits2a(va_arg(va, void *), w ? w : 8, bf, 1);
        putchw(putp, count, putf, 0, 0, bf);
        break;
      case 'V':
        pbits2a(va_arg(va, void *), w ? w : 8, bf, 0);
        putchw(putp, count, putf, 0, 0, bf);
        break;
      case 'x':
      case 'X':
        if (lng)
          uli2a(va_arg(va, unsigned long int), 16, (ch == 'X'), bf);
        else
          ui2a(va_arg(va, unsigned int), 16, (ch == 'X'), bf);
        putchw(putp, count, putf, w, lz, bf);
        break;
      case 'f': {
        double num = va_arg(va, double);
        int ord = (int)num;
        i2a(ord, bf);
        putchw(putp, count, putf, w, lz, bf);
        putf(putp, count, '.');
        num = num - ord;
        num *= 1000;
        ord = (int)num;
        i2a(ord, bf);
        putchw(putp, count, putf, w, lz, bf);
        break;
      }
      case 'c':
        putf(putp, count, (char)(va_arg(va, int)));
        break;
      case 's':
        putchw(putp, count, putf, w, 0, va_arg(va, char *));
        break;
      case '%':
        putf(putp, count, ch);
      default:
        break;
      }
    }
  }
}

static void _charc_stdout(void *p, size_t *count, char c) {
  if (TEST_COUNT(count)) {
    write(STDOUT_FILENO, &c, 1);
    DEC_COUNT(count);
  }
}
static void _charc_stderr(void *p, size_t *count, char c) {
  if (TEST_COUNT(count)) {
    write(STDERR_FILENO, &c, 1);
    DEC_COUNT(count);
  }
}
static void _charc_file(void *p, size_t *count, char c) {
  if (TEST_COUNT(count)) {
    write((size_t)p, &c, 1);
    DEC_COUNT(count);
  }
}

static void _charc_literal(void *p, size_t *count, char c) {
#define CHARC_LITERAL_WRITE(s, n)                                              \
  do {                                                                         \
    if (TEST_COUNT_N(count, (n)-1)) {                                          \
      write((size_t)p, s, n);                                                  \
      DEC_COUNT_N(count, n);                                                   \
    }                                                                          \
  } while (0)

  switch (c) {
  case '\r':
    CHARC_LITERAL_WRITE("\\r", 2);
    break;
  case '\f':
    CHARC_LITERAL_WRITE("\\f", 2);
    break;
  case '\b':
    CHARC_LITERAL_WRITE("\\b", 2);
    break;
  case '\a':
    CHARC_LITERAL_WRITE("\\a", 2);
    break;
  case '\n':
    CHARC_LITERAL_WRITE("\\n", 2);
    break;
  case '\t':
    CHARC_LITERAL_WRITE("\\t", 2);
    break;
  case '\0':
    CHARC_LITERAL_WRITE("\\0", 2);
    break;
  default:
    CHARC_LITERAL_WRITE(&c, 1);
  }
}

int rtl_printf(char *fmt, ...) {
  va_list va;
  va_start(va, fmt);
  int result = rtl_vprintf(fmt, va);
  va_end(va);
  return result;
}

int rtl_vprintf(char *fmt, va_list vlist) {
  RTL_IO_LOCK();
  _format(NULL, NULL, _charc_stdout, fmt, vlist);
  RTL_IO_UNLOCK();
  return 1;
}

int rtl_eprintf(char *fmt, ...) {
  va_list va;
  va_start(va, fmt);
  int result = rtl_veprintf(fmt, va);
  va_end(va);
  return result;
}

int rtl_veprintf(char *fmt, va_list vlist) {
  RTL_IO_LOCK();
  _format(NULL, NULL, _charc_stderr, fmt, vlist);
  RTL_IO_UNLOCK();
  return 1;
}

int rtl_dprintf(int fd, char *fmt, ...) {
  va_list va;
  va_start(va, fmt);
  int result = rtl_vdprintf(fd, fmt, va);
  va_end(va);
  return result;
}

int rtl_vdprintf(int fd, char *fmt, va_list vlist) {
  RTL_IO_LOCK();
  intptr_t fd_long = fd;
  _format((void *)fd_long, NULL, _charc_file, fmt, vlist);
  RTL_IO_UNLOCK();
  return 1;
}

int rtl_sprintf(char *s, char *fmt, ...) {
  va_list va;
  va_start(va, fmt);
  int result = rtl_vsprintf(s, fmt, va);
  va_end(va);
  return result;
}

int rtl_vsprintf(char *s, char *fmt, va_list vlist) {
  _format(&s, NULL, putcp, fmt, vlist);
  putcp(&s, NULL, 0);
  return 1;
}

int rtl_snprintf(char *s, size_t bufsize, char *fmt, ...) {
  va_list va;
  va_start(va, fmt);
  int result = rtl_vsnprintf(s, bufsize, fmt, va);
  va_end(va);
  return result;
}

int rtl_vsnprintf(char *s, size_t bufsize, char *fmt, va_list vlist) {
  if (bufsize > 0) {
    if (bufsize > 1) {
      // Only copy `bufsize - 1` characters
      --bufsize;
      _format(&s, &bufsize, putcp, fmt, vlist);
      ++bufsize;
    }
    // In any case, put `\0` as the last written character
    putcp(&s, &bufsize, 0);
  }
  return 1;
}
