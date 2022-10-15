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
 * \brief E-ACSL concurrency utility macros and functions.
 **************************************************************************/

#ifndef E_ACSL_CONCURRENCY
#define E_ACSL_CONCURRENCY

#ifdef E_ACSL_CONCURRENCY_PTHREAD
#  include <pthread.h>
#  include <string.h>

#  include "e_acsl_debug.h"
#  include "e_acsl_rtl_error.h"

/************************************************************************/
/*** Run once function {{{ ***/
/************************************************************************/

#  ifdef E_ACSL_DEBUG
/*! \brief Buffer to hold a thread-specific error message.

    This buffer and `rtl_strerror_t()` are used instead of directly
    `rtl_strerror()` because since `E_ACSL_RUN_ONCE` is called when processing
    logging functions, the message returned by `rtl_strerror()` in a
    `DVASSERT()` call could be overwritten. */
static __thread char __e_acsl_run_once_error_buffer[255];
#  endif

/*! \brief The first call to `E_ACSL_RUN_ONCE` will call the initialization
    function `init_fct()` without arguments. Any subsequent call to
    `E_ACSL_RUN_ONCE` will not call `init_fct()`. After calling
    `E_ACSL_RUN_ONCE`, the function `init_fct()` has been called. */
#  define E_ACSL_RUN_ONCE(init_fct)                                            \
    do {                                                                       \
      static pthread_once_t already_run = PTHREAD_ONCE_INIT;                   \
      int result = pthread_once(&already_run, init_fct);                       \
      DVASSERT(result == 0,                                                    \
               "Unable to initialize with function '" #init_fct "()': %s\n",   \
               rtl_strerror_r(errno, __e_acsl_run_once_error_buffer,           \
                              sizeof(__e_acsl_run_once_error_buffer)));        \
    } while (0)

/*! \brief The first call to `E_ACSL_RUN_ONCE_WITH_ARGS` will call the
    initialization function `init_fct()` with arguments `args...`. Any
    subsequent call to `E_ACSL_RUN_ONCE_WITH_ARGS` will not call `init_fct()`.
    After calling `E_ACSL_RUN_ONCE_WITH_ARGS`, the function `init_fct()` has
    been called. */
#  define E_ACSL_RUN_ONCE_WITH_ARGS(init_fct, args...)                         \
    do {                                                                       \
      static int already_run = 0;                                              \
      static pthread_rwlock_t rwlock = PTHREAD_RWLOCK_INITIALIZER;             \
      pthread_rwlock_rdlock(&rwlock);                                          \
      if (!already_run) {                                                      \
        pthread_rwlock_unlock(&rwlock);                                        \
        pthread_rwlock_wrlock(&rwlock);                                        \
        if (!already_run) {                                                    \
          init_fct(args);                                                      \
          already_run = 1;                                                     \
        }                                                                      \
      }                                                                        \
      pthread_rwlock_unlock(&rwlock);                                          \
    } while (0)

/* }}} */

/************************************************************************/
/*** Mutex {{{ ***/
/************************************************************************/

/*! \brief Declare a static mutex variable named `mutex` with the initialization
    `init`. */
#  define E_ACSL_MUTEX_DECL_INIT(mutex, init)                                  \
    static pthread_mutex_t mutex = init

/*! \brief Lock the given mutex */
#  define E_ACSL_MUTEX_LOCK(mutex) pthread_mutex_lock(&(mutex))

/*! \brief Unlock the given mutex */
#  define E_ACSL_MUTEX_UNLOCK(mutex) pthread_mutex_unlock(&(mutex))

/* }}} */

/************************************************************************/
/*** Read-write lock {{{ ***/
/************************************************************************/

/*! \brief Declare a read-write lock variable named `rwlock`. */
#  define E_ACSL_RWLOCK_DECL(rwlock) pthread_rwlock_t rwlock

/*! \brief Initialize the given read-write lock with the given attributes. */
#  define E_ACSL_RWINIT(rwlock, attrs) pthread_rwlock_init(&(rwlock), attrs)

/*! \brief Destroy the given read-write lock. */
#  define E_ACSL_RWDESTROY(rwlock) pthread_rwlock_destroy(&(rwlock))

/*! \brief Apply a read lock to the given read-write lock. */
#  define E_ACSL_RLOCK(rwlock)                                                 \
    pthread_rwlock_rdlock((pthread_rwlock_t *)&(rwlock))

/*! \brief Apply a write lock to the given read-write lock. */
#  define E_ACSL_WLOCK(rwlock) pthread_rwlock_wrlock(&(rwlock))

/*! \brief Unlock the given read-write lock. */
#  define E_ACSL_RWUNLOCK(rwlock)                                              \
    pthread_rwlock_unlock((pthread_rwlock_t *)&(rwlock))

/* }}} */

#else

#  define E_ACSL_RUN_ONCE_WITH_ARGS(init_fct, args...)                         \
    do {                                                                       \
      static int already_run = 0;                                              \
      if (!already_run) {                                                      \
        init_fct(args);                                                        \
        already_run = 1;                                                       \
      }                                                                        \
    } while (0)

#  define E_ACSL_RUN_ONCE(init_fct) E_ACSL_RUN_ONCE_WITH_ARGS(init_fct)

#  define E_ACSL_MUTEX_DECL_INIT(mutex, init)
#  define E_ACSL_MUTEX_LOCK(mutex)
#  define E_ACSL_MUTEX_UNLOCK(mutex)

#  define E_ACSL_RWLOCK_DECL(rwlock)
#  define E_ACSL_RWINIT(rwlock, attrs)
#  define E_ACSL_RWDESTROY(rwlock)
#  define E_ACSL_RLOCK(rwlock)
#  define E_ACSL_WLOCK(rwlock)
#  define E_ACSL_RWUNLOCK(rwlock)

#endif

#endif // E_ACSL_CONCURRENCY
