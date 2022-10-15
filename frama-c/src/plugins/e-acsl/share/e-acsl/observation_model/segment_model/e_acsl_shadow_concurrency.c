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
 * \brief Implementation of E-ACSL concurrency support for the shadow memory
 * model.
***************************************************************************/

#include "e_acsl_shadow_concurrency.h"

#ifdef E_ACSL_CONCURRENCY_PTHREAD

#  include <pthread.h>
#  include <stdlib.h>
#  include <string.h>

#  include "../../internals/e_acsl_concurrency.h"
#  include "../../internals/e_acsl_rtl_error.h"
#  include "../internals/e_acsl_patricia_trie.h"
#  include "e_acsl_shadow_layout.h"

/************************************************************************/
/*** Patricia trie for the thread memory partitions {{{ ***/
/* Each thread has its own stack and TLS segment. To be able to monitor the
 * threaded code, we need to track those memory segments and quickly determine
 * on which segment is a given pointer.
 * The patricia trie structure offers great lookup performance and adequate
 * insertion and removal performance for this use-case.
 */
/************************************************************************/

/*! Leaf of the patricia trie containing a memory segment belonging to a
    thread. */
typedef struct thread_partition {
  /*! Id of the thread */
  pthread_t id;
  /*! Memory segment belonging to a thread */
  memory_partition p;
} thread_partition_t;

/*! \param leaf Leaf of the patricia trie.
    \return The start address of the memory segment on the given leaf. */
static void *tp_get_ptr(pt_leaf_t leaf) {
  DASSERT(leaf != NULL);
  return (void *)((thread_partition_t *)leaf)->p.application.start;
}

/*! \param leaf Leaf of the patricia trie.
    \param ptr Pointer address that we are looking for.
    \return true (!= 0) if the pointer is contained in the memory segment
            represented by the leaf, false (== 0) otherwise. */
static int tp_contains_ptr(pt_leaf_t leaf, void *ptr) {
  DASSERT(leaf != NULL);
  thread_partition_t *tp = (thread_partition_t *)leaf;
  return IS_ON(ptr, tp->p.application);
}

/*! \brief Deallocate the leaf, i.e. deallocate the shadow regions used by the
    runtime analysis for the given leaf, and the leaf itself. */
static void tp_clean(pt_leaf_t leaf) {
  DASSERT(leaf != NULL);
  thread_partition_t *tp = (thread_partition_t *)leaf;
  if (tp->p.primary.mspace) {
    eacsl_destroy_mspace(tp->p.primary.mspace);
  }
  if (tp->p.secondary.mspace) {
    eacsl_destroy_mspace(tp->p.secondary.mspace);
  }
#  ifdef E_ACSL_TEMPORAL
  if (tp->p.temporal_primary.mspace) {
    eacsl_destroy_mspace(tp->p.temporal_primary.mspace);
  }
  if (tp->p.temporal_secondary.mspace) {
    eacsl_destroy_mspace(tp->p.temporal_secondary.mspace);
  }
#  endif
  private_free(tp);
}

/*! \brief Print the content of the given leaf */
static void tp_print(pt_leaf_t leaf) {
#  if defined(E_ACSL_DEBUG)
  DASSERT(leaf != NULL);
  thread_partition_t *tp = (thread_partition_t *)leaf;
  DLOG("thread id: %lu\n", tp->id);
  print_memory_partition(&tp->p);
#  endif
}

/*! \return true (!= 0) if the leaf corresponds to the current thread, false
    (== 0) otherwise. */
static int tp_is_same_thread(pt_leaf_t leaf) {
  DASSERT(leaf != NULL);
  pthread_t id = pthread_self();
  return pthread_equal(id, ((thread_partition_t *)leaf)->id);
}

/*! Instance of patricia trie to store the memory segments of the threads. */
pt_struct_t *thread_partitions = NULL;

/*! \brief Creates the thread partitions trie. This function should be used with
    E_ACSL_RUN_ONCE. */
static void create_thread_partitions_trie() {
  DVASSERT(thread_partitions == NULL,
           "Thread partitions trie already created\n");
  thread_partitions =
      pt_create(tp_get_ptr, tp_contains_ptr, tp_clean, tp_print);
}

/* }}} */

/************************************************************************/
/*** Thread shadow layout {{{ ***/
/************************************************************************/

/*! \brief Fill the given `memory_partition` with the addresses of the stack
    segment for the current thread. */
static void fill_thread_layout_stack(memory_partition *pstack,
                                     size_t stack_size) {
  // Scan /proc/self/maps to retrieve the memory segment corresponding to the
  // current thread stack
  FILE *maps = fopen("/proc/self/maps", "r");
  DVASSERT(maps != NULL, "Unable to open /proc/self/maps: %s\n",
           rtl_strerror(errno));

  int result;
  // Use the address of the local variable `maps`, stored on the stack, to find
  // the segment corresponding to the current stack
  uintptr_t stack_addr = (uintptr_t)&maps;
  uintptr_t start, end;
  char buffer[255];
  while (fgets(buffer, sizeof(buffer), maps) != NULL) {
    result = sscanf(buffer, "%lx-%lx", &start, &end);
    DVASSERT(result == 2, "Reading /proc/self/maps failed: %s\n",
             rtl_strerror(errno));

    if (start <= stack_addr && stack_addr <= end) {
      break;
    }
  }

  result = fclose(maps);
  DVASSERT(result == 0, "Unable to close /proc/self/maps: %s\n",
           rtl_strerror(errno));

  // Allocate shadow memory spaces and compute offsets
  set_application_segment(&pstack->application, start, stack_size,
                          "thread_stack", NULL);
  set_shadow_segment(&pstack->primary, &pstack->application, 1,
                     "thread_stack_primary");
  set_shadow_segment(&pstack->secondary, &pstack->application, 1,
                     "thread_stack_secondary");
#  ifdef E_ACSL_TEMPORAL
  set_shadow_segment(&pstack->temporal_primary, &pstack->application, 1,
                     "temporal_thread_stack_primary");
  set_shadow_segment(&pstack->temporal_secondary, &pstack->application, 1,
                     "temporal_thread_stack_secondary");
#  endif
}

/*! \brief Fill the given `memory_partition` with the addresses of the TLS
    segment for the current thread. */
static void fill_thread_layout_tls(memory_partition *ptls) {
  // Since the TLS is by design specific to each thread, we can reuse the
  // method used to identify the TLS segment in the main thread
  // We first need to collect the safe locations of the current thread,
  // since we need to register them in case the program uses one of them
  // inside the thread
  collect_safe_locations();
  set_application_segment(&ptls->application, get_tls_start(0), get_tls_size(),
                          "thread_tls", NULL);
  set_shadow_segment(&ptls->primary, &ptls->application, 1,
                     "thread_tls_primary");
  set_shadow_segment(&ptls->secondary, &ptls->application, 1,
                     "thread_tls_secondary");
#  ifdef E_ACSL_TEMPORAL
  set_shadow_segment(&ptls->temporal_primary, &ptls->application, 1,
                     "thread_temporal_tls_primary");
  set_shadow_segment(&ptls->temporal_secondary, &ptls->application, 1,
                     "thread_temporal_tls_secondary");
#  endif
}

void init_thread_shadow_layout(size_t stack_size) {
  DASSERT(thread_partitions != NULL);

  pthread_t id = pthread_self();

  thread_partition_t *stack = private_malloc(sizeof(thread_partition_t));
  stack->id = id;
  fill_thread_layout_stack(&stack->p, stack_size);
  pt_insert(thread_partitions, (pt_leaf_t)stack);

  thread_partition_t *tls = private_malloc(sizeof(thread_partition_t));
  tls->id = id;
  fill_thread_layout_tls(&tls->p);
  pt_insert(thread_partitions, (pt_leaf_t)tls);

#  if defined(E_ACSL_DEBUG) && defined(E_ACSL_DEBUG_VERBOSE)
  RTL_IO_LOCK();
  DLOG(">>> Thread stack -------------\n");
  print_memory_partition(&stack->p);
  DLOG(">>> Thread TLS ---------------\n");
  print_memory_partition(&tls->p);
  RTL_IO_UNLOCK();
#  endif

  // Safe location tracking for thread-specific locations
  register_safe_locations(E_ACSL_REGISTER_THREAD_LOCS);
}

void clean_thread_shadow_layout() {
  DASSERT(thread_partitions != NULL);
  pt_remove_if(thread_partitions, tp_is_same_thread);
}

/*! \return The memory segment corresponding to the given address or NULL if no
    memory segment can be found. */
static memory_partition *find_thread_partition(uintptr_t addr) {
  memory_partition *result = NULL;
  if (thread_partitions != NULL) {
    thread_partition_t *tp =
        (thread_partition_t *)pt_find(thread_partitions, (void *)addr);
    if (tp != NULL) {
      result = &tp->p;
    }
  }
  return result;
}

int is_on_thread(uintptr_t addr) {
  memory_partition *thread_partition = find_thread_partition(addr);
  return thread_partition != NULL;
}

intptr_t primary_thread_shadow(uintptr_t addr) {
  memory_partition *thread_partition = find_thread_partition(addr);
  return SHADOW_ACCESS(addr, thread_partition->primary.shadow_offset);
}

intptr_t secondary_thread_shadow(uintptr_t addr) {
  memory_partition *thread_partition = find_thread_partition(addr);
  return SHADOW_ACCESS(addr, thread_partition->secondary.shadow_offset);
}

#  ifdef E_ACSL_TEMPORAL
intptr_t temporal_primary_thread_shadow(uintptr_t addr) {
  memory_partition *thread_partition = find_thread_partition(addr);
  return SHADOW_ACCESS(addr, thread_partition->temporal_primary.shadow_offset);
}

intptr_t temporal_secondary_thread_shadow(uintptr_t addr) {
  memory_partition *thread_partition = find_thread_partition(addr);
  return SHADOW_ACCESS(addr,
                       thread_partition->temporal_secondary.shadow_offset);
}
#  endif // E_ACSL_TEMPORAL

/* }}} */

/************************************************************************/
/*** Pthread integration {{{ ***/
/************************************************************************/

/*! Wrapper around the original argument used in `pthread_create`. */
typedef struct eacsl_pthread_wrapper {
  /*! The original function pointer given to `pthread_create`. */
  pthread_routine_t start_routine;
  /*! The original argument given to `pthread_create`. */
  void *restrict arg;
  /*! The stack size of the created thread. */
  size_t stack_size;
} eacsl_pthread_wrapper_t;

/*! \brief Cleanup function called before destroying the thread.

    The shadow layout for the thread is destroyed and the memory allocated for
    the wrapper is freed. */
static void eacsl_pthread_cleanup(void *arg) {
  clean_thread_shadow_layout();
  private_free((eacsl_pthread_wrapper_t *)arg);
}

/*! \brief Wrapper function given to `pthread_create` instead of the original
    function.

    Initialize the shadow layout and register the cleanup function. */
static void *eacsl_pthread_wrapper(void *arg) {
  void *res = NULL;
  eacsl_pthread_wrapper_t *wrapped = (eacsl_pthread_wrapper_t *)arg;
  init_thread_shadow_layout(wrapped->stack_size);

  // Register cleanup function
  pthread_cleanup_push(eacsl_pthread_cleanup, arg);
  // Execute original thread function
  res = wrapped->start_routine(wrapped->arg);
  // Pop and execute (argument is 1) the cleanup function
  pthread_cleanup_pop(1);
  return res;
}

int eacsl_pthread_create(pthread_t *restrict thread,
                         const pthread_attr_t *restrict original_attr,
                         pthread_routine_t start_routine, void *restrict arg) {
  // Initialize the thread partitions trie on the first execution of this
  // function
  E_ACSL_RUN_ONCE(create_thread_partitions_trie);

  // Create a wrapper for the original routine and arguments
  eacsl_pthread_wrapper_t *wrapped =
      private_malloc(sizeof(eacsl_pthread_wrapper_t));
  wrapped->start_routine = start_routine;
  wrapped->arg = arg;

  // We need pthread creation attributes to customize the stack size for the
  // thread. If the user already provided pthread creation attributes, we can
  // update those, otherwise we need to use our own structure
  pthread_attr_t attr;
  pthread_attr_t *pattr;
  if (original_attr == NULL) {
    // There are no original attributes, initialize a new structure
    pthread_attr_init(&attr);
    pattr = &attr;
  } else {
    // There are original attributes, use them
    pattr = (pthread_attr_t *)original_attr;
  }

  // Update the stack size for the new thread, either to the default value set
  // in E-ACSL, or twice the original stack size if the original stack size is
  // already greater than the default value of E-ACSL
  size_t original_stack_size;
  pthread_attr_getstacksize(pattr, &original_stack_size);
  if (original_stack_size >= E_ACSL_THREAD_STACK_SIZE * MB) {
    wrapped->stack_size = original_stack_size * 2;
  } else {
    wrapped->stack_size = E_ACSL_THREAD_STACK_SIZE * MB;
  }
  pthread_attr_setstacksize(pattr, wrapped->stack_size);

  // Create the thread using our custom wrapper routine
  int result = pthread_create(thread, pattr, eacsl_pthread_wrapper, wrapped);

  // Destroy the attributes if we created them earlier, or restore the stack
  // size to its original value otherwise
  if (original_attr == NULL) {
    pthread_attr_destroy(pattr);
  } else {
    pthread_attr_setstacksize(pattr, original_stack_size);
  }

  return result;
}

/* }}} */

#else // E_ACSL_CONCURRENCY_PTHREAD

#  include <errno.h>

#  include "../../internals/e_acsl_private_assert.h"

#  define CONCURRENCY_ABORT_MESSAGE                                            \
    "Compile with option '--concurrency' of e-acsl-gcc.sh to support "         \
    "concurrency.\n"                                                           \
    "When compiling without e-acsl-gcc.sh, E_ACSL_CONCURRENCY_PTHREAD must\n " \
    "be defined and the pthread library linked.\n"

void init_thread_shadow_layout(size_t stack_size) {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
}

void clean_thread_shadow_layout() {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
}

int is_on_thread(uintptr_t addr) {
  return 0;
}

intptr_t primary_thread_shadow(uintptr_t addr) {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
  return 0;
}

intptr_t secondary_thread_shadow(uintptr_t addr) {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
  return 0;
}

#  ifdef E_ACSL_TEMPORAL
intptr_t temporal_primary_thread_shadow(uintptr_t addr) {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
  return 0;
}

intptr_t temporal_secondary_thread_shadow(uintptr_t addr) {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
  return 0;
}
#  endif // E_ACSL_TEMPORAL

extern int pthread_create(pthread_t *restrict thread,
                          const pthread_attr_t *restrict attr,
                          pthread_routine_t start_routine, void *restrict arg);

int eacsl_pthread_create(pthread_t *restrict thread,
                         const pthread_attr_t *restrict original_attr,
                         pthread_routine_t start_routine, void *restrict arg) {
  private_abort(CONCURRENCY_ABORT_MESSAGE);
  return EPERM;
}

#endif // E_ACSL_CONCURRENCY_PTHREAD
