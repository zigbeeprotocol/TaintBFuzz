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
 * \brief  Implementation of E-ACSL public API for a segment (shadow) memory
 *   model. See e_acsl.h for details.
 **************************************************************************/

#include <stddef.h>
#include <stdint.h>

#include "../../instrumentation_model/e_acsl_temporal.h"
#include "../../internals/e_acsl_concurrency.h"
#include "../../internals/e_acsl_debug.h"
#include "../../internals/e_acsl_malloc.h"
#include "../../internals/e_acsl_private_assert.h"
#include "../../numerical_model/e_acsl_floating_point.h"
#include "e_acsl_segment_tracking.h"
#include "e_acsl_shadow_layout.h"

#include "../e_acsl_observation_model.h"
#include "../internals/e_acsl_timestamp_retrieval.h"

#ifdef E_ACSL_CONCURRENCY_PTHREAD
/*! \brief Global read-write lock for the memory model. */
static pthread_rwlock_t __e_acsl_segment_model_global_lock =
    PTHREAD_RWLOCK_INITIALIZER;
#endif

void *malloc(size_t size) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  void *result = unsafe_malloc(size);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

void *calloc(size_t nbr_elt, size_t size_elt) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  void *result = unsafe_calloc(nbr_elt, size_elt);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

void *realloc(void *ptr, size_t size) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  void *result = unsafe_realloc(ptr, size);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

void free(void *ptr) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  unsafe_free(ptr);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
}

void *aligned_alloc(size_t alignment, size_t size) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  void *result = unsafe_aligned_alloc(alignment, size);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

int posix_memalign(void **memptr, size_t alignment, size_t size) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  int result = unsafe_posix_memalign(memptr, alignment, size);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

void *eacsl_store_block(void *ptr, size_t size) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  /* Only stack-global memory blocks are recorded explicitly via this function.
     Heap blocks should be tracked internally using memory allocation functions
     such as malloc or calloc. */
  shadow_alloca(ptr, size);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return ptr;
}

void eacsl_delete_block(void *ptr) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  /* Block deletion should be performed on stack/global addresses only,
   * heap blocks should be deallocated manually via free/cfree/realloc. */
  shadow_freea(ptr);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
}

void *eacsl_store_block_duplicate(void *ptr, size_t size) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  if (allocated((uintptr_t)ptr, size, (uintptr_t)ptr))
    shadow_freea(ptr);
  shadow_alloca(ptr, size);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return ptr;
}

/*! \brief Initialize a chunk of memory given by its start address (`addr`)
 * and byte length (`n`). */
void eacsl_initialize(void *ptr, size_t n) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  unsafe_initialize(ptr, n);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
}

void eacsl_full_init(void *ptr) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  unsafe_initialize(ptr, _block_length(ptr));
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
}

void eacsl_mark_readonly(void *ptr) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  mark_readonly_region((uintptr_t)ptr, _block_length(ptr));
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
}

/* ********************** */
/* E-ACSL annotations {{{ */
/* ********************** */

int eacsl_freeable(void *ptr) {
  E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
  int result = unsafe_freeable(ptr);
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

int eacsl_valid(void *ptr, size_t size, void *ptr_base, void *addrof_base) {
  int result = size == 0;
  if (!result) {
    E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
    result = allocated((uintptr_t)ptr, size, (uintptr_t)ptr_base)
             && !readonly(ptr)
#ifdef E_ACSL_TEMPORAL
             && temporal_valid(ptr_base, addrof_base)
#endif
        ;
    E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  }
  return result;
}

int eacsl_valid_read(void *ptr, size_t size, void *ptr_base,
                     void *addrof_base) {
  int result = size == 0;
  if (!result) {
    E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
    result = allocated((uintptr_t)ptr, size, (uintptr_t)ptr_base)
#ifdef E_ACSL_TEMPORAL
             && temporal_valid(ptr_base, addrof_base)
#endif
        ;
    E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  }
  return result;
}

/*! NB: The implementation for this function can also be specified via
   \p _base_addr macro that will eventually call ::TRY_SEGMENT. The following
   implementation is preferred for performance reasons. */
void *eacsl_base_addr(void *ptr) {
  void *result = NULL;
  E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
  TRY_SEGMENT(ptr, result = (void *)heap_info((uintptr_t)ptr, 'B'),
              result = (void *)static_info((uintptr_t)ptr, 'B'));
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

/*! NB: Implementation of the following function can also be specified
   via \p _block_length macro. A more direct approach via ::TRY_SEGMENT
   is preferred for performance reasons. */
size_t eacsl_block_length(void *ptr) {
  size_t result = 0;
  E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
  TRY_SEGMENT(ptr, result = heap_info((uintptr_t)ptr, 'L'),
              result = static_info((uintptr_t)ptr, 'L'))
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

size_t eacsl_offset(void *ptr) {
  size_t result = 0;
  E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
  TRY_SEGMENT(ptr, result = heap_info((uintptr_t)ptr, 'O'),
              result = static_info((uintptr_t)ptr, 'O'));
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}

int eacsl_initialized(void *ptr, size_t size) {
  int result = 0;
  uintptr_t addr = (uintptr_t)ptr;
  E_ACSL_RLOCK(__e_acsl_segment_model_global_lock);
  TRY_SEGMENT_WEAK(addr, result = heap_initialized(addr, size),
                   result = static_initialized(addr, size));
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
  return result;
}
/* }}} */

/* Track program arguments (ARGC/ARGV) {{{ */

/* POSIX-compliant array of character pointers to the environment strings. */
extern char **environ;

static void argv_alloca(int *argc_ref, char ***argv_ref) {
  /* Track a top-level containers */
  shadow_alloca((void *)argc_ref, sizeof(int));
  shadow_alloca((void *)argv_ref, sizeof(char **));
  int argc = *argc_ref;
  char **argv = *argv_ref;
  /* Track argv */
  size_t argvlen = (argc + 1) * sizeof(char *);
  shadow_alloca(argv, argvlen);
  initialize_static_region((uintptr_t)argv, (argc + 1) * sizeof(char *));

  /* Track argument strings */
  while (*argv) {
    /* Account for `\0` when copying C strings */
    size_t arglen = strlen(*argv) + 1;
#ifdef E_ACSL_TEMPORAL
    /* Move `argv` strings to heap. This is because they are allocated
       sparcely and there is no way to align they (if they are small), so there
       may no be sufficient space for storing origin time stamps.
       Generally speaking, this is not the best of ideas, more of a temporary
       fix to avoid various range comparisons. A different approach is
       therefore more than welcome. */
    *argv = shadow_copy(*argv, arglen, 1);
    /* TODO: These heap allocations are never freed in fact. Not super
       important, but for completeness purposes it may be feasible to define
       a buffer of implicitly allocated memory locations which need to be
       freed before a program exists. */
#else
    shadow_alloca(*argv, arglen);
    initialize_static_region((uintptr_t)*argv, arglen);
#endif
    argv++;
  }
#ifdef E_ACSL_TEMPORAL
  /* Fill temporal shadow */
  int i;
  argv = *argv_ref;
  eacsl_temporal_store_nblock(argv_ref, *argv_ref);
  for (i = 0; i < argc; i++)
    eacsl_temporal_store_nblock(argv + i, *(argv + i));
#endif

  while (*environ) {
    size_t envlen = strlen(*environ) + 1;
#ifdef E_ACSL_TEMPORAL
    *environ = shadow_copy(*environ, envlen, 1);
#else
    shadow_alloca(*environ, envlen);
    initialize_static_region((uintptr_t)*environ, envlen);
#endif
    environ++;
  }
}
/* }}} */

/* Program initialization {{{ */
extern int main(void);

static void do_mspaces_init() {
  describe_run();
  eacsl_make_memory_spaces(64 * MB, get_heap_size());
  /* Allocate and log shadow memory layout of the execution.
       Case of the segments available before main. */
  init_shadow_layout_pre_main();
}

void mspaces_init() {
  /* [E_ACSL_RUN_ONCE] avoids reentrancy issue (see Gitlab issue #83),
     e.g. in presence of a GCC's constructors that invokes malloc possibly
     several times before calling main. */
  E_ACSL_RUN_ONCE(do_mspaces_init);
}

void do_eacsl_memory_init(int *argc_ref, char ***argv_ref, size_t ptr_size) {
  mspaces_init();
  /* Verify that the given size of a pointer matches the one in the present
       architecture. This is a guard against Frama-C instrumentations using
       architectures different to the given one. */
  arch_assert(ptr_size);
  /* Initialize report file with debug logs (only in debug mode). */
  initialize_report_file(argc_ref, argv_ref);
  /* Lift stack limit to account for extra stack memory overhead.  */
  increase_stack_limit(E_ACSL_STACK_SIZE * MB);
  /* Allocate and log shadow memory layout of the execution. Case of the
       segments available after main. */
  init_shadow_layout_main(argc_ref, argv_ref);
  //DEBUG_PRINT_LAYOUT;
  /* Make sure the layout holds */
  DVALIDATE_SHADOW_LAYOUT;
  /* Track program arguments. */
  if (argc_ref && argv_ref)
    argv_alloca(argc_ref, argv_ref);
  /* Track main function */
  shadow_alloca(&main, sizeof(&main));
  initialize_static_region((uintptr_t)&main, sizeof(&main));
  /* Tracking safe locations */
  register_safe_locations(E_ACSL_REGISTER_ALL_LOCS);
  init_infinity_values();
}

void eacsl_memory_init(int *argc_ref, char ***argv_ref, size_t ptr_size) {
  /* [E_ACSL_RUN_ONCE_WITH_ARGS] avoids reentrancy issue (see Gitlab issue #83),
     e.g. in presence of a recursive call to 'main'. */
  E_ACSL_RUN_ONCE_WITH_ARGS(do_eacsl_memory_init, argc_ref, argv_ref, ptr_size);
}

void eacsl_memory_clean(void) {
  E_ACSL_WLOCK(__e_acsl_segment_model_global_lock);
  clean_shadow_layout();
  report_heap_leaks();
  E_ACSL_RWUNLOCK(__e_acsl_segment_model_global_lock);
}
/* }}} */
