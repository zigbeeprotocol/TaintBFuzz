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
 * \brief E-ACSL concurrency support for the shadow memory model.
***************************************************************************/

#ifndef E_ACSL_SHADOW_CONCURRENCY_H
#define E_ACSL_SHADOW_CONCURRENCY_H

/* Default size of a thread stack tracked via shadow memory */
#ifndef E_ACSL_THREAD_STACK_SIZE
#  define E_ACSL_THREAD_STACK_SIZE 4
#endif

/*! \brief Initialize memory layout for the current thread, i.e. determine
    bounds of program segments, allocate shadow memory spaces and compute
    offsets.

    \param stack_size The stack size of the current thread. */
void init_thread_shadow_layout(size_t stack_size);

/*! \brief Deallocate shadow regions used by the runtime analysis for the
    current thread. */
void clean_thread_shadow_layout();

/*! \brief Evaluate to true if `addr` is a thread address. */
int is_on_thread(uintptr_t addr);

/*! \brief Convert a thread address into its primary shadow counterpart. */
intptr_t primary_thread_shadow(uintptr_t addr);

/*! \brief Convert a thread address into its secondary shadow counterpart. */
intptr_t secondary_thread_shadow(uintptr_t addr);

#ifdef E_ACSL_TEMPORAL
/*! \brief Convert a thread address into its primary temporal shadow
    counterpart. */
intptr_t temporal_primary_thread_shadow(uintptr_t addr);

/*! \brief Convert a thread address into its secondary temporal shadow
    counterpart. */
intptr_t temporal_secondary_thread_shadow(uintptr_t addr);
#endif

#endif // E_ACSL_SHADOW_CONCURRENCY_H
