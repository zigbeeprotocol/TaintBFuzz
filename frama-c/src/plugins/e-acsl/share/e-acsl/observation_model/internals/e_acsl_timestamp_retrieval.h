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
 * \brief Temporal timestamp retrieval
 **************************************************************************/

#ifndef E_ACSL_TIMESTAMP_RETRIEVAL_H
#define E_ACSL_TIMESTAMP_RETRIEVAL_H

#ifdef E_ACSL_TEMPORAL

#  include <stdint.h>

/*! \brief Return origin time stamp associated with a memory block containing
 * address given by `ptr`. `0` indicates an invalid timestamp, i.e., timestamp
 * of a memory block which does not exist. */
uint32_t origin_timestamp(void *ptr);

/*! \brief Return address of referent shadow */
uintptr_t temporal_referent_shadow(void *addr);

/*! \brief Return referent time stamp associated with a pointer which address
 * is given by `ptr`. This function expects that `ptr` is allocated and at
 * least `sizeof(uintptr_t)` bytes long */
uint32_t referent_timestamp(void *ptr);

/*! \brief Store a referent number `ref` in the shadow of `ptr` */
void store_temporal_referent(void *ptr, uint32_t ref);

#endif // E_ACSL_TEMPORAL

#endif // E_ACSL_TIMESTAMP_RETRIEVAL_H
