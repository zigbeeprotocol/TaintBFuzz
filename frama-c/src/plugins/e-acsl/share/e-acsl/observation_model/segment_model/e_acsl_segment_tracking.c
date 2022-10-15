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

#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "../../instrumentation_model/e_acsl_temporal_timestamp.h"
#include "../../internals/e_acsl_bits.h"
#include "../../internals/e_acsl_rtl_error.h"
#include "../../internals/e_acsl_rtl_string.h"
#include "../internals/e_acsl_omodel_debug.h"
#include "e_acsl_shadow_layout.h"

#include "e_acsl_segment_tracking.h"

/* Segment settings and shadow values interpretation {{{ */

/*! \brief  Decrease _n to be a multiple of _m */
#define ALIGN_LEFT(_n, _m) (_n - _n % _m)

/*! \brief  Increase _n to be a multiple of _m */
#define ALIGN_RIGHT(_n, _m) (_n + ((_n % _m) ? (_m - _n % _m) : 0))

/*! \brief Heap shadow address aligned at a segment boundary */
#define ALIGNED_HEAP_SHADOW(_addr) HEAP_SHADOW(ALIGN_LEFT(_addr, HEAP_SEGMENT))

/* \brief Maximal size_t value that does not cause overflow via addition
 * when segment size is added. */
static const size_t max_allocated = ALIGN_LEFT(SIZE_MAX, HEAP_SEGMENT);

/* \brief Return actual allocation size which takes into account aligned
 * allocation. In the present implementation it is the requested size of
 * a heap block aligned at a segment boundary */
#define ALLOC_SIZE(_s) (_s < max_allocated ? ALIGN_RIGHT(_s, HEAP_SEGMENT) : 0)

/** \brief Evaluate to `true` if address _addr belongs to a memory block
 * with base address _base and length _length */
#define BELONGS(_addr, _base, _length)                                         \
  (_addr >= _base && _addr < _base + _length)

/*! \brief For short blocks numbers 1 to 36 represent lengths and offsets,
 * such that:
 * - 0 -> length 0, offset 0
 * - 1 -> length 1, offset 0,
 * - 2 -> length 2, offset 0,
 * - 3 -> length 2, offset 1 and so on.
 *
 * The below data is used to identify lengths and offsets:
 * Given x is a number from [1, 36] range:
 *   - short_lengths[x] -> length of a block
 *   - short_offsets[x] -> offset within a block */
// clang-format off
static const char short_lengths[] = {
  0,
  1,
  2,2,
  3,3,3,
  4,4,4,4,
  5,5,5,5,5,
  6,6,6,6,6,6,
  7,7,7,7,7,7,7,
  8,8,8,8,8,8,8,8
};

static const char short_offsets[] = {
  0,
  0,
  0,1,
  0,1,2,
  0,1,2,3,
  0,1,2,3,4,
  0,1,2,3,4,5,
  0,1,2,3,4,5,6,
  0,1,2,3,4,5,6,7
};
// clang-format on

/*! \brief Mask for marking a heap segment as initialized.
 * For instance, let `uintptr_t *p' point to the start of a heap segment
 * in the heap shadow, then 'p[1] | heap_init_mask` sets initialization bits.
 * NOTE: This approach cannot deal with segments larger than 64 bits. */
static const uint64_t heap_init_mask = ~(ONE << HEAP_SEGMENT);

/*! \brief Masks for checking of initialization of global/stack allocated blocks.
 * A byte allocated globally or on stack is deemed initialized if its
 * least significant bit is set to `1' and uninitialized otherwise.
 * The binary representation is then as follows (assuming the leftmost
 * bit is the least significant one):
 *
 *  00000000 00000000 00000000 00000000 ... (0)
 *  10000000 00000000 00000000 00000000 ... (1)
 *  10000000 10000000 00000000 00000000 ... (257)
 *  10000000 10000000 10000000 00000000 ... (65793)
 *  10000000 10000000 10000000 10000000 ... (16843009)
 *  ...
 *
 * For instance, mark first X bytes of a number N as initialised:
 *    N |= static_init_masks[X] */
static const uint64_t static_init_masks[] = {
    0,                /* 0 bytes */
    1,                /* 1 byte */
    257,              /* 2 bytes */
    65793,            /* 3 bytes */
    16843009,         /* 4 bytes */
    4311810305,       /* 5 bytes */
    1103823438081,    /* 6 bytes */
    282578800148737,  /* 7 bytes */
    72340172838076673 /* 8 bytes */
};

/*! \brief Bit masks for setting read-only (second least significant) bits.
 * Binary representation (assuming the least significant bit is the
 * leftmost bit) is follows:
 *
 *  00000000 00000000 00000000 00000000 ... (0)
 *  01000000 00000000 00000000 00000000 ... (2)
 *  01000000 01000000 00000000 00000000 ... (514)
 *  01000000 01000000 01000000 00000000 ... (131586)
 *  01000000 01000000 01000000 01000000 ... (33686018)
 *  ...
 *
 *  For instance, mark first X bytes of a number N as read-only:
 *    N |= static_readonly_masks[X] */
static const uint64_t static_readonly_masks[] = {
    0,                 /* 0 bytes */
    2,                 /* 1 byte */
    514,               /* 2 bytes */
    131586,            /* 3 bytes */
    33686018,          /* 4 bytes */
    8623620610,        /* 5 bytes */
    2207646876162,     /* 6 bytes */
    565157600297474,   /* 7 bytes */
    144680345676153346 /* 8 bytes */
};
/* }}} */

/* Runtime assertions (debug mode) {{{ */
#ifdef E_ACSL_DEBUG
void validate_shadow_layout() {
  /* Check that the struct holding memory layout is marked as initialized. */
  DVALIDATE_MEMORY_INIT;

#  ifdef E_ACSL_DEBUG_VERBOSE
  DEBUG_PRINT_LAYOUT;
#  endif

  /* Each segment has 3 partitions:
	 - application memory
     - primary/secondary shadows */
  int num_partitions = sizeof(mem_partitions) / sizeof(memory_partition *);
  int num_seg_in_part = 3;
#  ifdef E_ACSL_TEMPORAL
  num_seg_in_part = 5;
#  endif
  int num_segments = num_partitions * num_seg_in_part;
  uintptr_t segments[num_segments][2];
  const char *segment_names[num_segments];

  size_t i, app_idx, primary_idx, secondary_idx;
#  ifdef E_ACSL_TEMPORAL
  size_t primary_temporal_idx, secondary_temporal_idx;
#  endif
  for (i = 0; i < num_partitions; i++) {
    memory_partition *p = mem_partitions[i];

    app_idx = num_seg_in_part * i;
    segment_names[app_idx] = p->application.name;
    segments[app_idx][0] = p->application.start;
    segments[app_idx][1] = p->application.end;

    primary_idx = num_seg_in_part * i + 1;
    segment_names[primary_idx] = p->primary.name;
    segments[primary_idx][0] = p->primary.start;
    segments[primary_idx][1] = p->primary.end;

    secondary_idx = num_seg_in_part * i + 2;
    segment_names[secondary_idx] = p->secondary.name;
    segments[secondary_idx][0] = p->secondary.start;
    segments[secondary_idx][1] = p->secondary.end;

#  ifdef E_ACSL_TEMPORAL
    primary_temporal_idx = num_seg_in_part * i + 3;
    segment_names[primary_temporal_idx] = p->temporal_primary.name;
    segments[primary_temporal_idx][0] = p->temporal_primary.start;
    segments[primary_temporal_idx][1] = p->temporal_primary.end;

    secondary_temporal_idx = num_seg_in_part * i + 4;
    segment_names[secondary_temporal_idx] = p->temporal_secondary.name;
    segments[secondary_temporal_idx][0] = p->temporal_secondary.start;
    segments[secondary_temporal_idx][1] = p->temporal_secondary.end;
#  endif
  }

  /* Make sure all segments (shadow or otherwise) are disjoint */
  size_t j;
  for (int i = 0; i < num_segments; i++) {
    uintptr_t *src = segments[i];
    const char *src_name = segment_names[i];
    DVASSERT(src[0] < src[1],
             "Segment %s start is greater than segment end %a < %a\n", src_name,
             src[0], src[1]);
    for (j = 0; j < num_segments; j++) {
      if (i != j) {
        uintptr_t *dest = segments[j];
        const char *dest_name = segment_names[j];
        DVASSERT(src[1] < dest[0] || src[0] > dest[1],
                 "Segment %s [%a, %a] overlaps with segment %s [%a, %a]\n",
                 src_name, src[0], src[1], dest_name, dest[0], dest[1]);
      }
    }
  }
}
#endif
/* }}} */

/* E-ACSL predicates {{{ */
uintptr_t predicate(uintptr_t addr, char p) {
  TRY_SEGMENT(addr, return heap_info((uintptr_t)addr, p),
              return static_info((uintptr_t)addr, p));
  return 0;
}
/* }}} */

/* Static allocation {{{ */

/** The below numbers identify offset "bases" for short block lengths.
 * An offset base is a number (a code) that represents the length of a
 * short block with a byte offset of `0`.
 * For instance, for a block of 4 bytes its offset base if 7, that is
 *  length 4, offset 0 => 7,
 *  length 4, offset 1 => 8,
 *  length 4, offset 2 => 9,
 *  length 4, offset 3 => 10,
 * and then for a block of 5 bytes its base offset if 11 etc. */
static const char short_offsets_base[] = {0, 1, 2, 4, 7, 11, 16, 22, 29};

/** Shadow masks for setting values of short blocks */
static const uint64_t short_shadow_masks[] = {0UL,
                                              4UL,
                                              3080UL,
                                              1578000UL,
                                              673456156UL,
                                              258640982060UL,
                                              92703853921344UL,
                                              31644393008028760UL,
                                              10415850140873816180UL};

void shadow_alloca(void *ptr, size_t size) {
  DVALIDATE_IS_ON_STATIC(ptr, size);
#ifdef E_ACSL_TEMPORAL
  /* Make sure that during temporal analysis there is
   * sufficient space to store an origin timestamp.
   * NOTE: This does not apply to globals, because all the globals
   * have the timestamp of `1`. */
  if (!IS_ON_GLOBAL(ptr)) {
    DVALIDATE_STATIC_SUFFICIENTLY_ALIGNED((uintptr_t)ptr, 4);
  }
#endif

  unsigned char *prim_shadow = (unsigned char *)PRIMARY_SHADOW(ptr);
  uint64_t *prim_shadow_alt = (uint64_t *)PRIMARY_SHADOW(ptr);
  unsigned int *sec_shadow = (unsigned int *)SECONDARY_SHADOW(ptr);

  /* Make sure shadows are nullified */
  DVALIDATE_NULLIFIED(prim_shadow, size);
  DVALIDATE_NULLIFIED(sec_shadow, size);

  /* Flip read-only bit for zero-size blocks. That is, physically it exists
   * but one cannot write to it. Further, the flipped read-only bit will also
   * identify such block as allocated */
  if (!size)
    setbit(READONLY_BIT, prim_shadow[0]);

  unsigned int i, j = 0, k = 0;
  if (IS_LONG_BLOCK(size)) { /* Long blocks */
    unsigned int i, j = 0, k = 0;
    int boundary = LONG_BLOCK_BOUNDARY(size);
    for (i = 0; i < boundary; i += LONG_BLOCK) {
      /* Set-up a secondary shadow segment */
      sec_shadow[j++] = size;
      sec_shadow[j++] = i;
      /* Set primary shadow offsets */
      prim_shadow_alt[k++] = LONG_BLOCK_MASK;
    }

    /* Write out the remainder */
    for (i = boundary; i < size; i++) {
      unsigned char offset =
          i % LONG_BLOCK + LONG_BLOCK_INDEX_START + LONG_BLOCK;
      prim_shadow[i] = (offset << 2);
    }
  } else { /* Short blocks */
    for (i = 0; i < size; i++) {
      unsigned char code = short_offsets_base[size] + i;
      prim_shadow[i] = (code << 2);
    }
  }
#ifdef E_ACSL_TEMPORAL /*{{{*/
  /* Store a temporal origin timestamp in the first 4 bytes of a temporal
   * shadow. This, however applies only to TLS of stack blocks. Global blocks
   * are never deallocated, an origin time stamp of any global block is given
   * via `GLOBAL_TEMPORAL_TIMESTAMP` */
  if (!IS_ON_GLOBAL(ptr)) {
    uint32_t *temporal_shadow = (uint32_t *)TEMPORAL_PRIMARY_STATIC_SHADOW(ptr);
    *temporal_shadow = NEW_TEMPORAL_TIMESTAMP();
  }
#endif /*}}} E_ACSL_TEMPORAL*/
}
/* }}} */

/* Deletion of static blocks {{{ */
void shadow_freea(void *ptr) {
  DVALIDATE_STATIC_LOCATION(ptr);
  DASSERT(ptr == (void *)_base_addr(ptr));
  size_t size = _block_length(ptr);
  memset((void *)PRIMARY_SHADOW(ptr), 0, size);
  memset((void *)SECONDARY_SHADOW(ptr), 0, size);
#ifdef E_ACSL_TEMPORAL /*{{{*/
  memset((void *)TEMPORAL_PRIMARY_STATIC_SHADOW(ptr), 0, size);
  memset((void *)TEMPORAL_SECONDARY_STATIC_SHADOW(ptr), 0, size);
#endif /*}}} E_ACSL_TEMPORAL*/
}
/* }}} */

/* Static querying {{{ */

int static_allocated(uintptr_t addr, long size, uintptr_t base_ptr) {
  unsigned char *prim_shadow = (unsigned char *)PRIMARY_SHADOW(addr);
  /* Unless the address belongs to tracked allocation 0 is returned */
  if (prim_shadow[0]) {
    unsigned int code = (prim_shadow[0] >> 2);
    unsigned int long_block = (code >= LONG_BLOCK_INDEX_START);
    size_t length, offset;
    if (long_block) {
      offset = code - LONG_BLOCK_INDEX_START;
      unsigned int *sec_shadow =
          (unsigned int *)SECONDARY_SHADOW(addr - offset);
      length = sec_shadow[0];
      offset = sec_shadow[1] + offset;
    } else {
      offset = short_offsets[code];
      length = short_lengths[code];
    }

#ifndef E_ACSL_WEAK_VALIDITY
    if (addr != base_ptr) {
      return BELONGS(base_ptr, addr - offset, length)
             && offset + size <= length;
    }
#endif
    return offset + size <= length;
  }
  return 0;
}

int static_initialized(uintptr_t addr, long size) {
  /* Return 0 right away if the address does not belong to
   * static allocation */
  if (!static_allocated(addr, size, addr))
    return 0;
  DVALIDATE_STATIC_ACCESS(addr, size);

  int result = 1;
  uint64_t *shadow = (uint64_t *)PRIMARY_SHADOW(addr);
  while (size > 0) {
    int rem = (size >= ULONG_BYTES) ? ULONG_BYTES : size;
    uint64_t mask = static_init_masks[rem];
    size -= ULONG_BYTES;
    /* Note that most of the blocks checked for initialization will be smaller
    * than 64 bits, therefore in most cases it is more efficient to complete
    * the loop rather than do a test and return if the result is false */
    result = result && (((*shadow) & mask) == mask);
    shadow++;
  }
  return result;
}

uintptr_t static_info(uintptr_t addr, char type) {
  DVALIDATE_STATIC_LOCATION(addr);
  unsigned char *prim_shadow = (unsigned char *)PRIMARY_SHADOW(addr);

  /* Unless the address belongs to tracked allocation 0 is returned */
  if (prim_shadow[0]) {
    unsigned int code = (prim_shadow[0] >> 2);
    unsigned int long_block = (code >= LONG_BLOCK_INDEX_START);
    if (long_block) {
      unsigned int offset = code - LONG_BLOCK_INDEX_START;
      unsigned int *sec_shadow =
          (unsigned int *)SECONDARY_SHADOW(addr - offset);
      switch (type) {
      case 'B': /* Base address */
        return addr - offset - sec_shadow[1];
      case 'O': /* Offset */
        return sec_shadow[1] + offset;
      case 'L': /* Length */
        return sec_shadow[0];
      default:
        DVABORT("Unknown static query type\n");
      }
    } else {
      switch (type) {
      case 'B': /* Base address */
        return addr - short_offsets[code];
      case 'O': /* Offset */
        return short_offsets[code];
      case 'L': /* Length */
        return short_lengths[code];
      default:
        DVABORT("Unknown static query type\n");
      }
    }
  }
  return 0;
}

#ifdef E_ACSL_TEMPORAL /*{{{*/
uint32_t static_temporal_info(uintptr_t addr, int origin) {
  /* NOTE: No checking for allocated blocks, since an invalid
   timestamp is zero and ununsed memory is nullified then an invalid
   timestamp is also returned for allocated memory */
  if (origin) {
    int allocated = static_allocated_one(addr);
    if (allocated && !IS_ON_GLOBAL(addr)) {
      uintptr_t base = static_info(addr, 'B');
      return *((uint32_t *)TEMPORAL_PRIMARY_STATIC_SHADOW(base));
    } else if (allocated && IS_ON_GLOBAL(addr)) {
      return GLOBAL_TEMPORAL_TIMESTAMP;
    } else {
      return INVALID_TEMPORAL_TIMESTAMP;
    }
  } else {
    return *((uint32_t *)TEMPORAL_SECONDARY_STATIC_SHADOW(addr));
  }
}

void static_store_temporal_referent(uintptr_t addr, uint32_t ref) {
  DVALIDATE_STATIC_ACCESS(addr, PTR_SZ);
  *((uint32_t *)TEMPORAL_SECONDARY_STATIC_SHADOW(addr)) = ref;
}
#endif /*}}} E_ACSL_TEMPORAL*/
/* }}} */

/* Static initialization {{{ */
void initialize_static_region(uintptr_t addr, long size) {
  DVALIDATE_STATIC_ACCESS(addr, size);
  DVASSERT(!(addr - _base_addr(addr) + size > _block_length(addr)),
           "Attempt to initialize %lu bytes past block boundaries\n"
           "starting at %a with block length %lu at base address %a\n",
           size, addr, _block_length(addr), _base_addr(addr));

  /* Below code marks `size` bytes following `addr` in the stack shadow as
   * initialized. That is, least significant bits of all 9 bytes following
   * `addr` should be flipped to ones. While this is a common pattern in this
   * program, here are some explanations.
   *
   * Here we grab a shadow region and initialize 8 (::ULONG_SIZE) bits at a
   * time using masks stored in ::static_init_masks. This few lines below are
   * better explained using an example. Let's say we need to mark 9 bytes as
   * initialized starting from some address `addr`.
   *
   * In order to do that we first grab a shadow region storing it in `shadow`.
   * For the first 8 bytes we grab a mask stored at ::static_init_masks[8]:
   *   `10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000`
   * That is, `*shadow |= static_init_masks[8]` sets 8 lowest significant bits
   * of the 8 bytes following *shadow to ones.
   *
   * After that we need to mark the remaining 1 bite as initialized. For that
   * we grab mask ::static_init_masks[1]:
   *  `10000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000`
   * That is, `*shadow |= static_init_masks[1]` will set only the least
   * significant bit in *shadow. */

  uint64_t *shadow = (uint64_t *)PRIMARY_SHADOW(addr);
  while (size > 0) {
    int rem = (size >= ULONG_BYTES) ? ULONG_BYTES : size;
    size -= ULONG_BYTES;
    *shadow |= static_init_masks[rem];
    shadow++;
  }
}
/* }}} */

/* Read-only {{{ */
void mark_readonly_region(uintptr_t addr, long size) {
  /* Since read-only blocks can only be stored in the globals  segments (e.g.,
   * TEXT), this function required ptr carry a global address. */
  DASSERT(IS_ON_GLOBAL(addr));
  DASSERT(static_allocated_one(addr));
  DVASSERT(!(addr - _base_addr(addr) + size > _block_length(addr)),
           "Attempt to mark read-only %lu bytes past block boundaries\n"
           "starting at %a with block length %lu at base address %a\n",
           size, addr, _block_length(addr), _base_addr(addr));

  /* See comments in ::initialize_static_region for details */
  uint64_t *shadow = (uint64_t *)PRIMARY_GLOBAL_SHADOW(addr);
  while (size > 0) {
    int rem = (size >= ULONG_BYTES) ? ULONG_BYTES : size;
    size -= ULONG_BYTES;
    *shadow |= static_readonly_masks[rem];
    shadow++;
  }
}
/* }}} */

/* Heap allocation {{{ (malloc/calloc) */

/*! \brief Create a heap shadow for an allocated memory block starting at `ptr`
 * and of length `size`. Optionally mark it as initialized if `init`
 * evaluates to a non-zero value.
 * \b NOTE: This function assumes that `ptr` is a base address of a
 * heap-allocated memory block, such that HEAP_SEGMENT bytes preceding `ptr`
 * correspond to `unusable space`.
 * \b WARNING: Current implementation assumes that the size of a heap segment
 * does not exceed 64 bytes. */
static void set_heap_segment(void *ptr, size_t size, size_t alloc_size,
                             size_t init, const char *function) {

  /* Make sure that heap memspace has not been moved. This is likely if
     a really large chunk has been requested to be allocated. */
  private_assert(
      mem_spaces.heap_mspace_least
          == (uintptr_t)eacsl_mspace_least_addr(mem_spaces.heap_mspace),
      "Exceeded heap allocation limit of %luMB -- heap memory space moved. \n",
      E_ACSL_HEAP_SIZE);

  /* Similar check, make sure that allocated space does not exceed given
     allocation limit for mspace */
  uintptr_t max_addr = (uintptr_t)ptr + alloc_size;
  private_assert(mem_spaces.heap_end > max_addr,
                 "Exceeded heap allocation limit of %luMB\n", E_ACSL_HEAP_SIZE);

  DVALIDATE_MEMORY_PRE_MAIN_INIT;
  /* Ensure the shadowed block in on the tracked heap portion */
  DVALIDATE_IS_ON_HEAP(((uintptr_t)ptr) - HEAP_SEGMENT, size);
  DVALIDATE_ALIGNMENT(ptr);     /* Make sure alignment is right */
  update_heap_allocation(size); /* Adjust tracked allocation size */

  /* Get aligned size of the block, i.e., an actual size of the
   * allocated block */
  unsigned char *shadow = (unsigned char *)HEAP_SHADOW(ptr);

  /* Make sure shadow is nullified before setting it */
  DVALIDATE_NULLIFIED(shadow, alloc_size);

  /* The overall number of block segments in a tracked memory block  */
  size_t segments = alloc_size / HEAP_SEGMENT;
  uintptr_t *segment = (uintptr_t *)(shadow);
  segment[1] = size;

#ifdef E_ACSL_TEMPORAL /*{{{*/
  /* 4 bytes following a block's length store an origin timestamp */
  segment[2] = NEW_TEMPORAL_TIMESTAMP();
#endif /*}}} E_ACSL_TEMPORAL*/

  int i;
  /* Write the offsets per segment */
  for (i = 0; i < segments; i++) {
    segment = (uintptr_t *)(shadow + i * HEAP_SEGMENT);
    *segment = (uintptr_t)ptr;
  }

  /* If init is a non-zero value then mark all allocated bytes as initialized */
  if (init) {
    memset((void *)HEAP_INIT_SHADOW(ptr), (unsigned int)ONE, alloc_size / 8);
  }
}

void *unsafe_malloc(size_t size) {
  size_t alloc_size = ALLOC_SIZE(size);

  /* Return NULL if the size is too large to be aligned */
  char *res;
  if (alloc_size) {
    mspaces_init();
    res = (char *)public_malloc(alloc_size);
  } else
    res = NULL;

  if (res) {
    /* Make sure there is sufficient room in shadow */
    set_heap_segment(res, size, alloc_size, 0, "malloc");
  }

  return res;
}

void *unsafe_calloc(size_t nmemb, size_t size) {
  /* Since both `nmemb` and `size` are both of size `size_t` the multiplication
   * of the arguments (which gives the actual allocation size) might lead to an
   * integer overflow. The below code checks for an overflow and sets the
   * `alloc_size` (argument a memory allocation function) to zero. */
  size = (size && nmemb > SIZE_MAX / size) ? 0 : nmemb * size;

  size_t alloc_size = ALLOC_SIZE(size);

  /* Since aligned size is required by the model do the allocation through
   * `malloc` and nullify the memory space by hand */
  char *res;
  if (size) {
    mspaces_init();
    res = (char *)public_malloc(alloc_size);
  } else
    res = NULL;

  if (res) {
    /* Make sure there is sufficient room in shadow */
    memset(res, 0, size);
    set_heap_segment(res, size, alloc_size, 1, "calloc");
  }
  return res;
}

void *shadow_copy(const void *ptr, size_t size, int init) {
  char *ret = (init) ? unsafe_calloc(1, size) : unsafe_malloc(size);
  private_assert(ret != NULL, "Shadow copy failed\n", NULL);
  /* Shadow copy is internal, therefore heap status should not be updated.
     Since it is set via `set_heap_segment`, it needs to be reverted back. */
  update_heap_allocation(-size);
  return memcpy(ret, ptr, size);
}
/* }}} */

/* Heap deallocation (free) {{{ */

/*! \brief Remove a memory block with base address given by `ptr` from tracking.
 * This function effectively nullifies block shadow tracking an application
 * block.
 *
 * NOTE: ::unset_heap_segment assumes that `ptr` is a base address of an
 * allocated heap memory block, i.e., `eacsl_freeable(ptr)` evaluates to true.
 *
 * \param ptr - base address of the memory block to be removed from tracking
 * \param init - if evaluated to a non-zero value then initialization shadow
 *  of the memory block with base address `ptr` is nullified as well.
 * \param function - name of the de-allocation function (e.g., `free` or `cfree`)
*/
static void unset_heap_segment(void *ptr, int init, const char *function) {
  DVALIDATE_MEMORY_PRE_MAIN_INIT;
  DVALIDATE_FREEABLE(((uintptr_t)ptr));
  /* Base address of shadow block */
  uintptr_t *base_shadow = (uintptr_t *)HEAP_SHADOW(ptr);
  /* Physical allocation size */
  size_t alloc_size = ALLOC_SIZE(base_shadow[1]);
  /* Actual block length */
  size_t length = base_shadow[1];
  /* Nullify shadow block */
  memset(base_shadow, ZERO, alloc_size);
  /* Adjust tracked allocation size */
  update_heap_allocation(-length);
#ifdef E_ACSL_TEMPORAL /*{{{*/
  /* Nullify temporal shadow */
  uintptr_t *t_base_shadow = (uintptr_t *)TEMPORAL_HEAP_SHADOW(ptr);
  memset(t_base_shadow, ZERO, alloc_size);
#endif /*}}} E_ACSL_TEMPORAL*/
  /* Nullify init shadow */
  if (init) {
    memset((void *)HEAP_INIT_SHADOW(ptr), 0, alloc_size / 8);
  }
}

void unsafe_free(void *ptr) {
  if (ptr == NULL) {
/* Fail if instructed to treat NULL input to free as invalid. */
#ifdef E_ACSL_FREE_VALID_ADDRESS
    private_abort("NULL pointer in free\n");
#endif
    return;
  }

  if (ptr != NULL) { /* NULL is a valid behaviour */
    if (unsafe_freeable(ptr)) {
      unset_heap_segment(ptr, 1, "free");
      public_free(ptr);
    } else {
      private_abort("Not a start of block (%a) in free\n", ptr);
    }
  }
}
/* }}} */

/* Heap reallocation (realloc) {{{ */
void *unsafe_realloc(void *ptr, size_t size) {
  char *res = NULL; /* Resulting pointer */
  /* If the pointer is NULL then realloc is equivalent to malloc(size) */
  if (ptr == NULL)
    return unsafe_malloc(size);
  /* If the pointer is not NULL and the size is zero then realloc is
   * equivalent to free(ptr) */
  else if (ptr != NULL && size == 0) {
    unsafe_free(ptr);
  } else {
    if (unsafe_freeable(ptr)) { /* ... and can be used as an input to `free` */
      size_t alloc_size = ALLOC_SIZE(size);
      res = public_realloc(ptr, alloc_size);
      DVALIDATE_ALIGNMENT(res);

      /* realloc succeeds, otherwise nothing needs to be done */
      if (res != NULL) {
        size_t alloc_size = ALLOC_SIZE(size);
        size_t old_size = _block_length(ptr);
        size_t old_alloc_size = ALLOC_SIZE(old_size);

        /* Nullify old representation */
        unset_heap_segment(ptr, 0, "realloc");

        /* Set up new block shadow */
        set_heap_segment(res, size, alloc_size, 0, "realloc");

        /* Move init shadow */
        unsigned char *old_init_shadow = (unsigned char *)HEAP_INIT_SHADOW(ptr);
        unsigned char *new_init_shadow = (unsigned char *)HEAP_INIT_SHADOW(res);

        /* If realloc truncates allocation in the old init shadow it is first
         * needed to clear the old init shadow from the boundary of the old
         * shadow block to the size of the new allocation */
        if (old_size > size) {
          clearbits_right(old_alloc_size - size, // size in bits
                          old_init_shadow
                              + old_alloc_size
                                    / 8); // end of the old init shadow
        }

        /* Keep in mind that there is a ratio of 8 between the actual heap
         * memory and the init shadow memory. So a byte in the actual memory
         * corresponds to a bit in the shadow memory.
         */

        /* We need to keep the status of the init shadow up to `old_size` bits
         * (or `size` if `size < old_size`), and we need to make sure that the
         * bits of the init shadow correspondings to the bytes between
         * `old_size` and `size` are set to zero if `size > old_size`. */

        /* First of all, determine the number of bits in the init shadow that
         * must be kept */
        size_t keep_bits = (size < old_size) ? size : old_size;

        /* To avoid doing too much bitwise operations, separate this size in
         * the amount of bytes of init shadow that must be kept including any
         * incomplete byte, and the number of bits that must be kept in the last
         * byte if it is incomplete */
        size_t rem_keep_bits = keep_bits % 8;
        size_t keep_bytes = keep_bits / 8 + (rem_keep_bits > 0 ? 1 : 0);

        /* If the pointer has been moved, then we need to copy `keep_bytes`
         * from the old shadow to the new shadow to carry over all the needed
         * information. Then the old init shadow can be reset. */
        if (res != ptr) {
          DVASSERT(
              keep_bytes <= alloc_size / 8 && keep_bytes < old_alloc_size / 8,
              "Attempt to access out of bound init shadow. Accessing %lu bytes, \
            old init shadow size: %lu bytes, new init shadow size: %lu \
            bytes.\n",
              keep_bytes, old_alloc_size / 8, alloc_size / 8);
          memcpy(new_init_shadow, old_init_shadow, keep_bytes);
          memset(old_init_shadow, 0, old_alloc_size / 8);
        }

        if (size > old_size) {
          // Last kept byte index
          size_t idx = keep_bytes - 1; // idx < init_shadow_size by construction

          /* If the new size is greater than the old size and the last kept byte
           * is incomplete (`rem_keep_bits > 0`), then reset the unkept bits of
           * the last byte in the new init shadow */
          if (rem_keep_bits > 0) {
            DVASSERT(
                idx < alloc_size / 8,
                "Attempt to access out of bound init shadow. Accessing index %lu \
              with init shadow of size %lu bytes.\n",
                idx, alloc_size / 8);
            unsigned char mask = 0;
            setbits64(rem_keep_bits, mask);
            *(new_init_shadow + idx) &= mask;
          }

          /* Finally, if the new size is greater than the old size and the
           * pointer hasn't been moved, then we need to make sure that the
           * remaining bits of the init shadow corresponding to the memory
           * between `old_size` and `size` are set to zero. */
          if (res == ptr) {
            // Index of the byte after the last kept byte
            ++idx;
            // Number of bytes between the index and the end of the init
            // shadow corresponding to the new allocated memory
            size_t count = size / 8 - idx;

            DVASSERT(
                (idx + count) <= alloc_size / 8,
                "Attempt to access out of bound init shadow. Accessing %lu bytes \
              from index %lu with init shadow of size %lu bytes.\n",
                count, idx, alloc_size / 8);
            memset(new_init_shadow + idx, 0, count);
          }
        }
      }
    } else {
      private_abort("Not a start of block (%a) in realloc\n", ptr);
    }
  }
  return res;
}
/* }}} */

/* Heap aligned allocation (aligned_alloc) {{{ */
void *unsafe_aligned_alloc(size_t alignment, size_t size) {
  /* Check if:
   *  - size and alignment are greater than zero
   *  - alignment is a power of 2
   *  - size is a multiple of alignment */
  if (!size || !alignment || !is_pow_of_2(alignment) || (size % alignment))
    return NULL;

  char *res = public_aligned_alloc(alignment, size);

  if (res) {
    set_heap_segment(res, size, ALLOC_SIZE(size), 0, "aligned_alloc");
  }

  return (void *)res;
}
/* }}} */

/* Heap aligned allocation (posix_memalign) {{{ */
int unsafe_posix_memalign(void **memptr, size_t alignment, size_t size) {
  /* Check if:
   *  - size and alignment are greater than zero
   *  - alignment is a power of 2 and a multiple of sizeof(void*) */
  if (!size || !alignment || !is_pow_of_2(alignment)
      || alignment % sizeof(void *))
    return -1;

  /* Make sure that the first argument to posix memalign is indeed allocated */
  private_assert(
      allocated((uintptr_t)memptr, sizeof(void *), (uintptr_t)memptr),
      "\\invalid memptr in  posix_memalign\n", NULL);

  int res = public_posix_memalign(memptr, alignment, size);
  if (!res) {
    set_heap_segment(*memptr, size, ALLOC_SIZE(size), 0, "posix_memalign");
  }
  return res;
}
/* }}} */

/* Heap querying {{{ */
int heap_allocated(uintptr_t addr, size_t size, uintptr_t base_ptr) {
  /* Base address of the shadow segment the address belongs to */
  uintptr_t *shadow = (uintptr_t *)HEAP_SHADOW(addr - addr % HEAP_SEGMENT);

  /* Non-zero if the segment belongs to heap allocation */
  if (shadow[0]) {
    uintptr_t *base_shadow =
        (uintptr_t *)HEAP_SHADOW(base_ptr - base_ptr % HEAP_SEGMENT);
    uintptr_t *first_segment = (uintptr_t *)HEAP_SHADOW(shadow[0]);
    /* shadow[0] - base address of the tracked block
     * fist_segment[1] - length (i.e., location in the first segment
     *  after base address)
     * offset is the difference between the address and base address (shadow[0])
     * Then an address belongs to heap allocation if
     *  offset + size <= length
     *
     * Additionally, if strong validity is enforced
     * (i.e., E_ACSL_WEAK_VALIDITY macro undefined) make sure that both
     * `addr` and `base_ptr` belong to the same block. */
#ifndef E_ACSL_WEAK_VALIDITY
    return base_shadow[0] == shadow[0]
           && (addr - shadow[0]) + size <= first_segment[1];
#else
    return (addr - shadow[0]) + size <= first_segment[1];
#endif
  }
  return 0;
}

int unsafe_freeable(void *ptr) { /* + */
  uintptr_t addr = (uintptr_t)ptr;
  /* Address is not on the program's heap, so cannot be freed */
  if (!IS_ON_HEAP(addr))
    return 0;

  /* Address of the shadow segment the address belongs to */
  uintptr_t *shadow = (uintptr_t *)ALIGNED_HEAP_SHADOW(addr);
  /* Non-zero if the segment belongs to heap allocation with *shadow
   * capturing the base address of the tracked block */
  if (*shadow) {
    /* Block is freeable if `addr` is the base address of its block  */
    return (uintptr_t)*shadow == addr;
  }
  return 0;
}

uintptr_t heap_info(uintptr_t addr, char type) {
  /* Ensure that `addr` is an allocated location on a program's heap */
  DVALIDATE_HEAP_ACCESS(addr, 1);
  /* Base address of the shadow segment the address belongs to.
   * First `sizeof(uintptr_t)` bytes of each segment store application-level
   * base address of the tracked block */
  uintptr_t *aligned_shadow = (uintptr_t *)ALIGNED_HEAP_SHADOW(addr);

  switch (type) {
  case 'B': /* Base address */
    return *aligned_shadow;
  case 'L': { /* Block length */
    /* Pointer to the first-segment in the shadow block */
    uintptr_t *base_segment = (uintptr_t *)HEAP_SHADOW(*aligned_shadow);
    /* Length of the stored block is captured in `sizeof(uintptr_t)` bytes
       * past `sizeof(uintptr_t)` tracking the base address */
    return base_segment[1];
  }
  case 'O':
    /* Offset of a given address within its block. This is the difference
       * between the input address and the base address of the block. */
    return addr - *aligned_shadow;
  default:
    DVABORT("Unknown heap query type\n");
  }
  return 0;
}

int heap_initialized(uintptr_t addr, long len) {
  /* Base address of a shadow segment addr belongs to */
  unsigned char *shadow = (unsigned char *)(HEAP_INIT_SHADOW(addr));

  /* See comments in the `initialize_heap_region` function for more details */
  unsigned skip = (addr - HEAP_START) % 8;
  unsigned set;
  if (skip) {
    set = 8 - skip;
    set = (len > set) ? set : len;
    len -= set;
    unsigned char mask = 0;
    setbits64_skip(set, mask, skip);

    if ((*shadow & mask) != mask)
      return 0;
  }
  if (len > 0)
    return checkbits(len, shadow);
  return 1;
}
/* }}} */

/* Heap temporal querying {{{*/
#ifdef E_ACSL_TEMPORAL
uint32_t heap_temporal_info(uintptr_t addr, int origin) {
  /* NOTE: No checking for allocated blocks, since an invalid
     timestamp is zero and unused memory is nullified then an invalid
     timestamp is also returned for allocated memory */
  if (origin) {
    uintptr_t *aligned_shadow = (uintptr_t *)ALIGNED_HEAP_SHADOW(addr);
    uintptr_t *base_shadow = (uintptr_t *)HEAP_SHADOW(*aligned_shadow);
    return (uint32_t)base_shadow[2];
  } else {
    return *((uint32_t *)TEMPORAL_HEAP_SHADOW(addr));
  }
}

void heap_store_temporal_referent(uintptr_t addr, uint32_t ref) {
  DVALIDATE_HEAP_ACCESS(addr, PTR_SZ);
  uint32_t *temporal_shadow = (uint32_t *)TEMPORAL_HEAP_SHADOW(addr);
  *temporal_shadow = ref;
}
#endif /*}}} E_ACSL_TEMPORAL*/

/* Heap initialization {{{ */
void initialize_heap_region(uintptr_t addr, long len) {
  DVALIDATE_HEAP_ACCESS(addr, len);
  DVASSERT(!(addr - _base_addr(addr) + len > _block_length(addr)),
           "Attempt to initialize %lu bytes past block boundaries\n"
           "starting at %a with block length %lu at base address %a\n",
           len, addr, _block_length(addr), _base_addr(addr));

  /* Address within init shadow tracking initialization  */
  unsigned char *shadow = (unsigned char *)(HEAP_INIT_SHADOW(addr));

  /* First check whether the address in the init shadow is divisible by 8
   * (i.e., located on a byte boundary) */
  /* Leading bits in `*shadow` byte which do not need to be set
   * (i.e., skipped) */
  short skip = (addr - HEAP_START) % 8;
  if (skip) {
    /* The remaining bits in the shadow byte */
    short set = 8 - skip;
    /* The length of initialized region can be short (shorter then the
     * above remainder). Adjust the number of bits to set accordingly. */
    set = (len > set) ? set : len;
    len -= set;
    setbits64_skip(set, *shadow, skip);
    /* Move to the next location if there are more bits to set */
    shadow++;
  }

  if (len > 0) {
    /* Set the remaining bits. Note `shadow` is now aligned at a byte
     * boundary, thus one can set `len` bits starting with address given by
     * `shadow` */
    setbits(len, shadow);
  }
}
/* }}} */

/* Heap or static initialization {{{ */
void unsafe_initialize(void *ptr, size_t n) {
  TRY_SEGMENT((uintptr_t)ptr, initialize_heap_region((uintptr_t)ptr, n),
              initialize_static_region((uintptr_t)ptr, n))
}
/* }}} */

/* Internal state print (debug mode) {{{ */
#ifdef E_ACSL_DEBUG
void printbyte(unsigned char c, char buf[], size_t bufsize) {
  if (c >> 2 < LONG_BLOCK_INDEX_START) {
    rtl_snprintf(buf, bufsize, "PRIMARY: I{%u} RO{%u} OF{%2u} => %u[%u]",
                 checkbit(INIT_BIT, c), checkbit(READONLY_BIT, c), c >> 2,
                 short_lengths[c >> 2], short_offsets[c >> 2]);
  } else {
    rtl_snprintf(buf, bufsize, "SECONDARY:  I{%u} RO{%u} OF{%u} => %4u",
                 checkbit(INIT_BIT, c), checkbit(READONLY_BIT, c), (c >> 2),
                 (c >> 2) - LONG_BLOCK_INDEX_START);
  }
}

void print_static_shadows(uintptr_t addr, size_t size) {
  char prim_buf[256];
  char sec_buf[256];

  unsigned char *prim_shadow = (unsigned char *)PRIMARY_SHADOW(addr);
  unsigned int *sec_shadow = (unsigned int *)SECONDARY_SHADOW(addr);

  int i, j = 0;
  for (i = 0; i < size; i++) {
    sec_buf[0] = '\0';
    printbyte(prim_shadow[i], prim_buf, sizeof(prim_buf));
    if (IS_LONG_BLOCK(size) && (i % LONG_BLOCK) == 0) {
      j += 2;
      if (i < LONG_BLOCK_BOUNDARY(size)) {
        rtl_snprintf(sec_buf, sizeof(sec_buf), " %a  SZ{%u} OF{%u}",
                     &sec_shadow[j], sec_shadow[j - 2], sec_shadow[j - 1]);
      }
      if (i) {
        DLOG("---------------------------------------------\n");
      }
    }
    DLOG("| [%2d] %a | %s || %s\n", i, &prim_shadow[i], prim_buf, sec_buf);
  }
#  ifdef E_ACSL_TEMPORAL /* {{{ */
  uint32_t *origin_shadow = (uint32_t *)TEMPORAL_PRIMARY_STATIC_SHADOW(addr);
  uint32_t *ref_shadow = (uint32_t *)TEMPORAL_SECONDARY_STATIC_SHADOW(addr);
  DLOG(" | > Blk ID: %u\n", i, *origin_shadow);
  for (i = 0; i < size; i += PTR_SZ)
    DLOG(" | >   Ref ID[%u]: %u\n", i / 8, *(ref_shadow + 1));
#  endif /*}}} E_ACSL_TEMPORAL*/
}

void print_heap_shadows(uintptr_t addr) {
  unsigned char *block_shadow = (unsigned char *)HEAP_SHADOW(addr);
  unsigned char *init_shadow = (unsigned char *)HEAP_INIT_SHADOW(addr);

  size_t length = (size_t)((uintptr_t *)(block_shadow))[1];
  size_t alloc_size = ALLOC_SIZE(length);
  size_t segments = alloc_size / HEAP_SEGMENT;
  uintptr_t *segment = (uintptr_t *)(block_shadow);

  DLOG(" | === Block Shadow ======================================\n");
  DLOG(" | Access addr:    %a\n", addr);
  DLOG(" | Block Shadow:   %a\n", block_shadow);
  DLOG(" | Init	 Shadow:   %a\n", init_shadow);
  DLOG(" | Segments:       %lu\n", segments);
  DLOG(" | Actual size:    %lu bytes\n", alloc_size);
  DLOG(" | Tracked Length: %lu bytes\n", length);

  if (zeroed_out(block_shadow, alloc_size))
    DLOG(" | << Nullified >>  \n");

#  ifdef E_ACSL_TEMPORAL /*{{{*/
  DLOG(" | Origin TS:       %u\n", (uint32_t)segment[2]);
#  endif /*}}}*/

  size_t i;
  for (i = 0; i < segments; i++) {
    segment = (uintptr_t *)(block_shadow + i * HEAP_SEGMENT);
    DLOG(" |   Segment: %lu, Base: %a \n", i, *segment);
  }

  DLOG(" | Initialization: \n |   ");
  for (i = 0; i < alloc_size / 8; i++) {
    if (i > 0 && (i * 8) % HEAP_SEGMENT == 0)
      DLOG("\n |   ");
    DLOG("%8b ", init_shadow[i], init_shadow[i]);
  }
  DLOG("\n");
}

void print_shadows(uintptr_t addr, size_t size) {
  RTL_IO_LOCK();
  if (IS_ON_STATIC(addr))
    print_static_shadows(addr, size);
  else if (IS_ON_HEAP(addr))
    print_heap_shadows(addr);
  RTL_IO_UNLOCK();
}

void print_memory_segment(struct memory_segment *p, char *lab, int off) {
#  ifdef E_ACSL_DEBUG
  const char *unit = "MB";
  size_t size = MB_SZ(p->size);
  if (size == 0) {
    unit = "kB";
    size = KB_SZ(p->size);
  }
  if (size == 0) {
    unit = "B";
    size = p->size;
  }
  DLOG("   %s: %lu %s [%a, %a]", lab, size, unit, p->start, p->end);
#  endif
  if (off)
    DLOG("{ Offset: %ld }", p->shadow_offset);
  DLOG("\n");
}

void print_memory_partition(struct memory_partition *p) {
  print_memory_segment(&p->application, "Application", 0);
  print_memory_segment(&p->primary, "Primary    ", 1);
  print_memory_segment(&p->secondary, "Secondary  ", 1);
#  ifdef E_ACSL_TEMPORAL
  print_memory_segment(&p->temporal_primary, "Temporal Primary    ", 1);
  print_memory_segment(&p->temporal_secondary, "Temporal Secondary  ", 1);
#  endif
}

#  if E_ACSL_OS_IS_LINUX
/*! \brief Print the content of the `/proc/self/maps` file that is used to
    retrieve the addresses informations of some segments. */
static void print_all_segments() {
  FILE *maps = fopen("/proc/self/maps", "r");
  DVASSERT(maps != NULL, "Unable to open /proc/self/maps: %s\n",
           rtl_strerror(errno));

  int result;
  char buffer[255];
  uintptr_t start, end;
  while (fgets(buffer, sizeof(buffer), maps) != NULL) {
    result = sscanf(buffer, "%" SCNxPTR "-%" SCNxPTR, &start, &end);
    if (result == 2) {
      char *remaining = strchr(buffer, ' ');
      DLOG("%a - %a %s", start, end, remaining ? remaining : buffer);
    } else {
      DLOG("%s", buffer);
    }
  }

  result = fclose(maps);
  DVASSERT(result == 0, "Unable to close /proc/self/maps: %s\n",
           rtl_strerror(errno));
}
#  endif

void print_shadow_layout() {
  RTL_IO_LOCK();
  DLOG(">>> HEAP ---------------------\n");
  print_memory_partition(&mem_layout.heap);
  DLOG(">>> STACK --------------------\n");
  print_memory_partition(&mem_layout.stack);
#  if E_ACSL_OS_IS_LINUX
  DLOG(">>> GLOBAL -------------------\n");
  print_memory_partition(&mem_layout.global);
  DLOG(">>> TLS ----------------------\n");
  print_memory_partition(&mem_layout.tls);
  DLOG(">>> VDSO ---------------------\n");
  print_memory_partition(&mem_layout.vdso);
  // DLOG(">>> /proc/self/maps ----------\n");
  // print_all_segments();
#  elif E_ACSL_OS_IS_WINDOWS
  DLOG(">>> TEXT ---------------------\n");
  print_memory_partition(&mem_layout.text);
  DLOG(">>> BSS ----------------------\n");
  print_memory_partition(&mem_layout.bss);
  DLOG(">>> DATA --------------------\n");
  print_memory_partition(&mem_layout.data);
  DLOG(">>> IDATA --------------------\n");
  print_memory_partition(&mem_layout.idata);
  DLOG(">>> RDATA --------------------\n");
  print_memory_partition(&mem_layout.rdata);
#  endif
  DLOG(">>> --------------------------\n");
  RTL_IO_UNLOCK();
}

const char *which_segment(uintptr_t addr) {
  const char *loc = NULL;
  if (IS_ON_STACK(addr))
    loc = "stack";
  else if (IS_ON_HEAP(addr))
    loc = "heap";
#  if E_ACSL_OS_IS_LINUX
  else if (IS_ON_GLOBAL(addr))
    loc = "global";
  else if (IS_ON_TLS(addr))
    loc = "TLS";
#  elif E_ACSL_OS_IS_WINDOWS
  else if (IS_ON_TEXT(addr))
    loc = "text";
  else if (IS_ON_BSS(addr))
    loc = "bss";
  else if (IS_ON_DATA(addr))
    loc = "data";
  else if (IS_ON_IDATA(addr))
    loc = "idata";
  else if (IS_ON_RDATA(addr))
    loc = "rdata";
#  endif
  else
    loc = "untracked";
  return loc;
}
#endif
/* }}} */
