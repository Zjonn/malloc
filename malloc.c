/*
 * Daniel Dubiel
 * 291111
 * Oświadczam, że jestem jedynym autorem.
 */
#include "malloc.h"
#include <sys/queue.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <unistd.h>
#include <pthread.h>

#define MALLOC_DEBUG 1

typedef struct mem_block mem_block_t;
typedef struct mem_arena mem_arena_t;
typedef LIST_ENTRY(mem_block) mb_node_t;
typedef LIST_ENTRY(mem_arena) ma_node_t;
typedef LIST_HEAD(, mem_block) mb_list_t;
typedef LIST_HEAD(, mem_arena) ma_list_t;

#define MB_ALIGMENT 16

#define MA_MAXSIZE (MB_ALIGMENT * 32768)
#define MA_THRESHOLD (MA_MAXSIZE / 2)

#define MB_METADATA_SIZE ((int)sizeof(struct mem_block))
#define MA_METADATA_SIZE ((int)sizeof(mem_arena_t))

#define MA_SIZE (MA_MAXSIZE + MA_METADATA_SIZE)
#define MB_SIZE (BOUNDARY_TAG_SIZE + MB_METADATA_SIZE)

#define NEG_MASK (1l << 63)
#define POS_MASK (~(1l << 63))

#define BOUNDARY_TAG_SIZE 8
#define SET_BLOCK_BT(block)                                                    \
  (*(int64_t *)((void *)(block) + ((block)->mb_size & POS_MASK)) =             \
     (block)->mb_size)
#define READ_BLOCK_BT(block)                                                   \
  (*(int64_t *)((void *)(block) + ((block)->mb_size & POS_MASK)))

#define GET_DATA_ADR(block) ((void *)&((block)->mb_data[2]))
#define GET_METADATA_ADR(data) ((void *)(data)-MB_METADATA_SIZE)
#define GET_NEXT_BLOCK_ADR(block)                                              \
  ((void *)(block) + ((block)->mb_size & POS_MASK) + BOUNDARY_TAG_SIZE)

#define MARK_USED(block) ((block)->mb_size |= NEG_MASK)
#define MARK_UNUSED(block) ((block)->mb_size &= POS_MASK)

#define IS_PTR_IN_AREA(ptr, arena)                                             \
  ((void *)(arena) > (ptr) && (ptr) < (void *)(arena) + (arena)->size)

#define IS_SPACE_WITH_ALIGN(block, size, align)                                \
  (len >= MB_SIZE && block->mb_size >= len + (int64_t)size + MB_SIZE)

#define IS_SPACE_NO_ALIGN(block, size, align)                                  \
  (len == 0 && block->mb_size > (int64_t)size)

#define VALID_SIZE(size, err_return, cond)                                     \
  do {                                                                         \
    if (cond size >> 63) {                                                     \
      errno = ((size) >> 63) ? ENOMEM : 0;                                     \
      return (err_return);                                                     \
    }                                                                          \
  } while (0)

#define VALID_ALIGN(x, err_return)                                             \
  do {                                                                         \
    if ((x) >> 63) {                                                           \
      errno = EINVAL;                                                          \
      return (err_return);                                                     \
    }                                                                          \
  } while (0)

#define align_len(x, y) (align((x), (y)) - (x))

struct mem_block {
  int64_t mb_size; /* mb_size > 0 => free, mb_size < 0 => allocated */
  union {
    mb_node_t mb_link;   /* link on free block list, valid if block is free */
    uint64_t mb_data[0]; /* user data pointer, valid if block is allocated */
  };
};

struct mem_arena {
  ma_node_t ma_link;     /* link on list of all arenas */
  mb_list_t ma_freeblks; /* list of all free blocks in the arena */
  int64_t size;          /* arena size minus sizeof(mem_arena_t) */
  mem_block_t ma_first;  /* first block in the arena */
};

static ma_list_t *arenas __used = &(ma_list_t){}; /* list of all arenas */
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static mem_block_t *find_free_block(size_t size, size_t alignment);
static mem_block_t *prepare_arena();
static void *allocate_block(mem_block_t *block, size_t size, size_t alignment);

static mem_arena_t *get_ptr_arena(void *ptr);
static mem_block_t *get_pointed_block_mdata(void *ptr, mem_arena_t *arena);
static mem_block_t *find_free_block_before(mem_block_t *block,
                                           mem_arena_t *arena);
static mem_block_t *get_prev_block_mdata(mem_block_t *block,
                                         mem_arena_t *arena);
static mem_block_t *get_next_block_mdata(mem_block_t *block,
                                         mem_arena_t *arena);

static void print_arenas();

/* This procedure is called before any allocation happens. */
__constructor void __malloc_init(void) {
  __malloc_debug_init();
  LIST_INIT(arenas);
}

void *__my_malloc(size_t size) {
  debug("%s(%ld)", __func__, size);
  VALID_SIZE(size, NULL, (size) == 0 ||);

  pthread_mutex_lock(&mutex);

  mem_block_t *free_block = NULL;
  if (size < MA_MAXSIZE) {
    free_block = find_free_block(size, MB_ALIGMENT);
  }

  if (free_block == NULL) {
    if ((free_block = prepare_arena()) == NULL) {
      pthread_mutex_unlock(&mutex);
      return NULL;
    }
  }
  mem_block_t *alloc_block = allocate_block(free_block, size, MB_ALIGMENT);

  pthread_mutex_unlock(&mutex);
  return GET_DATA_ADR(alloc_block);
}

void __my_free(void *ptr) {
  debug("%s(%p)", __func__, ptr);
  pthread_mutex_lock(&mutex);

  mem_arena_t *arena;
  if (ptr == NULL || (arena = get_ptr_arena(ptr)) == NULL) {
    pthread_mutex_unlock(&mutex);
    return;
  }
  mem_block_t *pointed_block_mdata = get_pointed_block_mdata(ptr, arena);
  if (pointed_block_mdata == NULL || pointed_block_mdata->mb_size > 0) {
    pthread_mutex_unlock(&mutex);
    return;
  }

  mem_block_t *prev_block_mdata =
    get_prev_block_mdata(pointed_block_mdata, arena);
  mem_block_t *next_block_mdata =
    get_next_block_mdata(pointed_block_mdata, arena);

  pointed_block_mdata->mb_size = -pointed_block_mdata->mb_size;
  SET_BLOCK_BT(pointed_block_mdata);

  if (next_block_mdata && next_block_mdata->mb_size > 0) {
    pointed_block_mdata->mb_size +=
      next_block_mdata->mb_size + BOUNDARY_TAG_SIZE + MB_METADATA_SIZE;
    SET_BLOCK_BT(pointed_block_mdata);
  }

  if (!prev_block_mdata) {
    LIST_INSERT_HEAD(&(arena->ma_freeblks), pointed_block_mdata, mb_link);
    pthread_mutex_unlock(&mutex);
    return;
  } else if (prev_block_mdata->mb_size > 0) {
    prev_block_mdata->mb_size +=
      pointed_block_mdata->mb_size + BOUNDARY_TAG_SIZE + MB_METADATA_SIZE;
    SET_BLOCK_BT(prev_block_mdata);
  } else if (next_block_mdata->mb_size > 0) {
    LIST_INSERT_BEFORE(next_block_mdata, pointed_block_mdata, mb_link);
  } else {
    mem_block_t *block = find_free_block_before(pointed_block_mdata, arena);
    if (block) {
      LIST_INSERT_AFTER(block, pointed_block_mdata, mb_link);
    } else {
      LIST_INSERT_HEAD(&(arena->ma_freeblks), pointed_block_mdata, mb_link);
    }
  }

  if (next_block_mdata && next_block_mdata->mb_size > 0) {
    LIST_REMOVE(next_block_mdata, mb_link);
  }

  pthread_mutex_unlock(&mutex);
}

static mem_arena_t *get_ptr_arena(void *ptr) {
  mem_arena_t *arena;

  LIST_FOREACH(arena, arenas, ma_link) {
    if (IS_PTR_IN_AREA(ptr, arena)) {
      return arena;
    }
  }
  return NULL;
}

static mem_block_t *get_pointed_block_mdata(void *ptr, mem_arena_t *arena) {
  mem_block_t *potential_block = ptr - MB_METADATA_SIZE;
  if ((void *)potential_block + potential_block->mb_size <
        (void *)arena + arena->size &&
      READ_BLOCK_BT(potential_block) == potential_block->mb_size) {
    return potential_block;
  }
  return NULL;
}

static mem_block_t *find_free_block_before(mem_block_t *block,
                                           mem_arena_t *arena) {
  mem_block_t *prev_block = get_prev_block_mdata(block, arena);
  while (prev_block) {
    if (prev_block->mb_size > 0) {
      return prev_block;
    }
    prev_block = get_prev_block_mdata(prev_block, arena);
  }
  return NULL;
}

static mem_block_t *get_prev_block_mdata(mem_block_t *block,
                                         mem_arena_t *arena) {

  mem_block_t *prev_block_mdata =
    (void *)block - (*((int64_t *)block - BOUNDARY_TAG_SIZE) +
                     BOUNDARY_TAG_SIZE + MB_METADATA_SIZE);
  if (prev_block_mdata < &(arena->ma_first)) {
    return NULL;
  }
  return prev_block_mdata;
}

static mem_block_t *get_next_block_mdata(mem_block_t *block,
                                         mem_arena_t *arena) {
  mem_block_t *next_block_mdata =
    (void *)block + block->mb_size + MB_METADATA_SIZE + BOUNDARY_TAG_SIZE;
    
  if ((void *)next_block_mdata >=
      ((void *)arena + arena->size + MA_METADATA_SIZE)) {
    return NULL;
  }
  return next_block_mdata;
}

void *__my_realloc(void *ptr, size_t size) {
  debug("%s(%p, %ld)", __func__, ptr, size);
  if (ptr == NULL) {
    return __my_malloc(size);
  }
  if (size == 0) {
    __my_free(ptr);
    return NULL;
  }

  VALID_SIZE(size, ptr, (size) == 0 ||);
  return NULL;
}

void *__my_memalign(size_t alignment, size_t size) {
  debug("%s(%ld, %ld)", __func__, alignment, size);
  VALID_SIZE(size, NULL, );
  VALID_ALIGN(alignment, NULL);
  pthread_mutex_lock(&mutex);

  mem_block_t *free_block = NULL;
  if (size < MA_MAXSIZE) {
    free_block = find_free_block(size, alignment);
  }

  if (free_block == NULL) {
    if ((free_block = prepare_arena()) == NULL) {
      pthread_mutex_unlock(&mutex);
      return NULL;
    }
  }
  mem_block_t *alloc_block = allocate_block(free_block, size, alignment);
  pthread_mutex_unlock(&mutex);
  return GET_DATA_ADR(alloc_block);
  ;
}

size_t __my_malloc_usable_size(void *ptr) {
  debug("%s(%p)", __func__, ptr);
  pthread_mutex_lock(&mutex);

  mem_arena_t *arena;
  LIST_FOREACH(arena, arenas, ma_link) {
    if (IS_PTR_IN_AREA(ptr, arena)) {
      mem_block_t *potential_block = ptr - MB_METADATA_SIZE;
      if ((void *)potential_block + potential_block->mb_size <
            (void *)arena + arena->size &&
          READ_BLOCK_BT(potential_block) == potential_block->mb_size) {
        pthread_mutex_unlock(&mutex);
        return potential_block->mb_size;
      }
    }
  }

  errno = EFAULT;
  pthread_mutex_unlock(&mutex);
  return 0;
}

/* DO NOT remove following lines */
__strong_alias(__my_free, cfree);
__strong_alias(__my_free, free);
__strong_alias(__my_malloc, malloc);
__strong_alias(__my_malloc_usable_size, malloc_usable_size);
__strong_alias(__my_memalign, aligned_alloc);
__strong_alias(__my_memalign, memalign);
__strong_alias(__my_realloc, realloc);

static mem_block_t *find_free_block(size_t size, size_t alignment) {
  mem_arena_t *arena;
  mem_block_t *block;

  LIST_FOREACH(arena, arenas, ma_link) {
    LIST_FOREACH(block, &(arena->ma_freeblks), mb_link) {
      if (block->mb_size < MB_SIZE) {
        return NULL;
      }

      mem_block_t *algined =
        GET_METADATA_ADR(align(GET_DATA_ADR(block), alignment));
      int64_t len = (void *)algined - (void *)block;

      return (IS_SPACE_WITH_ALIGN(block, size, alignment) ||
              IS_SPACE_NO_ALIGN(block, size, alignment))
               ? block
               : NULL;

      if (len < MB_SIZE) {
        algined =
          GET_METADATA_ADR(align(GET_DATA_ADR(block) + MB_SIZE, alignment));
        len = (void *)algined - (void *)block;
        return (block->mb_size >= len + (int64_t)size + MB_SIZE) ? block : NULL;
      }
    }
  }
  return NULL;
}

static mem_block_t *prepare_arena() {
  mem_arena_t *arena = mmap(NULL, MA_MAXSIZE, PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (arena == MAP_FAILED) {
    return NULL;
  }

  arena->size = MA_SIZE;
  arena->ma_first.mb_size = MA_MAXSIZE - MA_METADATA_SIZE - BOUNDARY_TAG_SIZE;

  SET_BLOCK_BT(&(arena->ma_first));

  LIST_INIT(&(arena->ma_freeblks));
  LIST_INSERT_HEAD(&(arena->ma_freeblks), &(arena->ma_first), mb_link);
  LIST_INSERT_HEAD(arenas, arena, ma_link);

  return &(arena->ma_first);
}

static void *allocate_block(mem_block_t *block, size_t size, size_t alignment) {
  mem_block_t *new_data_block =
    GET_METADATA_ADR(align(GET_DATA_ADR(block), alignment));

  if (block != new_data_block) {
    new_data_block =
      ((void *)block + MB_SIZE > (void *)new_data_block)
        ? GET_METADATA_ADR(align(GET_DATA_ADR(block) + MB_SIZE, alignment))
        : new_data_block;

    new_data_block->mb_size = block->mb_size -
                              ((void *)new_data_block - (void *)block) -
                              BOUNDARY_TAG_SIZE;
  }

  // Determine adress of rigth side of the block
  if (new_data_block->mb_size + MB_SIZE >= (int64_t)size) {
    new_data_block->mb_size = size;

    mem_block_t *right_free_block = GET_NEXT_BLOCK_ADR(new_data_block);

    right_free_block->mb_size =
      block->mb_size - (new_data_block->mb_size + MB_SIZE) - (MB_SIZE);
    LIST_INSERT_AFTER(block, right_free_block, mb_link);

    block->mb_size =
      (block == new_data_block)
        ? 0
        : (void *)new_data_block - GET_DATA_ADR(block) - BOUNDARY_TAG_SIZE;

    SET_BLOCK_BT(right_free_block);
  }

  if (block == new_data_block) {
    LIST_REMOVE(block, mb_link);
    MARK_USED(block);
  }

  MARK_USED(new_data_block);
  SET_BLOCK_BT(new_data_block);

  SET_BLOCK_BT(block);

  return new_data_block;
}

static void __used print_arenas() {
  mem_arena_t *arena;
  mem_block_t *block;

  LIST_FOREACH(arena, arenas, ma_link) {
    debug("%p %p Blocks:", arena, arena->ma_link.le_next);
    LIST_FOREACH(block, &(arena->ma_freeblks), mb_link) {
      debug(" %p", block);
      debug(" %p  size: 0x%lx is_claimed: %ld", block,
            block->mb_size & POS_MASK, block->mb_size & NEG_MASK);
    }
  }
}
