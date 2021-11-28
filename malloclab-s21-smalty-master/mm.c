/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * This implementation of the malloc lab is an explicit implementation.
 * The method of find_fit is first fit, and the free list is doubly linked
 * null terminated. Headers and footers are 8 bytes, and currently allocated
 * blocks still have footers. The method of insertion in free list is LIFO.
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Edric Eun <eeun@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

static const size_t large_size_index = 8;
/**
 * TODO: Minimum initial heap size (bytes)
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: Mask used to extract allocate or free bit from header
 */
static const word_t alloc_mask = 0x1;

static const word_t prev_mask = 0x2;

static const word_t mini_mask = 0x4;

/**
 * TODO: Mask used to extract size from header
 */
static const word_t size_mask = ~(word_t)0xF;

static const size_t bckt = 14;

static const size_t max_small_size = 7 * dsize + min_block_size;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    union {
        struct {
            struct block *next;
            struct block *prev;
        };
        char payload[0];
    };
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/* 0:16, 1:32, 2:48, 3:64, 4:80, 5:96, 6:112, 7: 128, 8:129-256,
 * 9:257-512, 10:513-1024, 11:1025-2048, 12:2049-4096, 13:4097-inf*/
static block_t *roots[bckt];

static block_t *heap_end = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev, bool mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev) {
        word |= prev_mask;
    }
    if (mini) {
        word |= mini_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

static bool extract_prev(word_t word) {
    return (bool)((word & prev_mask) >> 1);
}

static bool get_prev(block_t *block) {
    return extract_prev(block->header);
}

static bool extract_mini(word_t word) {
    return (bool)((word & mini_mask) >> 2);
}

static bool get_mini(block_t *block) {
    return extract_mini(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block, bool mini) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, false, mini);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

static block_t *find_prev_mini(block_t *block) {
    dbg_requires(block != NULL);
    return (block_t *)((char *)block - min_block_size);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Size must be positive, the location of the block must be double-word
 * aligned.
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool mini) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc, prev_alloc, mini);
    if (!(alloc) && (size != min_block_size)) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prev_alloc, mini);
    }
}

static size_t findIndex(size_t free_size) {
    if (free_size >= min_block_size && free_size <= max_small_size) {
        return ((free_size - min_block_size) / dsize);
    } else {
        size_t i;
        size_t lower = max_small_size + 1;
        size_t upper = max_small_size * 2;
        for (i = large_size_index; i < bckt - 1; i++) {
            if (lower <= free_size && free_size <= upper &&
                free_size <= chunksize) {
                return i;
            }
            lower = (lower - 1) * 2 + 1;
            upper = upper * 2;
        }
        return bckt - 1;
    }
}

static void addBlock(block_t *block) {
    dbg_requires(!(get_alloc(block)));
    size_t block_size = get_size(block);
    size_t i = findIndex(block_size);
    if (i != 0) {
        if (roots[i] != NULL) {
            block->next = roots[i];
            roots[i]->prev = block;
            block->prev = NULL;
        } else {
            block->next = NULL;
            block->prev = NULL;
        }
        roots[i] = block;
    } else {
        block->next = roots[i];
        roots[i] = block;
    }
}

static void removeBlock(block_t *block) {
    block_t *block_next = block->next;
    size_t block_size = get_size(block);
    size_t i = findIndex(block_size);
    if (i != 0) {
        block_t *block_prev = block->prev;
        if (block != roots[i]) {
            if (block_next != NULL) {
                block_next->prev = block_prev;
            }
            block_prev->next = block_next;
        } else {
            if (block_next != NULL) {
                block->next = NULL;
                block_next->prev = NULL;
                roots[i] = block_next;
            } else {
                roots[i] = NULL;
            }
        }
    } else {
        block_t *block_prev = NULL;
        block_t *block_cur = roots[i];
        while (block_cur != NULL && block_cur != block) {
            block_prev = block_cur;
            block_cur = block_cur->next;
        }
        if (block_cur == NULL) {
            return;
        }
        if (block_cur == roots[i]) {
            roots[i] = block_cur->next;
            block_cur->next = NULL;
        } else {
            block_prev->next = block_cur->next;
        }
    }
}

bool is_acyclic(block_t *start) {
    if (start == NULL)
        return true;
    block_t *h = start->next;
    block_t *t = start;
    while (h != t) {
        if (h == NULL || h->next == NULL)
            return true;
        h = h->next->next;
        t = t->next;
    }
    return false;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * Coalesces free blocks together if there are any free blocks next to
 * given block.
 *
 * The input is the freed block that must now look to coalesce with surrounding
 * blocks. Returns the coalesced free block starting at the location of the
 * header. The input block must be freed.
 *
 * @param[in] block A freed block on the heap
 * @return The resulting coalesced block on the heap
 */
static block_t *coalesce_block(block_t *block) {
    // Requires input block to be freed
    dbg_requires(!get_alloc(block));

    // Find previous and next blocks
    block_t *block_next;
    block_next = find_next(block);

    size_t block_next_size = get_size(block_next);
    size_t block_size = get_size(block);
    size_t asize;

    // Case only previous is freed
    if (!(get_prev(block)) && get_alloc(block_next)) {
        block_t *block_prev;
        if (!(get_mini(block))) {
            block_prev = find_prev(block);
        }
        if (get_mini(block)) {
            block_prev = find_prev_mini(block);
        }
        size_t block_prev_size = get_size(block_prev);
        asize = block_prev_size + block_size;

        removeBlock(block_prev);

        write_block(block_prev, asize, false, get_prev(block_prev),
                    get_mini(block_prev));
        if (block == heap_end) {
            heap_end = block_prev;
        }
        if (get_mini(block_next)) {
            block_next->header =
                pack(get_size(block_next), get_alloc(block_next), false, false);
            if (!(get_alloc(block_next)) &&
                (get_size(block_next) != min_block_size)) {
                word_t *footer = header_to_footer(block_next);
                *footer = pack(get_size(block_next), get_alloc(block_next),
                               false, false);
            }
        }
        return block_prev;
    }
    // Case only next is freed
    if (get_prev(block) && !(get_alloc(block_next))) {
        asize = block_size + block_next_size;
        removeBlock(block_next);

        write_block(block, asize, false, true, get_mini(block));
        if (block_next == heap_end) {
            heap_end = block;
        }
        if (block_next_size == min_block_size) {
            block_t *block_next_next = find_next(block);
            block_next_next->header =
                pack(get_size(block_next_next), get_alloc(block_next_next),
                     false, false);
            if (!(get_alloc(block_next_next)) &&
                (get_size(block_next_next) != min_block_size)) {
                word_t *footer = header_to_footer(block_next_next);
                *footer = pack(get_size(block_next_next),
                               get_alloc(block_next_next), false, false);
            }
        }
        return block;
    }
    // Case both are freed
    if (!(get_prev(block)) && !(get_alloc(block_next))) {
        block_t *block_prev;
        if (!(get_mini(block))) {
            block_prev = find_prev(block);
        }
        if (get_mini(block)) {
            block_prev = find_prev_mini(block);
        }
        size_t block_prev_size = get_size(block_prev);
        asize = block_prev_size + block_size + block_next_size;
        removeBlock(block_prev);
        removeBlock(block_next);

        write_block(block_prev, asize, false, get_prev(block_prev),
                    get_mini(block_prev));
        if (block_next == heap_end) {
            heap_end = block_prev;
        }
        if (block_next_size == min_block_size) {
            block_t *block_next_next = find_next(block_prev);
            block_next_next->header =
                pack(get_size(block_next_next), get_alloc(block_next_next),
                     false, false);
            if (!(get_alloc(block_next_next)) &&
                (get_size(block_next_next) != min_block_size)) {
                word_t *footer = header_to_footer(block_next_next);
                *footer = pack(get_size(block_next_next),
                               get_alloc(block_next_next), false, false);
            }
        }
        return block_prev;
    }
    // Case none are freed
    return block;
}

/**
 * @brief
 *
 * This function extends the heap if no free blocks were found when needed.
 *
 * The input is the number of bytes to extend the heap. The function also
 * initializes the blocks in the extended heap and returns the first block.
 *
 *
 * @param[in] size The size that the heap extends by
 * @return The first block in the extended part of the heap
 */
static block_t *extend_heap(size_t size) {
    void *bp;
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    bool is_end_mini = (get_size(heap_end) == min_block_size);

    write_block(block, size, false, get_alloc(heap_end), is_end_mini);

    // Create new epilogue header
    bool mini = (size == min_block_size);
    block_t *block_next = find_next(block);
    write_epilogue(block_next, mini);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    heap_end = block;
    addBlock(block);

    return block;
}

/**
 * @brief
 *
 * Splits given block into two with different sizes. Takes in the block
 * needed to be split and the size of the first block of the split. Does not
 * return anything. The size of the first block must be at least minimum
 * block size, and the block must be allocated before and after the split.
 *
 *
 * @param[in] block The block in the heap needed to be split
 * @param[in] asize The size of the first block after split
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true, get_prev(block), get_mini(block));

        block_next = find_next(block);
        bool is_mini = (asize == min_block_size);

        write_block(block_next, block_size - asize, false, true, is_mini);

        block_t *block_next_next = find_next(block_next);

        bool is_next_mini = (block_size - asize == min_block_size);
        block_next_next->header =
            pack(get_size(block_next_next), get_alloc(block_next_next), false,
                 is_next_mini);

        if (!(get_alloc(block_next_next)) &&
            (get_size(block_next_next) != min_block_size)) {
            word_t *footer = header_to_footer(block_next_next);
            *footer = pack(get_size(block_next_next),
                           get_alloc(block_next_next), false, is_next_mini);
        }
        if (block == heap_end) {
            heap_end = block_next;
        }
        addBlock(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * Finds free block that is at least the size inputted. Minimum size of the free
 * block is inputted, and if a free block is found, returns the block. Otherwise
 * NULL is returned.
 *
 * @param[in] asize Minimum size of the free block needed.
 * @return Free block if found, otherwise NULL
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    size_t index = findIndex(asize);
    for (size_t i = index; i < bckt; i++) {
        for (block = roots[i]; block != NULL; block = block->next) {
            if (!(get_alloc(block)) && asize <= get_size(block)) {
                return block;
            }
        }
    }
    return NULL; // no fit found
}

/**
 * @brief
 *
 * Checks the heap to ensure it follows heap rules. Takes in line where it was
 * called, but may be called with argument 0. Prints out the line when called
 * for debugging purposes. Returns true if heap is good, otherwise false.
 *
 * @param[in] line The line number where function is called.
 * @return True if heap follows rules, otherwise false.
 */
bool mm_checkheap(int line) {
    printf("Checking heap in line %d... \n", line);
    word_t *prologue = find_prev_footer(heap_start);
    block_t *epilogue = (block_t *)((char *)(mem_heap_hi()) - 7);
    if (!(extract_alloc(*prologue)) || !(get_alloc(epilogue))) {
        printf("prologue not equal to epilogue");
        return false;
    }
    if (extract_size(*prologue) != 0 || get_size(epilogue) != 0) {
        printf("prologue not equal to epilogue");
        return false;
    }
    if (get_alloc(heap_end) != get_prev(epilogue)) {
        printf("Epilogue prev bit is not correct");
        return false;
    }
    block_t *block;
    block_t *fblock;
    word_t *headerp;
    word_t *footerp;
    size_t fblockCount = 0;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        block_t *block_next = find_next(block);
        headerp = (word_t *)(block);
        footerp = header_to_footer(block);
        if (!(get_alloc(block))) {
            fblockCount += 1;
        }
        if (get_alloc(block) != get_prev(block_next)) {
            printf("Prev alloc is not correct \n");
            return false;
        }
        if (((size_t)(block)&0xF) != 8) {
            printf("Incorrect alignment \n");
            return false;
        }
        if ((size_t)(block) < (size_t)(heap_start) ||
            (size_t)(block) + get_size(block) > (size_t)(epilogue)) {
            printf("Lies outside boundary \n");
            return false;
        }
        if (get_size(block) < min_block_size) {
            printf("Block size too small");
            return false;
        }
        if (get_size(block) % min_block_size != 0) {
            printf("Block size not multiple of 16");
            return false;
        }
        if (extract_size(*headerp) != extract_size(*footerp)) {
            printf("Header size and footer size are not the same");
            return false;
        }
        if (extract_alloc(*headerp) != extract_alloc(*footerp)) {
            printf("Header alloc and footer alloc are not the same");
            return false;
        }
        if (!(get_alloc(block)) && !(get_alloc(find_next(block)))) {
            printf("Failed coalesce");
            return false;
        }
    }
    size_t fblockList = 0;
    size_t i;
    for (i = 0; i < bckt; i++) {
        for (fblock = roots[i]; fblock != NULL; fblock = fblock->next) {
            fblockList += 1;
            if ((fblock->next != NULL && fblock->next->prev != fblock) ||
                (fblock->prev != NULL && fblock->prev->next != fblock)) {
                printf("Failed pointers");
                return false;
            }
            if (fblock->prev != NULL) {
                if ((size_t)(fblock->prev) < (size_t)(mem_heap_lo()) ||
                    (size_t)(fblock->prev) > (size_t)(mem_heap_hi())) {
                    printf("Prev pointer not in bounds \n");
                    printf("fblock: %ld, fblock->prev: %ld", (size_t)(fblock),
                           (size_t)(fblock->prev));
                    return false;
                }
            }
            if (fblock->next != NULL) {
                if ((size_t)(fblock->next) < (size_t)(mem_heap_lo()) ||
                    (size_t)(fblock->next) > (size_t)(mem_heap_hi())) {
                    printf("Next pointer not in bounds");
                    return false;
                }
            }
            if (findIndex(get_size(fblock)) != i) {
                printf("Incorrect bucket");
                return false;
            }
        }
        if (!is_acyclic(roots[i])) {
            printf("Free list is cyclic");
            return false;
        }
    }
    if (fblockList != fblockCount) {
        printf("Incorrect number of free blocks in circular list");
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * Initializes the heap. Takes no arguments, and returns true if successful,
 * otherwise false.
 *
 * @return True if initialize is successful, false otherwise.
 */
bool mm_init(void) {
    // Create the initial empty heap

    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    heap_end = (block_t *)&(start[1]);

    for (size_t i = 0; i < bckt; i++) {
        roots[i] = NULL;
    }
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * Allocates block with size of payload. Calls find_fit and allocates block
 * within heap. If no free block is found, extends the heap by extendsize.
 * Returns address of the block if allocation is successful, otherwise NULL.
 * Heap must be good before and after allocation.
 *
 * @param[in] size Size of payload
 * @return Address of allocated block if successful, otherwise NULL.
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);

    removeBlock(block);

    write_block(block, block_size, true, get_prev(block), get_mini(block));

    block_t *block_next = find_next(block);
    block_next->header = pack(get_size(block_next), get_alloc(block_next), true,
                              get_mini(block_next));
    if (!(get_alloc(block_next)) && (get_size(block_next) != min_block_size)) {
        word_t *footer = header_to_footer(block_next);
        *footer = pack(get_size(block_next), get_alloc(block_next), true,
                       get_mini(block_next));
    }

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * Frees an allocated block and coalesces. Takes in the address of the allocated
 * block and frees it. The heap must be good before and after free, and the
 * block inputted must be allocated.
 *
 * @param[in] bp The address of the allocated block to be freed.
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, get_prev(block), get_mini(block));

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    (find_next(block))->header =
        pack(get_size(find_next(block)), get_alloc(find_next(block)), false,
             get_mini(find_next(block)));
    if (!(get_alloc(find_next(block))) &&
        (get_size(find_next(block)) != min_block_size)) {
        word_t *footer = header_to_footer(find_next(block));
        *footer = pack(get_size(find_next(block)), get_alloc(find_next(block)),
                       false, get_mini(find_next(block)));
    }

    addBlock(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * If ptr is NULL, this is equivalent to malloc(size). If size is 0, then
 * this is equivalent to free(ptr). Otherwise, the function frees and mallocs
 * with new size, and the contents of the memory are the same as the previous
 * pointer.
 *
 * @param[in] ptr Address of block
 * @param[in] size New size to resize to
 * @return Address of new block, NULL if freed
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * Allocates memory of size by number of elements times, and intializes memory
 * as 0. Takes in number of elements and the size of each element. Returns
 * NULL if unsuccessful, otherwise address of block.
 *
 * @param[in] elements Number of elements
 * @param[in] size Size of each element
 * @return Address of block if successful, otherwise NULL
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
