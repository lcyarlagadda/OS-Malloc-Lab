/*
 *
 * Name: Chandrika(lvy5215)
 * Course: Operating Systems (CMPSC 473)
 * Implementation of memory management functions (malloc, free, realloc) and the required helper functions.
 *
Design:
----------------
The memory block starts with 8 bytes of padding, followed by 12 segmented list header blocks. These headers are then followed by a prologue header, a prologue footer, and an epilogue header, each occupying 8 bytes.

When a malloc request is made and there is insufficient space, the heap is extended by at least 4096 bytes by default. Blocks are immediately coalesced with neighboring blocks before the completion of malloc, free, or realloc operations. Each unallocated block has a header and footer of about 8 bytes each, which track the block size and allocation information.

To better utilize space, the footer is used for allocation when a block is allocated. This means we cannot move to previous blocks directly, so we store the previous block's allocation information in the current block's header.

All blocks are 16-byte aligned, providing 4 zero bits at the end of each header/footer to track the allocation status.
For header:
03 - Prev block allocated and current block allocated
02 - Prev block allocated and current block not allocated
01 - Prev block not allocated and current block allocated
00 - Prev block not allocated and current block not allocated
For footer:
01 - Current block allocated
00 - Current block not allocated

Initially, used an implicit free list, then moved to an explicit one. Now we are using 12 explicit free lists. The first list can accommodate 16 bytes of data, while the highest list can handle 65,536 bytes or more. Despite experimenting with the number and size of free lists, no significant difference in utilization or throughput was observed.

Each free list is maintained as a circular doubly linked list to track blocks of different sizes, with free blocks added to the end of the list and utilized in a FIFO manner.

To optimize space utilization, a best-3-fit strategy is used when searching for a block. The search begins with the lowest free list that can accommodate the block. If a suitable block is found, the smallest of the first three free blocks that can accommodate the request is chosen. If no suitable block is found in the current list, the search moves to the next segment list with slightly larger buckets. This design ensures efficient memory management, minimizing fragmentation, and improving memory utilization.

Initially used a struct to store the size, previous, and next pointers. Instead, we opted to store the size solely in the headers and footers. This decision was made because the previous method was highly error-prone, requiring us to update the size in both the headers and footers as well as in the struct, leading to numerous bugs and unexpected behavior. Additionally, the new method is more space-efficient.

On init:
---------------------------------------
| Padding         | Seg0-prev          |
----------------------------------------
| Seg0-next       | Seg1-prev          |
----------------------------------------
| Seg1-next       | Seg2-prev          |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Seg11-next      | Prologue header    |
----------------------------------------
| Prologue footer | Epilogue header    |
----------------------------------------

On extend heap:
---------------------------------------
| Padding         | Seg0-prev          |
----------------------------------------
| Seg0-next       | Seg1-prev          |
----------------------------------------
| Seg1-next       | Seg2-prev          |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Seg11-next      | Prologue header    |
----------------------------------------
| Prologue footer | Size...........|P|A|
----------------------------------------
| Seg-list prev   |  Seg-list next    |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Size..........|A| Epilogue header    |
----------------------------------------

On malloc:
---------------------------------------
| Padding         | Seg0-prev          |
----------------------------------------
| Seg0-next       | Seg1-prev          |
----------------------------------------
| Seg1-next       | Seg2-prev          |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Seg11-next      | Prologue header    |
----------------------------------------
| Prologue footer | Size...........|P|A|
----------------------------------------
| ..........      |  ..........        |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Size..........|A| Epilogue header    |
----------------------------------------

On free:
---------------------------------------
| Padding         | Seg0-prev          |
----------------------------------------
| Seg0-next       | Seg1-prev          |
----------------------------------------
| Seg1-next       | Seg2-prev          |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Seg11-next      | Prologue header    |
----------------------------------------
| Prologue footer | Block0 header      |
----------------------------------------
| Seg-list prev    |  Seg-list next    |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| ..........      | ........           |
----------------------------------------
| Block0 footer   | Epilogue header    |
----------------------------------------

The # of seglists, default block size and best-k-fit are all configurable. To test the functionality, a heap checker is also implemeted which will check the invariants when #define debug flag is uncommented.
 *
 *
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x + ALIGNMENT - 1) / ALIGNMENT);
}

#define ALIGNMENT 16
#define WSIZE 8             // Header/Footer size
#define DSIZE 16            // Double of the word size(header, footer combined)
#define CHUNKSIZE (1 << 9)   // Minimum block size(4096)
#define BESTFIT 3           // Return the first of the 3 blocks that fits the best
#define SEGLISTS 12         // Creating 12 seg lists

// Heap pointer
static char *heap_listp = 0;
// Seg lists created
static char *free_lists[SEGLISTS];

// Get the maximum of two sizes
static size_t MAX(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

// Pack size and allocation in to a single value(as the last 4 zeroes are always empty)
static size_t PACK(size_t size, size_t alloc)
{
    return (size | alloc);
}

// Get the value at the memory location p
static size_t GET(void *p)
{
    return (*(size_t *)(p));
}

// Put the value at the memory location p
static void PUT(void *p, size_t val)
{
    (*(size_t *)(p) = (val));
}

// Get the size of the block ( including header+footer )
static size_t GET_SIZE(void *p)
{
    return GET(p) & ~0xF;
}

// Get previous block allocation flag. As previous allocation is stored at 2nd bit, masking everything except the second bit and right shifting once.
static size_t GET_PREV_ALLOC(void *p)
{
    return (GET(p) & 0x2) >> 1;
}

// Know whether a block is allocated or not (get the last bit)
static size_t GET_ALLOC(void *p)
{
    return GET(p) & 0x1;
}

// Get the header of the block
static void *HDRP(void *bp)
{
    return (char *)bp - WSIZE;
}

// Get the footer of the block -- should be used carefully, as allocated blocks do not have footer
static void *FTRP(void *bp)
{
    return (char *)bp + GET_SIZE(HDRP(bp)) - DSIZE;
}

// Get the pointer to the next block in the heap
static void *NEXT_BLKP(void *bp)
{
    return (char *)bp + GET_SIZE(((char *)bp - WSIZE));
}

// Get the pointer to the previous block in the heap
static void *PREV_BLKP(void *bp)
{
    return (char *)bp - GET_SIZE(((char *)bp - DSIZE));
}

// Stores a pointer in the specified location in the heap
static void PUT_PTR(void *p, void *ptr)
{
    (*(void **)(p) = (ptr));
}

// Retrieves a pointer from specified location in the heap
static void *GET_PTR(void *p)
{
    return (*(void **)(p));
}

// Retrieves the next block in the free list node
static char *GET_NEXT_BLOCK(void *bp)
{
    return (*(char **)((char *)bp + WSIZE));
}

// Retrieves the previous block in the free list node
static char *GET_PREV_BLOCK(void *bp)
{
    return (*(char **)(bp));
}

// Updates the next block pointer in the free list node
static void PUT_NEXT_BLOCK(void *bp, void *pb)
{
    (*(char **)((char *)bp + WSIZE)) = (char *)pb;
}

// Updates the previous block pointer in the free list node
static void PUT_PREV_BLOCK(void *bp, void *pb)
{
    (*(char **)(bp)) = (char *)pb;
}

// Inserts a block at the end of the free list, free list is picked by the index
static void INSERT_FREE_BLOCK(void *bp, int index)
{
    // First save the last block ptr
    char *last_block = GET_PREV_BLOCK(free_lists[index]);

    // Establish connection between dummy header and current block
    PUT_PREV_BLOCK(free_lists[index], bp);
    PUT_NEXT_BLOCK(bp, free_lists[index]);
    //bp:[----|header]----header:[bp|-----]

    // Establish connection between last block and current block
    PUT_PREV_BLOCK(bp, last_block);
    PUT_NEXT_BLOCK(last_block, bp);
    //last:[---|bp]----bp:[last|header]----header:[bp|-----]
}

// Removes the given block from the free list
static void REMOVE_FREE_BLOCK(void *bp)
{
    // Save the prev and next blocks before update
    char *prev_block = GET_PREV_BLOCK(bp);
    char *next_block = GET_NEXT_BLOCK(bp);

    // Attach prev-next blocks without the current block
    PUT_NEXT_BLOCK(prev_block, next_block);
    PUT_PREV_BLOCK(next_block, prev_block);
    //prev:[---|next]---next:[prev|----]
}

// Get the seglist based on the size
static int GET_SEGLIST_INDEX(size_t size)
{
    int index = 0;

    // Starting seglist with size 32
    size_t starting_size = 32;

    // Increment the seglist size by powers of 2
    while (size > starting_size && index < SEGLISTS - 1)
    {
        starting_size *= 2;
        index++;
    }

    return index;
}

/**
 * Finds a first-k-bit for a block with at least asize bytes.
 * @param asize: The size of the block to find (including header+footer )
 * @return: Returns the pointer to the block(not header but block) if allocated, NULL if no such block found.
 **/
static void *find_fit(size_t asize)
{
    void *bp = NULL;
    int nfit = BESTFIT;
    char *free_listp = NULL;
    void *best_fit = NULL;
    size_t best_fit_size = (size_t)-1;

    // Get the free list index to be checked first
    int free_list_index = GET_SEGLIST_INDEX(asize);

    while (free_list_index < SEGLISTS)
    {
        free_listp = free_lists[free_list_index++];
        // Get the next block from the dummy head
        bp = GET_NEXT_BLOCK(free_listp);
        // If the next block is equal to dummy head, then the entire list is traversed, so return
        while (bp != free_listp && nfit > 0)
        {
            void *header_block = HDRP(bp);
            int alloc_bit = GET_ALLOC(header_block);
            size_t bp_size = (size_t)GET_SIZE(header_block);

            // Check if this can be allocated
            if (asize <= bp_size && !alloc_bit)
            {
                // If this is the first block, initialize
                if (best_fit_size == (size_t)-1)
                {
                    best_fit_size = bp_size;
                    best_fit = bp;
                    nfit--;
                }
                // Check if this is the smallest block found so far, update best_fit details
                else if (bp_size <= best_fit_size)
                {
                    best_fit = bp;
                    best_fit_size = bp_size;
                    nfit--;
                }
            }

            // Move to the next free block in the list
            bp = GET_NEXT_BLOCK(bp);
        }
        // If there is atleast one free block in the list, return it
        if (best_fit_size != (size_t)-1)
        {
            return best_fit;
        }

        // If not, check for the other lists.
        nfit = BESTFIT;
    }
    return NULL;
}

/**
 * Coalesces adjacent free blocks with the given block.
 * @param bp: A pointer to the current block to be coalesced.
 * @return: A pointer to the coalesced block.
 **/

static void *coalesce(void *bp)
{
    // Get the allocation flag of the prev block, next blocks
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    // Get the allocation size of the current block
    size_t size = GET_SIZE(HDRP(bp));

    // If both are allocated, cannot coalesce, return
    if (prev_alloc && next_alloc)
    {
        // Add newly freed block
        INSERT_FREE_BLOCK(bp, GET_SEGLIST_INDEX(size));
        return bp;
    }

    // If next block is free
    else if (prev_alloc && !next_alloc)
    {
        // Add the size of the next block to the current block
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // Remove the next block in the free list
        REMOVE_FREE_BLOCK(NEXT_BLKP(bp));

        // Update the header and footer of the current block with incremented size and allocation = false
        // Prev allocation is defaulted to 2 as previous block is allocated
        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 0));

        // Add newly freed block
        INSERT_FREE_BLOCK(bp, GET_SEGLIST_INDEX(size));
    }

    // If prev block is free
    else if (!prev_alloc && next_alloc)
    {
        // Add the size of the prev block to the current block
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        // Remove the prev block in the free list
        REMOVE_FREE_BLOCK(PREV_BLKP(bp));

        // Update the footer of the current block and header of the previous block incremented size and allocation = false
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        int prev_prev_alloc = GET_PREV_ALLOC(HDRP(bp));
        // Based on the previous allocation, update the header info for the new block
        PUT(HDRP(bp), PACK(size, prev_prev_alloc == 1 ? 2 : 0));
        int index = GET_SEGLIST_INDEX(size);

        // Add newly freed block
        INSERT_FREE_BLOCK(bp, index);
    }

    // If both the blocks are free
    else
    {
        void *prev_block = PREV_BLKP(bp);
        void *next_block = NEXT_BLKP(bp);
        // Add the size of both the blocks to the current block
        size += GET_SIZE(HDRP(prev_block)) + GET_SIZE(HDRP(next_block));

        // Remove the prev and next blocks from the free list
        REMOVE_FREE_BLOCK(prev_block);
        REMOVE_FREE_BLOCK(next_block);

        // Update the header of the previous block and footer of the next block with incremented size and allocation = false
        PUT(HDRP(prev_block), PACK(size, GET_PREV_ALLOC(HDRP(prev_block)) == 1 ? 2 : 0));
        PUT(FTRP(next_block), PACK(size, 0));
        bp = prev_block;

        // Add newly freed block
        INSERT_FREE_BLOCK(bp, GET_SEGLIST_INDEX(size));
    }

    return bp;
}

/**
 * Places the block in the allocated space and updates the metadata
 * @param asize: The size requested for allocation (including header+footer)
 * @param bp: Block pointer of the current block
 * @return: Returns the pointer to the block(not header but block) if allocated, NULL if no such block found.
 **/
static void place(void *bp, size_t asize)
{
    // Get the size of the current block
    size_t csize = GET_SIZE(HDRP(bp));

    // If there is minimum size remaining after allocation, split into two blocks
    if ((csize - asize) >= (2 * DSIZE))
    {
        // Update the header and footer with requested size and allocated block =1
        PUT(HDRP(bp), PACK(asize, GET_PREV_ALLOC(HDRP(bp)) == 1 ? 3 : 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // remove this block from free list
        REMOVE_FREE_BLOCK(bp);

        // Move to the next remaining space in the current block
        bp = NEXT_BLKP(bp);
        // Update the header and footer with remaining size and allocated flags
        // Since the above block is allocated, defaulting to 2
        PUT(HDRP(bp), PACK(csize - asize, 2));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        // Update the next block header to store previous block alloc info
        void *next_bp = NEXT_BLKP(bp);
        if (next_bp != NULL)
        {
            size_t size = GET_SIZE(HDRP(next_bp));
            int next_allocation = GET_ALLOC(HDRP(next_bp));
            PUT(HDRP(next_bp), PACK(size, next_allocation == 1 ? 1 : 0));
        }

        // Coalesc if there are any empty blocks
        coalesce(bp);
    }
    // Update the header and footer with current size and allocated block =1
    else
    {
        PUT(HDRP(bp), PACK(csize, GET_PREV_ALLOC(HDRP(bp)) == 1 ? 3 : 1));
        PUT(FTRP(bp), PACK(csize, 1));

        // Remove this block from free list
        REMOVE_FREE_BLOCK(bp);

        // Update the next block header to store previous block alloc info
        void *next_bp = NEXT_BLKP(bp);
        if (next_bp != NULL)
        {
            size_t size = GET_SIZE(HDRP(next_bp));
            int next_allocation = GET_ALLOC(HDRP(next_bp));
            PUT(HDRP(next_bp), PACK(size, next_allocation == 1 ? 3 : 2));
        }
    }
}

/**
 * Extends the heap for a new free block with header, footer. Add an epilogue at the end.
 * @param words: The number of words that the heap should be extendd by.
 * @return: A pointer to the newly extended block, or NULL if the request fails.
 **/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // Making even number of words for algniment.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // Extend the heap
    if ((long)(bp = mm_sbrk(size)) == -1)
        return NULL;

    // Update free block header and footer info
    PUT(HDRP(bp), PACK(size, 2));
    PUT(FTRP(bp), PACK(size, 0));

    // New epilogue header as the heap is extended
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // Coalesce if there are any unallocated blocks
    return coalesce(bp);
}

/**
 * Sets up the initial empty heap, including creating the prologue and epilogue blocks.
 * @return: true on success, false on failure.
 **/
bool mm_init(void)
{
    int index = 0;
    int blocks = (2 * SEGLISTS);

    // reserve 4 blocks for padding, prologue header, prologue footer, epilogue header
    // Also saves space for the dummy head with free list prev and next blocks for each seg list
    if ((heap_listp = mm_sbrk((4 + blocks) * WSIZE)) == (void *)-1)
        return -1;

    // Padding
    PUT(heap_listp, 0);

    // Add free list headers here
    for (index = 0; index < SEGLISTS; index++)
    {
        free_lists[index] = heap_listp + WSIZE;
        // Adding Freelist prev
        PUT_PTR(heap_listp + (1 * WSIZE), free_lists[index]);
        // Adding Freelist next
        PUT_PTR(heap_listp + (2 * WSIZE), free_lists[index]);
        heap_listp += (2 * WSIZE);
    }
    char *initial_heap = heap_listp + WSIZE;

    // Prologue header
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
    // Prologue footer
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    // Epilogue header
    PUT(heap_listp + (3 * WSIZE), PACK(0, 3));

    // Re-initialize heap_listp to the start for heap checker
    heap_listp = initial_heap + (WSIZE);

    return true;
}

/**
 * Allocates a block of memory and returns a pointer to the start of the allocated block.
 * @param size: The size of the memory block to allocate.
 * @return: A pointer to the start of the allocated block, or NULL on failure.
 **/
void *malloc(size_t size)
{
    mm_checkheap(__LINE__);

    size_t asize;
    size_t extendsize;
    char *bp;

    // If 0 size block is requested, return NULL
    if (size == 0)
    {
        return NULL;
    }

    // If the size is less than header+footer, give atleast header+footer
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    // 16 byte alignment with requested size + header size
    else
    {
        asize = align(size + WSIZE);
    }

    // Check if there is enough space in the existing heap
    if ((bp = find_fit(asize)) != NULL)
    {
        // If yes, place the block
        place(bp, asize);
        return bp;
    }

    // If the requested size is <4096, atleast extend 4096(can be used for furture purposes)
    extendsize = MAX(asize, CHUNKSIZE);

    // Extending the heap
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }

    // If extension is successful, place the block
    place(bp, asize);

    mm_checkheap(__LINE__);

    return bp;
}

/**
 * Free a previously allocated block of memory.
 * coalesce neighboring jobs
 * @param ptr: A pointer to the block of memory to free.
 **/
void free(void *ptr)
{
    mm_checkheap(__LINE__);

    // If the ptr is null, return
    if (!ptr)
    {
        return;
    }

    // Update allocation flags in both header and footer
    size_t size = GET_SIZE(HDRP(ptr));
    int alloc = GET_PREV_ALLOC(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, alloc == 1 ? 2 : 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // Update the allocation flag of the next block header
    void *next_ptr = NEXT_BLKP(ptr);
    if (next_ptr != NULL)
    {
        size = GET_SIZE(HDRP(next_ptr));
        alloc = GET_ALLOC(HDRP(next_ptr));
        PUT(HDRP(next_ptr), PACK(size, alloc == 1 ? 1 : 0));
    }

    // Coalesce if there are any unallocated blocks
    coalesce(ptr);

    mm_checkheap(__LINE__);
}

/**
 * realloc - Change the size of the allocated block of memory and returns the heap pointer.
 * Tries to reuse the same block, calls malloc otherwise.
 * @param oldptr: A pointer to the previously allocated block of memory.
 * @param size: The new size for the block of memory.
 * @return: A pointer to the newly allocated block of memory, or NULL if allocation fails.
 **/
void *realloc(void *oldptr, size_t size)
{
    mm_checkheap(__LINE__);

    // If oldptr is NULL, then realloc is equivalent to malloc
    if (oldptr == NULL)
    {
        return malloc(size);
    }

    // If size of the block is 0, then just free the current pointer
    if (size == 0)
    {
        free(oldptr);
        return NULL;
    }

    // Get the size of the exisiting block and alohn
    size_t oldsize = GET_SIZE(HDRP(oldptr));
    size_t newsize = align(size + WSIZE);

    // If the new size is smaller than or equal to the old size, just return the exisiting block
    if (newsize <= oldsize)
    {
        return oldptr;
    }

    // If the new size is larger, we need to allocate a new block
    void *newptr = malloc(newsize);
    if (newptr == NULL)
    {
        return NULL; // malloc failed
    }

    // Copy the data from the old block to the newly created block, excluding the header
    size_t copysize = oldsize - WSIZE;

    // If the newly created block is smaller, then only need to copy the required bits
    if (size < copysize)
    {
        copysize = size;
    }

    // Copy from oldblock to new block
    memcpy(newptr, oldptr, copysize);

    // Free the old block
    free(oldptr);

    // return the newly created blck
    mm_checkheap(__LINE__);
    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr)
    {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p)
{
    size_t ip = (size_t)p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 * You call the function via mm_checkheap(__LINE__)
 * The line number can be used to print the line number of the calling
 * function where there was an invalid heap.
 */
bool mm_checkheap(int line_number)
{
#ifdef DEBUG
    printf("Heap checker started----------------------------------------------------\n");

    // Invariant 1: Check if prologue is allocated
    char *bp = heap_listp;
    if (!GET_ALLOC(HDRP(heap_listp)))
    {
        printf("\nInvariant failed: Prologue is not allocated at line:%d\n", line_number);
        return false;
    }
    printf("\nInvariant passed: Prologue is allocated at line:%d\n", line_number);

    // For each block in the heap, check
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        // Invariant 2: Check the header and the footer of the block match
        if ((GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp)) || GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))))
        {
            printf("\nInvariant failed: Header/footer size mismatch at %p at line:%d\n", bp, line_number);
            return false;
        }
        else
        {
            printf("\nInvariant passed: Header/footer size matched at line:%d\n", line_number);
        }

        // Invariant 3: Check if the block is within heap
        if (!in_heap(bp))
        {
            printf("\nInvariant failed: Block pointer out of heap %p at line:%d\n", bp, line_number);
            return false;
        }
        printf("\nInvariant passed: Block pointer in heap at line:%d\n", line_number);

        // Invariant 4: Check if the block follows 16 byte alignment
        if (GET_SIZE(HDRP(bp)) % 16 != 0)
        {
            printf("\nInvariant failed: Block do not follow 16-byte alignment %p at line:%d\n", bp, line_number);
            return false;
        }
        printf("\nInvariant passed: Block properly follows 16-byte alignment at line:%d\n", line_number);

        // Invariant 5: Check if current and next block are properly coalesced.
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0)
        {
            printf("\nInvariant failed: Coaslescing failed at %p and %p, both blocks are unallocated and not-coalesced: line %d\n", bp, NEXT_BLKP(bp), line_number);
            return false;
        }
        printf("\nInvariant passed: Coalescing properly done at line:%d\n", line_number);

        // Invariant 6: Check that no blocks overlap
        if (GET_ALLOC(HDRP(bp)))
        {
            char *next_bp = NEXT_BLKP(bp);
            size_t size = GET_SIZE(HDRP(bp));
            if (next_bp != NULL)
            {
                // Check if bp steps over the next block
                if ((bp + (size - WSIZE)) > (next_bp - WSIZE))
                {
                    printf("\nInvariant failed: Blocks overlapping at line:%d\n", line_number);
                    return false;
                }
            }
        }
        printf("\nInvariant passed: No block overlapping at line:%d\n", line_number);
    }

    // Invariant 7: Check epilogue is allocated
    if (!GET_ALLOC(HDRP(bp)))
    {
        printf("\nInvariant failed: Epilogue is not allocated at line:%d\n", line_number);
        return false;
    }
    printf("\nInvariant passed: Epilogue is allocated at line:%d\n", line_number);

    int index = 0;
    char *free_listp = NULL;

    // For each free list, check
    while (index < SEGLISTS)
    {
        free_listp = free_lists[index];
        bp = GET_NEXT_BLOCK(free_listp);
        while (bp != free_listp)
        {
            // Invariant 8: Check if all free list blocks are actually free
            void *header_block = HDRP(bp);
            if (GET_ALLOC(header_block))
            {
                printf("\nInvariant failed: Allocated block in free list:%d at %p in line:%d\n", index, bp, line_number);
                return false;
            }

            // Invariant 9: Check if all free list blocks have footers and are not allocated
            if (GET_ALLOC(FTRP(bp)))
            {
                printf("\nInvariant failed: Allocated block in free list:%d does not have footer:%p at line:%d\n", index, bp, line_number);
                return false;
            }

            // Invariant 10: Check if the blocks belong to the correct seglist
            if (index != GET_SEGLIST_INDEX(GET_SIZE((header_block))))
            {
                printf("\nInvariant failed: Allocated block is not in the correct free list:%d at %p in line:%d\n", index, bp, line_number);
                return false;
            }

            // Invariant 11: Check if all the prev blocks and next blocks are properly connected
            char *next_free_block = GET_NEXT_BLOCK(bp);
            if (GET_PREV_BLOCK(next_free_block) != bp)
            {
                printf("\nInvariant failed: Blocks are not properly connected in freelist:%d at %p in line:%d\n", index, bp, line_number);
                return false;
            }

            // Move to the next free block in the list
            bp = GET_NEXT_BLOCK(bp);
        }
        printf("\nInvariant passed: All blocks in free list:%d are free at line:%d\n", index, line_number);
        printf("\nInvariant passed: All blocks in free list:%d are allocated to the corect free list at line:%d\n", index, line_number);
        printf("\nInvariant passed: All blocks are connected in free list:%d at line:%d\n", index, line_number);
        printf("\nInvariant passed: Allocated blocks in free list:%d have footer at line:%d\n", index, line_number);
        index++;
    }

    printf("----------------------------------------------------");
#endif
    return true;
}