/*
 * mm.c - Implements free block lists sorted into sizes between exponents of 2 with bidirectional coalescing
 * 
 * Block structure is as follows:
 * The first SIZE_T_SIZE bytes are the header.
 * The last SIZE_T_SIZE bytes are the footer.
 * The last 2 bits of the header and the footer are the allocation flag.
 * These bits are usable because the sizes are aligned bt 8 bytes.
 * The payload is the bytes between the header and footer.
 *
 * flag == 0x0
 *     FREE
 * flag == 0x1
 *     ALLOCATED
 * flag == 0x2
 *     ROOT
 *
 * The root flag is used to prevent modifying bookkeeping information.
 * The root block is the block at the bottom of the heap.
 *
 * The first free list accommodates block sizes up to but not equal to twice MIN_BLK_SIZE.
 * This pattern continues until LIST_MAX_SIZE(n) surpasses the limit of size_t.
 *
 * The free list root blocks are accessed rith the ROOT(n) macro.
 * Since the root block attribute that matters is NEXT, they are stored overlapping each other.
 * The first SIZE_T_SIZE bytes in the heap are the header of the root block.
 * The next PTR_SIZE bytes are the NEXT of ROOT(0).
 * Every PTR_SIZE chunk following that is the NEXT of ROOT(n),
 * until the last NEXT, after which is the footer of SIZE_T_SIZE.
 * This concludes the static bookkeeping information in the heap.
 *
 * Every time the mm_malloc is forced to extend the heap and there is not a free block at the top of the heap,
 *     it makes two blocks of the requested size, returning the latter. This design decision drastically decreases
 *     the amount of time spent searching for a similarly sized block that doesn't exist only to extend the heap
 *     again. In many cases, it even improves utilization by not wasting larger free blocks on allocating smaller
 *     ones.
 *
 * The package is guaranteed to:
 *     Never have adjacent free blocks
 *     Never have a free block in the wrong list
 *     Never leave behind space that can never be reused
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Nathan&Adrien",
	/* First member's full name */
	"Adrien Tateno",
	/* First member's email address */
	"adrientateno2016@u.northwestern.edu",
	/* Second member's full name (leave blank if none) */
	"Nathan Yeazel",
	/* Second member's email address (leave blank if none) */
	"nathanyeazel2016@u.northwestern.edu"
};

/*
 * When MM_CHECK is defined, mm_check is called at the end of every mm_init, mm_malloc, and mm_free call
 * When VERBOSE is defined, every mm_malloc and mm_free call prints its calling conditions.
 *     Additionally, every call to mm_check will print the contents of the heap and free lists.
 */
#define MM_CHECK
//#define VERBOSE

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Aligned sizes of common types */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define PTR_SIZE (ALIGN(sizeof(void *)))

/* Minimum size of a valid block */
#define MIN_BLK_SIZE (SIZE_T_SIZE*2 + PTR_SIZE*2)

/* Packs size and allocation bit, assuming proper alignment */
#define PACK(size, alloc) ((size) | (alloc))

/* Gets payload from block */
#define PAYLOADP(bp) ((void *)((char *)bp + SIZE_T_SIZE))
/* Gets block from payload */
#define BLOCKP(pp) ((void *)((char *)pp - SIZE_T_SIZE))

/* Accesses components of a header */
#define BLK_SIZE(bp) (HDR(bp) & ~0x3)
#define BLK_ALLOC(bp) (HDR(bp) & 0x3)

/* Accesses the header and footer of a block */
#define HDR(bp) (*((size_t *)bp))
#define FTR(bp) (*((size_t *)((char *)bp + BLK_SIZE(bp) - SIZE_T_SIZE)))

/* Acceses the next/previous block in a free list */
#define NEXT(bp) (*((void **)((char *)bp + SIZE_T_SIZE)))
#define PREV(bp) (*((void **)((char *)bp + SIZE_T_SIZE + PTR_SIZE)))

/* Accesses the next/previous block on the heap */
#define LIN_NEXT(bp) ((void *)((char *)bp + BLK_SIZE(bp)))
#define LIN_PREV(bp) ((void *)((char *)bp - (*((size_t *)((char *)bp - SIZE_T_SIZE)) & ~0x3)))

/* Information about the free lists */
#define NUM_LISTS (sizeof(size_t)*8-5)
#define LIST_MAX_SIZE(n) (0x40*(1 << n))

#define ROOT(n) ((void *)((char *) mem_heap_lo() + SIZE_T_SIZE * n))

/*
 * Static Function Prototypes
 */
static void *mm_append(size_t newsize, void *root);
static void *mm_findSpace(size_t newsize);
static void *mm_unfloat(void *ptr);
static void *mm_traverse(size_t newsize, void *root);
static void mm_putList(void *ptr);
static void mm_insert(void *dest, void *blkp);
static void mm_remove(void *blkp);
static void mm_setBounds(void *blkp, size_t value);
static int mm_check(void);
static void mm_printLists(void);

/* 
 * mm_init - Initialize the malloc package
 *     Makes a root block that provides access to all the free lists in the heap.
 */
int mm_init(void)
{
	size_t rootblocksize = MIN_BLK_SIZE+SIZE_T_SIZE*(NUM_LISTS-1);
	if(mem_sbrk(rootblocksize) == (void *)-1)
		return -1;
	int i;
	for(i = 0; i < NUM_LISTS; i++)
		NEXT(ROOT(i)) = NULL;
	mm_setBounds(mem_heap_lo(), PACK(rootblocksize, 0x2));

#ifdef MM_CHECK
	mm_check();
#endif

	return 0;
}

/*
 * mm_malloc - Returns a pointer to the payload of a block
 *     May split a larger free block for allocation. Relocates the tail free block.
 */
void *mm_malloc(size_t size)
{
#ifdef VERBOSE
	printf("\nmm_malloc(%#x)\n", size);
#endif

	size_t newsize = ALIGN(size + SIZE_T_SIZE*2);
	if(newsize < MIN_BLK_SIZE)
		newsize = MIN_BLK_SIZE;
	
	void *found = mm_findSpace(newsize);

	if(found == NULL)
		return NULL;

	// Float the block
	mm_remove(found);

	size_t tail_size = BLK_SIZE(found) - newsize;
	if(tail_size < MIN_BLK_SIZE)
		mm_setBounds(found, PACK(BLK_SIZE(found), 0x1));
	else
	{
		mm_setBounds(found, PACK(newsize, 0x1));

		void *tail = LIN_NEXT(found);
		mm_setBounds(tail, PACK(tail_size, 0x0));
		
		mm_putList(tail);
	}

#ifdef MM_CHECK
	mm_check();
#endif

	return PAYLOADP(found);
}

/*
 * mm_free - Mark a block as free then unfloat it.
 */
void mm_free(void *payload)
{
#ifdef VERBOSE
	printf("\nmm_free(%#08x)\n", payload);
#endif

	void *blkp = BLOCKP(payload);
	mm_setBounds(blkp, PACK(BLK_SIZE(blkp), 0x0));

	blkp = mm_unfloat(blkp);

#ifdef MM_CHECK
	mm_check();
#endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	void *oldptr = ptr;
	void *newptr;
	size_t copySize;
	
	newptr = mm_malloc(size);
	if(newptr == NULL)
		return NULL;
	copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
	if(size < copySize)
		copySize = size;
	memcpy(newptr, oldptr, copySize);
	mm_free(oldptr);
	return newptr;
}

/*
 * mm_append - Extends the heap to fit a new block
 *     If there is a free block at the top of the heap, add to that block and return.
 *     Otherwise, allocate two blocks of the requested size, and return the top block.
 */
static void *mm_append(size_t newsize, void *root)
{
	void *heaptail = LIN_PREV(mem_heap_hi()+1);
	void *found;

	if(BLK_ALLOC(heaptail) == 0x0)
	{
		size_t extension = newsize - BLK_SIZE(heaptail);
		found = mem_sbrk(extension);
		if (found == (void *)-1)
			return NULL;

		mm_setBounds(found, PACK(extension, 0x0));

		found = mm_unfloat(found);
	}
	else
	{
		void *extra = mem_sbrk(newsize);
		if (extra == (void *)-1)
			return NULL;

		mm_setBounds(extra, PACK(newsize, 0x0));
		mm_insert(root, extra);

		found = mem_sbrk(newsize);
		if (found == (void *)-1)
			return NULL;

		mm_setBounds(found, PACK(newsize, 0x0));
		mm_insert(root, found);
	}

	return found;
}

/*
 * mm_findSpace - Guaranteed to find a free block of size newsize or greater
 */
static void *mm_findSpace(size_t newsize)
{
	int i = 0;
	void *returnval = NULL;

	// Calculates and saves the first free list that should fit newsize
	for(i; LIST_MAX_SIZE(i) <= newsize; i++);
	int first = i;

	for(i; i < NUM_LISTS; i++)
	{
		if(NEXT(ROOT(i)) != NULL)
			returnval = mm_traverse(newsize, ROOT(i));

		if (returnval != NULL)
			return returnval;	
	}

	return mm_append(newsize, ROOT(first));
}

/*
 * mm_unfloat - Performs all the necessary operations to place a floating block in the heap, preserving validity
 *     Behavior is only defined for floating blocks.
 *     Returns a pointer to the input block, possibly coalesced with the immediately preceding and following blocks.
 */
static void *mm_unfloat(void *blkp)
{
	void *next = LIN_NEXT(blkp);
	void *prev = LIN_PREV(blkp);

	if(next < mem_heap_hi()+1 && BLK_ALLOC(next) == 0x0)
	{
		mm_remove(next);
		mm_setBounds(blkp, PACK(BLK_SIZE(blkp) + BLK_SIZE(next), 0x0));
	}
	if(BLK_ALLOC(prev) == 0x0)
	{
		mm_remove(prev);
		mm_setBounds(prev, PACK(BLK_SIZE(prev) + BLK_SIZE(blkp), 0x0));
		mm_putList(prev);
		return prev;
	}
	else
	{
		mm_putList(blkp);
		return blkp;
	}
}

/*
 * mm_traverse - Searches a free block list and returns the first block that fits newsize or NULL
 */
static void *mm_traverse(size_t newsize, void *root)
{
	void *blkp = NEXT(root);
	void *found = NULL;
	while(blkp != NULL && found == NULL)
	{
		if(BLK_SIZE(blkp) >= newsize)
			found = blkp;
		blkp = NEXT(blkp);
	}
	return found;
}

/*
 * mm_putList - Takes a floating block and puts in the appropriate list
 *     Behavior is only defined for floating blocks.
 *     Guaranteed to find an appropriate list.
 */
static void mm_putList(void *ptr)
{
	int i = 0;
	for(i; LIST_MAX_SIZE(i) <= BLK_SIZE(ptr); i++);
	mm_insert(ROOT(i), ptr);
}

/*
 * mm_insert - Inserts a block after a specified block
 *     Behavior is only defined for floating blocks.
 */
static void mm_insert(void *dest, void *blkp)
{
	PREV(blkp) = dest;
	NEXT(blkp) = NEXT(dest);
	if(NEXT(dest) != NULL)
		PREV(NEXT(dest)) = blkp;
	NEXT(dest) = blkp;
}

/*
 * mm_remove - Removes a FREE block from the chain
 *     Behavior is undefined for floating blocks or root blocks.
 */
static void mm_remove(void *blkp)
{
	NEXT(PREV(blkp)) = NEXT(blkp);
	if(NEXT(blkp) != NULL)
		PREV(NEXT(blkp)) = PREV(blkp);
}

/*
 * mm_setBounds - Sets the header and footer of a block to value
 *     Note that size also includes the allocation flag
 *     Common usage passes the result of PACK(size, alloc) to value
 *     It is imprtant that the header is set first, as a proper header is required to find the footer
 */
static void mm_setBounds(void *blkp, size_t value)
{
	HDR(blkp) = value;
	FTR(blkp) = value;
}

/*
 * mm_check - Peforms checks on the consistency of the heap. When VERBOSE is defined, prints heap contents.
 */
static int mm_check(void)
{
	void *blkp;
	void *current; 

#ifdef VERBOSE
	printf("\n");
	for(blkp = mem_heap_lo(); blkp < mem_heap_hi() + 1; blkp = LIN_NEXT(blkp))
		printf("%#08x 0x%x NEXT=0x%08x PREV=0x%08x size=%#x\n", blkp, BLK_ALLOC(blkp), NEXT(blkp), PREV(blkp), BLK_SIZE(blkp));
	mm_printLists();
#endif
	int i;
	for(i = 0; i < NUM_LISTS; i++) //This will check through all of the free lists for various problems
	{
		current = NEXT(ROOT(i));
		while(current != NULL)
		{
			if (current < mem_heap_lo() || current > mem_heap_hi())
			{
				printf("Block %#x does not point to a valid address.\n", current);
				return 0;
			}

			if(BLK_ALLOC(current) != 0x0)
			{
				printf("Block %#x is in a free list but is not free.\n", current);
				return 0;
			}

			if(BLK_SIZE(current) >= LIST_MAX_SIZE(i) || BLK_SIZE(current) < (LIST_MAX_SIZE(i) >> 1))
			{
				printf("Block %#x is in the wrong free list.\n", current);
				return 0;
			}
			current = NEXT(current);
		}


	}
	blkp = mem_heap_lo();
	while(blkp < mem_heap_hi()+1)
	{
		if(BLK_ALLOC(blkp) == 0x0 && BLK_ALLOC(LIN_PREV(blkp)) == 0x0)
		{
			printf("Free block %#x is preceded by a free block.\n", blkp);
			return 0;
		}

		blkp = LIN_NEXT(blkp);
	}

	return 1;
}

/*
 * mm_printLists - Prints the status of all free lists. If list is in use, prints contents.
 */
static void mm_printLists(void) {
	printf("\n");
	int i;
	for(i = 0; i < NUM_LISTS; i++)
	{
		printf("#%2d Max: 0x%08x Status: ", i, LIST_MAX_SIZE(i));
		if(NEXT(ROOT(i)) == NULL)
				printf("Empty\n");
		else
		{
			printf("In Use\n");
			void* blkp = ROOT(i);
			while(blkp != NULL)
			{
				printf("\t%#08x 0x%x NEXT=0x%08x size=0x%x\n", blkp, BLK_ALLOC(blkp), NEXT(blkp), BLK_SIZE(blkp));
				blkp = NEXT(blkp);
			}
		}
	}
}








