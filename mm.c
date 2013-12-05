/*
 * mm.c - Implements a LIFO Explicit Free Block List with Bidirectional Coalescing.
 * 
 * Block structure is as follows:
 * The first SIZE_T_SIZE bytes are the header.
 * The last SIZE_T_SIZE bytes are the footer.
 * The last 2 bits of the header and the footer are the allocation flag.
 * These bits are usable because the sizes are aligned bt 8 bytes.
 *
 * flag == 0x0
 *     FREE
 * flag == 0x1
 *     ALLOCATED
 * flag == 0x2
 *     ROOT
 *
 * The root flag is used to stop attempted access below the heap.
 * The root block is the block at the bottom of the heap.
 * The payload is the bytes between the header and footer.
 *
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

//#define MM_CHECK
//#define VERBOSE

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define PTR_SIZE (ALIGN(sizeof(void *)))

#define MIN_BLK_SIZE (SIZE_T_SIZE*2 + PTR_SIZE*2)

/* packs size and allocation bit, assuming that size is aligned */
#define PACK(size, alloc) ((size) | (alloc))

#define PAYLOADP(bp) ((void *)((char *)bp + SIZE_T_SIZE))
#define BLOCK(pp) ((void *)((char *)pp - SIZE_T_SIZE))

#define BLK_SIZE(bp) (HDR(bp) & ~0x3)
#define BLK_ALLOC(bp) (HDR(bp) & 0x3)

#define HDR(bp) (*((size_t *)bp))
#define FTR(bp) (*((size_t *)((char *)bp + BLK_SIZE(bp) - SIZE_T_SIZE)))

#define NEXT(bp) (*((void **)((char *)bp + SIZE_T_SIZE)))
#define PREV(bp) (*((void **)((char *)bp + SIZE_T_SIZE + PTR_SIZE)))

#define LIN_NEXT(bp) ((void *)((char *)bp + BLK_SIZE(bp)))
#define LIN_PREV(bp) ((void *)((char *)bp - (*((size_t *)((char *)bp - SIZE_T_SIZE)) & ~0x3)))

#define NUM_CLASSES (sizeof(size_t)*8-5)
#define CLASS_SIZE(n) (0x40*(1 << n))

#define ROOT(n) ((void *)((char *) mm_roots + SIZE_T_SIZE * n))

/* globals
 * mm_root - Pointer to the root block, located at the bottom of the heap
 */
void *mm_roots;

static void mm_setbounds(void *blkp, size_t value);
static void mm_setbounds(void *blkp, size_t value);
static void mm_remove(void *blkp);
static void mm_insert(void *dest, void *blkp);
static void *mm_coalesce(void *ptr);
static void *mm_traverse(size_t newsize, void *root);
static void mm_putList(void *ptr);
static void *mm_append(size_t newsize, void *root);
static void *mm_findSpace(size_t newsize);
void dumpclasses(void);

/*
 * mm_remove - Sets the header and footer of a block to value
 *     Note that size also includes the allocation flag
 *     Common usage passes the result of PACK(size, alloc) to value
 */
static void mm_setbounds(void *blkp, size_t value)
{
	HDR(blkp) = value;
	FTR(blkp) = value;
}

/*
 * mm_remove - For a consistent stack, this removes a FREE block from the chain
 *     Behavior is undefined for non FREE blocks
 */
static void mm_remove(void *blkp)
{
	NEXT(PREV(blkp)) = NEXT(blkp);
	if(NEXT(blkp) != NULL)
		PREV(NEXT(blkp)) = PREV(blkp);
}

/*
 * mm_insert - Inserts a FREE block in place of a specified non NULL block
 *     Behavior is undefined for non FREE blocks
 */

static void mm_insert(void *dest, void *blkp)
{
	PREV(blkp) = dest;
	NEXT(blkp) = NEXT(dest);
	if(NEXT(dest) != NULL)
		PREV(NEXT(dest)) = blkp;
	NEXT(dest) = blkp;
}

// Assumes that ptr is floating
static void *mm_coalesce(void *ptr)
{
	void *next = LIN_NEXT(ptr);
	void *prev = LIN_PREV(ptr);

	if(next < mem_heap_hi()+1 && BLK_ALLOC(next) == 0x0)
	{
		mm_remove(next);
		mm_setbounds(ptr, PACK(BLK_SIZE(ptr) + BLK_SIZE(next), 0x0));
	}
	if(BLK_ALLOC(prev) == 0x0)
	{
		mm_remove(prev);
		mm_setbounds(prev, PACK(BLK_SIZE(prev) + BLK_SIZE(ptr), 0x0));
		mm_putList(prev);
		return prev;
	}
	else
	{
		mm_putList(ptr);
		return ptr;
	}

}

static void __attribute__ ((noinline)) *mm_traverse(size_t newsize, void *root)
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

// this finds the list that fits a specific block, and then puts that block into the list. 
//Redo this code
static void mm_putList(void *ptr)
{
	int i;
	for(i = 0; i < NUM_CLASSES; i++)
	{	
		if(CLASS_SIZE(i) > BLK_SIZE(ptr))
		{
			mm_insert(ROOT(i), ptr);
			return;
		}
	}
}

static void *mm_append(size_t newsize, void *root)
{
	void *heaptail = LIN_PREV(mem_heap_hi()+1);
	void *found;

	if(BLK_ALLOC(heaptail) == 0x0)
	{
		found = mem_sbrk(newsize - BLK_SIZE(heaptail));
		if (found == (void *)-1)
			return NULL;

		mm_setbounds(found, PACK(newsize - BLK_SIZE(heaptail), 0x0));

		found = mm_coalesce(found);
	}
	else
	{
		found = mem_sbrk(newsize);
		if (found == (void *)-1)
			return NULL;

		mm_setbounds(found, PACK(newsize, 0x0));

		mm_insert(root, found);
	}

	return found;
}

// Redo this code to look cleaner
static void *mm_findSpace(size_t newsize)
{
	int i = 0;
	void *returnVal = NULL;

	for(i; CLASS_SIZE(i) <= newsize; i++);

	int first = i;

	for(i; i < NUM_CLASSES; i++)
	{
		if(NEXT(ROOT(i)) != NULL)
			returnVal = mm_traverse(newsize, ROOT(i));

		if (returnVal != NULL)
			return returnVal;	
	}

	return mm_append(newsize, ROOT(first));
}

/* 
 * mm_init - Initialize the malloc package
 */
int mm_init(void)
{
	size_t rootssize = MIN_BLK_SIZE+SIZE_T_SIZE*(NUM_CLASSES-1);
	// Set up the size classes
	mm_roots = mem_sbrk(rootssize);
	int i;
	for(i = 0; i < NUM_CLASSES; i++)
		NEXT(ROOT(i)) = NULL;
	mm_setbounds(mem_heap_lo(), PACK(rootssize, 0x2));

#ifdef MM_CHECK
	mm_check();
#endif

	return 0;
}

/*
 * mm_malloc - LIFO Explicit Free List
 *     
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

	mm_remove(found);

	size_t tail_size = BLK_SIZE(found) - newsize;
	if(tail_size < MIN_BLK_SIZE)
		mm_setbounds(found, PACK(BLK_SIZE(found), 0x1));
	else
	{
		mm_setbounds(found, PACK(newsize, 0x1));

		void *tail = LIN_NEXT(found);
		mm_setbounds(tail, PACK(tail_size, 0x0));
		
		mm_putList(tail);
	}

#ifdef MM_CHECK
	mm_check();
#endif

	return PAYLOADP(found);
}

/*
 * mm_free - No coalescing yet, just insert in the list.
 */
void mm_free(void *ptr)
{
#ifdef VERBOSE
	printf("\nmm_free(%#08x)\n", ptr);
#endif

	void *blkp = BLOCK(ptr);
	mm_setbounds(blkp, PACK(BLK_SIZE(blkp), 0x0));

	blkp = mm_coalesce(blkp);

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
 * mm_check - Peforms checks on the consistency of the stack.
 */
int mm_check(void)
{
	void *blkp;

#ifdef VERBOSE
	printf("\n");
	for(blkp = mem_heap_lo(); blkp < mem_heap_hi() + 1; blkp = LIN_NEXT(blkp))
		printf("%#08x 0x%x NEXT=0x%08x PREV=0x%08x size=%#x\n", blkp, BLK_ALLOC(blkp), NEXT(blkp), PREV(blkp), BLK_SIZE(blkp));
	dumpclasses();
#endif

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

void dumpclasses(void) {
	int i;
	printf("\n");
	for(i = 0; i < NUM_CLASSES; i++)
	{
		printf("#%2d Max: 0x%08x Status: ", i, CLASS_SIZE(i));
		if(NEXT(ROOT(i)) == NULL)
				printf("Uninitialized\n");
		else
		{
			printf("Initialized\n");
			void* blkp = ROOT(i);
			while(blkp != NULL)
			{
					printf("\t%#08x 0x%x NEXT=0x%08x size=0x%x\n", blkp, BLK_ALLOC(blkp), NEXT(blkp), BLK_SIZE(blkp));
					blkp = NEXT(blkp);
			}
		}
	}
}








