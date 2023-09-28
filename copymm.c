/*
 * mm.c -  Simple allocator based on implicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63       32   31        1   0
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more usr blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Christian Lung",
    /* UID */
    "005731615",
    /* Custom message (16 chars) */
    "CS33 is fun (?)",
};

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };
#define WSIZE	4
#define DSIZE	8
#define CHUNKSIZE (1 << 12) /* initial heap size (bytes) */
#define MAX(x,y) 		((x) > (y)? (x) : (y))
#define PACK(size, alloc)	((size) | (alloc))
#define GET(p)			(*(unsigned int *)(p))
#define PUTP(p,val)		(*((size_t *)(p)) = (val))
#define PUT(p, val)		(*(unsigned int *)(p) = (val))
#define GET_SIZE(p)		(GET(p) & ~0x7)
#define GET_ALLOC(p)		(GET(p) & 0x1)
#define HDRP(bp)		((char *)(bp) - WSIZE)
#define FTRP(bp)		((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp)		((char *)(bp) + GET_SIZE(((char *) (bp) - WSIZE)))
#define PREV_BLKP(bp)		((char *)(bp) - GET_SIZE(((char *) (bp) - DSIZE))) 
#define SUCC_FREE(bp)		((char *) ((char *)(bp)))
#define PRED_FREE(bp)		((char *) ((char *)(bp) + DSIZE))	

#define OVERHEAD 8 /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (24) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */
#define BUCKETS	14
#define BUCKET0 8
#define BUCKET1 16
#define BUCKET2 32
#define BUCKET3 64
#define BUCKET4 128
#define BUCKET5 256
#define BUCKET6 512
#define BUCKET7 1024
#define BUCKET8 2048
#define BUCKET9 4096
#define BUCKET10 8192
#define BUCKET11 16384
#define BUCKET12 32768
#define BUCKET13 65536
/* Global variables */
static block_t *prologue; /* pointer to first block */
void **freeLists;
int MAXBUCKETS = 14;

/* function prototypes for internal helper routines */
static int findBucket(size_t size);
static void addFree(void *ptr, size_t size);
static void removeFree(void *ptr, size_t size);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *ptr, size_t asize);
static void *coalesce(void *ptr);

static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);

/*finds corresponding bucket in segregated list*/
int findBucket(size_t size){
	if(size<=BUCKET1){
		return 0;
	}
	else if(size<=BUCKET2){
		return 1;
	}
	else if(size<=BUCKET3){
		return 2;
	}
	else if(size<=BUCKET4){
		return 3;
	}
	else if(size<=BUCKET5){
		return 4;
	}
	else if(size<=BUCKET6){
		return 5;
	}
	else if(size<=BUCKET7){
		return 6;
	}
	else if(size<=BUCKET8){
		return 7;
	}
	else if(size<=BUCKET9){
		return 8;
	}
	else if(size<=BUCKET10){
		return 9;
	}
	else if(size<=BUCKET11){
		return 10;
	}
	else if(size<=BUCKET12){
		return 11;
	}
	else if(size<=BUCKET13){
		return 12;
	}
	else{
		return 13;
	}
}
/*adds a free block to the segregated list*/
void addFree(void *ptr, size_t size){
	int bucketIndex = findBucket(size);
	void *bucket_ptr = NULL;
	/*checks for right bucket by size*/
        for(bucketIndex; bucketIndex<MAXBUCKETS-1; bucketIndex++){
		bucket_ptr = freeLists[bucketIndex];
		while(bucket_ptr != NULL){
			if(size <= GET_SIZE(HDRP(ptr))) break;
		}
	}
	if(bucketIndex==MAXBUCKETS-1){
		 bucket_ptr = freeLists[bucketIndex];
	}
	PUTP(PRED_FREE(ptr), (size_t) NULL);
	if(bucket_ptr != NULL){
		PUTP(SUCC_FREE(ptr), (size_t)bucket_ptr);
		PUTP(PRED_FREE(bucket_ptr), (size_t)ptr);
	}
	else{
		PUTP(SUCC_FREE(ptr), (size_t) NULL);
	}
	freeLists[bucketIndex] = ptr;
}

void removeFree(void *ptr, size_t size){
	if(ptr == NULL) return;
	int bucket = findBucket(size);
	char *next = SUCC_FREE(ptr);
	char *prev = PRED_FREE(ptr);
	/*if only item in segregated list*/
	if(prev == NULL && next == NULL){
		freeLists[bucket] = NULL;
	}
	/*if first item in segregated list*/
	if(prev == NULL && next != NULL){
		freeLists[bucket] = next;
		PUTP(PRED_FREE(next), (size_t)NULL);
	}
	/*if middle item in segregated list*/
	if(prev	!= NULL && next != NULL){
		PUTP(SUCC_FREE(prev), (size_t)next);
		PUTP(PRED_FREE(next), (size_t)prev);	
	}
	/*if last item in segregated list*/
	if(prev != NULL && next == NULL){
		PUTP(SUCC_FREE(prev), (size_t)NULL);
	}
}
/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {

/* initialize segregated list*/
freeLists = mem_sbrk(MAXBUCKETS * DSIZE);
for(int b=0; b<MAXBUCKETS; b++){
	freeLists[b] = NULL;
}
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(4*WSIZE)) == (void*)-1)
        return -1;
    /* initialize the prologue */
    PUT(prologue, 0);
    PUT(prologue + (1*WSIZE), PACK(DSIZE, 1));
    PUT(prologue + (2*WSIZE), PACK(DSIZE, 1));
    PUT(prologue + (3*WSIZE), PACK(0,1));
    prologue += (2*WSIZE);
    
    /*extend empty heap with freeblock of CHUNKSIZE bytes*/
    void *ptr;
    if((ptr = extend_heap(CHUNKSIZE/WSIZE)) == NULL) return -1;
    /*add free block into segregated list*/
    addFree(ptr, CHUNKSIZE/WSIZE);
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    size_t asize;       /* adjusted block size */
    size_t extendsize;  /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    //if(asize<MIN_BLOCK_SIZE) asize = MIN_BLOCK_SIZE;
    if(size <= DSIZE){
    	asize = 2*DSIZE;
    }
    else{
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /*Search the free list for a fit*/
    if((bp = find_fit(asize))!=NULL){
	place(bp,asize);
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
                     ? asize
                     : CHUNKSIZE;
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
	/*no more memory*/
        return NULL;
    }
    /*place new block*/
    place(bp,asize);
    return bp;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *payload) {
    size_t size = GET_SIZE(HDRP(payload));
    PUT(HDRP(payload), PACK(size,0));
    PUT(FTRP(payload), PACK(size,0));
    coalesce(payload);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {
    block_t *block = prologue;

    if (verbose)
        printf("Heap (%p):\n", prologue);

    if (block->block_size != sizeof(header_t) || !block->allocated)
        printf("Bad prologue header\n");
    checkblock(prologue);

    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue+prologue->block_size; block->block_size > 0; block = (void *)block + block->block_size) {
        if (verbose)
            printblock(block);
        checkblock(block);
    }

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if(size<MIN_BLOCK_SIZE) size = MIN_BLOCK_SIZE;
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;
    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)) , PACK(0,1));
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(void *ptr, size_t asize) {
    size_t freeSize = GET_SIZE(HDRP(ptr));
    size_t split_size = freeSize - asize;
    if (split_size >= MIN_BLOCK_SIZE) {
        /* split the block by updating the header/footer and marking it allocated*/
        PUT(HDRP(ptr), PACK(asize,1));
	PUT(FTRP(ptr), PACK(asize,1));
        /* update the header/footer of the new free block */
        void *new_block = ptr + GET_SIZE(HDRP(ptr));
        PUT(HDRP(new_block), PACK(split_size,0));
	PUT(FTRP(new_block), PACK(split_size,0));
	/*add new block to segregated list*/
	addFree(new_block, split_size);
    } else {
        /* splitting the block will cause a splinter so we just include it in the allocated block */
        PUT(HDRP(ptr), PACK(freeSize,1));
	PUT(FTRP(ptr), PACK(freeSize,1));
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize) {
    /* first fit search */
    /*find corresponding bucket*/
    int bucket = findBucket(asize);
    void *bucketIt;
    for(bucket; bucket<MAXBUCKETS; bucket++){
	/*iterate through the different buckets*/
    	bucketIt = freeLists[bucket];
	/*iterate through the bucket until fit is found*/
	while(bucketIt != NULL){
		if(GET_SIZE(bucketIt)>=asize){
			return bucketIt;
		}
		bucketIt = NEXT_BLKP(bucketIt);
	}
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *ptr) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) { /* Case 1 */
        /* no coalesceing */
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
	size += next_size;
	/*remove next free block*/
	removeFree(NEXT_BLKP(ptr), next_size);
	/*update header/footer of new block*/
	PUT(HDRP(ptr),PACK(size,0));
	PUT(FTRP(ptr),PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
	size += prev_size;
	/*remove previous free block*/
	removeFree(PREV_BLKP(ptr), prev_size);
	/*update header/footer of new block*/
	ptr = PREV_BLKP(ptr);
	PUT(HDRP(ptr), PACK(size,0));
	PUT(FTRP(ptr), PACK(size,0));
    }

    else { /* Case 4 */
        size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
	size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
	size = size + prev_size + next_size;
	/*remove previous and next blocks*/
	removeFree(PREV_BLKP(ptr), prev_size);
	removeFree(NEXT_BLKP(ptr), next_size);
	/*update header/footer of new block*/
	ptr = PREV_BLKP(ptr);
	PUT(HDRP(ptr), PACK(size,0));
	PUT(FTRP(ptr), PACK(size,0));
    }
    addFree(ptr,size);
    return ptr;
}

static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t *footer = get_footer(block);
    if (block->block_size != footer->block_size) {
        printf("Error: header does not match footer\n");
    }
}
