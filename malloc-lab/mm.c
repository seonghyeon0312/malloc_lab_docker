/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "301-09",
    /* First member's full name */
    "flaska99",
    /* First member's email address */
    "flaska99@gmail.com",
    /* Second member's full name (leave blank if none) */
    "msms804",
    /* Second member's email address (leave blank if none) */
    "msms804@gmail.com"};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // single word
#define DSIZE 8 // double word
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x)> (y) ? (x):(y))

#define PACK(size, alloc) ((size)|(alloc)) // allocate bit change

#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p)=(val))

#define GET_SIZE(p) (GET(p) & ~0x7) // block size
#define GET_ALLOC(p) (GET(p) & 0x1) // allocated bit state check 1=>allocate, 0=>free

#define HDRP(bp) ((char *)(bp) - WSIZE) // header
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp))-DSIZE) // footer

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void* heap_listp;
static void * extend_heap(size_t words);
static void* coalesce(void * bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize;
    char* bp;

    if(size ==0){
        return NULL;
    }

    if(size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/(DSIZE));
    }

    if((bp=find_fit(asize))!= NULL){
        place(bp,asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //     return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //     copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;

    if (ptr == NULL) {
        return mm_malloc(size);  // realloc(NULL, size) == malloc(size)
    }

    if (size == 0) {
        mm_free(ptr);            // realloc(ptr, 0) == free(ptr)
        return NULL;
    }

    void* old = ptr;
    void* new;
    size_t oldSize = GET_SIZE(HDRP(ptr));

    new = mm_malloc(size);
    if(new == NULL){
        return NULL;
    }

    size_t copySize = oldSize - DSIZE;

    if(size<copySize){
        copySize = size;
    }
    memcpy(new, old, copySize);
    mm_free(old);
    return new;
}

static void* extend_heap(size_t words){
    char* bp;
    size_t size;

    size = (words%2) ? (words+1)*WSIZE : words*WSIZE;
    if((long)(bp=mem_sbrk(size))==-1){
        return NULL;
    }

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    
    return coalesce(bp);
}

static void* coalesce(void * bp){

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록 footer로 이전 블록 할당 상태 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록 header로 다음 블록 할당 상태 확인
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록 사이즈

    if(prev_alloc && next_alloc){
        return bp;
    }else if(prev_alloc && !next_alloc){
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }else if(!prev_alloc && next_alloc){
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);
    }else{
        size+=GET_SIZE(FTRP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);
    }
    return bp;
}

static void* find_fit(size_t asize){
    // void* ptr = heap_listp;

    // while(GET_SIZE(HDRP(ptr)) != 0 && GET_ALLOC(HDRP(ptr)) != 1){
    //     if(GET_SIZE(HDRP(ptr))>= asize && GET_ALLOC(HDRP(ptr)) == 0){
    //         return ptr;
    //     }
    //     ptr = HDRP(NEXT_BLKP(ptr));
    // }
    // return NULL;

    void* bp;

    for(bp=heap_listp;GET_SIZE(HDRP(bp))>0;bp=NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp))&&(asize<=GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

static void place(void* bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize-asize)>=(2*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize, 1));
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize, 0));
    }else{
        PUT(HDRP(bp),PACK(csize, 1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}