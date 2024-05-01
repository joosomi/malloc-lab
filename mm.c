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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4  /*Word and header/footer size (bytes)*/
#define DSIZE 8 /*Double word size (bytes)*/
#define CHUNKSIZE (1<<12) /*extend heap by this amount (bytes)*/ 

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word*/
// OR 연산자를 이용하여 header, footer에 들어갈 수 있는 값 리턴
// size | alloc (0 - freed, 1 - allocated)
#define PACK(size, alloc) ((size) | (alloc))

/*Read and write a word at address p*/
#define GET(p) (*(unsigned int *)(p)) // 주소 p가 참조하는 워드를 읽는 GET
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))  //주소 p가 가리키는 워드에 val을 저장하는 함수 PUT

/*Read the size and allocated fields from address p*/
// GET_SIZE:  not 연산자를 활용하여 사이즈 정보만 가져오도록, 맨 뒷자리만 가져오도록  -> 하위 3비트 0
// GET_ALLOC: 마지막 &0x1=> 맨 뒷자리 allocated 정보만 가져오도록
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer*/
//header, footer는 1word 
//bp에서 WSIZE 4를 뺸다는 것은 주소가 4byte 이전으로 간다는 것 -> 헤더.
#define HDRP(bp) ((char *)(bp) - WSIZE) // header를 가리키는 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer를 가리키는 포인터

/*Given block ptr bp, compute address of next, and previous blocks*/
//NEXT_BLKP: 지금 블록의 bp(페이로드의 주소)
//PREV_BLKP: 이전 블록의 bp
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


/* free list - Successor, Predecessor를 가리킬 포인터*/

//explicit free list 
//=> 메모리에 빈 공간, 할당되지 않은 블록 관리를 위해 Free block에 이전/다음 Free block 가리키는 포인터 포함
// Predecessor free block 가리키는 포인터
// + one word => Successor Free block을 가리키는 포인터 
#define PREDP(bp) (*(void **)(bp)) 
#define SUCCP(bp) (*(void **)(bp + WSIZE))


/*explicit free list 
=> header, pred(이전 가용 블록), succ(이후 가용 블록), payload, padding, footer*/
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);

void removeBlock(void *);
void putFreeBlock(void *);

static char *heap_listp; // points to the prologue block or first block
static char *free_listp; // 명시적 가용 리스트의 시작 부분

static void *last_bp = NULL; // NEXT_FIT

/* 
 * mm_init - initialize the malloc package.
 힙의 초기화 -> 메모리 관리를 위한 prologue, epilogue 블록 생성과 초기 가용 블록 생성
 */
int mm_init(void)
{
    /* Create the initial empty heap*/
    //초기 힙 생성 => 6*WSIZE : 프롤로그, 에필로그, 초기 가용 블록 관리를 위한 최소 공간
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0); // 미사용 패딩 -> 메모리 정렬을 위해
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE*2, 1)); /* Prologue header */
    
    //현재는 다른 가용 블록이 없으니 NULL로 설정
    PUT(heap_listp + (2*WSIZE), (int)NULL); /* Prologue SUCCESOR */
    PUT(heap_listp + (3*WSIZE), (int)NULL); /* Prologue PREDECCESSOR */

    PUT(heap_listp + (4*WSIZE), PACK(DSIZE*2, 1)); /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));     /* Epilogue header */
    
    free_listp = heap_listp + DSIZE; 
   
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    //힙을 더 확장해서 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

//extend_heap -> 메모리 할당자가 더 많은 메모리 필요로 할 때 힙 크기 확장
static void *extend_heap(size_t words){
    char * bp;
    size_t size;

    /*Allocate an even number of words to maintain alignment*/
    //더블 워드 정렬> 짝수 단어 수 할당
    //size = 힙의 총 byte 수
    //words 홀수라면 하나를 더해서 짝수로 만들고, WSIZE(4 바이트) 곱해서 => 블록의 크기 size 결정
    //words 짝수라면 이미 words * WSIZE
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    //요청한 크기만큼 힙 확장
    //실패시 NULL 반환
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    /*Initialize free block header/footer and the epilogue header*/
    //새로 할당된 공간의 헤더, 푸터 초기화, 새로운 에필로그 헤더 설정
    PUT(HDRP(bp), PACK(size, 0)); /*Free block header*/
    PUT(FTRP(bp), PACK(size, 0)); /*Free block footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /*New epilogue header*/
    // 새 에필로그 헤더는 항상 size = 0, alloc = 1

    /*Coalesce if the previous block was free*/
    //이전 블록이 free -> coalesce 과정 
    return coalesce(bp);
}


/*Coalesce*/
static void *coalesce(void *bp)
{
    //직전과 직후 블록의 할당 상태 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록 크기 확인

    //CASE 1. 이전과 다음 블록 모두 할당된 상태
    if (prev_alloc && next_alloc)
    { 
        // return bp;
    }

    //CASE2 이전 블록 allocated, 다음 블록 free인 상태  
    if (prev_alloc && !next_alloc)
    { 
        removeBlock(NEXT_BLKP(bp)); //free 상태였던 직후 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //CASE 3 이전 블록 free, 다음 블록 allocated
    else if (!prev_alloc && next_alloc)
    { 
        removeBlock(PREV_BLKP(bp)); // 직전 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //CASE4 이전, 다음 블록 모두 free
    else if (!prev_alloc && !next_alloc)
    { 
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //연결된 새 가용 블록을 가용 리스트에 추가
    putFreeBlock(bp);
    return bp;
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    /* Ignore spurious requests */ 
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ( ( size + (DSIZE) + (DSIZE-1) ) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

   /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // extend_heap은 인자가 WORD 단위로 들어감
        return NULL;
    place(bp, asize);
    return bp;
}


// first_fit - 최고 84점
// 주어진 크기(asize)의 블록 찾기 
static void *find_fit(size_t asize)
{
    /* first-fit search */
    //free_list의 시작에서부터 끝까지 블록을 순회하는 포인터 bp
    void *bp;

    // Free list 순회 시작
    // 할당되지 않은 블록을 만날 때까지
    // 다음 가용 블록으로 포인터 이동 
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCCP(bp)){
        //만약 현재 블록의 크기가 요구하는 크기(asize)보다 크거나 같으면 => 적합한 블록 찾은 것.
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            // If a fit is found, return the address the of block pointer
            return bp;
        }
    }

    return NULL; /* No fit. 적합한 블록 찾지 못했다면 NULL 반환 */
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    //현재 블록을 가용 블록 리스트에서 제거 
    removeBlock(bp);
    // 분할이 가능한지 체크 
    if ((csize - asize) >= (2 * DSIZE)) 
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        putFreeBlock(bp); // 분할 하고 남은 할당 되지 않은 블록을 Free list에 추가함
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;

    
//     copySize = GET_SIZE(HDRP(oldptr));

//     if (size < copySize) // oldptr 사이즈가 새로 만들 newptr의 size보다 더 작은 경우
//       copySize = size;
      
//     //memcpy(destination, source, num)
//     memcpy(newptr, oldptr, copySize); // newptr 위치에 oldptr 주소로부터 copySize 만큼 복사하기 
//     mm_free(oldptr);
//     return newptr;
// }



// mm_realloc:  이미 할당 받은 메모리 블록의 크기 변경 
// ptr : mm_realloc 함수에서 재할당하고자 하는 메모리 블록의 포인터
// size를 통해서 지정한 크기로 해당 메모리 블록 확장/축소
void *mm_realloc(void *ptr, size_t size) {
    
    //ptr = NULL
    // -> 새로운 메모리 블록 할당
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    //size = 0이면 메모리 해제 후 NULL 반환
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr;
    void *newptr;
    size_t origin_size = GET_SIZE(HDRP(oldptr)); // 현재 블록의 실제 크기 (헤더에서 얻음)
    size_t new_size = size + 2*WSIZE; // 새로운 크기 (헤더와 푸터를 고려)

    // 새로 요구된 크기가 현재 블록의 크기와 같거나 작다면, 복사나 이동 필요 없음
    if (new_size <= origin_size) {
        return oldptr;
    } else {
        // 인접한 다음 블록의 크기를 현재 블록 크기에 추가
        size_t next_block_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 다음 블록의 크기
        size_t combined_size = origin_size + next_block_size; // 합쳐진 크기
        
        // 다음 블록이 가용 상태이고, 합쳐진 크기가 요구 사항을 만족할 경우
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (new_size <= combined_size)) {
            // 인접한 블록을 합치고, 새 크기로 재설정
            removeBlock(NEXT_BLKP(oldptr)); // 가용 블록 리스트에서 다음 블록 제거
            PUT(HDRP(oldptr), PACK(combined_size, 1)); // 새로운 합쳐진 크기와 할당 상태로 현재 블록의 헤더 업데이트
            PUT(FTRP(oldptr), PACK(combined_size, 1)); // footer도 업데이트
            return oldptr;
        } else {

            // 기존의 조건들을 만족하지 못할 경우, 충분한 공간이 없는 경우
            //새로운 블록 할당
            newptr = mm_malloc(size);
            // 메모리 할당 실패 시 NULL 반환
            if (newptr == NULL) {
                return NULL; 
            }
            
            // 새로운 메모리 블록에 이전 데이터 복사. 
            //복사할 데이터는 원본 크기와 새 크기 중 작은 값 사용
            if (origin_size > new_size) {
                origin_size = new_size;
            }
            memcpy(newptr, oldptr, origin_size - 2*WSIZE); //헤더와 푸터를 제외한 데이터만 복사
            mm_free(oldptr); // 기존 블록 해제
            return newptr; // 새로 할당된 블록 포인터 반환
        }
    }
}



////////////////////////////////////////////////////////////////////////

// 새로 반환되거나 생성된 Free 블록을 가용리스트 맨 앞에 추가함.
void putFreeBlock(void *bp){
    PREDP(bp) = NULL;
    SUCCP(bp) = free_listp;
    PREDP(free_listp) = bp;
    free_listp = bp;
}

// 가용 리스트에서 특정 블록 제거 
void removeBlock(void *bp){

    // Free list의 첫번째 블록을 없앨 때
    if (bp == free_listp){
        PREDP(SUCCP(bp)) = NULL;
        free_listp = SUCCP(bp);
    }
    // Free list 안에서 없앨 때
    else{
        SUCCP(PREDP(bp)) = SUCCP(bp);
        PREDP(SUCCP(bp)) = PREDP(bp);
    }
}
