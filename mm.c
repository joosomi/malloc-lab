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
// double word 정렬
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// 입력된 size를 정해진 ALIGNMENT의 배수로 올림

//예시) 
/* size = 7, ALIGNMENT = 8
15 & (~0x7) => 00001111 & 11111000 => 00001000 => 7과 가장 가까운 8의 배수 8
*/
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


/*size_t : unsigned int 대부분 32bit system - 4byte, 64bit system - 8byte*/
// ALIGN(sizeof(4byte)) => 8 
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

////Basic constatns and macros 
// 1 word : 4byte, double word: 8byte 상수로 정의 
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
#define PUT(p, val) (*(unsigned int *)(p) = (val)) //주소 p가 가리키는 워드에 val을 저장하는 함수 PUT

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
// 
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


//global variable & functions
static void *heap_listp;  // 항상 프롤로그 블록을 가리키는 Static 전역 변수
static char *last_bp; // 마지막으로 검색한 블록을 추적하는 static 전역 변수

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);


static void *extend_heap(size_t words);
static void *coalesce (void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);



/* 
 * mm_init - initialize the malloc package.
 */
//초기화된 빈 힙
int mm_init(void)
{   
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
        return -1;
    }

    // 전체 힙
    // 빈 공간 + 프롤로그 헤더 + 프롤로그 푸터 + 에필로그 헤더
    PUT(heap_listp, 0);// 미사요 패딩 -> 
    //미사용 패딩을 사용해야 prologue block 뒤의 실제 데이터 블록들이 8의 배수로 정렬될 수 있다.
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //Epilogue header

    //늘 Prologue block을 가리키도록 포인터 이동
    heap_listp += (2*WSIZE);

    /*Extend the empty heap with a free block of CHUNKSIZE bytes*/
    //CHUNKSIZE 만큼 힙 확장 
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    
    return 0;
}


//extend_heap
static void *extend_heap(size_t words){
    char * bp;
    size_t size;

    /*Allocate an even number of words to maintain alignment*/
    //더블 워드 정렬>
    //size = 힙의 총 byte 수
    //word 홀수라면 짝수로 만들고 * WSIZE(4) => 블록의 크기 결정
    //짝수라면 그냥 words * WSIZE
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    /*Initialize free block header/footer and the epilogue header*/
    PUT(HDRP(bp), PACK(size, 0)); /*Free block header*/
    PUT(FTRP(bp), PACK(size, 0)); /*Free block footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /*New epilogue header*/
    // 헤더는 항상 size = 0, alloc = 1

    /*Coalesce if the previous block was free*/
    return coalesce(bp);
}


/* Coalesce*/
// free block을 앞 뒤 free block과 연결하고,
// free block의 주소를 리턴
static void *coalesce (void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));//직전 블록 Footer에서의 alloc 정보
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));//직후 블록 header에서의 alloc 정보
    size_t size = GET_SIZE(HDRP(bp));

    //CASE 1. 이전과 다음 블록 모두 할당된 상태 -> 연결 불가 
    if (prev_alloc && next_alloc) {
        last_bp = bp;
        return bp;
    }

    //CASE2 이전 블록 allocated, 다음 블록 free
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //현재 블록 size + 다음 블록의 size
        PUT(HDRP(bp), PACK(size, 0)); //header : a -> free
        PUT(FTRP(bp), PACK(size, 0)); //footer : a -> free 갱신 
        // bp는 변경할 필요 없음
    }

    //CASE 3 이전 블록 free, 다음 블록 allocated
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //현재 블록 size에 직전 블록 size 더하기  
        PUT(FTRP(bp), PACK(size, 0)); //footer : a-> free 갱신 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 Size, a->free로 갱신
        bp = PREV_BLKP(bp); // 블록 포인터를 직전 블록으로 이동
    }

    //CASE4 이전, 다음 블록 모두 free
    else {
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + 
            GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        //이전 블록의 Footer, 다음 블록의 header에서 size가져와서 더함
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //직전 블록의 header값 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); //다음 블록의 footer 값 갱신
        bp = PREV_BLKP(bp); // bp 직전 블록으로 이동
    }
    last_bp = bp;
    return bp;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; //조정된 블록 size
    size_t extendsize; // 메모리 할당할 자리가 없을 때 힙을 연장할 크기
    char *bp;

    /*Ignore spurious requests*/
    if (size == 0) {
        return NULL;
    }
    
    /*Adjust block size to include overhead and alignment reqs*/
     //size가 8바이트(double word) 보다 작으면 asize를 16바이트로 만듦
     //최소 블록 크기 16 바이트 할당 ( 헤더 4, 푸터 4, 저장공간 8)
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
   //요청받은 크기가 8바이트 보다 크다면
   //
    else {
        //8의 배수로 올림 처리
        asize = DSIZE * ((size + (DSIZE) + (DSIZE -1)) / DSIZE);
    }


    /*Search the free list for a fit */
    // 할당할 수 있는 가용 영역이 있다면
    if ((bp = find_fit(asize)) != NULL ) {
        place(bp, asize); //할당
        return bp; //새로 할당된 블록의 포인터 return
    }

    /*No fit found. Get more memory and place the block*/
    //할당할 영역이 없는 경우, 힙 영역을 확장하기
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}




// // first_fit 
// static void *find_fit(size_t asize){
//     void *bp;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             return bp;
//         }
//     }

//     return NULL; /*NO fit*/
// }


// //Next_fit
static void *find_fit(size_t asize) {
    char *bp = last_bp;
    

    if (last_bp == NULL) {
        last_bp = heap_listp;
    }

    for (bp = last_bp; GET_SIZE(HDRP(bp)) >0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp))> 0 ; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}


// // Best_fit
// static void *find_fit(size_t asize){
//     void *bp;

//     void *best_fit = NULL;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))) {
//                 best_fit = bp;
//             }
//         }
//     }
//     return best_fit;
// }



/*Free*/
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); //현재 블록의 크기


    //현재 블록의 크기 - 선택한 가용 블록 
    //차이가 16보다 같거나 크면 
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize,1 ));
        PUT(FTRP(bp), PACK(asize,1 ));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize , 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    //만약 앞 뒤 블록이 둘 다 free라면 연결
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr; // 이전 포인터 
//     void *newptr; // 새로운 메모리 할당할 포인터 
//     size_t copySize;
    
//     newptr = mm_malloc(size);
    
//     if (newptr == NULL)
//       return NULL;
//     copySize = GET_SIZE(HDRP(oldptr));
//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }



void *mm_realloc(void *ptr, size_t size){

    void *oldptr = ptr; // 이전 포인터
    void *newptr; //새로운 메모리 할당할 포인터

    size_t origin_size = GET_SIZE(HDRP(oldptr));
    size_t new_size = size + DSIZE;

    if (new_size <= origin_size){
        return oldptr;
    }
    else {
        size_t add_size = origin_size + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (new_size <= add_size)) {
            PUT(HDRP(oldptr), PACK(add_size, 1));
            PUT(FTRP(oldptr), PACK(add_size, 1));
            return oldptr;
        }
        else {
            newptr = mm_malloc(new_size);
            if (newptr == NULL){
                return NULL;
            }
            memmove(newptr, oldptr, new_size);
            mm_free(oldptr);
            return newptr;
        }
    }


}













