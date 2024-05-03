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
    //현재 블록의 헤더로 이동해서 GET_SIZE 매크로를 사용해서 블록의 크기를 가져와서
    //현재 블록의 시작 주소 + 현재 블록의 크기 => 다음 블록을 가리키도록.
//PREV_BLKP: 이전 블록의 bp
    //GET_SIZE(((char *)(bp) - DSIZE)) : 이전 블록의 푸터에서 size 정보를 가져와서 
    //현재  블록 시작 주소에서 이전 블록의 크기를 빼서 이전 블록의 시작 주소를 구함
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
    // 4*WSIZE, 16 바이트 힙에 추가. 실패하면 -1 반환
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
        return -1;
    }

    // 전체 힙 초기화 과정
    // 빈 공간 + 프롤로그 헤더 + 프롤로그 푸터 + 에필로그 헤더
    // double word 정렬 (8 바이트) 

    PUT(heap_listp, 0);// 미사용 패딩 -> 
    //미사용 패딩을 사용해야 prologue block 뒤의 실제 데이터 블록들이 8의 배수로 정렬될 수 있다.
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //Prologue header 8 byte
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //Prologue footer 8 byte
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //Epilogue header 힙의 끝

    //늘 Prologue block을 가리키도록 포인터 이동 - 프롤로그 블록의 헤더 바로 뒤로 이동
    heap_listp += (2*WSIZE);

    /*Extend the empty heap with a free block of CHUNKSIZE bytes*/
    //CHUNKSIZE 만큼 힙 확장, 실패하면 -1 반환
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    
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


/* Coalesce*/
// free block을 앞 뒤 free block과 연결하고,
// 연결된 free block의 시작 주소를 리턴
static void *coalesce (void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));//직전 블록 Footer에서의 alloc 여부 확인 (0: free, 1: allocated)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));//직후 블록 header에서의 alloc 여부 확인
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록의 크기를 가져옴

    //CASE 1. 이전과 다음 블록 모두 할당된 상태 -> 연결 불가. 현재 블록 변화 없음
    if (prev_alloc && next_alloc) {
        last_bp = bp;
        return bp;
    }

    //CASE2 이전 블록 allocated, 다음 블록 free인 상태
    else if (prev_alloc && !next_alloc) {
        //다음 블록과 현재 블록 합침
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //현재 블록 size + 다음 블록의 size
        PUT(HDRP(bp), PACK(size, 0)); //header : a -> free
        PUT(FTRP(bp), PACK(size, 0)); //footer : a -> free 업데이트
        // bp는 변경할 필요 없음
    }

    //CASE 3 이전 블록 free, 다음 블록 allocated
    //이전 블록과 현재 블록을 합침
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //현재 블록 size에 이전 블록 size 더하기  
        PUT(FTRP(bp), PACK(size, 0)); //footer : a-> free 갱신 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 Size, a->free로 갱신
        bp = PREV_BLKP(bp); // 블록 포인터를 직전 블록으로 이동
    }

    //CASE4 이전, 다음 블록 모두 free
    //이전 블록과 다음 블록 모두 현재 블록과 합침
    else {
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + 
            GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        //이전 블록의 Footer, 다음 블록의 header에서 size가져와서 더함
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //직전 블록의 header 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); //다음 블록의 footer 업데이트
        bp = PREV_BLKP(bp); // bp를 이전 블록으로 이동
    }
    // coalesce 이후, 
    // bp를 저장하여 추후 활용
    last_bp = bp;
    return bp; 
    //새로운 시작 주소 리턴
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
/*brk 포인터 증가시켜서 블록 할당. 항상 정렬하는 배수 크기의 블록을 할당함*/

//사용자가 요청한 크기의 메모리 블록 할당, 할당된 블록의 포인터 반환
//가용 블록 목록에서 적절한 공간 찾아서 할당, 필요한 경우에는 heap 확장해서 추가 공간 확보
void *mm_malloc(size_t size)
{
    size_t asize; //조정된 블록 size
    size_t extendsize; // 메모리 할당할 자리가 없을 때 힙 확장할 크기
    char *bp;

    /*Ignore spurious requests*/
    //크기가 0인 할당요청은 무시함
    if (size == 0) {
        return NULL;
    }
    
    /*Adjust block size to include overhead and alignment reqs*/
     //요청 받은 크기가 8바이트(double word) 보다 작으면 asize를 16바이트로 만듦
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
    //할당할 영역이 없는 경우, 메모리 (힙 영역)을 확장하기
    extendsize = MAX(asize, CHUNKSIZE);
    //힙 확장. 확장 실패시 return NULL 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    
    place(bp, asize); //확장된 곳에 블록 할당
    last_bp = bp; //마지막으로 할당된 블록 포인터 Update
    return bp;
}



// // first_fit 
// 힙에서 처음부터 검색하여 요청한 크기 이상, free인 첫 번째 블록을 찾음

// static void *find_fit(size_t asize){
//     void *bp;
//     //heap_listp에서 시작해서 힙의 끝까지 탐색
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         //현재 블록이 할당되지 않았으며, 
//         //요구되는 크기 (asize) 보다 크거나 같으면 
//         //조건에 맞는 블록을 찾아서 포인터 반환
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             return bp;
//         }
//     }

//     return NULL; /*NO fit이면 NULL 반환*/
// }


// //Next_fit: 이전 할당 작업에서 사용된 지점부터 탐색 시작! 
// 2개의 반복문 
// 1) last_bp에서 시작하여 힙의 끝 부분 탐색 
    //:적절한 크기의 Free 블록 찾으면 Last_bp = 현재 블록으로 업데이트, bp 반환
// 2) 첫 반복문에서 적절한 블록을 찾지 못했으면 힙의 시작 부분 heap_listp에서 last_p까지 다시 탐색

// next_fit이 점수가 제일 좋다.

static void *find_fit(size_t asize) {
    char *bp = last_bp; // 마지막으로 참조된 bp
    
    //이전에 참조된 블록이 없는 경우, 
    // Heap의 시작 지점을 할당
    if (last_bp == NULL) {
        last_bp = heap_listp;
    }

    //1. 마지막으로 참조된 bp에서부터 리스트의 끝까지 탐색
    //last_bp에서 시작하여, 
    //힙의 끝에 도달할 때까지 -> GET_SIZE(HDRP(bp)) > 0 이 False가 될 때까지
    //bp를 NEXT_BLKP(bp) -> bp를 다음 블록으로 이동시키겠음.
    for (bp = last_bp; GET_SIZE(HDRP(bp)) >0; bp = NEXT_BLKP(bp)) {
        // 가용 상태이고, 요청된 크기보다 크거나 작은 블록을 찾았으면
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp; //현재 블록을 마지막으로 참조된 블록으로 update
            return bp;
        }
    }

    //2. 리스트의 시작부터, 
    //마지막 할당 위치까지 탐색
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0 && last_bp > bp; bp = NEXT_BLKP(bp)){
    // for (bp = heap_listp; bp <= last_bp ; bp = NEXT_BLKP(bp)) {
        //가용 상태이고, 요청된 크기보다 크거나 같은 블록 찾았으면
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL; //적절한 블록을 찾지 못했으면 NULL 반환
}


// Best_fit: 요청된 크기와 가장 잘 맞는 블록을 찾아서 할당하는 방식.
// 메모리 낭비 최소화  but 매번 적절한 블록을 찾기 위해 전체 힙을 탐색 -> 시간 길어짐
// static void *find_fit(size_t asize){
//     void *bp;

//     void *best_fit = NULL; // 가장 적합한 블록을 저장할 포인터
//     size_t smallest_diff = ~0; // 가장 작은 차이값 -> 초기화를 위해 최대값으로 설정(비트 NOT 연산자 이용)

//     // 힙 전체를 순회
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         size_t current_size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기
        
//         //현재 블록이 할당되지 않았고, 요청된 크기보다 크거나 같을 때
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= current_size)) {
//             //현재 블록크기와 요청 크기의 차이
//             size_t diff = current_size - asize;

//             //이 차이가 현재까지 발견한 가장 작은 차이보다 작다면
//             if (diff < smallest_diff) {
//                 best_fit = bp; // 현재 블록을 최적 블록으로 설정
//                 smallest_diff = diff; // 가장 작은 차이값 update
//             }
//         }
//     }
//     // 가장 적합한 블록 봔환, 못찾았다면 NULL
//     return best_fit;
// }

// BEST_FIT
// // asize에 가장 적합한 가용 블록 찾아서 반환
// static void *find_fit(size_t asize) {
//     void *bp; 
//     void *best_fit = NULL; // 가장 적합한 블록을 가리키는 포인터

//     //힙의 모든 블록 탐색
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         //현재 블록이 할당되지 않았고, 요청한 크기보다 크거나 같은 경우
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             //아직 best fit이 선택되지 않은 경우 (루프 처음 돌 때)
//             // || 현재 블록의 크기가 best_fit으로 선택된 블록의 크기 보다 작을 떄 best_fit update
//             if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))) {
//                 best_fit = bp;
//             }
//         }
//     }
//     return best_fit;
// }





/*place*/
// 메모리 블록(bp)에 요청된 크기(asize)로 데이터 할당
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); //현재 블록의 크기

    //현재 블록의 크기 - 선택한 가용 블록 크기 
    //차이가 16보다 같거나 크면 -> 분할이 가능함 
    if ((csize - asize) >= (2*DSIZE)) {
        //앞 블록은 할당 블록으로 
        PUT(HDRP(bp), PACK(asize,1 )); // 현재 블록 헤더 설정
        PUT(FTRP(bp), PACK(asize,1 )); // 현재 블록 푸터 설정

        //현재 블록을 할당 블록과 나머지 가용 블록으로 분할
        bp = NEXT_BLKP(bp);

        //남은 가용 블록의 헤더와 푸터 설정 
        // 크기는 csize-asize, 가용 상태는 0
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize , 0));
    } else {
        //분할이 불가능하면 전체 블록을 할당상태로 변경
        //현재 블록 전체를 요청 받은 크기로 할당함
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

    //-> 연결할 수 있으면 연결해준다.
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 이미 할당된 메모리 블록(ptr)의 크기를 새로운 크기(size)로 조정
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr; // 이전에 할당된 메모리 블록 포인터 
//     void *newptr; // 새로 할당될 메모리 블록의 포인터 
//     size_t copySize;
    
//     newptr = mm_malloc(size); //새로운 크기의 메모리 블록 할당

//     //새로운 크기의 메모리 할당 실패시 NULL 반환    
//     if (newptr == NULL)
//       return NULL;

//     copySize = GET_SIZE(HDRP(oldptr)); //이전 메모리 블록의 실제 크기 가져옴
//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);


//     // 요청한 새 크기가 이전 크기 보다 작은 경우, 
//     // 복사할 크기를 새 크기로 조정
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize); // 이전 메모리 블록에서 새 메모리 블록으로 데이터 복사
//     mm_free(oldptr); //이전 메모리 블록 해제

//     return newptr; //새로 할당된 메모리 블록의 포인터 반환
// }



void *mm_realloc(void *ptr, size_t size){

    void *oldptr = ptr; // 이전에 할당된 메모리 블록 가리키는 포인터
    void *newptr; //새로 할당할 메모리 블록의 포인터

    size_t origin_size = GET_SIZE(HDRP(oldptr)); //기존 메모리 블록 크기
    size_t new_size = size + DSIZE; // 요청된 새로운 크기에 header, footer 사이즈 추가

    // 새로 요청된 크기가 원래 메모리 블록 크기보다 작거나 같으면
    // 재할당 없이 기존 포인터 반환
    if (new_size <= origin_size){
        return oldptr;
    }
    else {
        //인접한 다음 메모리 블록의 크기를 현재 블록에 더함
        size_t add_size = origin_size + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
        
        //다음 블록이 할당되지 않았고,
        //합친 크기가 새로운 크기를 수용할 수 있으면
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (new_size <= add_size)) {
            //현재 블록과 인접한 블록 합친 후 새 크기로 설정
            PUT(HDRP(oldptr), PACK(add_size, 1));
            PUT(FTRP(oldptr), PACK(add_size, 1));
            return oldptr;
        }
        else {
            //위의 경우에 해당하지 않으면 새로운 메모리 할당
            newptr = mm_malloc(new_size);
            if (newptr == NULL){
                return NULL; // 메모리 할당 실패시 NULL 반환
            }
            //새로운 메모리에 이전 데이터 복사, 원본 크기와 새 크기 중 작은 값으로 복사 진행
            memmove(newptr, oldptr, new_size);
            mm_free(oldptr); // 이전 메모리 블록 해제
            return newptr; // 새로운 메모리 블록 포인터 반환
        }
    }
}













