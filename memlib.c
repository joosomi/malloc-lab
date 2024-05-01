/*
 * memlib.c - a module that simulates the memory system.  Needed because it 
 *            allows us to interleave calls from the student's malloc package 
 *            with the system's malloc package in libc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>

#include "memlib.h"
#include "config.h"

/* private variables */
static char *mem_start_brk;  /* points to first byte of heap 힙의 첫 바이트를 가리키는 변수*/
static char *mem_brk;        /* points to last byte of heap  힙의 마지막 바이트를 가리키는 변수*/
/*여기다가 mem_sbrk함수를 이용해서 새로운 사이즈의 힙으로 */
static char *mem_max_addr;   /* largest legal heap address 힙 최대 크기의 주소를 가리키는 변수 */

/* 
 * mem_init - initialize the memory system model
 */
// config.h => MAX_HEAP 20 MB
// 최대 힙 메모리 공간을 할당 받고 초기화
void mem_init(void)
{
    /* allocate the storage we will use to model the available VM */
    if ((mem_start_brk = (char *)malloc(MAX_HEAP)) == NULL) {
	fprintf(stderr, "mem_init_vm: malloc error\n"); // 동적할당 실패 시 에러 메시지
	exit(1);
    }

    mem_max_addr = mem_start_brk + MAX_HEAP;  /* max legal heap address */
    mem_brk = mem_start_brk;                  
    /* heap is empty initially, 아직 힙이 비어있음. 
    mem_brk와 mem_start_brk는 같다.*/
}

/* 
 * mem_deinit - free the storage used by the memory system model
 */
void mem_deinit(void)
{
    free(mem_start_brk);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
void mem_reset_brk()
{
    mem_brk = mem_start_brk;
}

/* 
 * mem_sbrk - simple model of the sbrk function. Extends the heap 
 *    by incr bytes and returns the start address of the new area. In
 *    this model, the heap cannot be shrunk.
 *  byte 단위로 힙을 늘려주고, 새 메모리의 시작 주소를 Return
 *  이 모델에서는 힙은 줄어들 수 없음.
 */
void *mem_sbrk(int incr) // incr -> byte 형태로 받음
{
    char *old_brk = mem_brk;


    //만약 incr < 0 이거나 최대 힙 사이즈를 벗어나게 된다면 에러 처리 -1 return
    if ( (incr < 0) || ((mem_brk + incr) > mem_max_addr)) {
	errno = ENOMEM;
	fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
	return (void *)-1;
    }
    mem_brk += incr; 
    return (void *)old_brk; // 새로 늘어난 힙의 시작 주소이기 때문에 old_brk 리턴
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo()
{
    return (void *)mem_start_brk;
}

/* 
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi()
{
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize() 
{
    return (size_t)(mem_brk - mem_start_brk);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize()
{
    return (size_t)getpagesize();
}
