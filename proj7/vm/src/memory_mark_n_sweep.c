#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "memory.h"
#include "fail.h"
#include "engine.h"

#if GC_VERSION == GC_MARK_N_SWEEP

static void* memory_start = NULL;
static void* memory_end = NULL;

static uvalue_t* bitmap_start = NULL;

static value_t* heap_start = NULL;
static value_t* heap_end = NULL;
static value_t heap_start_v = 0;
static value_t heap_end_v = 0;
static value_t* heap_first_block = NULL;

#define FREE_LISTS_COUNT 32
static value_t* free_list_heads[FREE_LISTS_COUNT];

#define MIN_BLOCK_SIZE 1
#define HEADER_SIZE 1

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

// Bitmap management

static int bitmap_is_bit_set(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  return (bitmap_start[word_index] & ((uvalue_t)1 << bit_index)) != 0;
}

static void bitmap_set_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] |= (uvalue_t)1 << bit_index;
}

static void bitmap_clear_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] &= ~((uvalue_t)1 << bit_index);
}

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Free lists management

static value_t real_size(value_t size) {
  assert(0 <= size);
  return size < MIN_BLOCK_SIZE ? MIN_BLOCK_SIZE : size;
}

static unsigned int free_list_index(value_t size) {
  assert(0 <= size);
  return size >= FREE_LISTS_COUNT ? FREE_LISTS_COUNT - 1 : (unsigned int)size;
}

char* memory_get_identity() {
  return "mark & sweep garbage collector";
}

void memory_setup(size_t total_byte_size) {
  memory_start = malloc(total_byte_size);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = (char*)memory_start + total_byte_size;
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);

  memory_start = memory_end = NULL;
  bitmap_start = NULL;
  heap_start = heap_end = NULL;
  heap_start_v = heap_end_v = 0;
  for (int l = 0; l < FREE_LISTS_COUNT; ++l)
    free_list_heads[l] = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* ptr) {
  assert(memory_start <= ptr && ptr < memory_end);

  const size_t bh_size =
    (size_t)((char*)memory_end - (char*)ptr) / sizeof(value_t);

  const size_t bitmap_size = (bh_size - 1) / (VALUE_BITS + 1) + 1;
  const size_t heap_size = bh_size - bitmap_size;

  bitmap_start = ptr;
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));

  heap_start = (value_t*)bitmap_start + bitmap_size;
  heap_end = heap_start + heap_size;
  assert(heap_end == memory_end);

  heap_start_v = addr_p_to_v(heap_start);
  heap_end_v = addr_p_to_v(heap_end);

  heap_first_block = heap_start + HEADER_SIZE;
  const value_t initial_block_size = (value_t)(heap_end - heap_first_block);
  heap_first_block[-1] = header_pack(tag_None, initial_block_size);
  heap_first_block[0] = 0;

  for (int l = 0; l < FREE_LISTS_COUNT - 1; ++l)
    free_list_heads[l] = memory_start;
  free_list_heads[FREE_LISTS_COUNT - 1] = heap_first_block;
}

/*
==================HELPERS====================
*/
int inheap(value_t *block) {
  return (heap_start <= block && block < heap_end);
}

static void print_all_fl() {
  for (int i = 0; i < FREE_LISTS_COUNT; i++) {
    value_t * head = free_list_heads[i];
    printf("list %d ", i);
    while (1) {
      if (head == memory_start) {
        printf(" => mem_start");
        break;
      }
      printf(" => [ %d ]", memory_get_block_size(head));
      head = addr_v_to_p(head[0]);
    }
    printf("\n");
  }
}

static void print_heap() {
  value_t * head = heap_start;
  int i = 0;
  printf("~~~~~ heap ~~~~~\n");
  while (inheap(head)) {
    if (bitmap_is_bit_set(head)) printf("[ %d *] ", memory_get_block_size(head));
    else printf("[ %d ] ", memory_get_block_size(head));
    head = head + memory_get_block_size(head) + HEADER_SIZE;
    i++;
    if (i % 10 == 0) printf("\n");
  }
  printf("\n~~~~~~~~~~~~~~~~\n");
}

static value_t * split_block(value_t * block, value_t requested_size, value_t cur_b_size, int ishead) {
  if (!(heap_start <= block && block < heap_end)) return NULL;
  value_t remaining_size = cur_b_size - requested_size - HEADER_SIZE;
  value_t * leftover = block + requested_size + HEADER_SIZE;
  assert(inheap(leftover));
  assert(remaining_size >= MIN_BLOCK_SIZE);
  leftover[-1] = header_pack(tag_None, remaining_size);
  block[-1] = header_pack(tag_None, requested_size);
  
  if (ishead)
    free_list_heads[free_list_index(cur_b_size)] = addr_v_to_p(block[0]);

  //add leftover to respective FL
  value_t l_index = free_list_index(remaining_size);
  leftover[0] = addr_p_to_v(free_list_heads[l_index]);
  free_list_heads[l_index] = leftover;
  assert(heap_start <= block && block < heap_end);

  return block;
}

value_t find_index(value_t rs) {
  value_t index = free_list_index(rs); //1~30 for block sizes of 2~31; 31 for bigger blocks; 0 is not used

  if (free_list_heads[index] != memory_start) return index;

  index = rs + MIN_BLOCK_SIZE + HEADER_SIZE; // pad the block so the remainder is also a viable block for allocations
  while (index < FREE_LISTS_COUNT) { //check all the list heads
    if (free_list_heads[index] != memory_start)return index;
    index += HEADER_SIZE;
  }
  return -1; //there is no free block
}

/*
==================HELPERS END====================
*/
static value_t* allocate(tag_t tag, value_t size) {
  printf("====== Allocating block size %d ======\n", size);
  //print_all_fl();
  //print_heap();
  assert(0 <= size);
  value_t * ptr;
  value_t rs = real_size(size);
  value_t index = find_index(rs);

  if (index == -1) return NULL; //no available free list found
  value_t * head = free_list_heads[index]; //found head for potential allocation
  value_t * prev = memory_start;
  value_t current_block_size = memory_get_block_size(head);
  //printf("Found block size of %d under index %d\n", current_block_size, index);
  int ishead = 1;

  if (index == FREE_LISTS_COUNT - 1) { //fell under last list
    int found = 0;

    while (inheap(head) && head != memory_start) { //traverse free list
      if(current_block_size == rs || current_block_size > rs + MIN_BLOCK_SIZE){
        found = 1;
        break;
      }
      ishead = 0;
      prev = head;
      head = addr_v_to_p(head[0]);
      current_block_size = memory_get_block_size(head);
    }
    if (!found) return NULL; //couldn't find

    if (rs == current_block_size && ishead) {
      ptr = head;
      ptr[-1] = header_pack(tag, rs);
      free_list_heads[index] = addr_v_to_p(head[0]);
    } else if (rs == current_block_size && !ishead) {
      ptr = head;
      ptr[-1] = header_pack(tag, rs);
      prev[0] = head[0];
    } else { //blocksize is bigger
      if (ishead) {
        ptr = split_block(head, rs, current_block_size, 1);
      } else {
        ptr = split_block(head, rs, current_block_size ,0);
        prev[0] = head[0];
      }
    }
  } else { //not last list
    if (index == rs) { //if the size is same in list <31, must be head
      ptr = head;
      ptr[-1] = header_pack(tag, rs);
      free_list_heads[index] = addr_v_to_p(head[0]);
    } else {
      ptr = split_block(head, rs, current_block_size, 1);
    }
  }

  bitmap_set_bit(ptr);
  if (size == 0) ptr[-1] = header_pack(tag, size);
  printf("===== after alloc =====\n");
  // print_all_fl();
  // print_heap();
  return ptr;
}

static void mark(value_t* block) {
  // TODO
  if (heap_start <= block && block < heap_end) {
    value_t size = real_size(memory_get_block_size(block));
    bitmap_clear_bit(block);
    for (int i = 0; i < size; i++) { //check the block's content
      value_t v_ptr = block[i];
      if (!(v_ptr & 0b0011)) { //if it's a valid pointer,
        value_t * addr = addr_v_to_p(v_ptr);
        if ((heap_start <= addr && addr < heap_end) && bitmap_is_bit_set(addr)) //mark if it's still alive
          mark(addr);
      }
    }
  } else {
    return;
  }
}

// SWEEEEEEEEEEP
static void sweep() {
  //print_all_fl();
  printf("sweeping...\n");
  //dump everything out of free list
  for (int i = 0; i < FREE_LISTS_COUNT - 1; ++i) {
    value_t * head = free_list_heads[i];
    while (head != memory_start && inheap(head)) {
      bitmap_set_bit(head);
      head = addr_v_to_p(head[0]);
    }
    free_list_heads[i] = memory_start;
  }
  //print_all_fl();

  value_t * ptr = heap_start;
  value_t * prev = heap_start;
  value_t free_index = 0;
  int can_coalesce = 0;
  while (ptr != heap_end) {
    // printf("===== while loooooooooooop iteration =====\n");
    // printf("ptr size %d\n", memory_get_block_size(ptr));
    // printf("prev size %d\n", memory_get_block_size(prev));
    // print_heap();
    
    if (!inheap(ptr)) ptr = memory_end;
    else {
      value_t ptr_size = real_size(memory_get_block_size(ptr));
      
      if (!bitmap_is_bit_set(ptr)) { //still alive
        can_coalesce = 0;
        bitmap_set_bit(ptr); //set bit 
      } else {
        bitmap_clear_bit(ptr);
        if (can_coalesce) {
          //free_list_heads[free_index] = addr_v_to_p(prev[0]);
          value_t p_size = real_size(memory_get_block_size(prev));
          ptr_size = p_size + ptr_size + 1;
          prev[-1] = header_pack(tag_None, ptr_size);
          ptr = prev;
        }
        prev = ptr;
        free_index = free_list_index(real_size(memory_get_block_size(prev)));
        can_coalesce = 1;
      }
      ptr = ptr + HEADER_SIZE + ptr_size;
    }
  }
  //after this, bit set ones are alloced, bit cleared ones are free to be added
  printf("== COALESCING IS DONE ==\n\n");
  //print_heap();
  ptr = heap_start;
  while (inheap(ptr)) {
    //print_all_fl();
    //printf("\n");
    value_t ptr_size = real_size(memory_get_block_size(ptr));
    value_t index = free_list_index(ptr_size);
    if (!bitmap_is_bit_set(ptr)) {
      //for (int i = 0; i < ptr_size; i++) ptr[i] = memory_start;
      ptr[0] = addr_p_to_v(free_list_heads[index]);
      free_list_heads[index] = ptr;
    }
    ptr = ptr + HEADER_SIZE + ptr_size;
  }
  //print_heap();
  //print_all_fl();
}

value_t* memory_allocate(tag_t tag, value_t size) {
  value_t* first_try = allocate(tag, size);
  if (first_try != NULL)
    return first_try;

  value_t* lb = engine_get_Lb();
  if (lb != memory_start) mark(lb);
  value_t* ib = engine_get_Ib();
  if (ib != memory_start) mark(ib);
  value_t* ob = engine_get_Ob();
  if (ob != memory_start) mark(ob);

  sweep();

  value_t* second_try = allocate(tag, size);
  if (second_try != NULL)
    return second_try;

  fail("\ncannot allocate %d words of memory, even after GC\n", size);
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}

#endif
