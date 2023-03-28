# Malloclab
I implemented the C standard library of malloc and related functions. 

<h2>Data Organization</h2>
This implementation features a segregated free list, which poses higher throughout and greater memory utilization than a free list. The segregated list is an array of free lists (implemented bylinked lists), categorizing blocks by block size of powers of 2. 

Each block is denoted by a struct

- Contains the payload, metadata and tag, and pointer to previous and next blocks

<h2>Library Main Functions</h2>

<i>mm_init: </i>Initializes the empty heap, prologue, and epilogue

<i>mm_malloc: </i>Places block with first fit; extends heap if more memory required; returns null if unable to place

<i>mm_free: </i> Frees block and coalesces


<h2>Library Auxillary Functions</h2>

<i>mm_extendheap: </i>Extends memory as allowed by mem_sbrk(); creates new epilogue; forms new free block and coalesces

<i>mm_place: </i>Replaces free block with memory block

<i>mm_coalesce: </i> Coalesces free blocks according to 3 coalescing scenarios

<i>find_fit: </i> Employs first fit search in segregated list

