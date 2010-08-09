/* Simple memory allocator and garbage collector. */
#include "libvex_basictypes.h"
#include "libvex.h"

#include "main_globals.h"
#include "main_util.h"

void dump_heap(void);

/* The main arena. */
#define N_TEMPORARY_BYTES 4000000
static HChar temporary[N_TEMPORARY_BYTES] __attribute__((aligned(8)));

/* Each allocation in the arena is prefixed by an allocation header. */
struct alloc_header {
  const VexAllocType *type; /* Or NULL for free blocks */
  unsigned size; /* Includes header */
  unsigned flags;
#define ALLOC_FLAG_GC_MARK 1
  const char *file;
  unsigned line;
};

#define NR_GC_ROOTS 128
static unsigned nr_gc_roots;
static void **gc_roots[NR_GC_ROOTS];
static unsigned long heap_used;
static struct alloc_header *allocation_cursor;

static void *
header_to_alloc(struct alloc_header *ah)
{
  return ah + 1;
}

static struct alloc_header *
alloc_to_header(const void *x)
{
  return (struct alloc_header *)(void *)x - 1;
}

static struct alloc_header *
first_alloc_header(void)
{
  return (struct alloc_header *)temporary;
}

static struct alloc_header *
next_alloc_header(struct alloc_header *h)
{
  struct alloc_header *maybe = (struct alloc_header *)((unsigned long)h + h->size);
  if ( (unsigned long)maybe >= (unsigned long)temporary + N_TEMPORARY_BYTES )
    return NULL;
  return maybe;
}

static void
gc_visit(const void *what)
{
  struct alloc_header *what_header;

  if (!what)
    return;
  what_header = alloc_to_header(what);
  vassert(what_header->type != NULL); /* Shouldn't be visiting free memory... */
  if (what_header->flags & ALLOC_FLAG_GC_MARK)
    return;
  what_header->flags |= ALLOC_FLAG_GC_MARK;
  if (what_header->type->gc_visit)
    what_header->type->gc_visit(what, gc_visit);
}

static void
poison(void *start, unsigned nr_bytes, unsigned pattern)
{
  unsigned x;
  for (x = 0; x < nr_bytes / 4; x++)
    ((unsigned *)start)[x] = pattern;
}

static void
do_gc(void)
{
  unsigned x;
  struct alloc_header *h;
  struct alloc_header *p;
  struct alloc_header *n;

  zap_cache();

  for (h = first_alloc_header(); h; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
  for (x = 0; x < nr_gc_roots; x++)
    gc_visit(*gc_roots[x]);

  allocation_cursor = NULL;
  h = first_alloc_header();
  p = NULL;
  while (h) {
    n = next_alloc_header(h);
    if (h->type && !(h->flags & ALLOC_FLAG_GC_MARK)) {
      /* We're going to free off this block. */
      heap_used -= h->size;
      if (h->type->destruct)
	h->type->destruct(header_to_alloc(h));
      h->type = NULL;
      poison(h + 1, h->size - sizeof(*h), 0xa1b2c3d4);
      if (p && !p->type) {
	p->size += h->size;
	if (n && !n->type) {
	  p->size += n->size;
	}
	n = next_alloc_header(p);
	h = p;
      } else if (n && !n->type) {
	h->size += n->size;
	n = next_alloc_header(h);
      }
      if (!allocation_cursor || allocation_cursor->size < h->size)
	allocation_cursor = h;
    }

    p = h;
    h = n;
  }
}

void vexSetAllocModeTEMP_and_clear ( void )
{
  static Bool done_init;
  struct alloc_header *entire_arena_hdr;

  if (!done_init) {
    entire_arena_hdr = first_alloc_header();
    entire_arena_hdr->type = NULL;
    entire_arena_hdr->size = N_TEMPORARY_BYTES;
    entire_arena_hdr->flags = 0;
    done_init = True;
  }

  if (heap_used > N_TEMPORARY_BYTES / 2)
    do_gc();
}


static VexAllocType byte_alloc_type = { -1, 0, 0, "<bytes>" };

static void
visit_ptr_array(const void *this, void (*visit)(const void *))
{
  struct alloc_header *ah = alloc_to_header(this);
  void **payload = (void **)(ah + 1);
  unsigned x;
  for (x = 0; x < (ah->size - sizeof(*ah)) / sizeof(void *); x++)
    visit(payload[x]);
}

static VexAllocType ptr_array_type = { -1, visit_ptr_array, NULL, "<array>" };


static void *
alloc_bytes(const VexAllocType *type, unsigned size, const char *file, unsigned line)
{
  struct alloc_header *cursor;
  struct alloc_header *next;
  unsigned old_size;
  void *res;

  size += sizeof(struct alloc_header);
  size = (size + 15) & ~15;

  /* First-fit policy */
  for (cursor = allocation_cursor;
       cursor != NULL;
       cursor = next_alloc_header(cursor)) {
    vassert(!(cursor->flags & ~ALLOC_FLAG_GC_MARK));
    if (!cursor->type && cursor->size >= size)
      break;
  }
  if (!cursor) {
    for (cursor = first_alloc_header();
	 cursor != allocation_cursor;
	 cursor = next_alloc_header(cursor)) {
      vassert(!(cursor->flags & ~ALLOC_FLAG_GC_MARK));
      if (!cursor->type && cursor->size >= size)
	break;
    }
    if (!cursor) {
      /* Whoops, out of memory */
      vpanic("VEX temporary storage exhausted.\n"
	     "Increase N_TEMPORARY_BYTES and recompile.");
    }
  }

  /* Consider splitting the block */
  if (cursor->size >= size + 32) {
    /* Do split. */
    old_size = cursor->size;
    cursor->size = size;
    next = next_alloc_header(cursor);
    vassert(next != NULL);
    next->type = NULL;
    next->size = old_size - size;
    next->flags = 0;
    allocation_cursor = next;
  } else {
    allocation_cursor = next_alloc_header(cursor);
  }

  cursor->type = type;
  cursor->file = file;
  cursor->line = line;
  heap_used += cursor->size;
  res = header_to_alloc(cursor);
  poison(res, size - sizeof(struct alloc_header), 0xaabbccdd);
  return res;
}

/* Exported to library client. */
void *
__LibVEX_Alloc_Bytes(Int nbytes, const char *file, unsigned line)
{
  return alloc_bytes(&byte_alloc_type, nbytes, file, line);
}

struct libvex_alloc_type *
__LibVEX_Alloc(const VexAllocType *t, const char *file, unsigned line)
{
  return alloc_bytes(t, t->nbytes, file, line);
}

struct libvex_alloc_type *
__LibVEX_Alloc_Ptr_Array(unsigned len, const char *file, unsigned line)
{
  struct alloc_header *ah;
  void **res;
  unsigned x;

  res = alloc_bytes(&ptr_array_type, sizeof(void *) * len, file, line);
  ah = alloc_to_header(res);
  for (x = 0; x < (ah->size - sizeof(*ah)) / sizeof(void *); x++)
    res[x] = NULL;
  return (struct libvex_alloc_type *)res;
}

void vexAllocSanityCheck ( void )
{
}

void
vexRegisterGCRoot(void **w)
{
  vassert(nr_gc_roots < NR_GC_ROOTS);
  gc_roots[nr_gc_roots] = w;
  nr_gc_roots++;
}

static void
my_memmove(void *dest, const void *src, unsigned n)
{
  int x;

  if (dest < src) {
    for (x = 0; x < n; x++) {
      ((char *)dest)[x] = ((const char *)src)[x];
    }
  } else {
    for (x = n - 1; x >= 0; x++)
      ((char *)dest)[x] = ((const char *)src)[x];
  }
}

void
vexUnregisterGCRoot(void **w)
{
  unsigned x;
  for (x = 0; x < nr_gc_roots; x++) {
    if (gc_roots[x] == w) {
      my_memmove(gc_roots + x, gc_roots + x + 1, (nr_gc_roots - x - 1) * sizeof(gc_roots[0]));
      nr_gc_roots--;
      return;
    }
  }
  vpanic("Unregistering a GC root which was never registered.");
}

void
dump_heap(void)
{
  unsigned x;
  unsigned depth;
  struct alloc_header *h;

  void visitor(const void *what) {
    struct alloc_header *ah = alloc_to_header(what);
    if (!what)
      return;
    if (!ah->type || ah->flags & ALLOC_FLAG_GC_MARK)
      return;
    ah->flags |= ALLOC_FLAG_GC_MARK;
    vex_printf("%d %p %s %s:%d\n", depth, what, ah->type->name, ah->file, ah->line);
    depth++;
    if (ah->type && ah->type->gc_visit)
      ah->type->gc_visit(what, visitor);
    depth--;
  }

  for (h = first_alloc_header(); h; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
  depth = 0;
  for (x = 0; x < nr_gc_roots; x++) {
    vex_printf("Root %d:\n", x);
    visitor(*gc_roots[x]);
    vassert(depth == 0);
  }

  for (h = first_alloc_header(); h; h = next_alloc_header(h)) {
    if (!h->type || (h->flags & ALLOC_FLAG_GC_MARK))
      continue;
    vex_printf("Unattached but allocated:\n");
    visitor(h + 1);
  }
}
