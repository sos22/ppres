#define MK_SLIST_FUNCS(type, tag)			    \
struct slist_entry_ ## tag {                                \
	struct slist_entry_ ##tag *next;                    \
	type val;                                           \
};                                                          \
                                                            \
struct slist_head_ ## tag {                                 \
	struct slist_entry_ ## tag *head, *tail;            \
};                                                          \
                                                            \
                                                            \
static inline Bool                                          \
slist_empty_ ## tag (struct slist_head_ ## tag *t)          \
{                                                           \
	return t->head == NULL;                             \
}                                                           \
                                                            \
static inline void                                          \
slist_push_ ## tag (struct slist_head_ ## tag *q,           \
		    type val)                               \
{                                                           \
	struct slist_entry_ ## tag * v;                     \
	v = VG_(malloc)("slist_entry_" #tag , sizeof(*v));  \
	VG_(memset)(v, 0, sizeof(*v));                      \
	v->next = NULL;                                     \
	v->val = val;                                       \
	if (q->tail)                                        \
		q->tail->next = v;                          \
	else                                                \
		q->head = v;                                \
	q->tail = v;                                        \
}                                                           \
                                                            \
static inline type                                          \
slist_pop_ ## tag (struct slist_head_ ## tag *q)            \
{                                                           \
	type res;                                           \
	struct slist_entry_ ## tag *v;                      \
	v = q->head;                                        \
	tl_assert(v != NULL);                               \
	q->head = v->next;                                  \
	if (q->tail == v)                                   \
		q->tail = NULL;                             \
	res = v->val;                                       \
	VG_(free)(v);                                       \
	return res;                                         \
}

/* A zipper list.  You have two processes, both of which are producing
   records at some rate.  You don't particularly care which one is
   faster, or if one gets ahead of the other, but you do care that the
   sequences they produce are consistent.  This is a datastructure for
   matching them up. */
#define MK_ZIPPER_LIST(type, tag, validate)                 \
struct zipper_list_ ## tag {                                \
	Bool pending_are_from_A;                            \
	struct slist_head_ ## tag pending;                  \
};                                                          \
                                                            \
static inline void                                          \
zipper_add_A_ ## tag(struct zipper_list_ ## tag *list,      \
		     type val)                              \
{                                                           \
	if (slist_empty_ ## tag(&list->pending) ||          \
	    list->pending_are_from_A) {                     \
		list->pending_are_from_A = True;            \
		slist_push_ ## tag (&list->pending, val);   \
	} else {                                            \
		type tmp;                                   \
		tmp = slist_pop_ ## tag (&list->pending);   \
		validate(&val, &tmp);                       \
	}                                                   \
}                                                           \
                                                            \
static inline void                                          \
zipper_add_B_ ## tag(struct zipper_list_ ## tag *list,      \
		     type val)                              \
{                                                           \
	if (slist_empty_ ## tag(&list->pending) ||          \
	    !list->pending_are_from_A) {                    \
		list->pending_are_from_A = False;           \
		slist_push_ ## tag (&list->pending, val);   \
	} else {                                            \
		type tmp;                                   \
		tmp = slist_pop_ ## tag (&list->pending);   \
		validate(&val, &tmp);                       \
	}                                                   \
}
