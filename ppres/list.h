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
static type                                                 \
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
