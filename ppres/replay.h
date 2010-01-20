struct record_consumer {
	int fd;
	unsigned offset_in_current_chunk;
	unsigned avail_in_current_chunk;
	void *current_chunk;
	OffT offset_in_file;

	void *peek_chunk;
	OffT peek_chunk_start;
	unsigned peek_chunk_size;
};

void finish_this_record(struct record_consumer *rc);
struct record_header *get_current_record(struct record_consumer *rc);
void open_logfile(struct record_consumer *res,
		  const signed char *fname);
void close_logfile(struct record_consumer *rc);
void hit_end_of_log(void);

OffT logfile_tell(struct record_consumer *rc);
Bool peek_record(struct record_consumer *rc, OffT ptr, struct record_header *rh);
