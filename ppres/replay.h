struct record_consumer {
	int fd;
	unsigned offset_in_current_chunk;
	unsigned avail_in_current_chunk;
	void *current_chunk;
	OffT offset_in_file;
};

void finish_this_record(struct record_consumer *rc);
struct record_header *get_current_record(struct record_consumer *rc);
void open_logfile(struct record_consumer *res,
		  const signed char *fname);
void close_logfile(struct record_consumer *rc);
void success(void);
