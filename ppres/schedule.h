struct execution_schedule {
	int fd;
	void *window;
	Bool replay_mode; /* False -> replay mode, True -> explore
			   * mode */
	unsigned offset_in_window;
	unsigned avail_in_window;
	OffT window_offset_in_file;
	OffT file_size;
};

void open_execution_schedule(struct execution_schedule *es,
			     const Char *filename);
void create_empty_execution_schedule(const Char *filename);
void advance_schedule_to_next_choice(const Char *filename);
void close_execution_schedule(struct execution_schedule *es);
unsigned make_nd_choice(struct execution_schedule *es,
			unsigned max_allowed);
