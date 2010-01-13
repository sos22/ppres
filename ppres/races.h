void racetrack_read_region(Addr start, unsigned size,  ThreadId this_thread);
void racetrack_write_region(Addr start, unsigned size, ThreadId this_thread);
void new_race_address(Addr addr);
void mark_address_as_racy(Addr addr);
void dump_racetrack_state(void);
Bool racetrack_address_races(Addr start, unsigned size);
void racetrack_thread_message(ThreadId sender, ThreadId receiver);
