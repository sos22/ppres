Bool is_racy(Addr addr);
void racetrack_read_region(Addr start, unsigned size,  ThreadId this_thread);
void racetrack_write_region(Addr start, unsigned size, ThreadId this_thread);
