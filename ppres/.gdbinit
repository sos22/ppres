define dump_tracelog_entry
  set $code = ($arg0)->code
  if $code == 1
    printf "footstep "
  else
    if $code == 2
      printf "syscall "
    else
      if $code == 3
	printf "rdtsc "
      else
	if $code == 4
	  printf "load "
	else
	  if $code == 5
	    printf "store "
	  else
	    if $code == 6
	      printf "calling "
	    else
	      if $code == 7
		printf "called "
	      else
		if $code == 8
		  printf "enter monitor "
		else
		  if $code == 9
		    printf "exit monitor "
		  else
		    printf "%x ", ($arg0)->code
		  end
		end
	      end
	    end
	  end
	end
      end
    end
  end
  set $x = 0
  while $x < ($arg0)->nr_args
    printf "%x ", ($arg0)->args[($x)]
    set $x = $x + 1
  end
  printf "\n"
end

define dump_trace_arena
  set $arena = $arg0
  set $ptr = 0
  while $ptr < $arena->used
    set $log_entry = (struct tracelog *)($arena->body + $ptr)
    dump_tracelog_entry $log_entry
    set $ptr = $ptr + ($log_entry->nr_args + 1) * 8
  end
end

define dump_trace
  set $idx = current_trace_arena + 1
  print $idx
  while $idx != current_trace_arena + 17
    set $arena = &tracelog[($idx) % 16]
    dump_trace_arena $arena
    set $idx = $idx + 1
  end
end

define dump_control_command
  set $cmd = ($arg0)->cmd
  if $cmd == 0x1234
    print "snapshot"
  else
    if $cmd == 0x1235
      print "kill"
    else
      if $cmd == 0x1236
	printf "run to %ld\n", ($arg0)->u.run.nr
      else
	if $cmd == 0x1237
	  printf "trace to %ld\n", ($arg0)->u.trace.nr
	else
	  if $cmd == 0x1238
	    printf "run memory thread %ld for %ld\n", ($arg0)->u.runm.thread, ($arg0)->u.runm.nr
	  else
	    if $cmd == 0x1239
	      printf "trace thread %d\n", ($arg0)->u.trace_thread.thread
	    else
	      if $cmd == 0x123a
		printf "trace address 0x%lx\n", ($arg0)->u.trace_mem.address
	      else
		if $cmd == 0x123b
		  print "thread state"
		else
		  if $cmd == 0x123c
		    print "replay state"
		  else
		    if $cmd == 0x123d
		      printf "control trace %ld\n", ($arg0)->u.control_trace.nr
		    else
		      if $cmd == 0x123e
			printf "fetch memory $lx %lx\n", ($arg0)->u.get_memory.addr, ($arg0)->u.get_memory.size
		      else
			if $cmd == 0x123f
			  printf "vg intermediate %lx\n", ($arg0)->u.vg_intermediate.addr
			else
			  if $cmd == 0x1240
			    print "next thread"
			  else
			    inspect /x $arg0
			  end
			end
		      end
		    end
		  end
		end
	      end
	    end
	  end
	end
      end
    end
  end
end

define dump_control_log
  set $idx = 0
  while $idx < nr_logged_control_commands
    dump_control_command command_log[($idx)]
    set $idx = $idx + 1
  end
end
