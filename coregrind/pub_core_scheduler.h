
/*--------------------------------------------------------------------*/
/*--- The scheduler.                          pub_core_scheduler.h ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2000-2010 Julian Seward
      jseward@acm.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#ifndef __PUB_CORE_SCHEDULER_H
#define __PUB_CORE_SCHEDULER_H

//--------------------------------------------------------------------
// PURPOSE: This module is the scheduler, which is the main loop
// controlling the running of all the program's threads.
// It's at the centre of everything.
//--------------------------------------------------------------------

/* Allocate a new ThreadState */
extern ThreadId VG_(alloc_ThreadState)(void);

/* A thread exits.  tid must currently be running. */
extern void VG_(exit_thread)(ThreadId tid);

/* If 'tid' is blocked in a syscall, send it SIGVGKILL so as to get it
   out of the syscall and onto doing the next thing, whatever that is.
   If it isn't blocked in a syscall, has no effect on the thread. */
extern void VG_(get_thread_out_of_syscall)(ThreadId tid);

/* Nuke all threads except tid. */
extern void VG_(nuke_all_threads_except) ( ThreadId me,
                                           VgSchedReturnCode reason );

// The scheduler.
extern VgSchedReturnCode VG_(scheduler) ( ThreadId tid );

// Initialise, phase 1.  Zero out VG_(threads), decide on the root
// ThreadId and initialise the bigLock.
extern ThreadId VG_(scheduler_init_phase1) ( void );

// Initialise, phase 2.  Is passed the extent of the root thread's
// client stack and the root ThreadId decided on by phase 1.
extern void VG_(scheduler_init_phase2) ( ThreadId main_tid, 
                                         Addr     clstack_end, 
                                         SizeT    clstack_size );

/* Stats ... */
extern void VG_(print_scheduler_stats) ( void );

/* If False, a fault is Valgrind-internal (ie, a bug) */
extern Bool VG_(in_generated_code);

/* Sanity checks which may be done at any time.  The scheduler decides when. */
extern void VG_(sanity_check_general) ( Bool force_expensive );

#endif   // __PUB_CORE_SCHEDULER_H

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
