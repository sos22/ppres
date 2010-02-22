
/*---------------------------------------------------------------*/
/*---                                                         ---*/
/*--- This file (main_util.c) is                              ---*/
/*--- Copyright (C) OpenWorks LLP.  All rights reserved.      ---*/
/*---                                                         ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of LibVEX, a library for dynamic binary
   instrumentation and translation.

   Copyright (C) 2004-2009 OpenWorks LLP.  All rights reserved.

   This library is made available under a dual licensing scheme.

   If you link LibVEX against other code all of which is itself
   licensed under the GNU General Public License, version 2 dated June
   1991 ("GPL v2"), then you may use LibVEX under the terms of the GPL
   v2, as appearing in the file LICENSE.GPL.  If the file LICENSE.GPL
   is missing, you can obtain a copy of the GPL v2 from the Free
   Software Foundation Inc., 51 Franklin St, Fifth Floor, Boston, MA
   02110-1301, USA.

   For any other uses of LibVEX, you must first obtain a commercial
   license from OpenWorks LLP.  Please contact info@open-works.co.uk
   for information about commercial licensing.

   This software is provided by OpenWorks LLP "as is" and any express
   or implied warranties, including, but not limited to, the implied
   warranties of merchantability and fitness for a particular purpose
   are disclaimed.  In no event shall OpenWorks LLP be liable for any
   direct, indirect, incidental, special, exemplary, or consequential
   damages (including, but not limited to, procurement of substitute
   goods or services; loss of use, data, or profits; or business
   interruption) however caused and on any theory of liability,
   whether in contract, strict liability, or tort (including
   negligence or otherwise) arising in any way out of the use of this
   software, even if advised of the possibility of such damage.

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.
*/

#include "libvex_basictypes.h"
#include "libvex.h"

#include "main_globals.h"
#include "main_util.h"


/*---------------------------------------------------------*/
/*--- Storage                                           ---*/
/*---------------------------------------------------------*/

/* Try to keep this as low as possible -- in particular, less than the
   size of the smallest L2 cache we might encounter.  At 50000, my VIA
   Nehemiah 1 GHz (a weedy machine) can satisfy 27 million calls/
   second to LibVEX_Alloc(16) -- that is, allocate memory at over 400
   MByte/sec.  Once the size increases enough to fall out of the cache
   into memory, the rate falls by about a factor of 3. 
*/
#define N_TEMPORARY_BYTES 4000000

static HChar  temporary[N_TEMPORARY_BYTES] __attribute__((aligned(8)));
static HChar* temporary_first = &temporary[0];
static HChar* temporary_curr  = &temporary[0];
static HChar* temporary_last  = &temporary[N_TEMPORARY_BYTES-1];

static ULong  temporary_bytes_allocd_TOT = 0;

#define N_PERMANENT_BYTES 10000

static HChar  permanent[N_PERMANENT_BYTES] __attribute__((aligned(8)));
static HChar* permanent_first = &permanent[0];
static HChar* permanent_curr  = &permanent[0];
static HChar* permanent_last  = &permanent[N_PERMANENT_BYTES-1];

static VexAllocMode mode = VexAllocModeTEMP;

void vexAllocSanityCheck ( void )
{
   vassert(temporary_first == &temporary[0]);
   vassert(temporary_last  == &temporary[N_TEMPORARY_BYTES-1]);
   vassert(permanent_first == &permanent[0]);
   vassert(permanent_last  == &permanent[N_PERMANENT_BYTES-1]);
   vassert(temporary_first <= temporary_curr);
   vassert(temporary_curr  <= temporary_last);
   vassert(permanent_first <= permanent_curr);
   vassert(permanent_curr  <= permanent_last);
   vassert(private_LibVEX_alloc_first <= private_LibVEX_alloc_curr);
   vassert(private_LibVEX_alloc_curr  <= private_LibVEX_alloc_last);
   if (mode == VexAllocModeTEMP){
      vassert(private_LibVEX_alloc_first == temporary_first);
      vassert(private_LibVEX_alloc_last  == temporary_last);
   } 
   else
   if (mode == VexAllocModePERM) {
      vassert(private_LibVEX_alloc_first == permanent_first);
      vassert(private_LibVEX_alloc_last  == permanent_last);
   }
   else 
      vassert(0);

#  define IS_WORD_ALIGNED(p)   (0 == (((HWord)p) & (sizeof(HWord)-1)))
   vassert(sizeof(HWord) == 4 || sizeof(HWord) == 8);
   vassert(IS_WORD_ALIGNED(temporary_first));
   vassert(IS_WORD_ALIGNED(temporary_curr));
   vassert(IS_WORD_ALIGNED(temporary_last+1));
   vassert(IS_WORD_ALIGNED(permanent_first));
   vassert(IS_WORD_ALIGNED(permanent_curr));
   vassert(IS_WORD_ALIGNED(permanent_last+1));
   vassert(IS_WORD_ALIGNED(private_LibVEX_alloc_first));
   vassert(IS_WORD_ALIGNED(private_LibVEX_alloc_curr));
   vassert(IS_WORD_ALIGNED(private_LibVEX_alloc_last+1));
#  undef IS_WORD_ALIGNED
}

/* The current allocation mode. */

void vexSetAllocMode ( VexAllocMode m )
{
   vexAllocSanityCheck();

   /* Save away the current allocation point .. */
   if (mode == VexAllocModeTEMP){
      temporary_curr = private_LibVEX_alloc_curr;
   } 
   else
   if (mode == VexAllocModePERM) {
      permanent_curr = private_LibVEX_alloc_curr;
   }
   else 
      vassert(0);

   /* Did that screw anything up? */
   vexAllocSanityCheck();

   if (m == VexAllocModeTEMP){
      private_LibVEX_alloc_first = temporary_first;
      private_LibVEX_alloc_curr  = temporary_curr;
      private_LibVEX_alloc_last  = temporary_last;
   } 
   else
   if (m == VexAllocModePERM) {
      private_LibVEX_alloc_first = permanent_first;
      private_LibVEX_alloc_curr  = permanent_curr;
      private_LibVEX_alloc_last  = permanent_last;
   }
   else 
      vassert(0);

   mode = m;
}

VexAllocMode vexGetAllocMode ( void )
{
   return mode;
}

/* Visible to library client, unfortunately. */

HChar* private_LibVEX_alloc_first = &temporary[0];
HChar* private_LibVEX_alloc_curr  = &temporary[0];
HChar* private_LibVEX_alloc_last  = &temporary[N_TEMPORARY_BYTES-1];

__attribute__((noreturn))
void private_LibVEX_alloc_OOM(void)
{
   HChar* pool = "???";
   if (private_LibVEX_alloc_first == &temporary[0]) pool = "TEMP";
   if (private_LibVEX_alloc_first == &permanent[0]) pool = "PERM";
   vex_printf("VEX temporary storage exhausted.\n");
   vex_printf("Pool = %s,  start %p curr %p end %p (size %lld)\n",
              pool, 
              private_LibVEX_alloc_first,
              private_LibVEX_alloc_curr,
              private_LibVEX_alloc_last,
              (Long)(private_LibVEX_alloc_last + 1 - private_LibVEX_alloc_first));
   vpanic("VEX temporary storage exhausted.\n"
          "Increase N_{TEMPORARY,PERMANENT}_BYTES and recompile.");
}

void vexSetAllocModeTEMP_and_clear ( void )
{
   /* vassert(vex_initdone); */ /* causes infinite assert loops */
   temporary_bytes_allocd_TOT 
      += (ULong)(private_LibVEX_alloc_curr - private_LibVEX_alloc_first);

   mode = VexAllocModeTEMP;
   temporary_curr            = &temporary[0];
   private_LibVEX_alloc_curr = &temporary[0];

   /* Set to (1) and change the fill byte to 0x00 or 0xFF to test for
      any potential bugs due to using uninitialised memory in the main
      VEX storage area. */
   if (0) {
      Int i;
      for (i = 0; i < N_TEMPORARY_BYTES; i++)
         temporary[i] = 0x00;
   }

   vexAllocSanityCheck();
}


/* Exported to library client. */

void LibVEX_ShowAllocStats ( void )
{
   vex_printf("vex storage: T total %lld bytes allocated\n",
              (Long)temporary_bytes_allocd_TOT );
   vex_printf("vex storage: P total %lld bytes allocated\n",
              (Long)(permanent_curr - permanent_first) );
}


/*---------------------------------------------------------*/
/*--- Bombing out                                       ---*/
/*---------------------------------------------------------*/

__attribute__ ((noreturn))
void vex_assert_fail ( const HChar* expr,
                       const HChar* file, Int line, const HChar* fn )
{
   vex_printf( "\nvex: %s:%d (%s): Assertion `%s' failed.\n",
               file, line, fn, expr );
   (*vex_failure_exit)();
}

__attribute__ ((noreturn))
void vpanic ( HChar* str )
{
   vex_printf("\nvex: the `impossible' happened:\n   %s\n", str);
   (*vex_failure_exit)();
}


/*---------------------------------------------------------*/
/*--- vex_printf                                        ---*/
/*---------------------------------------------------------*/

/* This should be the only <...> include in the entire VEX library.
   New code for vex_util.c should go above this point. */
#include <stdarg.h>

Bool vex_streq ( const HChar* s1, const HChar* s2 )
{
   while (True) {
      if (*s1 == 0 && *s2 == 0)
         return True;
      if (*s1 != *s2)
         return False;
      s1++;
      s2++;
   }
}

UInt vex_printf ( HChar* format, ... )
{
   UInt ret;
   va_list vargs;
   va_start(vargs,format);
   ret = vgPlain_vprintf(format, vargs);
   va_end(vargs);

   return ret;
}


/* A general replacement for sprintf(). */

UInt vex_sprintf ( HChar* buf, HChar *format, ... )
{
   Int ret;
   va_list vargs;

   va_start(vargs,format);
   ret = vgPlain_sprintf(buf, format, vargs);
   va_end(vargs);
   return ret;
}


/*---------------------------------------------------------------*/
/*--- end                                         main_util.c ---*/
/*---------------------------------------------------------------*/
