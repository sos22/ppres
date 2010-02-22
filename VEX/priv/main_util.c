
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
