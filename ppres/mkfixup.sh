#! /bin/bash

fixup_c=$1
outfile=$2
gcc -g -fPIC -shared -Wall fixup.ld fixup_asm.S $fixup_c -o $outfile
