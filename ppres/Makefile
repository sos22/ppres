CFLAGS=-DHAVE_CONFIG_H -I../include -I../VEX/pub -DVGA_amd64=1 -DVGO_linux=1 -DVGP_amd64_linux=1 -g -Wall -fno-strict-aliasing -fno-stack-protector -Wundef

all: ppres_record ppres_replay2 ppres_audit.so driver/UI pplogfile

ppres_record: record.o
	gcc  -Wall -fno-stack-protector -o ppres_record -static -Wl,-defsym,valt_load_address=0x38000000 -nodefaultlibs -nostartfiles -u _start -Wl,-T,../valt_load_address_amd64_linux.lds record.o ../coregrind/libcoregrind-amd64-linux.a ../VEX/libvex-amd64-linux.a -lgcc                

record.o: record.c
	gcc -DHAVE_CONFIG_H -I. -I. -I..  -I.. -I../include -I../VEX/pub -DVGA_x86=1 -DVGO_linux=1 -DVGP_x86_linux=1 -I/local/scratch/sos22/stage/include -g -Wall -fno-strict-aliasing -fno-stack-protector -c -o record.o record.c


ppres_replay: replay.o coroutines.o replay_logfile.o schedule.o races.o
	gcc  -Wall -fno-stack-protector -o ppres_replay -static -Wl,-defsym,valt_load_address=0x38000000 -nodefaultlibs -nostartfiles -u _start -Wl,-T,../valt_load_address_amd64_linux.lds $^ ../coregrind/libcoregrind-amd64-linux.a ../VEX/libvex-amd64-linux.a -lgcc

ppres_replay2: replay2.o coroutines.o replay_logfile.o ../coregrind/libcoregrind-amd64-linux.a ../VEX/libvex-amd64-linux.a ui.o expression.o interpreter.o debug.o
	gcc  -Wall -fno-stack-protector -o ppres_replay2 -static -Wl,-defsym,valt_load_address=0x38000000 -nodefaultlibs -nostartfiles -u _start -Wl,-T,../valt_load_address_amd64_linux.lds $^ -lgcc

replay.o: transform_expr.c
replay2.o: transform_expr.c ppres.h replay2.h
record.o: transform_expr.c ppres.h
expression.o: replay2.h
interpreter.o: replay2.h
debug.o: replay2.h

schedule.o: schedule.h

%.o: %.c
	gcc $(CFLAGS) -c $<

tests: schedule races
	./schedule && ./races


schedule: schedule.c
	gcc schedule.c -o schedule -Wall -g -DUNIT_TEST

races: races.c
	gcc races.c -o races -Wall -g -DUNIT_TEST

ppres_audit.so: catch_pthread.o /usr/local/lib/libaudit.a
	gcc -fPIC -nostdlib -shared -o ppres_audit.so /usr/local/lib/libaudit.a catch_pthread.o -Wl,-u -Wl,la_version

catch_pthread.o: catch_pthread.c
	gcc -Wall -I/usr/local/include -I../include -shared -c -fPIC catch_pthread.c

driver/UI:
	cd driver && ghc --make -Wall -fno-warn-orphans UI.hs

pplogfile: pplogfile.c ppres.h
	gcc pplogfile.c -o pplogfile -Wall -g

.PHONY: driver/UI
