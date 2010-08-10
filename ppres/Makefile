CFLAGS=-DHAVE_CONFIG_H -I../include -I../VEX/pub -DVGA_amd64=1 -DVGO_linux=1 -DVGP_amd64_linux=1 -g -Wall -fno-strict-aliasing -fno-stack-protector -Wundef

RECORD_OBJS=record.o recordi.o
REPLAY_OBJS=replay2.o coroutines.o ui.o expression.o interpreter.o debug.o
VG_OBJS=../coregrind/libcoregrind-amd64-linux.a ../VEX/libvex-amd64-linux.a

DEP_OBJS=$(RECORD_OBJS) $(REPLAY_OBJS) catch_pthread.o pplogfile.o

VG_LDFLAGS=-Wall -fno-stack-protector -static -Wl,-defsym,valt_load_address=0x38000000 -nodefaultlibs -nostartfiles -u _start -Wl,-T,../valt_load_address_amd64_linux.lds -lgcc
AUDIT_LDFLAGS=-fPIC -nostdlib -shared -Wl,-u -Wl,la_version
AUDIT_CFLAGS=-Wall -I/usr/local/include -I../include -shared -c -fPIC

all: ppres_record ppres_audit.so driver/UI pplogfile

.depend: Makefile
	for x in $(DEP_OBJS); \
	do \
		echo include $$(echo $$x | sed "s/\(.*\)\.o/.\1.dep/");\
	done > .depend

include .depend

.%.dep: %.c Makefile
	gcc -M -MT $@ -MT $(basename $<).o -MT Makefile $(CFLAGS) $< > $@

ppres_record: $(RECORD_OBJS) $(VG_OBJS)
	gcc  $(VG_LDFLAGS) $^ -o $@

ppres_replay2: $(REPLAY_OBJS) $(VG_OBJS)
	gcc  $(VG_LDFLAGS) $^ -o $@

%.o: %.c
	gcc $(CFLAGS) -c $<

ppres_audit.so: catch_pthread.o /usr/local/lib/libaudit.a
	gcc $(AUDIT_LDFLAGS) -o ppres_audit.so /usr/local/lib/libaudit.a catch_pthread.o

catch_pthread.o: catch_pthread.c
	gcc $(AUDIT_CFLAGS) -c catch_pthread.c

driver/UI:
	cd driver && ghc -prof -auto-all -caf-all --make -Wall -fno-warn-orphans UI.hs

pplogfile: pplogfile.o
	gcc -Wall pplogfile.o -o pplogfile

pplogfile.o: pplogfile.c ppres.h
	gcc -Wall -c pplogfile.c

.PHONY: driver/UI

clean:
	rm -f *.o *~ *.so pplogfile ppres_record ppres_replay2 core ppres_replay driver/*.o driver/*.hi driver/*~ driver/UI .depend .*.dep

