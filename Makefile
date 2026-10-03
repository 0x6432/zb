CC ?= cc
CFLAGS ?= -O1 -g -Wall -Wno-misleading-indentation -Wno-unused-function
QBE = qbe-1.2/qbe
ifeq ($(GC),1)
CFLAGS += -DZB_GC
LIBS += -lgc
endif
zb: src/*.c src/zb.h
	$(CC) $(CFLAGS) -rdynamic -o zb src/*.c -lm $(LIBS)
test: zb
	./run_tests.sh
