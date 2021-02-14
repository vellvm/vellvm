.PHONY: clean test
.SECONDARY: %.s %.ll %.o

LLC=llc
LLCFLAGS=-relocation-model=pic -asm-verbose -O0
ASM=gcc
ASMFLAGS=-c


%.o: %.s Makefile
	$(ASM) $(ASMFLAGS) $<

%.s: %.ll Makefile
	$(LLC) $(LLCFLAGS) $<

main_dynwin64: main_dynwin64.c test_dynwin64.o

all: main_dynwin64

clean:
	rm -f *.s *.o a.out main_dynwin64
