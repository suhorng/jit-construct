CC = gcc
BIN = interpreter \
      compiler-x86 \
      jit-x86

CROSS_COMPILE = arm-linux-gnueabihf-
QEMU_ARM = qemu-arm -L /usr/arm-linux-gnueabihf
LUA = ./minilua

all: $(BIN)

CFLAGS = -Wall -Werror -std=gnu99 -I. -g

interpreter: interpreter.c
	$(CC) $(CFLAGS) -o $@ $^

compiler-x86: compiler-x86.c
	$(CC) $(CFLAGS) -o $@ $^

compiler-x64: compiler-x64.c
	$(CC) $(CFLAGS) -o $@ $^

compiler-arm: compiler-arm.c
	$(CC) $(CFLAGS) -o $@ $^

run-compiler: compiler-x86 compiler-x64 compiler-arm
	./compiler-x86 progs/hello.b > hello.s
	$(CC) -m32 -o hello-x86 hello.s
	@echo 'x86: ' `./hello-x86`
	@echo

jit0-x64: tests/jit0-x64.c
	$(CC) $(CFLAGS) -o $@ $^

jit-x86: dynasm-driver.c jit-x86.h
	$(CC) $(CFLAGS) -o $@ -DJIT=\"jit-x86.h\" \
		dynasm-driver.c
jit-x86.h: jit-x86.dasc
	        $(LUA) dynasm/dynasm.lua -o $@ jit-x86.dasc
run-jit-x86: jit-x86
	./jit-x86 progs/hello.b && objdump -D -b binary \
		-mi386 -Mx86 jitcode

jit0-arm: tests/jit0-arm.c
	$(CROSS_COMPILE)gcc $(CFLAGS) -o $@ $^

jit-arm: dynasm-driver.c jit-arm.h
	$(CROSS_COMPILE)gcc $(CFLAGS) -o $@ -DJIT=\"jit-arm.h\" \
		dynasm-driver.c
jit-arm.h: jit-arm.dasc
	$(LUA) dynasm/dynasm.lua -o $@ jit-arm.dasc
run-jit-arm: jit-arm
	$(QEMU_ARM) jit-arm progs/hello.b && \
	$(CROSS_COMPILE)objdump -D -b binary -marm /tmp/jitcode

bench-jit-x86: jit-x85
	@echo
	@echo Executing Brainf*ck benchmark suite. Be patient.
	@echo
	@env PATH='.:${PATH}' BF_RUN='$<' tests/bench.py

test: test_stack jit0-x64 jit0-arm
	./test_stack
	(./jit0-x64 42 ; echo $$?)
	($(QEMU_ARM) jit0-arm 42 ; echo $$?)

test_stack: tests/test_stack.c
	$(CC) $(CFLAGS) -o $@ $^

clean:
	$(RM) $(BIN) \
	      hello-x86 hello-x64 hello-arm hello.s \
	      test_stack jit0-x64 jit0-arm \
	      jit-x64.h jit-arm.h
