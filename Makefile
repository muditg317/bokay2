CC=clang
CFLAGS=-Wall -Wextra -Werror -g -O0

main: main.c tools.h lexer.h parser.h program.h
	$(CC) $(CFLAGS) -o main main.c

run: main
	./main $(FILE)

gdb: main
	gdb ./main

.PHONY: run