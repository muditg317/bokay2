CC=clang
CFLAGS=-Wall -Wextra -Werror -g

main: main.c tools.h
	$(CC) $(CFLAGS) -o main main.c

run: main
	./main $(FILE)

.PHONY: run