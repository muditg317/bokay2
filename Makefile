CC=clang
CFLAGS=-Wall -Wextra -Werror -g

bokay: bokay.c tools.h
	$(CC) $(CFLAGS) -o bokay bokay.c

run: bokay
	./bokay $(FILE)

.PHONY: run