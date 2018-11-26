TYPE ?= uint8_t
solver: main.cpp avx256.h bitvector_helpers.h Makefile
	g++ -O3 -ggdb -DDEBUG -DASSIGN_TYPE=$(TYPE) -march=core-avx-i -mtune=core-avx-i -mavx2 main.cpp -o solver -Wall

.phony: clean
clean:
	rm -f solver
