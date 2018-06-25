solver: main.cpp avx256.h bitvector_helpers.h Makefile
	g++ -O3 -march=core-avx-i -mtune=core-avx-i -mavx2 main.cpp -o solver -Wall

.phony: clean
clean:
	rm -f solver
