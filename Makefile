solver: main.cpp avx256.h Makefile
	g++ -O3 -DNDEBUG -march=core-avx-i -mtune=core-avx-i -mavx2 main.cpp -o solver

.phony: clean
clean:
	rm -f solver