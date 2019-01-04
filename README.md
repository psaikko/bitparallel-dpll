# bitparallel-dpll

Experiments with AVX2 instuctions and bitparallelism for SAT 
inspired by Ch. 7 of [Marijn Heule's PhD thesis](https://repository.tudelft.nl/islandora/object/uuid%3Ad41522e3-690a-4eb7-a352-652d39d7ac81).

Implements DPLL algorithm with bitparallel unit-propagation but without pure literal elimination.

Supports word sizes of 8, 16, 32, 64, 128 (via gcc __uint128_t), 256 (via a AVX2 wrapper type).

Compile with `make TYPE=<type>` where `<type>` is one of:

* `uint8_t`
* `uint16_t`
* `uint32_t`
* `uint64_t`
* `__uint128_t`
* `avx256i`

The resulting binary `solver-<type>` takes input in [DIMACS CNF format](https://www.satcompetition.org/2009/format-benchmarks2009.html).

This is not currently a competitive SAT solver for any application nor does its performance scale with word size.
