#include <cstdio>
#include <cstdlib>
#include <memory>
#include <cstring>
#include <algorithm>
#include <cassert>
#include <cinttypes>
#include <cmath>

#include "avx256.h"
#include "bitvector_helpers.h"

#define SAT 1
#define UNSAT 0
#define UNKNOWN -1

#ifndef NDEBUG
  #define DPRINT(...) printf(__VA_ARGS__)
  #define DPRINT_BITMASK(x) print_bitmask(x)
  #define DPRINT_CLAUSE(c, n) print_clause(c, n);
  #define DPRINT_ASSIGNMENT() print_assignment()
#else
  #define DPRINT(...) 
  #define DPRINT_BITMASK(x)
  #define DPRINT_CLAUSE(c, n) 
  #define DPRINT_ASSIGNMENT() 
#endif

typedef int lit;
typedef unsigned int var;

typedef ASSIGN_TYPE assign_t;

inline var VAR(lit l) { return std::abs(l); }
inline lit POS(lit l) { return std::abs(l); }
inline lit NEG(lit l) { return -std::abs(l); }

inline assign_t bitnot(assign_t m) { return ~m; }

unsigned n_clauses, n_vars;

lit ** clauses;
int * clauses_len;

assign_t all_true = ones<assign_t>();
assign_t all_false = zero<assign_t>();

assign_t * assign_bitmasks;
unsigned n_bitmasks;

void init_bitmasks() {
  /*
    bitmask pattern like
    00001111
    00110011
    01010101
    for arbitrary-length assign_t
  */
  n_bitmasks = log2(sizeof(assign_t) * 8);

  if (sizeof(assign_t) >= 16) {
    assign_bitmasks = (assign_t *) aligned_alloc(sizeof(assign_t), sizeof(assign_t) * n_bitmasks);
  } else {
    assign_bitmasks = (assign_t *) malloc( sizeof(assign_t) * n_bitmasks);
  }

  assign_t m = zero<assign_t>();

  int shift = sizeof(assign_t) * 8 / 2;
  int i = 0;
  
  while (shift > 0) {
    m ^= ((~m) << shift);
    assign_bitmasks[i++] = m;
    shift /= 2;
  }
}

void print_clause(lit * clause, unsigned n) {
  for (unsigned i = 0; i < n; ++i)
    printf(" %d", clause[i]);
  printf("\n");
}

void print_assignment();
void make_assignment(var v, assign_t assignment, assign_t mask);

void parse(const char * file) {
  FILE* cnf_file = fopen(file, "r");

  int res;
  do {
    // TODO: fails if comment contains "p-line"
    res = fscanf(cnf_file, "p cnf %u %u\n", &n_vars, &n_clauses);
    if (res == 2) break;
    res = fscanf(cnf_file, "%*s\n");
  } while (res != EOF);

  if (res == EOF) {
    printf("parse error\n");
    exit(1);
  }

  printf("c %u vars %u clauses\n", n_vars, n_clauses);

  lit l;
  bool ok = true;
  unsigned read_clauses = 0;
  int read_lits = 0;

  lit * clause_buffer = (lit *) malloc(sizeof(lit) * n_vars);
  clauses = (lit **) malloc(sizeof(lit *) * n_clauses);
  clauses_len = (int *) malloc(sizeof(int) * n_clauses);

  while (read_clauses < n_clauses && ok) {

    ok = (fscanf(cnf_file, "%d", &l) == 1); 

    if (ok) {
      if (l == 0) {
        // end of clause
        lit * clause = (lit *) malloc(sizeof(lit) * read_lits);
        memcpy(clause, clause_buffer, sizeof(lit) * read_lits);

        clauses_len[read_clauses] = read_lits;
        clauses[read_clauses++] = clause;

        read_lits = 0;
      } else {
        // append literal to buffer
        clause_buffer[read_lits++] = l;
      }
    }
  }

  printf("c read %d clauses\n", read_clauses);

  for (unsigned i = 0; i < n_clauses; ++i) {
    printf("c");
    print_clause(clauses[i], clauses_len[i]);
  }

  free(clause_buffer);
  fclose(cnf_file);
}

assign_t * var_assignment; // bitvalues of var assignments
assign_t * var_undef;      // which bits of var assignment are undefined

void print_assignment() {
  for (unsigned i = 1; i <= n_vars; ++i) {
    printf("%d val = ", i);
    for (size_t j = 0; j < sizeof(assign_t)*8; ++j) {
      if (var_undef[i] & single_bit_mask<assign_t>(j)) {
        printf(".");
      } else {
        if (var_assignment[i] & single_bit_mask<assign_t>(j)) {
          printf("1");
        } else {
          printf("0");  
        }
      }
    }
    printf("\n");
  }
}

var * trail_var;       // what variable was touched
assign_t * trail_val;  // what bit values were set
assign_t * trail_mask; // what bits were touched
int * trail_depth;

int trail_head;
int search_depth;

var select_branch_variable() {
  for (var i = search_depth+1; i <= n_vars; ++i)
    if (var_undef[i] != all_false)
      return i;
  return 0;
}

assign_t sat_bit_position;

int propagate() {

  lit l;
  var v;
  unsigned unset_lits;
  unsigned total_unset_lits;
  unsigned propagations; 

  assign_t sat_mask, clause_sat_mask, lit_sat_mask;
  assign_t undef_mask_1, undef_mask_2, undef_tmp;
  assign_t propagate_mask, propagate_bits, propagate_val;
  assign_t incomplete_assignment_mask;

 restart:
  sat_mask = all_true;
  propagations = 0;
  total_unset_lits = 0;
  incomplete_assignment_mask = zero<assign_t>();

  DPRINT("propagating\n");
  DPRINT_ASSIGNMENT();

  // todo: do this more efficiently
  for (unsigned i = 1; i <= n_vars; ++i) 
    incomplete_assignment_mask |= var_undef[i];

  for (unsigned i = 0; i < n_clauses; ++i) {

    DPRINT("c clause");
    DPRINT_CLAUSE(clauses[i], clauses_len[i]);

    undef_mask_1 = zero<assign_t>();
    undef_mask_2 = zero<assign_t>();

    clause_sat_mask = all_false;    
    unset_lits = 0;

    for (int j = 0; j < clauses_len[i]; ++j) {
      l = clauses[i][j];
      v = VAR(l);

      undef_tmp = var_undef[v] & undef_mask_1;
      if (undef_tmp != all_false) {
        undef_mask_2 |= undef_tmp;
      }

      undef_mask_1 |= var_undef[v];

      if (var_undef[v] == all_true) {
        ++total_unset_lits;
        if (unset_lits++) {
          DPRINT("UNDEF on all\n");
          goto next_clause;
        }
      } else {
        lit_sat_mask = (l > 0 ? var_assignment[v] : bitnot(var_assignment[v]));
        clause_sat_mask |= (lit_sat_mask & bitnot(var_undef[v])); 

        //print_bitmask(clause_sat_mask);

        if (clause_sat_mask == all_true) {
          DPRINT("SAT on "); 
          DPRINT_BITMASK(clause_sat_mask);
          goto next_clause;
        }
      } 
    }

    // clause is satisfied on some bits
    if (clause_sat_mask) {

      DPRINT("SAT on "); 
      DPRINT_BITMASK(clause_sat_mask);

      // update sat mask for completely defined bits
      sat_mask &= (clause_sat_mask | undef_mask_1);

      // are all bits unsat for formula?
      if (sat_mask == all_false) return UNSAT;

      if (undef_mask_1 == all_false) goto next_clause;
    }

    // all clause bits are set
    // and sat mask is 0
    if (undef_mask_1 == all_false) {
      DPRINT("UNSAT \n");
      return UNSAT;
    }

    // propagate on all bits where exactly one var is undef
    propagate_mask = undef_mask_1 & bitnot(undef_mask_2) & bitnot(clause_sat_mask);

    if (propagate_mask) {
      DPRINT("propagate clause on %d bits\n", __builtin_popcount(propagate_mask));

      for (int j = 0; j < clauses_len[i]; ++j) {
        l = clauses[i][j];
        v = VAR(l);

        // propagate v?
        if (var_undef[v] & propagate_mask) {

          propagate_bits = var_undef[v] & propagate_mask;

          DPRINT("propagate %d on bits ", l);
          DPRINT_BITMASK(propagate_bits);
          DPRINT("var_undef[%d]    ", v); 
          DPRINT_BITMASK(var_undef[v]);
          DPRINT("propagate_mask  "); 
          DPRINT_BITMASK(propagate_mask);
          DPRINT("undef_mask_1    "); 
          DPRINT_BITMASK(undef_mask_1);
          DPRINT("clause_sat_mask "); 
          DPRINT_BITMASK(clause_sat_mask);

          ++propagations;

          propagate_val = l > 0 ? all_true : all_false;

          make_assignment(v, propagate_val, propagate_bits);   
        }
      }
    }

    DPRINT("Fallthrough\n");
    DPRINT_BITMASK(clause_sat_mask);
    DPRINT_BITMASK(incomplete_assignment_mask);

    sat_mask &= (clause_sat_mask | incomplete_assignment_mask);

    next_clause: continue;
  }

  sat_mask &= bitnot(incomplete_assignment_mask);
  if (sat_mask != all_false) {

    DPRINT("sat_mask        ");
    DPRINT_BITMASK(sat_mask);
    DPRINT("incomplete_mask ");
    DPRINT_BITMASK(incomplete_assignment_mask);

    unsigned i = 1;
    sat_bit_position = single_bit_mask<assign_t>(i);

    // find first bit with solution
    while (!(sat_mask & sat_bit_position)) {
      sat_bit_position = single_bit_mask<assign_t>(i++);
    }
    
    DPRINT_ASSIGNMENT();
    DPRINT("sat mask ");
    DPRINT_BITMASK(sat_mask);

    return SAT;
  }

  if (propagations) {
    #ifndef NDEBUG
    printf("restart\n");
    #endif
    goto restart;
  }

  return UNKNOWN;
}

void make_assignment(var v, assign_t assignment, assign_t mask) {

  var_assignment[v] &= bitnot(mask); // unset touched assignment bits
  var_assignment[v] |= (assignment & mask); // set assignment bits
  var_undef[v]      &= bitnot(mask); // unset undef bits touched by decision

  ++trail_head;

  trail_var[trail_head] = v;
  trail_val[trail_head] = assignment & mask;
  trail_mask[trail_head] = mask;
  trail_depth[trail_head] = search_depth;
}

void backtrack(int to_depth) {
  while (trail_head >= 0 && trail_depth[trail_head] > to_depth) {
    var v = trail_var[trail_head];
    //assign_t unassign_val = trail_val[trail_head];
    assign_t unassign_mask = trail_mask[trail_head];
    
    var_undef[v] |= unassign_mask;    // set bits as undefined
    var_assignment[v] &= ~unassign_mask; // undo assignment (not necessary)

    --trail_head;
  }

  search_depth = to_depth;
}

int search() {
  int res = propagate();

  int level = search_depth;

  if (res != UNKNOWN) {
    return res;
  }

  printf("c %u %d %d\n", n_vars, search_depth, trail_head);

  var branch = select_branch_variable();
  assign_t pattern = assign_bitmasks[search_depth % n_bitmasks];

  assert(branch != 0);

  assign_t decision_mask = var_undef[branch];

  ++search_depth;
  make_assignment(branch, pattern, decision_mask);

  DPRINT("branch on %d = ", branch);
  DPRINT_BITMASK(pattern);
  DPRINT_BITMASK(var_assignment[branch]);

  if (search() == SAT) {
    return SAT;
  }
  //printf("%d %d %d\n", n_vars, search_depth, trail_head);
  //printf("backtrack\n");
  backtrack(level);
  //printf("%d %d %d\n", n_vars, search_depth, trail_head);

  ++search_depth;
  make_assignment(branch, bitnot(pattern), decision_mask);

  DPRINT("branch on %d = ", branch);
  DPRINT_BITMASK(bitnot(pattern));
  DPRINT_BITMASK(var_assignment[branch]);

  res = search();
  return res;
}

void dpll() {
  search_depth = 0;

  // init assignment

  if (sizeof(assign_t) >= 16) {
    var_assignment = (assign_t *) aligned_alloc(sizeof(assign_t), sizeof(assign_t) * (n_vars+1));
    var_undef      = (assign_t *) aligned_alloc(sizeof(assign_t), sizeof(assign_t) * (n_vars+1));
  } else {
    var_assignment = (assign_t *) malloc(sizeof(assign_t) * (n_vars+1));
    var_undef      = (assign_t *) malloc(sizeof(assign_t) * (n_vars+1));
  }

  std::fill(var_assignment, var_assignment+n_vars+1, zero<assign_t>());
  //for (unsigned i = 0; i <= n_vars + 1; ++i)
  //  var_assignment[i] = zero<assign_t>();

  std::fill(var_undef, var_undef+n_vars+1, ones<assign_t>());
  //for (unsigned i = 0; i <= n_vars + 1; ++i)
  //  var_undef[i] = ones<assign_t>();

  // init trail
  trail_var = (var *) malloc(sizeof(var) * n_vars * sizeof(assign_t) * 8);

  if (sizeof(assign_t) >= 16) {
    trail_val  = (assign_t *) aligned_alloc(sizeof(assign_t), sizeof(assign_t) * n_vars * sizeof(assign_t) * 8);
    trail_mask = (assign_t *) aligned_alloc(sizeof(assign_t), sizeof(assign_t) * n_vars * sizeof(assign_t) * 8);
  } else {
    trail_val  = (assign_t *) malloc(sizeof(assign_t) * n_vars * sizeof(assign_t) * 8);
    trail_mask = (assign_t *) malloc(sizeof(assign_t) * n_vars * sizeof(assign_t) * 8);
  }

  if (!trail_val || !trail_mask || !var_undef || !var_assignment) {
    printf("adsfasdf\n");
    exit(0);
  }


  trail_depth = (int *) malloc(sizeof(int) * n_vars * sizeof(assign_t) * 8);
  trail_head = -1;

  int res = search();

  if (res == SAT) {
    //std::sort(var_assignment+1, var_assignment+n_vars, [](const lit l1, const lit l2){ return var(l1) < var(l2); });
    printf("s SATISFIABLE\n");
    printf("v");
    for (var i = 1; i <= n_vars; ++i) {
      //assert(bitnot(var_undef[i]) & sat_bit_position); 
      printf(" %d", (var_assignment[i] & sat_bit_position) ? POS(i) : NEG(i));
    };
    printf("\n");
  } else if (res == UNSAT) {
    printf("s UNSATISFIABLE\n");
  } else {
    printf("s UNKNOWN\n");
  }
}
  
int main(int argv, char ** argc) {

  init_bitmasks();

  for (unsigned i = 0; i < n_bitmasks; ++i) {
    printf("c ");
    print_bitmask(assign_bitmasks[i]);
  }

  printf("bits: %lu\n", sizeof(assign_t)*8);

  if (argv == 2) {
    parse( argc[1] );
    dpll();
  }
}
