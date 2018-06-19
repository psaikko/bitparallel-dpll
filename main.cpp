#include <cstdio>
#include <cstdlib>
#include <memory>
#include <cstring>
#include <algorithm>
#include <cassert>

#define SAT 1
#define UNSAT 0
#define UNKNOWN -1

#define TRUE 1
#define FALSE 0
#define UNDEF -1

#define VAR(l) (abs(l))
#define POS(l) (abs(l))
#define NEG(l) (-abs(l))

#define SIGN(l) ((l) > 0 ? TRUE : FALSE)

typedef long long int ll;
typedef int lit;
typedef unsigned int var;

ll n_clauses, n_vars;

lit ** clauses;
int * clauses_len;

void parse(const char * file) {
  FILE* cnf_file = fopen(file, "r");

  int res;
  do {
    res = fscanf(cnf_file, "p cnf %lld %lld\n", &n_vars, &n_clauses);
    if (res == 2) break;
    res = fscanf(cnf_file, "%*s\n");
  } while (res != EOF);

  if (res == EOF) {
    printf("parse error\n");
    exit(1);
  }

  printf("c %lld vars %lld clauses\n", n_vars, n_clauses);

  lit l;
  bool ok = true;
  int read_clauses = 0;
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

  for (int i = 0; i < n_clauses; ++i) {
    printf("c");
    for (int j = 0; j < clauses_len[i]; ++j) {
      printf(" %d", clauses[i][j]);
    }
    printf(" 0\n");
  }

  free(clause_buffer);
  fclose(cnf_file);
}

lit * current_assignment;
lit * trail;
int * trail_depth;

int trail_head;
int search_depth;

var select_branch_variable() {
  for (var i = search_depth+1; i <= n_vars; ++i)
    if (current_assignment[i] == UNDEF)
      return i;
  return 0;
}



int propagate() {

  unsigned sat_clauses;
  unsigned undef_lits;
  unsigned propagations;
  int undef_j;
  lit l;
  var v;

restart: 
  propagations = 0;
  sat_clauses = 0;

  for (int i = 0; i < n_clauses; ++i) {
    
    undef_lits = 0;
    undef_j = -1;

    for (int j = 0; j < clauses_len[i]; ++j) {
      l = clauses[i][j];
      v = VAR(l);

      if (current_assignment[v] == SIGN(l)) {
        // clause is satisfied
        ++sat_clauses;
        goto next_clause;
      }

      if (current_assignment[v] == UNDEF) {
        // clause can be satisfied
        if (undef_lits) goto next_clause;
        ++undef_lits;
        undef_j = j;
      }
    }

    if (!undef_lits) return UNSAT;

    l = clauses[i][undef_j];
    //printf("up %d @ %d\n", l, search_depth);
    current_assignment[VAR(l)] = SIGN(l);
    ++trail_head;
    trail[trail_head] = l;
    trail_depth[trail_head] = search_depth;
    ++propagations;
    ++sat_clauses;

    next_clause: continue;
  }

  if (sat_clauses == n_clauses) {
    return SAT;
  }

  if (propagations) goto restart;

  return UNDEF;
}

void make_decision(lit l) {
  ++search_depth;
  current_assignment[VAR(l)] = SIGN(l);
  ++trail_head;
  trail[trail_head] = l;
  trail_depth[trail_head] = search_depth;
}

void backtrack(int to_depth) {
  while (trail_head >= 0 && trail_depth[trail_head] > to_depth) {
    lit unassign = trail[trail_head];
    current_assignment[VAR(unassign)] = UNDEF;
    --trail_head;
  }

  search_depth = to_depth;
}

int search() {
  int res = propagate();

  int level = search_depth;

  if (res != UNDEF) {
    return res;
  }

  printf("%d %d %d\n", n_vars, search_depth, trail_head);

  var branch = select_branch_variable();
  printf("branch on %d\n", branch);

  assert(branch != 0);

  make_decision(POS(branch));
  
  //printf("branch %d\n", branch);

  if (search() == SAT) {
    return SAT;
  }
  //printf("%d %d %d\n", n_vars, search_depth, trail_head);
  //printf("backtrack\n");
  backtrack(level);
  //printf("%d %d %d\n", n_vars, search_depth, trail_head);

  make_decision(NEG(branch));
  //printf("branch %d FALSE\n", branch);
  res = search();

  return res;
}

void dpll() {
  search_depth = 0;
  current_assignment = (lit *) malloc(sizeof(lit) * n_vars+1);
  std::fill(current_assignment, current_assignment+n_vars+1, UNDEF);

  trail = (lit *) malloc(sizeof(lit) * n_vars);
  trail_depth = (int *) malloc(sizeof(int) * n_vars);
  trail_head = -1;

  int res = search();

  if (res == SAT) {
    std::sort(current_assignment+1, current_assignment+n_vars, [](const lit l1, const lit l2){ return var(l1) < var(l2); });
    printf("s SATISFIABLE\n");
    printf("v");
    for (var i = 1; i <= n_vars; ++i) {
      printf(" %d", current_assignment[i] == TRUE ? POS(i) : NEG(i));
    };
    printf("\n");
  } else if (res == UNSAT) {
    printf("s UNSATISFIABLE\n");
  } else {
    printf("s UNKNOWN\n");
  }
}

int main(int argv, char ** argc) {
  if (argv == 2) {
    parse( argc[1] );
    dpll();
  }
}
