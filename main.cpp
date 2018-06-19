#include <cstdio>
#include <cstdlib>
#include <memory>
#include <cstring>

typedef long long int ll;
typedef int lit;

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

int main(int argv, char ** argc) {
  if (argv == 2) parse( argc[1] );
}
