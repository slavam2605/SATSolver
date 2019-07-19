#ifndef SATSOLVER_DIMACS_H
#define SATSOLVER_DIMACS_H

#include "solver_types.h"
#include <string>
#include <vector>

struct dimacs {
    unsigned int nb_vars, nb_clauses;
    std::vector<clause*> clauses;

    static dimacs read(const std::string& path);
};


#endif //SATSOLVER_DIMACS_H
