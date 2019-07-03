#ifndef SATSOLVER_DIMACS_H
#define SATSOLVER_DIMACS_H

#include <string>
#include <vector>

struct dimacs {
    unsigned int nb_vars, nb_clauses;
    std::vector<std::vector<int>> clauses;

    static dimacs read(const std::string& path);
};


#endif //SATSOLVER_DIMACS_H
