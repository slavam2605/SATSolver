#ifndef SATSOLVER_SAT_PREPROCESSOR_H
#define SATSOLVER_SAT_PREPROCESSOR_H

#include <vector>
#include "dimacs.h"
#include "solver.h"
#include "sat_remapper.h"

class sat_preprocessor {
    uint32_t nb_vars;
    std::vector<std::vector<int>> clauses;
    std::vector<value_state> prior_values;
    sat_remapper remapper;
public:
    explicit sat_preprocessor(const dimacs& formula);
    std::pair<dimacs, sat_remapper> preprocess();

private:
    void propagate_all();
    void set_signed_prior_value(int signed_var);
    value_state get_signed_prior_value(int signed_var);
};

#endif //SATSOLVER_SAT_PREPROCESSOR_H
