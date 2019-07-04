#ifndef SATSOLVER_SAT_REMAPPER_H
#define SATSOLVER_SAT_REMAPPER_H

#include "solver.h"

class sat_remapper {
    std::vector<value_state> prior_map;
    std::vector<int> variable_map;
    uint32_t next_var;
    uint32_t old_nb_vars;
public:
    explicit sat_remapper(uint32_t nb_vars);
    value_state get_prior(int var);
    int get_mapped_variable(int var);
    void add_prior(int var, bool value);
    void add_undef_var(int var);
    std::vector<int8_t> remap(std::vector<int8_t> values);
};


#endif //SATSOLVER_SAT_REMAPPER_H
