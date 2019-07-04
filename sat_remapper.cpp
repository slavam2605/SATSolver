#include "sat_remapper.h"

sat_remapper::sat_remapper(uint32_t nb_vars) {
    old_nb_vars = nb_vars;
    prior_map.resize(nb_vars + 1);
    std::fill(prior_map.begin(), prior_map.end(), UNDEF);
    variable_map.resize(nb_vars + 1);
    next_var = 1;
}

void sat_remapper::add_prior(int var, bool value) {
    prior_map[var] = value ? TRUE : FALSE;
}

void sat_remapper::add_undef_var(int var) {
    variable_map[var] = next_var++;
}

std::vector<int8_t> sat_remapper::remap(std::vector<int8_t> values) {
    std::vector<int8_t> result;
    result.push_back(0);
    for (auto var = 1; var <= old_nb_vars; var++) {
        auto value = prior_map[var];
        if (value != UNDEF) {
            result.push_back(value);
        } else {
            auto new_var = variable_map[var];
            result.push_back(values[new_var]);
        }
    }
    return result;
}

value_state sat_remapper::get_prior(int var) {
    return prior_map[var];
}

int sat_remapper::get_mapped_variable(int var) {
    return variable_map[var];
}
