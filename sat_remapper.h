#ifndef SATSOLVER_SAT_REMAPPER_H
#define SATSOLVER_SAT_REMAPPER_H

#include <vector>
#include <cstdint>

enum class preprocessor_value_state {
    TRUE, FALSE, UNDEF, ANY, VER
};

class sat_remapper {
    std::vector<preprocessor_value_state> prior_map;
    std::vector<int> variable_map;
    std::vector<std::pair<int, std::vector<std::vector<int>>>> ver_clauses;
    uint32_t next_var;
    uint32_t old_nb_vars;
public:
    explicit sat_remapper(uint32_t nb_vars);
    preprocessor_value_state get_prior(int var);
    int get_mapped_variable(int var);
    void add_prior(int var, preprocessor_value_state value);
    void add_undef_var(int var);
    void add_ver_var(int var, const std::vector<std::vector<int>>& clauses);
    void add_any_var(int var);
    std::vector<int8_t> remap(std::vector<int8_t> values);
};


#endif //SATSOLVER_SAT_REMAPPER_H
