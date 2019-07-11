#ifndef SATSOLVER_SAT_REMAPPER_H
#define SATSOLVER_SAT_REMAPPER_H

#include <vector>
#include <cstdint>

enum class preprocessor_value_state {
    TRUE, FALSE, UNDEF, ANY, VER, EQ
};

enum class remap_event_type {
    VER, EQ
};

struct remap_event {
    remap_event_type type;
    std::vector<std::vector<int>> ver_clauses;
    int eq_var;

    static remap_event create_ver(const std::vector<std::vector<int>>& clauses) {
        return {
            remap_event_type::VER,
            clauses,
            0
        };
    }

    static remap_event create_eq(int eq_var) {
        return {
            remap_event_type::EQ,
            {},
            eq_var
        };
    }
};

class sat_remapper {
    std::vector<preprocessor_value_state> prior_map;
    std::vector<int> variable_map;
    std::vector<std::pair<int, remap_event>> remap_events;
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
    void add_eq_var(int var, int eq_var);
    std::vector<int8_t> remap(std::vector<int8_t> values);
};


#endif //SATSOLVER_SAT_REMAPPER_H
