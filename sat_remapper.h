#ifndef SATSOLVER_SAT_REMAPPER_H
#define SATSOLVER_SAT_REMAPPER_H

#include "solver_types.h"
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
    std::vector<std::vector<literal>> ver_clauses;
    literal eq_lit;

    static remap_event create_ver(const std::vector<std::vector<literal>>& clauses) {
        return {
            remap_event_type::VER,
            clauses,
            literal::undef
        };
    }

    static remap_event create_eq(literal eq_lit) {
        return {
            remap_event_type::EQ,
            {},
            eq_lit
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
    void add_ver_var(int var, const std::vector<std::vector<literal>>& clauses);
    void add_any_var(int var);
    void add_eq_var(int var, literal eq_lit);
    std::vector<int8_t> remap(std::vector<int8_t> values);
};


#endif //SATSOLVER_SAT_REMAPPER_H
