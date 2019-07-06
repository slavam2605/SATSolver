#include <cmath>
#include "sat_remapper.h"
#include "debug.h"

sat_remapper::sat_remapper(uint32_t nb_vars) {
    old_nb_vars = nb_vars;
    prior_map.resize(nb_vars + 1);
    std::fill(prior_map.begin(), prior_map.end(), preprocessor_value_state::UNDEF);
    variable_map.resize(nb_vars + 1);
    next_var = 1;
}

void sat_remapper::add_prior(int var, preprocessor_value_state value) {
    prior_map[var] = value;
}

void sat_remapper::add_undef_var(int var) {
    variable_map[var] = next_var++;
}

void sat_remapper::add_ver_var(int var, const std::vector<std::vector<int>>& clauses) {
    prior_map[var] = preprocessor_value_state::VER;
    ver_clauses.emplace_back(var, clauses);
}

void sat_remapper::add_any_var(int var) {
    // TODO: Support ANY (replace TRUE with ANY here)
    prior_map[var] = preprocessor_value_state::TRUE;
}

std::vector<int8_t> sat_remapper::remap(std::vector<int8_t> values) {
    std::vector<preprocessor_value_state> result;
    result.push_back(preprocessor_value_state::UNDEF);
    for (auto var = 1; var <= old_nb_vars; var++) {
        auto value = prior_map[var];
        switch (value) {
            case preprocessor_value_state::TRUE:
            case preprocessor_value_state::FALSE:
                result.push_back(value);
                break;
            case preprocessor_value_state::UNDEF: {
                auto new_var = variable_map[var];
                result.push_back(values[new_var] ? preprocessor_value_state::TRUE : preprocessor_value_state::FALSE);
                break;
            }
            case preprocessor_value_state::ANY:
                // TODO support iteration over all solutions
                result.push_back(preprocessor_value_state::TRUE);
                break;
            case preprocessor_value_state::VER:
                result.push_back(preprocessor_value_state::VER);
                break;
        }
    }
    for (auto riter = ver_clauses.rbegin(); riter != ver_clauses.rend(); ++riter) {
        const auto& [var, old_clauses] = *riter;
        for (const auto& clause: old_clauses) {
            auto unsat = true;
            auto var_positive = true;
            for (int signed_var: clause) {
                if (signed_var == var) {
                    var_positive = true;
                    continue;
                }
                if (signed_var == -var) {
                    var_positive = false;
                    continue;
                }
                auto value = result[abs(signed_var)];
                switch (value) {
                    case preprocessor_value_state::TRUE:
                    case preprocessor_value_state::FALSE:
                        break;
                    default:
                        debug(debug_logic_error("Expected TRUE or FALSE, found: " << (int) result[var]))
                }
                if ((value == preprocessor_value_state::TRUE && signed_var > 0) ||
                    (value == preprocessor_value_state::FALSE && signed_var < 0)) {
                    unsat = false;
                    break;
                }
            }
            if (!unsat)
                continue;

            result[var] = var_positive ? preprocessor_value_state::TRUE : preprocessor_value_state::FALSE;
            break;
        }
        if (result[var] == preprocessor_value_state::VER) {
            // TODO: Support ANY (replace TRUE with ANY here)
            result[var] = preprocessor_value_state::TRUE;
        }
    }
    std::vector<int8_t> bool_result;
    bool_result.push_back(false);
    for (auto var = 1; var <= old_nb_vars; var++) {
        switch (result[var]) {
            case preprocessor_value_state::TRUE:
                bool_result.push_back(true);
                break;
            case preprocessor_value_state::FALSE:
                bool_result.push_back(false);
                break;
            default:
                debug(debug_logic_error("Unexpected value in final remap: " << (int) result[var]))
        }
    }
    return bool_result;
}

preprocessor_value_state sat_remapper::get_prior(int var) {
    return prior_map[var];
}

int sat_remapper::get_mapped_variable(int var) {
    return variable_map[var];
}
