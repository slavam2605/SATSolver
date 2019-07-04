#include <algorithm>
#include "sat_preprocessor.h"

sat_preprocessor::sat_preprocessor(const dimacs &formula) :
        nb_vars(formula.nb_vars),
        clauses(formula.clauses),
        remapper(nb_vars) {
    prior_values.resize(nb_vars + 1);
    std::fill(prior_values.begin(), prior_values.end(), UNDEF);
}

std::pair<dimacs, sat_remapper> sat_preprocessor::preprocess() {
    auto old_nb_clauses = clauses.size();
    propagate_all();
    dimacs new_formula;
    uint32_t new_nb_vars = 0;
    for (auto var = 1; var <= nb_vars; var++) {
        if (prior_values[var] == UNDEF) {
            remapper.add_undef_var(var);
            new_nb_vars++;
        } else {
            remapper.add_prior(var, prior_values[var]);
        }
    }
    for (auto& clause: clauses) {
        for (int& signed_var: clause) {
            auto sign = signed_var > 0 ? 1 : -1;
            auto var = abs(signed_var);
            debug(if (remapper.get_prior(var) != UNDEF)
                debug_logic_error("Prior value is still in preprocessed clause: " << var))

            signed_var = sign * remapper.get_mapped_variable(var);
        }
    }
    new_formula.nb_vars = new_nb_vars;
    new_formula.clauses = clauses;
    new_formula.nb_clauses = (uint32_t) new_formula.clauses.size();
    info("Preprocessor: nb_vars: " << nb_vars << " -> " << new_nb_vars)
    info("Preprocessor: nb_clauses: " << old_nb_clauses << " -> " << new_formula.nb_clauses)
    return std::make_pair(new_formula, remapper);
}

void sat_preprocessor::propagate_all() {
    auto changed = true;
    while (changed) {
        changed = false;
        for (auto& clause: clauses) {
            auto true_value = std::find_if(clause.begin(), clause.end(), [this](int signed_var) {
                return get_signed_prior_value(signed_var) == TRUE;
            });
            if (true_value != clause.end())
                continue;

            auto old_size = clause.size();
            clause.erase(
                    std::remove_if(clause.begin(), clause.end(), [this](int signed_var) {
                        return get_signed_prior_value(signed_var) == FALSE;
                    }),
                    clause.end()
            );
            changed |= old_size != clause.size();
            if (clause.size() == 1) {
                changed = true;
                set_signed_prior_value(clause[0]);
            }
        }
        auto old_size = clauses.size();
        clauses.erase(
                std::remove_if(clauses.begin(), clauses.end(), [this](const auto& clause) {
                    auto true_value = std::find_if(clause.begin(), clause.end(), [this](int signed_var) {
                        return get_signed_prior_value(signed_var) == TRUE;
                    });
                    return true_value != clause.end();
                }),
                clauses.end()
        );
        changed |= old_size != clauses.size();
    }
}

value_state sat_preprocessor::get_signed_prior_value(int signed_var) {
    auto value = prior_values[abs(signed_var)];
    if (value == UNDEF)
        return UNDEF;

    if ((value == TRUE) ^ (signed_var < 0))
        return TRUE;
    else
        return FALSE;
}

void sat_preprocessor::set_signed_prior_value(int signed_var) {
    debug(if (prior_values[abs(signed_var)] != UNDEF)
        debug_logic_error("Tried to reassign value in preprocessing: " << signed_var))

    if (signed_var > 0)
        prior_values[signed_var] = TRUE;
    else
        prior_values[-signed_var] = FALSE;
}
