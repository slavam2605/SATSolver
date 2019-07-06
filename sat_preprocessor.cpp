#include <algorithm>
#include <unordered_set>
#include <chrono>
#include <iomanip>
#include "sat_preprocessor.h"
#include "debug.h"

sat_preprocessor::sat_preprocessor(const dimacs &formula) :
        nb_vars(formula.nb_vars),
        clauses(formula.clauses),
        remapper(nb_vars) {
    prior_values.resize(nb_vars + 1);
    std::fill(prior_values.begin(), prior_values.end(), preprocessor_value_state::UNDEF);
}

std::pair<dimacs, sat_remapper> sat_preprocessor::preprocess() {
    auto start_time = std::chrono::steady_clock::now();
    auto old_nb_clauses = clauses.size();

    auto changed = true;
    while (changed) {
        changed = false;
        changed |= propagate_all();
        changed |= niver();
    }

    dimacs new_formula;
    uint32_t new_nb_vars = 0;
    for (auto var = 1; var <= nb_vars; var++) {
        switch (prior_values[var]) {
            case preprocessor_value_state::UNDEF:
                remapper.add_undef_var(var);
                new_nb_vars++;
                break;
            case preprocessor_value_state::TRUE:
            case preprocessor_value_state::FALSE:
                remapper.add_prior(var, prior_values[var]);
                break;
            case preprocessor_value_state::ANY:
                remapper.add_any_var(var);
                break;
            case preprocessor_value_state::VER:
                // ver clauses have been already added to remapper
                break;
        }
    }
    for (auto& clause: clauses) {
        for (int& signed_var: clause) {
            auto sign = signed_var > 0 ? 1 : -1;
            auto var = abs(signed_var);
            debug(if (remapper.get_prior(var) != preprocessor_value_state::UNDEF)
                debug_logic_error("Prior value is still in preprocessed clause: " << var << ", value: " << (int) remapper.get_prior(var)))

            signed_var = sign * remapper.get_mapped_variable(var);
        }
    }
    new_formula.nb_vars = new_nb_vars;
    new_formula.clauses = clauses;
    new_formula.nb_clauses = (uint32_t) new_formula.clauses.size();
    info("Preprocessor: nb_vars: " << nb_vars << " -> " << new_nb_vars)
    info("Preprocessor: nb_clauses: " << old_nb_clauses << " -> " << new_formula.nb_clauses)
    auto duration = std::chrono::steady_clock::now() - start_time;
    info("Preprocessor: Elapsed time: " << std::fixed << std::setprecision(1)
         << std::chrono::duration_cast<std::chrono::milliseconds>(duration).count() / 1000.0 << " seconds")
    return std::make_pair(new_formula, remapper);
}

std::vector<int> sat_preprocessor::resolve(int var, const std::vector<int>& clause1, const std::vector<int>& clause2) {
    std::vector<int> result;
    result.insert(result.end(), clause1.begin(), clause1.end());
    result.insert(result.end(), clause2.begin(), clause2.end());
    auto remove_var = std::remove(result.begin(), result.end(), var);
    auto remove_nvar = std::remove(result.begin(), remove_var, -var);
    std::sort(result.begin(), remove_nvar);
    auto remove_unique = std::unique(result.begin(), remove_nvar);
    result.erase(remove_unique, result.end());
    return result;
}

bool sat_preprocessor::is_tautology(const std::vector<int>& clause) {
    static std::unordered_set<int> used_vars;

    used_vars.clear();
    for (int signed_var: clause) {
        auto var = abs(signed_var);
        if (used_vars.find(var) != used_vars.end())
            return true;

        used_vars.insert(var);
    }
    return false;
}

bool sat_preprocessor::niver() {
    static auto invalidate_clause = [](std::vector<int>& clause) {
        clause = std::vector<int> {0};
    };
    static auto is_invalidated = [](const std::vector<int>& clause) {
        return clause.size() == 1 && clause[0] == 0;
    };

    auto changed = false;
    std::vector<int8_t> invalidated;
    std::vector<std::vector<int>> pvar_clauses;
    std::vector<std::vector<int>> nvar_clauses;
    invalidated.resize(nb_vars + 1);
    pvar_clauses.resize(nb_vars + 1);
    nvar_clauses.resize(nb_vars + 1);
    for (auto clause_id = 0; clause_id < clauses.size(); clause_id++) {
        for (int signed_var: clauses[clause_id]) {
            if (signed_var > 0) {
                pvar_clauses[signed_var].push_back(clause_id);
            } else {
                nvar_clauses[-signed_var].push_back(clause_id);
            }
        }
    }

    for (auto var = 1; var <= nb_vars; var++) {
        if (prior_values[var] != preprocessor_value_state::UNDEF || invalidated[var])
            continue;

        if (pvar_clauses[var].empty() && nvar_clauses[var].empty()) {
            changed = true;
            prior_values[var] = preprocessor_value_state::ANY;
            continue;
        }

        debug(
            for (int pclause_id: pvar_clauses[var]) {
                if (is_invalidated(clauses[pclause_id]))
                    debug_logic_error("Deleted clause encountered")
            }
            for (int nclause_id: nvar_clauses[var]) {
                if (is_invalidated(clauses[nclause_id]))
                    debug_logic_error("Deleted clause encountered")
            }
        )

        auto old_size = 0;
        auto new_size = 0;
        for (int pclause_id: pvar_clauses[var]) {
            old_size += clauses[pclause_id].size();
        }
        for (int nclause_id: nvar_clauses[var]) {
            old_size += clauses[nclause_id].size();
        }
        std::vector<std::vector<int>> new_clauses;
        for (int pclause_id: pvar_clauses[var]) {
            for (int nclause_id: nvar_clauses[var]) {
                auto new_clause = resolve(var, clauses[pclause_id], clauses[nclause_id]);
                if (!is_tautology(new_clause)) {
                    new_clauses.push_back(new_clause);
                    new_size += new_clause.size();
                    if (new_size > old_size)
                        break;
                }
            }
            if (new_size > old_size)
                break;
        }

        if (new_size <= old_size) {
            if (pvar_clauses[var].size() == 0) {
                set_signed_prior_value(-var);
            } else if (nvar_clauses[var].size() == 0) {
                set_signed_prior_value(var);
            } else {
                prior_values[var] = preprocessor_value_state::VER;
                std::vector<std::vector<int>> ver_clauses;
                for (int pclause_id: pvar_clauses[var]) {
                    ver_clauses.push_back(clauses[pclause_id]);
                }
                for (int nclause_id: nvar_clauses[var]) {
                    ver_clauses.push_back(clauses[nclause_id]);
                }
                remapper.add_ver_var(var, ver_clauses);
            }
            for (int pclause_id: pvar_clauses[var]) {
                for (int signed_var: clauses[pclause_id]) {
                    invalidated[abs(signed_var)] = true;
                }
                invalidate_clause(clauses[pclause_id]);
            }
            for (int nclause_id: nvar_clauses[var]) {
                for (int signed_var: clauses[nclause_id]) {
                    invalidated[abs(signed_var)] = true;
                }
                invalidate_clause(clauses[nclause_id]);
            }
            clauses.insert(clauses.end(), new_clauses.begin(), new_clauses.end());
            changed = true;
        }
    }
    clauses.erase(
            std::remove_if(clauses.begin(), clauses.end(), is_invalidated),
            clauses.end()
    );
    return changed;
}

bool sat_preprocessor::propagate_all() {
    auto changed = true;
    auto ever_changed = false;
    while (changed) {
        changed = false;
        for (auto& clause: clauses) {
            if (find_true_literal(clause) != clause.end())
                continue;

            changed |= remove_false_literals(clause);
            if (clause.size() == 1) {
                changed = true;
                set_signed_prior_value(clause[0]);
            }
        }
        changed |= remove_true_clauses();
        ever_changed |= changed;
    }
    return ever_changed;
}

bool sat_preprocessor::remove_true_clauses() {
    auto old_size = clauses.size();
    clauses.erase(
            std::remove_if(clauses.begin(), clauses.end(), [this](const auto& clause) {
                return find_true_literal(clause) != clause.end();
            }),
            clauses.end()
    );
    return old_size != clauses.size();
}

bool sat_preprocessor::remove_false_literals(std::vector<int>& clause) {
    auto old_size = clause.size();
    clause.erase(
            std::remove_if(clause.begin(), clause.end(), [this](int signed_var) {
                return get_signed_prior_value(signed_var) == preprocessor_value_state::FALSE;
            }),
            clause.end()
    );
    return old_size != clause.size();
}

std::vector<int>::const_iterator sat_preprocessor::find_true_literal(const std::vector<int>& clause) {
    return std::find_if(clause.begin(), clause.end(), [this](int signed_var) {
        return get_signed_prior_value(signed_var) == preprocessor_value_state::TRUE;
    });
}

preprocessor_value_state sat_preprocessor::get_signed_prior_value(int signed_var) {
    auto value = prior_values[abs(signed_var)];
    if (value != preprocessor_value_state::TRUE && value != preprocessor_value_state::FALSE)
        return value;

    if ((value == preprocessor_value_state::TRUE) ^ (signed_var < 0))
        return preprocessor_value_state::TRUE;
    else
        return preprocessor_value_state::FALSE;
}

void sat_preprocessor::set_signed_prior_value(int signed_var) {
    debug(if (prior_values[abs(signed_var)] != preprocessor_value_state::UNDEF)
        debug_logic_error("Tried to reassign value in preprocessing: " << signed_var))

    if (signed_var > 0)
        prior_values[signed_var] = preprocessor_value_state::TRUE;
    else
        prior_values[-signed_var] = preprocessor_value_state::FALSE;
}
