#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <chrono>
#include <iomanip>
#include "sat_preprocessor.h"
#include "debug.h"

sat_preprocessor::sat_preprocessor(const dimacs &formula) :
        nb_vars(formula.nb_vars),
        clauses(formula.clauses),
        remapper(nb_vars),
        propagated(0),
        niver_eliminated(0),
        hyp_bin_res_resolved(0),
        equality_eliminated(0) {
    prior_values.resize(nb_vars + 1);
    std::fill(prior_values.begin(), prior_values.end(), preprocessor_value_state::UNDEF);
    unsat = false;
}

std::pair<dimacs, sat_remapper> sat_preprocessor::preprocess() {
    start_time = std::chrono::steady_clock::now();
    auto old_nb_clauses = clauses.size();

    info("nb_vars = " << nb_vars << ", nb_clauses = " << clauses.size());
    auto changed = true;
    // TODO: maybe add edges from implication graph to the formula
    // TODO: maybe filter out defined variables from implication graph to improve performance
    while (changed && !is_interrupted()) {
        changed = false;
        changed |= propagate_all();
        changed |= niver();
        changed |= hyper_binary_resolution();
        changed |= eliminate_equality();

        debug(
            std::unordered_set<int> vars;
            for (const auto& clause: clauses) {
                for (int signed_var: clause) {
                    vars.insert(abs(signed_var));
                }
            }
            info("nb_vars = " << vars.size() << ", nb_clauses = " << clauses.size())
            print_clause_statistics();
        )
    }
    if (check_unsat()) {
        info("UNSAT in preprocessor")
        return std::make_pair(dimacs{0, 1, {{}}}, remapper);
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
            case preprocessor_value_state::EQ:
                // eq variable have been already added to remapper
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
    info("Preprocessor: variables propagated: " << propagated << ", " <<
         hyp_bin_res_resolved << " of them resolved with hyp_bin_res")
    info("Preprocessor: NiVER eliminated: " << niver_eliminated)
    info("Preprocessor: eliminated with equality: " << equality_eliminated)
    auto duration = std::chrono::steady_clock::now() - start_time;
    info("Preprocessor: Elapsed time: " << std::fixed << std::setprecision(1)
         << std::chrono::duration_cast<std::chrono::milliseconds>(duration).count() / 1000.0 << " seconds")
    return std::make_pair(new_formula, remapper);
}

void sat_preprocessor::add_implication_edge(int from, int to) {
    implication_graph[from].insert(to);
};

bool sat_preprocessor::has_implication_edge(int from, int to) {
    const auto& set = implication_graph[from];
    return set.find(to) != set.end();
};

bool sat_preprocessor::hyper_binary_resolution() {
    if (is_interrupted())
        return false;

    info("Started HypBinRes...")
    bool changed = false;
    auto local_start = std::chrono::steady_clock::now();
    std::unordered_set<int> unit_literals;

    for (const auto& clause: clauses) {
        if (clause.size() == 2) {
            add_implication_edge(-clause[0], clause[1]);
            add_implication_edge(-clause[1], clause[0]);
        }
        if (clause.size() == 1) {
            unit_literals.insert(clause[0]);
        }
    }

    for (auto clause_id = 0; clause_id < clauses.size(); clause_id++) {
        if (is_interrupted_hyp_bin_res(local_start))
            break;

        auto clause = clauses[clause_id];
        std::unordered_map<int, int> literal_count {};
        for (int signed_var: clause) {
            for (int implied_literal: implication_graph[signed_var]) {
                if (prior_values[abs(implied_literal)] != preprocessor_value_state::UNDEF)
                    continue;

                literal_count[implied_literal]++;
            }
        }
        for (auto [literal, count]: literal_count) {
            if (count < clause.size() - 1)
                continue;

            auto failed = false;
            auto missed_literal = 0;
            for (int signed_var: clause) {
                if (!has_implication_edge(signed_var, literal)) {
                    if (missed_literal != 0) {
                        failed = true;
                        break;
                    }
                    missed_literal = signed_var;
                }
            }
            if (failed)
                continue;

            if (missed_literal == 0 || missed_literal == literal) {
                if (unit_literals.find(literal) == unit_literals.end()) {
                    clauses.push_back({literal});
                    unit_literals.insert(literal);
                    hyp_bin_res_resolved++;
                    changed = true;
                }
                continue;
            }

            // tautology
            if (missed_literal == -literal)
                continue;

            if (has_implication_edge(-missed_literal, literal))
                continue;

            add_implication_edge(-missed_literal, literal);
            add_implication_edge(-literal, missed_literal);
        }
    }

    return changed;
}

bool sat_preprocessor::eliminate_equality() {
    if (is_interrupted())
        return false;

    info("Started equality elimination...")
    auto changed = false;
    std::vector<int> equality;
    equality.resize(nb_vars + 1);

    auto set_equal = [&equality](int signed_from, int signed_to) {
        if (abs(signed_to) < abs(signed_from))
            std::swap(signed_from, signed_to);

        auto from = abs(signed_from);
        auto sign = signed_from > 0 ? 1 : -1;
        equality[from] = signed_to * sign;
    };
    auto get_equal = [&equality](int signed_from) -> int {
        auto from = abs(signed_from);
        auto sign = signed_from > 0 ? 1 : -1;
        return equality[from] * sign;
    };

    for (const auto& [from, set]: implication_graph) {
        if (prior_values[abs(from)] != preprocessor_value_state::UNDEF)
            continue;

        for (auto to: set) {
            if (prior_values[abs(to)] != preprocessor_value_state::UNDEF)
                continue;

            if (has_implication_edge(to, from)) {
                set_equal(from, to);
            }
        }
    }

    for (auto var = 1; var <= nb_vars; var++) {
        auto eq_var = get_equal(var);
        while (get_equal(eq_var) != 0) {
            eq_var = get_equal(eq_var);
        }
        if (eq_var != 0) {
            set_equal(var, eq_var);
        }
    }

    for (auto& clause: clauses) {
        for (int& signed_var: clause) {
            auto eq_var = get_equal(signed_var);
            if (eq_var == 0)
                continue;

            signed_var = eq_var;
            changed = true;
        }
        std::sort(clause.begin(), clause.end());
        clause.erase(
                std::unique(clause.begin(), clause.end()),
                clause.end()
        );
        if (is_tautology(clause)) {
            invalidate_clause(clause);
        }
    }
    clauses.erase(
            std::remove_if(clauses.begin(), clauses.end(), is_invalidated),
            clauses.end()
    );

    for (auto var = 1; var <= nb_vars; var++) {
        auto eq_var = get_equal(var);
        if (eq_var == 0)
            continue;

        prior_values[var] = preprocessor_value_state::EQ;
        remapper.add_eq_var(var, eq_var);
        equality_eliminated++;
    }

    return changed;
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

void sat_preprocessor::invalidate_clause(std::vector<int>& clause) {
    clause = std::vector<int> {0};
};

bool sat_preprocessor::is_invalidated(const std::vector<int>& clause) {
    return clause.size() == 1 && clause[0] == 0;
};

bool sat_preprocessor::niver() {
    if (is_interrupted())
        return false;

    info("Started NiVER...")
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
        if (is_interrupted())
            break;

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
            niver_eliminated++;
        }
    }
    clauses.erase(
            std::remove_if(clauses.begin(), clauses.end(), is_invalidated),
            clauses.end()
    );
    return changed;
}

bool sat_preprocessor::propagate_all() {
    info("Started propagation...")
    auto changed = true;
    auto ever_changed = false;
    while (changed && !is_interrupted()) {
        changed = false;
        for (auto& clause: clauses) {
            if (find_true_literal(clause) != clause.end())
                continue;

            changed |= remove_false_literals(clause);
            if (clause.size() == 1) {
                changed = true;
                set_signed_prior_value(clause[0]);
                propagated++;
            }
        }
        for (auto [literal, set]: implication_graph) {
            if (get_signed_prior_value(literal) != preprocessor_value_state::TRUE)
                continue;

            for (auto implied_literal: set) {
                if (prior_values[abs(implied_literal)] != preprocessor_value_state::UNDEF)
                    continue;

                changed = true;
                set_signed_prior_value(implied_literal);
                propagated++;
            }
        }
        changed |= remove_true_clauses();
        ever_changed |= changed;
    }
    for (auto& clause: clauses) {
        remove_false_literals(clause);
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
    unsat |= clause.size() == 0;
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

bool sat_preprocessor::is_interrupted() {
    if (unsat)
        return true;

    auto now = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(now - start_time);
    return elapsed >= global_timeout;
}

bool sat_preprocessor::is_interrupted_hyp_bin_res(std::chrono::steady_clock::time_point start) {
    if (is_interrupted())
        return true;

    auto now = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(now - start);
    return elapsed >= hyp_bin_res_timeout;
}

bool sat_preprocessor::check_unsat() {
    if (unsat)
        return true;

    debug(
        for (const auto& clause: clauses) {
            if (clause.empty()) {
                debug_logic_error("UNSAT was detected only with linear check")
            }
        }
    )
    return false;
}

debug_def(
        void sat_preprocessor::print_clause_statistics() {
            std::vector<int> clause_size;
            clause_size.resize(10);
            auto other = 0;
            for (const auto& clause: clauses) {
                if (clause.size() >= clause_size.size()) {
                    other++;
                    continue;
                }

                clause_size[clause.size()]++;
            }
            for (auto size = 0; size < clause_size.size(); size++) {
                if (clause_size[size] == 0)
                    continue;

                std::cout << "<" << size << ">: " << clause_size[size] << ", ";
            }
            std::cout << "other: " << other << std::endl << std::endl;
        }
)