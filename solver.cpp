#include "solver.h"
#include "debug.h"
#include "clause_allocator.h"
#include <sstream>
#include <iostream>
#include <iomanip>
#include <cmath>
#include <cstdlib>
#include <algorithm>
#include <random>
#include <unordered_set>
#include <queue>

solver::solver(const dimacs &formula, std::chrono::seconds timeout)
        : nb_vars(formula.nb_vars),
          vsids(*this),
          priors(0),
          decisions(0),
          propagations(0),
          conflicts(0),
          timeout(timeout) {
    // init prior values
    prior_values.resize(nb_vars + 1);
    std::fill(prior_values.begin(), prior_values.end(), UNDEF);

    // init clauses
    for (auto pclause: formula.clauses) {
        if (pclause->size() == 1) {
            set_prior_value(pclause->literals[0]);
        } else {
            clauses.push_back(pclause);
        }
    }

    init(false);
}

void solver::init(bool restart) {
    unsat = false;
    pconflict_clause = nullptr;
    values_count = 0;
    debug(if (!propagation_queue.empty())
        debug_logic_error("Propagation queue is not empty on restart"))

    if (restart) {
        values.clear();
        antecedent_clauses.clear();
        var_implied_depth.clear();
        var_to_decision_level.clear();
        var_to_watch_clauses[0].clear();
        var_to_watch_clauses[1].clear();
        watch_vars.clear();
        values_stack.clear();
        snapshots.clear();

        auto initial_clauses_count = 0;
        for (auto pclause: clauses) {
            if (pclause->is_learnt())
                break;

            initial_clauses_count++;
        }

        debug(
            for (auto clause_id = initial_clauses_count; clause_id < clauses.size(); clause_id++) {
                if (!clauses[clause_id]->is_learnt())
                    debug_logic_error("Found a non-learnt clause after prefix")
            }
        )

        std::sort(clauses.begin() + initial_clauses_count, clauses.end(), [this](auto p1, auto p2) {
            return p1->stat.lbd < p2->stat.lbd;
        });
        auto keep_count = (size_t) ((clauses.size() - initial_clauses_count) * clause_keep_ratio) + initial_clauses_count;
        // Always keep 'glue' clauses
        while (keep_count < clauses.size() && clauses[keep_count]->stat.lbd <= 2)
            keep_count++;

        clauses.resize(keep_count);
        current_clause_limit = (size_t) ((current_clause_limit - initial_clauses_count)* clause_limit_inc_factor + initial_clauses_count);

        vsids.rebuild();
    } else {
        current_clause_limit = (size_t) (clauses.size() * (clause_limit_init_factor + 1));
        log_iteration = 0;

        // init vsids score
        vsids.init();
    }

    // init values
    values.resize(nb_vars + 1);
    std::fill(values.begin(), values.end(), UNDEF);

    // init antecedent clauses
    antecedent_clauses.resize(nb_vars + 1);
    std::fill(antecedent_clauses.begin(), antecedent_clauses.end(), -1);

    // init implied depth of variables
    var_implied_depth.resize(nb_vars + 1);
    std::fill(var_implied_depth.begin(), var_implied_depth.end(), 0);

    // init var to decision level
    var_to_decision_level.resize(nb_vars + 1);

    // build 2-watch-literals structures
    var_to_watch_clauses[0].resize(nb_vars + 1);
    var_to_watch_clauses[1].resize(nb_vars + 1);
    for (auto i = 0; i < clauses.size(); i++) {
        debug(if (clauses[i]->size() <= 1)
            debug_logic_error("Size of initial clause is too small: " << clauses[i]->size()))

        auto x = clauses[i]->literals[0];
        auto y = clauses[i]->literals[1];
        watch_vars.emplace_back(x, y);
        var_to_watch_clauses[x.sign()][x.var()].push_back(i);
        var_to_watch_clauses[y.sign()][y.var()].push_back(i);
    }

    probe_literals();
}

void solver::probe_literals() {
    static std::vector<int> vars_order;

    vars_order.resize(nb_vars);
    for (auto var = 1; var <= nb_vars; var++) {
        vars_order[var - 1] = var;
    }
    std::random_shuffle(vars_order.begin(), vars_order.end());

    auto start = std::chrono::steady_clock::now();

    apply_prior_values();

    auto var_count = 0;
    auto changed = true;
    while (changed) {
        changed = false;
        for (auto var: vars_order) {
            auto duration = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - start);
            if (duration > probe_timeout)
                goto end;

#ifdef TRACE
            auto milliseconds_duration = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start);
            auto speed = (double) var_count / milliseconds_duration.count();
            std::cout << "Performance[" << var_count << "]: \t" << speed * 1000 << " probes/sec" << std::endl;
            var_count++;
#endif

            for (auto value: {false, true}) {
                if (values[var] != UNDEF)
                    continue;

                take_snapshot(var);
                set_value(var, value, -1);
                propagate_all();
                if (unsat) {
                    auto conflict_clause = find_1uip_conflict_clause();
                    auto best_lit = literal::undef;
                    for (auto lit: conflict_clause) {
                        if (var_to_decision_level[lit.var()] == 1) {
                            if (best_lit == literal::undef) {
                                best_lit = lit;
                            } else {
                                debug(debug_logic_error("More than 1 var from current decision level => not a UIP clause"))
                            }
                        }
                    }
                    changed |= true;
                    backtrack();
                    set_prior_value(best_lit);
                    set_literal_value(best_lit, -1);
                    propagate_all(true);
                    if (unsat)
                        goto end;
                } else {
                    backtrack();
                }
            }
        }
    }
    end:
    if (unsat) {
        info("UNSAT from literals probing")
    }

    auto duration = std::chrono::steady_clock::now() - start;
    info("Failed literals probing: " << std::chrono::duration_cast<std::chrono::milliseconds>(duration).count() << " ms, tried: " << var_count)
}

void solver::clear_state() {
    // TODO this method may break some invariants
    values_count = 0;
    std::fill(values.begin(), values.end(), UNDEF);
    std::fill(antecedent_clauses.begin(), antecedent_clauses.end(), -1);
    values_stack.clear();
    vsids.rebuild();
}

sat_result solver::current_result() {
    if (unsat)
        return UNSAT;

    if (values_count == nb_vars)
        return SAT;

    return UNKNOWN;
}

std::pair<sat_result, std::vector<int8_t>> solver::solve() {
    start_time = std::chrono::steady_clock::now();
    log_time = start_time;

    apply_prior_values();
    if (current_result() != UNKNOWN) {
        return report_result(current_result());
    }

    // TODO: sort clauses with usage count along with LBD and size
    // TODO: clause deletion while solving (before restart)
    // TODO: get rid of implied_depth and traverse in order of trail
    while (unsat || values_count < nb_vars) {
        int next_var;
        bool value;
        if (unsat) {
            auto decision_level = analyse_conflict();
            trace("Level from analyse_conflict: " << decision_level << ", current: " << current_decision_level())

            do {
                backtrack();
            } while (current_decision_level() >= decision_level);

            if (current_decision_level() == 0) {
                clear_state();
                apply_prior_values();
                if (current_result() != UNKNOWN) {
                    return report_result(current_result());
                }
            }
        }

        next_var = pick_var();
        value = pick_polarity();
        take_snapshot(next_var);

        if (!set_value(next_var, value, -1))
            debug(debug_logic_error("Decision failed"))
        decisions++;

        propagate_all();
        if (clauses.size() > current_clause_limit) {
            init(true);
            if (unsat) {
                return report_result(false);
            }
            apply_prior_values();
            info("Restart, new clause limit: " << current_clause_limit << ", clause count: " << clauses.size())
            debug(if (unsat)
                debug_logic_error("UNSAT just after restart: should be detected earlier"))
        }

        if (!timer_log())
            return std::make_pair(UNKNOWN, std::vector<int8_t>());
    }

    return report_result(true);
}

std::vector<literal> solver::find_1uip_conflict_clause() {
    static std::vector<int8_t> var_count;

    conflicts++;
    if (pconflict_clause->is_learnt())
        pconflict_clause->stat.used++;

    vsids.on_conflict();

    var_count.resize(nb_vars + 1);
    std::fill(var_count.begin(), var_count.end(), 0);
    auto level_count = 0;
    for (auto lit: pconflict_clause->literals) {
        auto level = var_to_decision_level[lit.var()];
        if (level == current_decision_level())
            level_count++;
        var_count[lit.var()]++;
    }

    auto compare = [this](auto left_lit, auto right_lit) {
        return var_implied_depth[left_lit.var()] < var_implied_depth[right_lit.var()];
    };
    std::priority_queue<literal, std::vector<literal>, decltype(compare)> new_clause_queue(compare);
    for (auto lit: pconflict_clause->literals) {
        new_clause_queue.push(lit);
    }
    std::vector<literal> new_literals;

    if (level_count > 1) {
        while (!new_clause_queue.empty()) {
            auto lit = new_clause_queue.top();
            new_clause_queue.pop();
            auto level = var_to_decision_level[lit.var()];
            if (level != current_decision_level()) {
                if (prior_values[lit.var()] == UNDEF)
                    new_literals.push_back(lit);
                continue;
            }

            auto clause_id = antecedent_clauses[lit.var()];
            if (clauses[clause_id]->is_learnt())
                clauses[clause_id]->stat.used++;

            debug(if (clause_id == -1)
                debug_logic_error("1-UIP algorithm reached decision variable from current level"))

            level_count--;
            for (auto other_lit: clauses[clause_id]->literals) {
                if (other_lit.var() == lit.var() || var_count[other_lit.var()] > 0)
                    continue;

                auto other_level = var_to_decision_level[other_lit.var()];
                new_clause_queue.push(other_lit);
                if (other_level == current_decision_level())
                    level_count++;
                var_count[other_lit.var()]++;
            }

            // Stop at first UIP
            if (level_count == 1)
                break;
        }
        while (!new_clause_queue.empty()) {
            if (prior_values[new_clause_queue.top().var()] == UNDEF)
                new_literals.push_back(new_clause_queue.top());
            new_clause_queue.pop();
        }
    }

    return new_literals;
}

int solver::analyse_conflict() {
    auto new_clause = find_1uip_conflict_clause();

    if (new_clause.size() == 1) {
        set_prior_value(new_clause[0]);
        return 1;
    }

    auto max = -1;
    for (auto lit: new_clause) {
        auto level = var_to_decision_level[lit.var()];
        if (level == current_decision_level())
            continue;

        if (level > max)
            max = level;
    }

    debug(if (max == -1)
        debug_logic_error("All vars from current decision level and size of clause is not 1 => not a UIP clause"))

    auto next_level = max == 0 ? 1 : max;

    for (auto lit: new_clause) {
        vsids.bump_variable(lit.var());
    }

    add_clause(std::move(new_clause), next_level);
    return next_level;
}

bool solver::pick_polarity() {
    std::default_random_engine rd((uint32_t) time(0));
    std::uniform_int_distribution<int> coin(0, 1);

    switch (pick_polarity_mode) {
        case polarity_mode::TRUE:
            return true;
        case polarity_mode::FALSE:
            return false;
        case polarity_mode::RANDOM:
            return coin(rd) == 1;
    }
}

int solver::pick_var() {
    static std::default_random_engine rd((uint32_t) time(0));
    static std::uniform_real_distribution<double> dist(0.0, 1.0);

    auto var = 0;
    if (dist(rd) < random_pick_var_prob) {
        trace("Pick var using random")
        var = pick_var_random();
    } else {
        trace("Pick var using VSIDS")
        var = vsids.pick();
    }

    trace("Pick variable: " << var)
    return var;
}

int solver::pick_var_random() {
    static std::default_random_engine rd((uint32_t) time(0));

    std::uniform_int_distribution<size_t> dist(1, nb_vars - values_count);
    auto index = dist(rd);
    auto counter = 0;
    for (auto var = 1; var <= nb_vars; var++) {
        if (values[var] == UNDEF) {
            counter++;
            if (counter == index)
                return var;
        }
    }

    debug(debug_logic_error("Failed to pick a random variable"))
}

void solver::take_snapshot(int next_var) {
    snapshots.push_back({next_var, values_stack.size()});
}

std::pair<int, bool> solver::backtrack() {
    if (snapshots.empty())
        return std::make_pair(0, false);

    auto snapshot = snapshots.back();
    snapshots.pop_back();
    unsat = false;
    pconflict_clause = nullptr;

    auto old_value = values[snapshot.next_var] == TRUE;

    for (auto i = snapshot.values_stack_length; i < values_stack.size(); i++) {
        unset_value(values_stack[i]);
    }
    values_stack.resize(snapshot.values_stack_length);

    return std::make_pair(snapshot.next_var, old_value);
}

int solver::current_decision_level() {
    return (int) snapshots.size();
}

void solver::propagate_all(bool prior) {
    while (!propagation_queue.empty()) {
        if (unsat)
            break;

        auto var = propagation_queue.front();
        propagation_queue.pop();
        propagate_var(var, prior);
        propagations++;
    }
    while (!propagation_queue.empty()) {
        propagation_queue.pop();
    }
}

void solver::propagate_var(int var, bool prior) {
    auto ever_found = false;
    auto self_lit = literal(values[var] == FALSE ? var : -var);
    auto& watch_clauses = var_to_watch_clauses[self_lit.sign()][var];

    for (auto clause_id: watch_clauses) {
        auto other_lit = watch_vars[clause_id].first == self_lit
                ? watch_vars[clause_id].second
                : watch_vars[clause_id].first;

        auto found = false;
        for (auto candidate_lit: clauses[clause_id]->literals) {
            if (candidate_lit == other_lit ||
                candidate_lit == self_lit ||
                get_literal_value(candidate_lit) == FALSE)
                continue;

            found = true;
            replace_watch_var(watch_clauses, clause_id, other_lit, candidate_lit);
            break;
        }
        ever_found |= found;
        if (!found) {
            if (get_literal_value(other_lit) == FALSE) {
                unsat = true;
                pconflict_clause = clauses[clause_id];
                watch_clauses.erase(
                        std::remove(watch_clauses.begin(), watch_clauses.end(), -1),
                        watch_clauses.end()
                );
                return;
            }
            set_literal_value(other_lit, clause_id);
            if (prior) {
                set_prior_value(other_lit);
            }
        }
    }
    if (ever_found) {
        watch_clauses.erase(
                std::remove(watch_clauses.begin(), watch_clauses.end(), -1),
                watch_clauses.end()
        );
    }
}

void solver::replace_watch_var(std::vector<int>& from_watch_clauses, int clause_id, literal other_lit, literal to_lit) {
    auto position = std::find(from_watch_clauses.begin(), from_watch_clauses.end(), clause_id);
    debug(if (position == from_watch_clauses.end())
        debug_logic_error("from_var was not a watch literal for clause_id: " << clause_id))

    *position = -1;
    watch_vars[clause_id] = std::make_pair(other_lit, to_lit);
    var_to_watch_clauses[to_lit.sign()][to_lit.var()].push_back(clause_id);
}

void solver::apply_prior_values() {
    for (auto var = 1; var <= nb_vars; var++) {
        if (prior_values[var] != UNDEF)
            set_value(var, prior_values[var], -1);
    }
    propagate_all(true);
}

bool solver::set_value(int var, bool value, int reason_clause) {
    if (unsat)
        return false;

    if (values[var] == UNDEF) {
        values[var] = (value_state) value;
        values_count++;
        values_stack.push_back(var);
        antecedent_clauses[var] = reason_clause;
        auto implied_depth = 0;
        if (reason_clause != -1) {
            for (auto lit: clauses[reason_clause]->literals) {
                if (var_to_decision_level[lit.var()] != current_decision_level())
                    continue;

                implied_depth = std::max(implied_depth, var_implied_depth[lit.var()] + 1);
            }
        }
        var_implied_depth[var] = implied_depth;
        var_to_decision_level[var] = current_decision_level();
        propagation_queue.push(var);
        return true;
    }
    debug(if (values[var] != value)
        debug_logic_error("Tried to reassign variable " << var << ": old value was " << values[var] << ", new value was " << value))
    return false;
}

void solver::unset_value(int var) {
    debug(if (values[var] == UNDEF)
        debug_logic_error("Trying to unset already undefined var: " << var))

    values[var] = UNDEF;
    antecedent_clauses[var] = -1;
    var_implied_depth[var] = 0;
    values_count--;
    vsids.on_var_unset(var);
}

void solver::set_prior_value(literal lit) {
    if (prior_values[lit.var()] == UNDEF)
        priors++;

    prior_values[lit.var()] = (value_state) lit.sign();
}

bool solver::set_literal_value(literal lit, int reason_clause) {
    return set_value(lit.var(), lit.sign(), reason_clause);
}

value_state solver::get_literal_value(literal lit) {
    auto value = values[lit.var()];
    if (value == UNDEF)
        return UNDEF;

    return (value_state) (value ^ !lit.sign());
}

bool solver::add_clause(std::vector<literal>&& literals, int next_decision_level) {
    trace("New clause: " << debug_print_literals(clause))

    debug(if (literals.size() <= 1)
              debug_logic_error("Size of new clause is too small: " << literals.size()))

    static std::unordered_set<int> levels;
    levels.clear();
    for (auto lit: literals) {
        auto level = var_to_decision_level[lit.var()];
        if (level == 0)
            continue;

        levels.insert(level);
    }

    auto watch1 = literal::undef, watch2 = literal::undef;
    for (auto lit: literals) {
        if (get_literal_value(lit) == UNDEF ||
            var_to_decision_level[lit.var()] >= next_decision_level ||
            (var_to_decision_level[lit.var()] == 0 && next_decision_level == 1)) {
            if (watch1 == literal::undef) {
                watch1 = lit;
            } else {
                watch2 = lit;
                break;
            }
        }
    }

    debug(if (watch1 == literal::undef || watch2 == literal::undef)
              debug_logic_error("Could not find potentially UNDEF watch variables for new clause, watch1 = " << watch1.var() << ", watch2 = " << watch2.var()))

    clauses.push_back(clause_allocator::allocate_clause(std::move(literals), clause_stat {(uint32_t) levels.size(), 0}));
    auto clause_id = (int) (clauses.size() - 1);

    watch_vars.emplace_back(watch1, watch2);
    var_to_watch_clauses[watch1.sign()][watch1.var()].push_back(clause_id);
    var_to_watch_clauses[watch2.sign()][watch2.var()].push_back(clause_id);
    return true;
}

void solver::print_format_seconds(double duration) {
    auto units = "seconds";
    if (duration > 3600) {
        duration /= 3600;
        units = "hours";
        if (duration > 24) {
            duration /= 24;
            units = "days";
            if (duration > 365) {
                duration /= 365;
                units = "years";
            }
        }
    }
    std::cout << std::setprecision(1) << std::fixed;
    std::cout << duration << " " << units << std::endl;
}

void solver::slow_log() {
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start_time);
    std::cout << "Elapsed time: ";
    print_format_seconds(elapsed.count() / 1000.0);
    print_statistics(elapsed);
}

bool solver::timer_log() {
    constexpr int iterations = 20000;
    constexpr int64_t interval = 5000;

    log_iteration++;
    if (log_iteration == iterations) {
        log_iteration = 0;

        auto now = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - log_time);
        if (duration.count() >= interval) {
            log_time = now;
            slow_log();

            auto duration_from_start = std::chrono::duration_cast<std::chrono::seconds>(now - start_time);
            if (duration_from_start > timeout)
                return false;
        }
    }
    return true;
}

bool solver::verify_result() {
    auto result = true;
    for (auto pclause: clauses) {
        if (pclause->is_learnt())
            continue;

        auto all_false = true;
        for (auto lit: pclause->literals) {
            if (get_literal_value(lit) != FALSE) {
                all_false = false;
                break;
            }
        }
        if (all_false) {
            info(debug_print_literals(pclause->literals) << " => false")
            result = false;
        }
    }
    return result;
}

std::pair<sat_result, std::vector<int8_t>> solver::report_result(bool result) {
    if (result) {
        std::cout << "SAT" << std::endl;
        debug(if (!verify_result())
            debug_logic_error("Found solution is not a solution"))
    } else {
        std::cout << "UNSAT" << std::endl;
    }
    std::cout << "Elapsed time: ";
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start_time);
    print_format_seconds(elapsed.count() / 1000.0);
    print_statistics(elapsed);

    if (result) {
        std::vector<int8_t> result_values;
        result_values.push_back(0);
        for (auto var = 1; var <= nb_vars; var++) {
            result_values.push_back(values[var]);
        }
        return std::make_pair(SAT, result_values);
    } else {
        return std::make_pair(UNSAT, std::vector<int8_t>());
    }
}

void solver::print_statistics(std::chrono::milliseconds elapsed) {
    auto propagates_per_second = (double) propagations / elapsed.count() * 1000;
    auto conflicts_per_second = (double) conflicts / elapsed.count() * 1000;

    std::cout << "Decisions made: \t" << decisions << std::endl;
    std::cout << "Variables propagated: \t" << propagations << ", \t" << propagates_per_second << " / sec" << std::endl;
    std::cout << "Conflicts resolved: \t" << conflicts << ", \t" << conflicts_per_second << " / sec" << std::endl;
    std::cout << "Deduced values: \t" << priors
              << " (of total " << nb_vars << ")" << std::endl;
    std::cout << "Clause count: \t\t" << clauses.size()
              << " with limit " << current_clause_limit << std::endl;
    std::cout << std::endl;
}