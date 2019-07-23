#include "solver.h"
#include "debug.h"
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
    for (const auto& clause: formula.clauses) {
        if (clause.size() == 1) {
            set_prior_value(clause[0]);
        } else {
            clauses.push_back(clause);
        }
    }
    initial_clauses_count = clauses.size();

    init(false);
}

void solver::init(bool restart) {
    debug(if (!propagation_queue.empty())
        debug_logic_error("Propagation queue is not empty on restart"))

    if (restart) {
        backtrack_until(0);

        debug(clause_filter.clear();)
        pos_var_to_watch_clauses.clear();
        neg_var_to_watch_clauses.clear();
        watch_vars.clear();

        std::vector<std::pair<std::vector<int>, clause_stat>> learnt_clauses;
        for (auto i = 0; i < clauses.size() - initial_clauses_count; i++) {
            learnt_clauses.emplace_back(clauses[i + initial_clauses_count], learnt_clause_stat[i]);
        }
        clauses.resize(initial_clauses_count);
        learnt_clause_stat.clear();

        std::sort(learnt_clauses.begin(), learnt_clauses.end(), [this](const auto& p1, const auto& p2) {
            auto [lbd1, used1] = p1.second;
            auto [lbd2, used2] = p2.second;
            return lbd1 < lbd2;
        });
        auto rest_count = (int) (learnt_clauses.size() * clause_keep_ratio);
        // Always keep 'glue' clauses
        while (rest_count < learnt_clauses.size() && learnt_clauses[rest_count].second.lbd <= 2)
            rest_count++;

        for (auto i = 0; i < rest_count; i++) {
            clauses.push_back(learnt_clauses[i].first);
            learnt_clause_stat.emplace_back(learnt_clauses[i].second.lbd, learnt_clauses[i].second.used);
        }

        current_clause_limit = (size_t) (current_clause_limit * clause_limit_inc_factor);
    } else {
        unsat = false;
        conflict_clause = -1;
        values_count = 0;

        current_clause_limit = (size_t) (clauses.size() * clause_limit_init_factor);
        log_iteration = 0;

        // init vsids score
        vsids.init();

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
    }

    // debug: init clause filter
    debug(for (const auto& clause: clauses) {
        clause_filter.insert(clause);
    })

    // build 2-watch-literals structures
    pos_var_to_watch_clauses.resize(nb_vars + 1);
    neg_var_to_watch_clauses.resize(nb_vars + 1);
    watch_vars.resize(clauses.size());
    for (auto i = 0; i < clauses.size(); i++) {
        debug(if (clauses[i].size() <= 1)
            debug_logic_error("Size of initial clause is too small: " << clauses[i].size()))
        auto x = clauses[i][0];
        auto y = clauses[i][1];
        watch_vars[i] = std::make_pair(x, y);
        if (x > 0) {
            pos_var_to_watch_clauses[x].push_back(i);
        } else {
            neg_var_to_watch_clauses[-x].push_back(i);
        }
        if (y > 0) {
            pos_var_to_watch_clauses[y].push_back(i);
        } else {
            neg_var_to_watch_clauses[-y].push_back(i);
        }
    }

    take_snapshot(0);
    apply_prior_values();
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

    auto old_priors = priors;
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
                    auto best_var = std::find_if(conflict_clause.begin(), conflict_clause.end(), [this](int signed_var) {
                        return var_to_decision_level[abs(signed_var)] == 1;
                    });
                    changed |= true;
                    backtrack();
                    set_prior_value(*best_var);
                    set_signed_value(*best_var, -1);
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
    info("Failed literals probing: " << std::chrono::duration_cast<std::chrono::milliseconds>(duration).count() << " ms, deduced: " << priors - old_priors)
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

    // TODO: sort clauses with usage count along with LBD and size
    // TODO: clause deletion while solving (before restart)
    // TODO: get rid of implied_depth and traverse in order of trail
    while (unsat || values_count < nb_vars) {
        int next_var;
        bool value;
        if (unsat) {
            int deduced_signed_var;
            auto decision_level = analyse_conflict(deduced_signed_var);
            trace("Level from analyse_conflict: " << decision_level << ", current: " << current_decision_level())

            if (decision_level == 0)
                return report_result(false);

            backtrack_until(decision_level);

            if (deduced_signed_var != 0) {
                set_signed_value(deduced_signed_var, -1);
                propagate_all(true);
            }

            if (current_result() != UNKNOWN) {
                return report_result(current_result());
            }
        }

        next_var = pick_var();
        value = pick_polarity();
        take_snapshot(next_var);

        trace("Current decision level: " << current_decision_level())
        if (!set_value(next_var, value, -1))
            debug(debug_logic_error("Decision failed"))
        decisions++;

        propagate_all();
        if (clauses.size() - initial_clauses_count > current_clause_limit) {
            init(true);
            info("Restart, new clause limit: " << current_clause_limit << ", learnt clause count: " << (clauses.size() - initial_clauses_count))
        }

        if (!timer_log())
            return std::make_pair(UNKNOWN, std::vector<int8_t>());
    }

    return report_result(true);
}

std::vector<int> solver::find_1uip_conflict_clause() {
    static std::vector<int8_t> var_count;

    conflicts++;
    if (conflict_clause >= initial_clauses_count)
        learnt_clause_stat[conflict_clause - initial_clauses_count].used++;
    vsids.on_conflict();

    var_count.resize(nb_vars + 1);
    std::fill(var_count.begin(), var_count.end(), 0);
    auto new_clause = clauses[conflict_clause];
    auto level_count = 0;
    for (auto signed_var: new_clause) {
        auto level = var_to_decision_level[abs(signed_var)];
        if (level == current_decision_level())
            level_count++;
        var_count[abs(signed_var)]++;
    }

    auto compare = [this](int left_signed_var, int right_signed_var) {
        auto left_var = abs(left_signed_var);
        auto right_var = abs(right_signed_var);
        return var_implied_depth[left_var] < var_implied_depth[right_var];
    };
    std::priority_queue<int, std::vector<int>, decltype(compare)> new_clause_queue(compare);
    for (int signed_var: new_clause) {
        new_clause_queue.push(signed_var);
        vsids.bump_variable(abs(signed_var));
    }
    new_clause.clear();

    while (level_count != 1 && !new_clause_queue.empty()) {
        auto signed_var = new_clause_queue.top();
        auto var = abs(signed_var);
        new_clause_queue.pop();
        auto level = var_to_decision_level[var];
        if (level != current_decision_level()) {
            if (prior_values[abs(signed_var)] == UNDEF)
                new_clause.push_back(signed_var);
            continue;
        }

        auto clause_id = antecedent_clauses[var];
        if (clause_id >= initial_clauses_count)
            learnt_clause_stat[clause_id - initial_clauses_count].used++;
        debug(if (clause_id == -1)
            debug_logic_error("1-UIP algorithm reached decision variable from current level"))

        level_count--;
        for (auto other_signed_var: clauses[clause_id]) {
            if (abs(other_signed_var) == var || var_count[abs(other_signed_var)] > 0)
                continue;

            auto other_level = var_to_decision_level[abs(other_signed_var)];
            new_clause_queue.push(other_signed_var);
            vsids.bump_variable(abs(other_signed_var));
            if (other_level == current_decision_level())
                level_count++;
            var_count[abs(other_signed_var)]++;
        }
    }
    while (!new_clause_queue.empty()) {
        if (prior_values[abs(new_clause_queue.top())] == UNDEF)
            new_clause.push_back(new_clause_queue.top());
        new_clause_queue.pop();
    }

    return new_clause;
}

int solver::analyse_conflict(int& deduced_signed_var) {
    auto new_clause = find_1uip_conflict_clause();
    deduced_signed_var = 0;

    if (new_clause.empty()) {
        return 0;
    }

    if (new_clause.size() == 1) {
        set_prior_value(new_clause[0]);
        deduced_signed_var = new_clause[0];
        return 1;
    }

    auto max = -1;
    for (auto signed_var: new_clause) {
        auto level = var_to_decision_level[abs(signed_var)];
        if (level == current_decision_level())
            continue;

        if (level > max)
            max = level;
    }

    debug(if (max == -1)
        debug_logic_error("All vars from current decision level and size of clause is not 1 => not a UIP clause"))

    auto next_level = max;
    add_clause(new_clause, next_level);

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

void solver::backtrack() {
    debug(if (snapshots.empty())
        debug_logic_error("Tried to backtrack with empty stack"))

    auto snapshot = snapshots.back();
    snapshots.pop_back();
    unsat = false;
    conflict_clause = -1;

    for (auto i = snapshot.values_stack_length; i < values_stack.size(); i++) {
        unset_value(values_stack[i]);
    }
    values_stack.resize(snapshot.values_stack_length);
}

void solver::backtrack_until(int decision_level) {
    do {
        backtrack();
    } while (current_decision_level() >= decision_level);
}

int solver::current_decision_level() {
    return (int) snapshots.size() - 1;
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
    auto signed_self = values[var] == FALSE ? var : -var;
    auto& watch_clauses = signed_self > 0
            ? pos_var_to_watch_clauses[var]
            : neg_var_to_watch_clauses[var];

    for (auto clause_id: watch_clauses) {
        auto signed_other = watch_vars[clause_id].first == signed_self
                ? watch_vars[clause_id].second
                : watch_vars[clause_id].first;

        auto found = false;
        for (auto signed_candidate_var: clauses[clause_id]) {
            if (signed_candidate_var == signed_other ||
                signed_candidate_var == signed_self ||
                get_signed_value(signed_candidate_var) == FALSE)
                continue;

            found = true;
            replace_watch_var(watch_clauses, clause_id, signed_other, signed_candidate_var);
            break;
        }
        ever_found |= found;
        if (!found) {
            if (get_signed_value(signed_other) == FALSE) {
                unsat = true;
                conflict_clause = clause_id;
                watch_clauses.erase(
                        std::remove(watch_clauses.begin(), watch_clauses.end(), -1),
                        watch_clauses.end()
                );
                return;
            }
            set_signed_value(signed_other, clause_id);
            if (prior) {
                set_prior_value(signed_other);
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

void solver::replace_watch_var(std::vector<int>& from_watch_clauses, int clause_id, int signed_other_var, int signed_to_var) {
    auto position = std::find(from_watch_clauses.begin(), from_watch_clauses.end(), clause_id);
    debug(if (position == from_watch_clauses.end())
        debug_logic_error("from_var was not a watch literal for clause_id: " << clause_id))

    *position = -1;
    watch_vars[clause_id] = std::make_pair(signed_other_var, signed_to_var);
    if (signed_to_var > 0) {
        pos_var_to_watch_clauses[signed_to_var].push_back(clause_id);
    } else {
        neg_var_to_watch_clauses[-signed_to_var].push_back(clause_id);
    }
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
        values[var] = value ? TRUE : FALSE;
        values_count++;
        values_stack.push_back(var);
        antecedent_clauses[var] = reason_clause;
        auto implied_depth = 0;
        if (reason_clause != -1) {
            for (int signed_var: clauses[reason_clause]) {
                if (var_to_decision_level[abs(signed_var)] != current_decision_level())
                    continue;

                implied_depth = std::max(implied_depth, var_implied_depth[abs(signed_var)] + 1);
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
    debug(if (get_signed_value(var) == UNDEF)
        debug_logic_error("Trying to unset already undefined var: " << var))

    values[var] = UNDEF;
    antecedent_clauses[var] = -1;
    var_implied_depth[var] = 0;
    values_count--;
    vsids.on_var_unset(var);
}

void solver::set_prior_value(int signed_var) {
    if (prior_values[abs(signed_var)] == UNDEF)
        priors++;

    prior_values[abs(signed_var)] = signed_var > 0 ? TRUE : FALSE;
}

bool solver::set_signed_value(int signed_var, int reason_clause) {
    return set_value(abs(signed_var), signed_var > 0, reason_clause);
}

value_state solver::get_signed_value(int signed_var) {
    auto var = abs(signed_var);
    auto value = values[var];
    if (value == UNDEF)
        return UNDEF;

    if ((value == TRUE) ^ (signed_var < 0))
        return TRUE;
    else
        return FALSE;
}

bool solver::add_clause(const std::vector<int>& clause, int next_decision_level) {
    debug(
        auto duplicate = clause_filter.find(clause) != clause_filter.end();
        if (duplicate) {
            debug_logic_error("Tried to add already existed clause")
        }
        clause_filter.insert(clause);
    )
    trace("New clause: " << trace_print_vector(clause))

    static std::unordered_set<int> levels;
    levels.clear();
    for (auto signed_var: clause) {
        auto level = var_to_decision_level[abs(signed_var)];
        if (level == 0)
            continue;

        levels.insert(level);
    }

    clauses.push_back(clause);
    learnt_clause_stat.emplace_back(levels.size(), 0);
    auto clause_id = (int) (clauses.size() - 1);

    debug(if (clause.size() <= 1)
        debug_logic_error("Size of new clause is too small: " << clause.size()))

    auto watch1 = 0, watch2 = 0;
    for (auto signed_var: clause) {
        if (get_signed_value(signed_var) == UNDEF ||
            var_to_decision_level[abs(signed_var)] >= next_decision_level ||
            (var_to_decision_level[abs(signed_var)] == 0 && next_decision_level == 1)) {
            if (watch1 == 0) {
                watch1 = signed_var;
            } else {
                watch2 = signed_var;
                break;
            }
        }
    }
    debug(if (watch1 == 0 || watch2 == 0)
        debug_logic_error("Could not find potentially UNDEF watch variables for new clause, watch1 = " << watch1 << ", watch2 = " << watch2))

    watch_vars.emplace_back(watch1, watch2);
    if (watch1 > 0) {
        pos_var_to_watch_clauses[watch1].push_back(clause_id);
    } else {
        neg_var_to_watch_clauses[-watch1].push_back(clause_id);
    }
    if (watch2 > 0) {
        pos_var_to_watch_clauses[watch2].push_back(clause_id);
    } else {
        neg_var_to_watch_clauses[-watch2].push_back(clause_id);
    }
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
    for (auto clause_id = 0; clause_id < initial_clauses_count; clause_id++) {
        const auto& clause = clauses[clause_id];
        auto all_false = true;
        for (auto signed_var: clause) {
            if (get_signed_value(signed_var) != FALSE) {
                all_false = false;
                break;
            }
        }
        if (all_false) {
            info(trace_print_vector(clause) << " => false")
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
              << " (learned clauses: " << (clauses.size() - initial_clauses_count)
              << " with limit " << current_clause_limit << ")" << std::endl;
    std::cout << std::endl;
}