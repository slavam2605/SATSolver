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
          priors(0),
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
    unsat = false;
    conflict_clause = -1;
    values_count = 0;
    decisions = 0;
    propagations = 0;
    conflicts = 0;

    if (restart) {
        values.clear();
        antecedent_clauses.clear();
        var_implied_depth.clear();
        var_to_decision_level.clear();
        debug(clause_filter.clear();)
        var_to_watch_clauses.clear();
        watch_vars.clear();
        values_stack.clear();
        snapshots.clear();

        std::vector<std::pair<std::vector<int>, int>> learnt_clauses;
        for (auto i = 0; i < clauses.size() - initial_clauses_count; i++) {
            learnt_clauses.emplace_back(clauses[i + initial_clauses_count], learnt_clause_lbd[i]);
        }
        clauses.resize(initial_clauses_count);
        learnt_clause_lbd.clear();

        std::sort(learnt_clauses.begin(), learnt_clauses.end(), [](const auto& p1, const auto& p2) {
            return p1.second < p2.second;
        });
        auto rest_count = (int) (learnt_clauses.size() * clause_keep_ratio);
        // Always keep 'glue' clauses
        while (rest_count < learnt_clauses.size() && learnt_clauses[rest_count].second <= 2)
            rest_count++;

        for (auto i = 0; i < rest_count; i++) {
            clauses.push_back(learnt_clauses[i].first);
            learnt_clause_lbd.push_back(learnt_clauses[i].second);
        }

        current_clause_limit = (size_t) (current_clause_limit * clause_limit_inc_factor);
    } else {
        current_clause_limit = (size_t) (clauses.size() * clause_limit_init_factor);
        log_iteration = 0;

        // init vsids score
        vsids_score.resize(nb_vars + 1);
        for (const auto& clause: clauses) {
            for (auto signed_var: clause) {
                vsids_score[abs(signed_var)]++;
            }
        }
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

    // debug: init clause filter
    debug(for (const auto& clause: clauses) {
        clause_filter.insert(clause);
    })

    // build 2-watch-literals structures
    var_to_watch_clauses.resize(nb_vars + 1);
    watch_vars.resize(clauses.size());
    for (auto i = 0; i < clauses.size(); i++) {
        debug(if (clauses[i].size() <= 1)
            debug_logic_error("Size of initial clause is too small: " << clauses[i].size()))
        auto x = clauses[i][0];
        auto y = clauses[i][1];
        watch_vars[i] = std::make_pair(x, y);
        var_to_watch_clauses[abs(x)].push_back(i);
        var_to_watch_clauses[abs(y)].push_back(i);
    }
}

void solver::clear_state() {
    values_count = 0;
    std::fill(values.begin(), values.end(), UNDEF);
    std::fill(antecedent_clauses.begin(), antecedent_clauses.end(), -1);
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

        if (clauses.size() - initial_clauses_count > current_clause_limit) {
            init(true);
            apply_prior_values();
            info("Restart, new clause limit: " << current_clause_limit << ", learnt clause count: " << (clauses.size() - initial_clauses_count))
            debug(if (unsat)
                debug_logic_error("UNSAT just after restart: should be detected earlier"))
        }

        if (!timer_log())
            return std::make_pair(UNKNOWN, std::vector<int8_t>());
    }

    return report_result(true);
}

int solver::analyse_conflict() {
    static std::vector<int8_t> var_count;

    conflicts++;
    if (conflicts % vsids_decay_iteration == 0) {
        for (auto var = 1; var <= nb_vars; var++) {
            vsids_score[var] *= vsids_decay_factor;
        }
    }

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
    }
    new_clause.clear();

    if (level_count > 1) {
        while (!new_clause_queue.empty()) {
            auto signed_var = new_clause_queue.top();
            auto var = abs(signed_var);
            new_clause_queue.pop();
            auto level = var_to_decision_level[var];
            if (level != current_decision_level()) {
                new_clause.push_back(signed_var);
                continue;
            }

            auto clause_id = antecedent_clauses[var];
            debug(if (clause_id == -1)
                debug_logic_error("1-UIP algorithm reached decision variable from current level"))

            level_count--;
            for (auto other_signed_var: clauses[clause_id]) {
                if (abs(other_signed_var) == var || var_count[abs(other_signed_var)] > 0)
                    continue;

                auto other_level = var_to_decision_level[abs(other_signed_var)];
                new_clause_queue.push(other_signed_var);
                if (other_level == current_decision_level())
                    level_count++;
                var_count[abs(other_signed_var)]++;
            }

            // Stop at first UIP
            if (level_count == 1)
                break;
        }
        while (!new_clause_queue.empty()) {
            new_clause.push_back(new_clause_queue.top());
            new_clause_queue.pop();
        }
    }
    new_clause.erase(
            std::remove_if(
                    new_clause.begin(),
                    new_clause.end(),
                    [this](int signed_var) { return prior_values[abs(signed_var)] != UNDEF; }
            ),
            new_clause.end()
    );

    if (new_clause.size() == 1) {
        set_prior_value(new_clause[0]);
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

    auto next_level = max == 0 ? 1 : max;
    add_clause(new_clause, next_level);

    for (auto signed_var: new_clause) {
        vsids_score[abs(signed_var)]++;
    }

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
        var = pick_var_vsids();
    }

    trace("Pick variable: " << var)
    return var;
}

int solver::pick_var_vsids() {
    double max = -1;
    auto max_var = 0;
    for (auto var = 1; var <= nb_vars; var++) {
        if (values[var] == UNDEF && vsids_score[var] > max) {
            max = vsids_score[var];
            max_var = var;
        }
    }
    debug(if (max_var == 0)
        debug_logic_error("Can't pick new variable"))

    return max_var;
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
    conflict_clause = -1;

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

void solver::try_propagate(int var) {
    std::vector<std::pair<int, int>> inferred_pairs;

    auto ever_found = false;
    for (auto clause_id: var_to_watch_clauses[var]) {
        if (maybe_clause_disabled(clause_id))
            continue;

        auto watch_pair = watch_vars[clause_id];
        int signed_self;
        int signed_other;
        if (abs(watch_pair.first) == var) {
            std::tie(signed_self, signed_other) = watch_pair;
        } else {
            std::tie(signed_other, signed_self) = watch_pair;
        }
        auto found = false;
        for (auto signed_candidate_var: clauses[clause_id]) {
            if (signed_candidate_var == signed_other ||
                signed_candidate_var == signed_self ||
                get_signed_value(signed_candidate_var) == FALSE)
                continue;

            found = true;
            replace_watch_var(clause_id, signed_other, signed_self, signed_candidate_var);
            break;
        }
        ever_found |= found;
        if (!found) {
            if (get_signed_value(signed_other) == FALSE) {
                unsat = true;
                conflict_clause = clause_id;
                var_to_watch_clauses[var].erase(
                        std::remove(var_to_watch_clauses[var].begin(), var_to_watch_clauses[var].end(), -1),
                        var_to_watch_clauses[var].end()
                );
                return;
            }
            inferred_pairs.emplace_back(signed_other, clause_id);
        }
    }
    if (ever_found) {
        var_to_watch_clauses[var].erase(
                std::remove(var_to_watch_clauses[var].begin(), var_to_watch_clauses[var].end(), -1),
                var_to_watch_clauses[var].end()
        );
    }
    if (unsat)
        return;

    for (auto [signed_var, reason_clause]: inferred_pairs) {
        if (get_signed_value(signed_var) == FALSE) {
            debug(if (!unsat)
                debug_logic_error("Expected conflict to be found earlier"))
            return;
        }
        if (set_signed_value(signed_var, reason_clause))
            propagations++;
    }
}

void solver::replace_watch_var(int clause_id, int signed_other_var, int signed_from_var, int signed_to_var) {
    auto from_var = abs(signed_from_var);
    auto position = std::find(var_to_watch_clauses[from_var].begin(), var_to_watch_clauses[from_var].end(), clause_id);
    debug(if (position == var_to_watch_clauses[from_var].end())
        debug_logic_error("from_var: " << from_var << " was not a watch literal for clause_id: " << clause_id))

    *position = -1;
    watch_vars[clause_id] = std::make_pair(signed_other_var, signed_to_var);
    var_to_watch_clauses[abs(signed_to_var)].push_back(clause_id);
}

void solver::apply_prior_values() {
    for (auto var = 1; var <= nb_vars; var++) {
        if (prior_values[var] != UNDEF)
            set_value(var, prior_values[var], -1);
    }
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
        try_propagate(var);
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
}

void solver::set_prior_value(int signed_var) {
    prior_values[abs(signed_var)] = signed_var > 0 ? TRUE : FALSE;
    priors++;
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
    learnt_clause_lbd.push_back(levels.size());
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
    var_to_watch_clauses[abs(watch1)].push_back(clause_id);
    var_to_watch_clauses[abs(watch2)].push_back(clause_id);
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
    print_statistics();
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
        for (auto i = 1; i <= nb_vars; i++) {
            auto value = get_signed_value(i);
            if (value == TRUE)
                std::cout << i << " ";
            if (value == FALSE)
                std::cout << -i << " ";
            if (value == UNDEF)
                std::cout << "? ";
        }
        std::cout << std::endl;
        debug(if (!verify_result())
            debug_logic_error("Found solution is not a solution"))
    } else {
        std::cout << "UNSAT" << std::endl;
    }
    std::cout << "Elapsed time: ";
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start_time);
    print_format_seconds(elapsed.count() / 1000.0);
    print_statistics();

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

void solver::print_statistics() {
    std::cout << "Decisions made: \t" << decisions << std::endl;
    std::cout << "Variables propagated: \t" << propagations << std::endl;
    std::cout << "Conflicts resolved: \t" << conflicts << std::endl;
    std::cout << "Deduced values: \t" << priors
              << " (of total " << nb_vars << ")" << std::endl;
    std::cout << "Clause count: \t\t" << clauses.size()
              << " (learned clauses: " << (clauses.size() - initial_clauses_count)
              << " with limit " << current_clause_limit << ")" << std::endl;
    std::cout << std::endl;
}

bool solver::maybe_clause_disabled(int clause_id) {
    auto watch_pair = watch_vars[clause_id];
    return get_signed_value(watch_pair.first) == TRUE || get_signed_value(watch_pair.second) == TRUE;
}

debug_def(
    std::string solver::values_state() {
        std::stringstream ss;
        for (auto var = 1; var <= nb_vars; var++) {
            auto value = get_signed_value(var);
            if (value == UNDEF)
                ss << "? ";
            if (value == TRUE)
                ss << var << " ";
            if (value == FALSE)
                ss << -var << " ";
        }
        return ss.str();
    }
)
