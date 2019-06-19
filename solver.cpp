#include "solver.h"
#include "debug.h"
#include <sstream>
#include <iostream>
#include <iomanip>
#include <cmath>
#include <cstdlib>
#include <algorithm>

solver::solver(dimacs& formula) : formula(formula),
                                  unsat(false),
                                  values_count(0),
                                  disabled_clauses_count(0),
                                  log_iteration(0),
                                  decisions(0),
                                  propagations(0),
                                  pure_vars(0),
                                  try_propagates(0),
                                  total_watch_clauses(0) {
    // init values
    values.resize(formula.nb_vars + 1);
    std::fill(values.begin(), values.end(), UNDEF);

    // init disabled clauses
    disabled_clauses.resize(formula.nb_clauses);

    // build var -> clauses map
    var_to_clauses.resize(formula.nb_vars + 1);
    for (auto i = 0; i < formula.nb_clauses; i++) {
        for (auto signed_var: formula.clauses[i]) {
            auto var = abs(signed_var);
            var_to_clauses[var].push_back(i);
        }
    }

    // build 2-watch-literals structures
    var_to_watch_clauses.resize(formula.nb_vars + 1);
    watch_vars.resize(formula.nb_clauses);
    for (auto i = 0; i < formula.nb_clauses; i++) {
        auto x = abs(formula.clauses[i][0]);
        auto y = abs(formula.clauses[i][1]);
        watch_vars[i] = std::make_pair(x, y);
        var_to_watch_clauses[x].push_back(i);
        var_to_watch_clauses[y].push_back(i);
    }

    // build var -> +-clauses map
    var_to_positive_clauses.resize(formula.nb_vars + 1);
    var_to_negative_clauses.resize(formula.nb_vars + 1);
    for (auto i = 0; i < formula.nb_clauses; i++) {
        for (auto signed_var: formula.clauses[i]) {
            if (signed_var > 0) {
                var_to_positive_clauses[signed_var].push_back(i);
            } else {
                var_to_negative_clauses[-signed_var].push_back(i);
            }
        }
    }

    // init var polar count
    var_positive_count.resize(formula.nb_vars + 1);
    var_negative_count.resize(formula.nb_vars + 1);
    for (auto var = 1; var <= formula.nb_vars; var++) {
        var_positive_count[var] = (int) var_to_positive_clauses[var].size();
        var_negative_count[var] = (int) var_to_negative_clauses[var].size();
    }
}

bool solver::solve() {
    start_time = std::chrono::steady_clock::now();
    log_time = start_time;
    while (true) {

        auto result = current_result();
        if (result == SAT) {
            report_result(result);
            return result;
        }

        int next_var;
        bool value;
        if (values_count < formula.nb_vars && result != UNSAT) {
            next_var = pick_var();
            value = true;
            take_snapshot(next_var);
        } else {
            bool old_value;
            while (true) {
                std::tie(next_var, old_value) = backtrack();
                if (!next_var) {
                    report_result(false);
                    return false;
                }

                if (old_value)
                    break;
            }
            value = false;
        }

        if (set_value(next_var, value))
            decisions++;

        timer_log();
    }
}

int solver::pick_var() {
    for (auto var = 1; var <= formula.nb_vars; var++) {
        if (values[var] == UNDEF)
            return var;
    }
}

sat_result solver::current_result() {
    if (unsat)
        return UNSAT;

    if (disabled_clauses_count == formula.nb_clauses)
        return SAT;

    return UNKNOWN;
}

void solver::take_snapshot(int next_var) {
    snapshots.push_back({next_var, values_stack.size(), disabled_clauses_stack.size()});
}

std::pair<int, bool> solver::backtrack() {
    if (snapshots.empty())
        return std::make_pair(0, false);

    auto snapshot = snapshots.back();
    snapshots.pop_back();
    unsat = false;

    auto old_value = values[snapshot.next_var] == TRUE;

    for (auto i = snapshot.values_stack_length; i < values_stack.size(); i++) {
        values[values_stack[i]] = UNDEF;
    }
    values_count -= values_stack.size() - snapshot.values_stack_length;
    values_stack.resize(snapshot.values_stack_length);

    for (auto i = snapshot.disabled_clauses_stack_length; i < disabled_clauses_stack.size(); i++) {
        enable_clause(disabled_clauses_stack[i]);
    }
    disabled_clauses_stack.resize(snapshot.disabled_clauses_stack_length);

    return std::make_pair(snapshot.next_var, old_value);
}

void solver::try_propagate(int var) {
    static std::vector<int> signed_vars;

    signed_vars.clear();
    total_watch_clauses++;
    try_propagates += var_to_watch_clauses[var].size();
    auto ever_found = false;
    for (auto i: var_to_watch_clauses[var]) {
        if (disabled_clauses[i])
            continue;

        auto watch_pair = watch_vars[i];
        auto other = watch_pair.first == var ? watch_pair.second : watch_pair.first;
        auto found = false;
        for (auto signed_var: formula.clauses[i]) {
            auto abs_var = abs(signed_var);
            if (abs_var == other || abs_var == var || get_signed_value(signed_var) != UNDEF)
                continue;

            found = true;
            replace_watch_var(i, other, var, abs_var);
        }
        ever_found |= found;
        if (!found) {
            for (auto signed_var: formula.clauses[i]) {
                if (abs(signed_var) == other) {
                    signed_vars.push_back(signed_var);
                    break;
                }
            }
        }
    }
    if (ever_found) {
        var_to_watch_clauses[var].erase(
                std::remove(var_to_watch_clauses[var].begin(), var_to_watch_clauses[var].end(), -1),
                var_to_watch_clauses[var].end()
        );
    }
    for (auto signed_var: signed_vars) {
        if (get_signed_value(signed_var) == FALSE) {
            unsat = true;
            return;
        }
        if (set_signed_value(signed_var))
            propagations++;
    }
}

void solver::replace_watch_var(int clause_id, int other_var, int from_var, int to_var) {
    watch_vars[clause_id] = std::make_pair(other_var, to_var);

    auto position = std::find(var_to_watch_clauses[from_var].begin(), var_to_watch_clauses[from_var].end(), clause_id);
    debug(if (position == var_to_watch_clauses[from_var].end())
        debug_logic_error("from_var: " << from_var << " was not a watch literal for clause_id: " << clause_id))
    *position = -1;

    var_to_watch_clauses[to_var].push_back(clause_id);
}

bool solver::set_value(int var, bool value) {
    if (unsat)
        return false;

    if (values[var] == UNDEF) {
        values[var] = value ? TRUE : FALSE;
        values_count++;
        values_stack.push_back(var);
        disable_clauses_for_var(var, value);
        try_propagate(var);
        return true;
    }
    debug(
        if (values[var] != value)
            debug_logic_error("Tried to reassign variable " << var << ": old value was " << values[var] << ", new value was " << value)
    )
    return false;
}

void solver::disable_clause(int clause) {
    debug(if (disabled_clauses[clause])
        debug_logic_error("Tried to disable already disabled clause " << clause))

    disabled_clauses[clause] = true;
    disabled_clauses_count++;
    disabled_clauses_stack.push_back(clause);

    for (auto signed_var: formula.clauses[clause]) {
        if (signed_var > 0) {
            --var_positive_count[signed_var];
        } else {
            --var_negative_count[-signed_var];
        }

        if (get_signed_value(signed_var) != UNDEF)
            continue;

        auto var = abs(signed_var);
        auto positive = var_positive_count[var];
        auto negative = var_negative_count[var];
        int resigned_var;
        if (positive > 0 && negative == 0) {
            resigned_var = var;
        } else if (positive == 0 && negative > 0) {
            resigned_var = -var;
        } else
            continue;

        if (get_signed_value(resigned_var) == FALSE) {
            unsat = true;
            return;
        }
        if (set_signed_value(resigned_var))
            pure_vars++;
    }
}

void solver::enable_clause(int clause) {
    debug(if (!disabled_clauses[clause])
        debug_logic_error("Tried to enabled already enabled clause " << clause))

    disabled_clauses[clause] = false;
    disabled_clauses_count--;

    for (auto signed_var: formula.clauses[clause]) {
        if (signed_var > 0) {
            ++var_positive_count[signed_var];
        } else {
            ++var_negative_count[-signed_var];
        }
    }
}

void solver::disable_clauses_for_var(int var, bool value) {
    const auto& clauses = value
            ? var_to_positive_clauses[var]
            : var_to_negative_clauses[var];

    for (auto clause_id: clauses) {
        if (disabled_clauses[clause_id])
            continue;

        disable_clause(clause_id);
    }
}

bool solver::set_signed_value(int signed_var) {
    return set_value(abs(signed_var), signed_var > 0);
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
    std::cout << std::setprecision(1);
    std::cout << duration << " " << units << std::endl;
}

void solver::slow_log() {
    double result = 0;
    double multiplier = 1.0;
    for (auto var = 1; var <= formula.nb_vars; var++) {
        multiplier /= 2;
        auto value = get_signed_value(var);
        if (value == FALSE)
            result += multiplier;

        if (value == UNDEF)
            std::cout << "?";
        if (value == FALSE)
            std::cout << 0;
        if (value == TRUE)
            std::cout << 1;
    }
    std::cout << std::endl;
    std::cout << std::fixed << std::setprecision(10);
    std::cout << "Status: " << 100 * result << "%" << std::endl;

    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start_time);
    auto rest = round(elapsed.count() * (1.0 - result) / result / 1000);
    std::cout << "Estimated time left: ";
    print_format_seconds(rest);

    std::cout << "Decisions made: \t" << decisions << std::endl;
    std::cout << "Variables propagated: \t" << propagations << std::endl;
    std::cout << "Pure variables found: \t" << pure_vars << std::endl;
    std::cout << "Average clauses for 2-watch: " << try_propagates << "/" << total_watch_clauses << " = " << (double) try_propagates / total_watch_clauses << std::endl << std::endl;
}

void solver::timer_log() {
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
        }
    }
}

void solver::report_result(bool result) {
    if (result) {
        std::cout << "SAT" << std::endl;
        for (auto i = 1; i <= formula.nb_vars; i++) {
            auto value = get_signed_value(i);
            if (value == TRUE)
                std::cout << i << " ";
            if (value == FALSE)
                std::cout << -i << " ";
            if (value == UNDEF)
                std::cout << "? ";
        }
        std::cout << std::endl;
    } else {
        std::cout << "UNSAT" << std::endl;
    }
    std::cout << "Elapsed time: ";
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start_time);
    print_format_seconds(elapsed.count() / 1000.0);

    std::cout << "Decisions made: \t" << decisions << std::endl;
    std::cout << "Variables propagated: \t" << propagations << std::endl;
    std::cout << "Pure variables found: \t" << pure_vars << std::endl;
    std::cout << "Average clauses for 2-watch: " << try_propagates << "/" << total_watch_clauses << " = " << (double) try_propagates / total_watch_clauses << std::endl << std::endl;
}

