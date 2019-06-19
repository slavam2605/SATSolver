#ifndef SATSOLVER_SOLVER_H
#define SATSOLVER_SOLVER_H

#include "dimacs.h"
#include <vector>
#include <chrono>

struct snapshot {
    int next_var;
    size_t values_stack_length;
    size_t disabled_clauses_stack_length;
};

enum sat_result {
    UNSAT = false,
    SAT = true,
    UNKNOWN = 2
};

enum value_state {
    FALSE = false,
    TRUE = true,
    UNDEF = 2
};

class solver {
    dimacs& formula;

    // static state
    std::vector<std::vector<int>> var_to_clauses;
    std::vector<std::vector<int>> var_to_watch_clauses;
    std::vector<std::pair<int, int>> watch_vars;
    std::vector<std::vector<int>> var_to_positive_clauses;
    std::vector<std::vector<int>> var_to_negative_clauses;

    // volatile state
    bool unsat;

    // backtrackable state
    std::vector<value_state> values;
    size_t values_count;
    std::vector<int8_t> disabled_clauses;
    size_t disabled_clauses_count;
    std::vector<int> var_positive_count;
    std::vector<int> var_negative_count;

    // stack of state changes
    std::vector<int> values_stack;
    std::vector<int> disabled_clauses_stack;
    std::vector<snapshot> snapshots;

    // internal stuff
    int log_iteration;
    std::chrono::steady_clock::time_point log_time;
    std::chrono::steady_clock::time_point start_time;

    // statistics
    int64_t decisions;
    int64_t propagations;
    int64_t pure_vars;
    int64_t try_propagates;
    int64_t total_watch_clauses;
public:
    explicit solver(dimacs& formula);
    bool solve();

private:
    int pick_var();
    sat_result current_result();
    void take_snapshot(int next_var);
    std::pair<int, bool> backtrack();

    void try_propagate(int var);

    bool set_value(int var, bool value);
    void disable_clause(int clause);
    void enable_clause(int clause);
    void disable_clauses_for_var(int var, bool value);
    bool set_signed_value(int signed_var);
    value_state get_signed_value(int signed_var);
    void replace_watch_var(int clause_id, int other_var, int from_var, int to_var);

    void timer_log();
    void slow_log();

    void report_result(bool result);
    void print_format_seconds(double duration);
};

#endif //SATSOLVER_SOLVER_H
