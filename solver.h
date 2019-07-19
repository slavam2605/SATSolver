#ifndef SATSOLVER_SOLVER_H
#define SATSOLVER_SOLVER_H

#include "dimacs.h"
#include "debug.h"
#include "solver_types.h"
#include <vector>
#include <chrono>
#include <queue>

#ifdef DEBUG
#include <unordered_set>
#endif

struct snapshot {
    int next_var;
    size_t values_stack_length;
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

enum class polarity_mode {
    TRUE, FALSE, RANDOM
};

class solver {
    unsigned int nb_vars;
    std::vector<clause*> clauses;

    // static state
    std::vector<std::vector<int>> var_to_watch_clauses[2];
    std::vector<std::pair<literal, literal>> watch_vars;
    std::vector<value_state> prior_values;
    std::vector<double> vsids_score;
    size_t current_clause_limit;
    std::chrono::seconds timeout;

    // volatile state
    bool unsat;
    clause* pconflict_clause;
    std::queue<int> propagation_queue;

    // backtrackable state
    std::vector<value_state> values;
    size_t values_count;
    std::vector<int> antecedent_clauses;
    std::vector<int> var_implied_depth;
    std::vector<int> var_to_decision_level;

    // stack of state changes
    std::vector<int> values_stack;
    std::vector<snapshot> snapshots;

    // internal stuff
    int log_iteration;
    std::chrono::steady_clock::time_point log_time;
    std::chrono::steady_clock::time_point start_time;

    // statistics
    int64_t decisions;
    int64_t propagations;
    int64_t conflicts;
    int64_t priors;

    // constants
    static constexpr int64_t vsids_decay_iteration = 256;
    static constexpr double vsids_decay_factor = 0.5;
    static constexpr double random_pick_var_prob = 0.02;
    static constexpr double clause_limit_init_factor = 1.0 / 3.0;
    static constexpr double clause_limit_inc_factor = 1.1;
    static constexpr double clause_keep_ratio = 0.5;
    static constexpr polarity_mode pick_polarity_mode = polarity_mode::FALSE;
    static constexpr std::chrono::seconds probe_timeout {20};
public:
    explicit solver(
            const dimacs& formula,
            std::chrono::seconds timeout
    );
    std::pair<sat_result, std::vector<int8_t>> solve();

private:
    void init(bool restart);

    int pick_var();
    int pick_var_vsids();
    int pick_var_random();

    bool pick_polarity();
    void take_snapshot(int next_var);
    std::pair<int, bool> backtrack();
    int current_decision_level();
    std::vector<literal> find_1uip_conflict_clause();
    int analyse_conflict();
    void clear_state();
    void probe_literals();

    void propagate_all(bool prior = false);
    void propagate_var(int var, bool prior);

    bool set_value(int var, bool value, int reason_clause);
    void unset_value(int var);

    bool add_clause(std::vector<literal>&& literals, int next_decision_level);

    void apply_prior_values();
    bool maybe_clause_disabled(int clause_id);
    bool set_literal_value(literal lit, int reason_clause);
    value_state get_literal_value(literal lit);
    void replace_watch_var(std::vector<int>& from_watch_clauses, int clause_id, literal other_lit, literal to_lit);
    void set_prior_value(literal lit);

    bool timer_log();
    void slow_log();

    sat_result current_result();
    std::pair<sat_result, std::vector<int8_t>> report_result(bool result);
    bool verify_result();
    void print_statistics(std::chrono::milliseconds elapsed);
    void print_format_seconds(double duration);
};

#endif //SATSOLVER_SOLVER_H
