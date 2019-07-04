#ifndef SATSOLVER_SOLVER_H
#define SATSOLVER_SOLVER_H

#include "dimacs.h"
#include "debug.h"
#include <vector>
#include <chrono>

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

debug_def(
template <class T>
inline void hash_combine(std::size_t& seed, T const& v)
{
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

namespace std
{
    template<typename T>
    struct hash<vector<T>>
    {
        typedef vector<T> argument_type;
        typedef std::size_t result_type;
        result_type operator()(argument_type const& in) const
        {
            size_t size = in.size();
            size_t seed = 0;
            for (size_t i = 0; i < size; i++)
                hash_combine(seed, in[i]);
            return seed;
        }
    };
}
)

class solver {
    unsigned int nb_vars;
    std::vector<std::vector<int>> clauses;

    // static state
    std::vector<std::vector<int>> var_to_watch_clauses;
    std::vector<std::pair<int, int>> watch_vars;
    std::vector<value_state> prior_values;
    std::vector<double> vsids_score;
    std::vector<int> learnt_clause_lbd;
    debug_def(std::unordered_set<std::vector<int>> clause_filter;)
    size_t initial_clauses_count;
    size_t current_clause_limit;
    std::chrono::seconds timeout;

    // volatile state
    bool unsat;
    int conflict_clause;

    // backtrackable state
    std::vector<value_state> values;
    size_t values_count;
    std::vector<int> antecedent_clauses;
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
public:
    explicit solver(
            const dimacs& formula,
            std::chrono::seconds timeout = std::chrono::seconds::max()
    );
    std::pair<sat_result, std::vector<int8_t>> solve();

private:
    void init(bool restart);

    int pick_var();
    int pick_var_vsids();
    int pick_var_random();

    void take_snapshot(int next_var);
    std::pair<int, bool> backtrack();
    int current_decision_level();
    int analyse_conflict();
    void clear_state();

    void try_propagate(int var);

    bool set_value(int var, bool value, int reason_clause);
    void unset_value(int var);

    bool add_clause(const std::vector<int>& clause, int next_decision_level);

    void apply_prior_values();
    bool maybe_clause_disabled(int clause_id);
    bool set_signed_value(int signed_var, int reason_clause);
    value_state get_signed_value(int signed_var);
    void replace_watch_var(int clause_id, int other_var, int from_var, int to_var);
    void set_prior_value(int signed_var);

    bool timer_log();
    void slow_log();

    sat_result current_result();
    std::pair<sat_result, std::vector<int8_t>> report_result(bool result);
    bool verify_result();
    void print_statistics();
    void print_format_seconds(double duration);

    debug_def(std::string values_state();)
};

#endif //SATSOLVER_SOLVER_H
