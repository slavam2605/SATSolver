#ifndef SATSOLVER_SAT_PREPROCESSOR_H
#define SATSOLVER_SAT_PREPROCESSOR_H

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "debug.h"
#include "dimacs.h"
#include "sat_remapper.h"

class sat_preprocessor {
    uint32_t nb_vars;
    std::vector<std::vector<int>> clauses;
    std::vector<preprocessor_value_state> prior_values;
    std::unordered_map<int, std::unordered_set<int>> implication_graph;
    sat_remapper remapper;
    bool unsat;
    std::chrono::steady_clock::time_point start_time;

    // statistics
    int64_t propagated;
    int64_t niver_eliminated;
    int64_t hyp_bin_res_resolved;
    int64_t equality_eliminated;

    static constexpr std::chrono::seconds global_timeout {40};
    static constexpr std::chrono::seconds hyp_bin_res_timeout {5};
public:
    explicit sat_preprocessor(const dimacs& formula);
    std::pair<dimacs, sat_remapper> preprocess();

private:
    bool propagate_all();
    bool niver();
    bool hyper_binary_resolution();
    bool eliminate_equality();

    void filter_implication_graph();
    bool is_interrupted();
    bool is_interrupted_hyp_bin_res(std::chrono::steady_clock::time_point start);
    bool check_unsat();
    debug_def(void print_clause_statistics();)
    bool is_tautology(const std::vector<int>& clause);
    void add_implication_edge(int from, int to);
    bool has_implication_edge(int from, int to);
    std::vector<int> resolve(int var, const std::vector<int>& clause1, const std::vector<int>& clause2);
    bool remove_true_clauses();
    bool remove_false_literals(std::vector<int>& clause);
    std::vector<int>::const_iterator find_true_literal(const std::vector<int>& clause);
    void set_signed_prior_value(int signed_var);
    preprocessor_value_state get_signed_prior_value(int signed_var);

    static void invalidate_clause(std::vector<int>& clause);
    static bool is_invalidated(const std::vector<int>& clause);
};

#endif //SATSOLVER_SAT_PREPROCESSOR_H
