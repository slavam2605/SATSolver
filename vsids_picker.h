#ifndef SATSOLVER_VSIDS_PICKER_H
#define SATSOLVER_VSIDS_PICKER_H

#include "debug.h"
#include "solver_types.h"
#include "min_heap.h"
#include <set>
#include <cmath>

class vsids_compare {
    const std::vector<double>& score;

public:
    vsids_compare(const std::vector<double>& score) : score(score) {}

    bool operator()(int a, int b) {
        if (score[a] != score[b])
            return score[a] > score[b];
        return a < b;
    }
};

template <typename Solver>
class vsids_picker {
    const Solver& solver;
    std::vector<double> vsids_score;
    min_heap<int, vsids_compare> vsids_queue;
    std::vector<int> vars_vector;
    uint32_t restart_count;
    double current_bump_value;

public:
    vsids_picker(const Solver& solver) : solver(solver), vsids_queue(vsids_compare(vsids_score)) {}

    void init() {
        restart_count = 0;
        current_bump_value = 1.0;
        vsids_score.clear();
        vsids_score.resize(solver.nb_vars + 1);
        for (const auto& clause: solver.clauses) {
            for (auto signed_var: clause) {
                vsids_score[abs(signed_var)] += current_bump_value;
            }
        }
        vars_vector.clear();
        vars_vector.reserve(solver.nb_vars);
        for (auto var = 1; var <= solver.nb_vars; var++) {
            vars_vector.push_back(var);
        }
        vsids_queue.rebuild_heap(vars_vector);
    }

    void bump_variable(int var) {
        vsids_score[var] += current_bump_value;
        vsids_queue.decrease(var);
    }

    void rescale() {
        for (auto var = 1; var <= solver.nb_vars; var++) {
            vsids_score[var] /= max_bump_value;
        }
        current_bump_value /= max_bump_value;
    }

    void on_conflict() {
        restart_count++;
        if (restart_count % vsids_decay_iteration == 0) {
            current_bump_value /= vsids_decay_factor;
            if (current_bump_value >= max_bump_value) {
                rescale();
            }
        }
    }

    void on_var_unset(int var) {
        if (!vsids_queue.in_heap(var))
            vsids_queue.insert(var);
    }

    int pick() {
        auto var = vsids_queue.min();
        while (solver.values[var] != UNDEF) {
            vsids_queue.extract_min();
            var = vsids_queue.min();
        }
        return var;
    }

private:
    static constexpr int64_t vsids_decay_iteration = 256;
    static constexpr double vsids_decay_factor = 0.5;
    static constexpr double max_bump_value = 1e100;
};

#endif //SATSOLVER_VSIDS_PICKER_H