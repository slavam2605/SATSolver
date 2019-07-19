#include <stdexcept>
#include <chrono>
#include "solver_runner.h"

solver_runner::solver_runner(const std::string &filename)
        : original_formula(dimacs::read(filename)),
          preprocesor(original_formula),
          solved(false) {}

sat_result solver_runner::solve(bool preprocess, std::chrono::seconds timeout) {
    if (solved)
        return result;

    if (!preprocess) {
        solver solver(original_formula, timeout);
        auto [solve_result, values] = solver.solve();
        if (solve_result == SAT) {
            answer.insert(answer.begin(), values.begin(), values.end());
        }
        result = solve_result;
    } else {
        auto [formula, remapper] = preprocesor.preprocess();
        if (formula.clauses.size() == 1 && formula.clauses[0] == nullptr) {
            result = UNSAT;
        } else {
            solver solver(formula, timeout);
            auto[solve_result, values] = solver.solve();
            if (solve_result == SAT) {
                auto remapped_values = remapper.remap(values);
                answer.insert(answer.begin(), remapped_values.begin(), remapped_values.end());
            }
            result = solve_result;
        }
    }

    debug(if (result == SAT && !verify_result(original_formula, answer))
        debug_logic_error("Verification failed: wrong result after remapping"))

    solved = true;
    return result;
}

sat_result solver_runner::get_result() {
    if (!solved)
        throw std::logic_error("Can't get result: instance was not solved");

    return result;
}

const std::vector<int8_t>& solver_runner::get_answer() {
    if (!solved)
        throw std::logic_error("Can't get answer: instance was not solved");

    return answer;
}

const dimacs &solver_runner::get_formula() {
    return original_formula;
}

bool solver_runner::verify_result(const dimacs& formula, const std::vector<int8_t>& values) {
    auto result = true;
    for (auto clause_id = 0; clause_id < formula.nb_clauses; clause_id++) {
        const auto& clause = formula.clauses[clause_id];
        auto all_false = true;
        for (auto lit: clause->literals) {
            if (values[lit.var()] ^ !lit.sign() != FALSE) {
                all_false = false;
                break;
            }
        }
        if (all_false) {
            info(debug_print_literals(clause->literals) << " => false")
            result = false;
        }
    }
    return result;
}
