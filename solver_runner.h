#ifndef SATSOLVER_SOLVER_RUNNER_H
#define SATSOLVER_SOLVER_RUNNER_H

#include <string>
#include "dimacs.h"
#include "sat_preprocessor.h"
#include "sat_remapper.h"
#include "solver.h"

class solver_runner {
    dimacs original_formula;
    sat_preprocessor preprocesor;
    sat_result result;
    std::vector<int8_t> answer;
    bool solved;
public:
    explicit solver_runner(const std::string& filename);
    sat_result solve(bool preprocess = true, std::chrono::seconds timeout = std::chrono::seconds::max());
    sat_result get_result();
    const std::vector<int8_t>& get_answer();
    const dimacs& get_formula();

private:
    static bool verify_result(const dimacs& formula, const std::vector<int8_t>& values);
};


#endif //SATSOLVER_SOLVER_RUNNER_H
