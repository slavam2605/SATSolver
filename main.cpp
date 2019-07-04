#include <iostream>
#include "dimacs.h"
#include "solver.h"
#include "sat_preprocessor.h"
#include "solver_runner.h"
#include <chrono>
#include <iomanip>

#define SAT_RETURN_CODE 0
#define UNSAT_RETURN_CODE 1
#define WRONG_USAGE_RETURN_CODE 2

#define benchmark(N, x) {\
    auto start = std::chrono::steady_clock::now();\
    for (auto i = 0; i < N; i++) {\
        {x}\
    }\
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start);\
    std::cout << "Average time: " << std::setprecision(2) << duration.count() / 1000.0 / N << " s" << std::endl;\
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cout << "Usage: SATSolver [dimacs-file]" << std::endl;
        return WRONG_USAGE_RETURN_CODE;
    }

    solver_runner runner(argv[1]);
    auto result = runner.solve();

    return result ? SAT_RETURN_CODE : UNSAT_RETURN_CODE;
}