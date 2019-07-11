#include <string>
#include <iostream>
#include <fstream>
#include <dirent.h>
#include "dimacs.h"
#include "solver.h"
#include "solver_runner.h"

bool ends_with(const std::string& string, const std::string& ending) {
    if (string.length() < ending.length())
        return false;

    return string.compare(string.length() - ending.length(), ending.length(), ending) == 0;
}

#define measure_time(result, x) {\
    auto start = std::chrono::steady_clock::now();\
    {x}\
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start);\
    result = duration.count();\
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cout << "Usage: SATSolverBenchmark [folder with .cnf files] [log-file]" << std::endl;
        return 1;
    }

    auto folder_name = argv[1];
    auto log_file = argv[2];
    std::ofstream fout(log_file);
    DIR* dir;
    dirent* ent;
    if ((dir = opendir(folder_name)) != nullptr) {
        while ((ent = readdir(dir)) != nullptr) {
            std::string filename(ent->d_name, ent->d_namlen);
            if (ends_with(filename, ".cnf")) {
                fout << filename << "... \t";
                size_t elapsed_time;
                sat_result result;
                measure_time(elapsed_time,
                    solver_runner runner(folder_name + ("/" + filename));
                    result = runner.solve(
                        /*preprocess = */true,
                        /*timeout = */std::chrono::seconds {1000}
                    );
                )
                fout << (result == SAT ? "SAT" : (result == UNSAT ? "UNSAT" : "TIMEOUT")) << ", time: " << elapsed_time / 1000 << " seconds" << std::endl;
            }
        }
        closedir(dir);
    }
}