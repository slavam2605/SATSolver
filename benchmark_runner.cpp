#include <string>
#include <iostream>
#include <dirent.h>
#include "dimacs.h"
#include "solver.h"

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
    if (argc < 2) {
        std::cout << "Usage: SATSolverBenchmark [folder with .cnf files]" << std::endl;
        return 1;
    }

    auto folder_name = argv[1];
    DIR* dir;
    dirent* ent;
    if ((dir = opendir(folder_name)) != nullptr) {
        while ((ent = readdir(dir)) != nullptr) {
            std::string filename(ent->d_name, ent->d_namlen);
            if (ends_with(filename, ".cnf")) {
                std::cout << filename << "... \t";
                size_t elapsed_time;
                sat_result result;
                measure_time(elapsed_time,
                    auto file = dimacs::read(folder_name + ("/" + filename));
                    solver solver(file);
                    result = solver.solve();
                )
                std::cout << (result == SAT ? "SAT" : (result == UNSAT ? "UNSAT" : "TIMEOUT")) << ", time: " << elapsed_time / 1000 << " seconds" << std::endl;
            }
        }
        closedir(dir);
    }
}