#include "dimacs.h"
#include "debug.h"
#include "sat_utils.h"
#include <fstream>
#include <sstream>
#include <algorithm>

dimacs dimacs::read(const std::string& path) {
    info("Reading dimacs...")
    dimacs result;
    std::ifstream fin(path);
    std::string line;
    while (std::getline(fin, line)) {
        if (line.length() == 0)
            continue;

        std::stringstream ss;
        ss << line;
        if (line[0] == 'c') {
            continue;
        } else if (line[0] == 'p') {
            std::string __tmp;
            ss >> __tmp >> __tmp;
            uint32_t clause_number;
            ss >> result.nb_vars >> clause_number;
            result.clauses.reserve(clause_number);
        } else {
            auto last_index = result.clauses.size();
            result.clauses.resize(last_index + 1);
            int __tmp;
            while (ss >> __tmp) {
                if (__tmp == 0)
                    break;

                result.clauses[last_index].push_back(__tmp);
            }

            std::sort(
                    result.clauses[last_index].begin(),
                    result.clauses[last_index].end(),
                    [](int i, int j) { return abs(i) < abs(j); }
            );
            auto last = std::unique(result.clauses[last_index].begin(), result.clauses[last_index].end());
            result.clauses[last_index].erase(last, result.clauses[last_index].end());
            if (sat_utils::is_tautology(result.clauses[last_index]))
                result.clauses.resize(result.clauses.size() - 1);
        }
    }
    result.nb_clauses = (uint32_t) result.clauses.size();
    return result;
}
