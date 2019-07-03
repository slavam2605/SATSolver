#include "dimacs.h"
#include <fstream>
#include <sstream>
#include <algorithm>

dimacs dimacs::read(const std::string& path) {
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
            ss >> result.nb_vars >> result.nb_clauses;
            result.clauses.reserve(result.nb_clauses);
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
        }
    }
    return result;
}
