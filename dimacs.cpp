#include "dimacs.h"
#include "debug.h"
#include "sat_utils.h"
#include "clause_allocator.h"
#include <fstream>
#include <sstream>
#include <algorithm>
#include <chrono>

dimacs dimacs::read(const std::string& path) {
    info("Reading dimacs...")
    auto start = std::chrono::steady_clock::now();
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
            std::vector<literal> new_clause;
            int __tmp;
            while (ss >> __tmp) {
                if (__tmp == 0)
                    break;

                new_clause.emplace_back(__tmp);
            }

            std::sort(
                    new_clause.begin(),
                    new_clause.end(),
                    [](literal x, literal y) { return x.var() < y.var(); }
            );
            auto last = std::unique(new_clause.begin(), new_clause.end());
            new_clause.erase(last, new_clause.end());
            if (!sat_utils::is_tautology(new_clause)) {
                result.clauses.push_back(clause_allocator::allocate_clause(std::move(new_clause)));
            }
        }
    }
    info("Dimacs was read in " << std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - start).count() << " ms")
    result.nb_clauses = (uint32_t) result.clauses.size();
    return result;
}
