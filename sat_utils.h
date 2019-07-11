#ifndef SATSOLVER_SAT_UTILS_H
#define SATSOLVER_SAT_UTILS_H

#include <vector>

namespace sat_utils {
    void invalidate_clause(std::vector<int>& clause);
    bool is_invalidated(const std::vector<int>& clause);
    bool is_tautology(const std::vector<int>& clause);
}

#endif //SATSOLVER_SAT_UTILS_H
