#ifndef SATSOLVER_SAT_UTILS_H
#define SATSOLVER_SAT_UTILS_H

#include "solver_types.h"
#include <unordered_set>
#include <vector>

namespace sat_utils {
    inline bool is_tautology(const std::vector<literal>& clause) {
        static std::unordered_set<int> used_vars;

        used_vars.clear();
        for (auto lit: clause) {
            auto var = lit.var();
            if (used_vars.find(var) != used_vars.end())
                return true;

            used_vars.insert(var);
        }
        return false;
    }

    inline void invalidate_clause(std::vector<literal>& clause) {
        clause = std::vector<literal> {literal::undef};
    };

    inline bool is_invalidated(const std::vector<literal>& clause) {
        return clause.size() == 1 && clause[0] == literal::undef;
    };
}

#endif //SATSOLVER_SAT_UTILS_H
