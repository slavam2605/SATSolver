#include "sat_utils.h"

#include <unordered_set>

namespace sat_utils {
    bool is_tautology(const std::vector<int>& clause) {
        static std::unordered_set<int> used_vars;

        used_vars.clear();
        for (int signed_var: clause) {
            auto var = abs(signed_var);
            if (used_vars.find(var) != used_vars.end())
                return true;

            used_vars.insert(var);
        }
        return false;
    }

    void invalidate_clause(std::vector<int>& clause) {
        clause = std::vector<int> {0};
    };

    bool is_invalidated(const std::vector<int>& clause) {
        return clause.size() == 1 && clause[0] == 0;
    };
}
