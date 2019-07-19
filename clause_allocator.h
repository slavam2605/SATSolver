#ifndef SATSOLVER_CLAUSE_ALLOCATOR_H
#define SATSOLVER_CLAUSE_ALLOCATOR_H

#include "solver_types.h"
#include "debug.h"
#include <vector>
#include <cstdlib>

namespace clause_allocator {
    inline constexpr uint32_t CHUNK_SIZE = 10000;
    inline std::vector<void*> clause_pool;
    inline int32_t chunk_index = -1;
    inline uint32_t allocated = CHUNK_SIZE;

    template <typename ...Args>
    clause* allocate_clause(Args&& ...args) {
        if (allocated >= CHUNK_SIZE) {
            clause_pool.push_back(malloc(CHUNK_SIZE * sizeof(clause)));
            allocated = 0;
            chunk_index++;
        }

        auto ptr = (clause*) clause_pool[chunk_index] + allocated++;
        return new (ptr) clause(std::forward<Args>(args)...);
    }
}

#endif //SATSOLVER_CLAUSE_ALLOCATOR_H
