#ifndef SATSOLVER_SOLVER_TYPES_H
#define SATSOLVER_SOLVER_TYPES_H

#include <cstdint>
#include <vector>
#include <limits>

class literal {
    int repr;
public:
    explicit literal(int signed_var);
    int var() const;
    bool sign() const;
    literal operator~() const;
    literal operator^(bool other) const;
    bool operator==(const literal& other) const;
    bool operator!=(const literal& other) const;
    bool operator<(const literal& other) const;

    static const literal undef;

private:
    literal() = default;
    friend class std::hash<literal>;
};

struct clause_stat {
    uint32_t lbd;
    uint32_t used;

    clause_stat(uint32_t lbd, uint32_t used) : lbd(lbd), used(used) {}

    static constexpr uint32_t invalid_lbd = std::numeric_limits<decltype(lbd)>::max();
};

struct clause {
    std::vector<literal> literals;
    clause_stat stat;

    clause(std::vector<literal>&& literals, clause_stat stat) : stat(stat), literals(literals) {}
    explicit clause(std::vector<literal>&& literals) : stat(clause_stat::invalid_lbd, 0), literals(literals) {}

    bool is_learnt() const;
    uint32_t size() const;
};

enum value_state {
    FALSE = false,
    TRUE = true,
    UNDEF = 2
};

// ======================= Implementation =======================

inline literal::literal(int signed_var) {
    repr = signed_var > 0
            ? (signed_var << 1) + 1
            : -signed_var << 1;
}

inline int literal::var() const {
    return repr >> 1;
}

inline bool literal::sign() const {
    return (bool) (repr & 1);
}

inline literal literal::operator~() const {
    literal result;
    result.repr = repr ^ 1;
    return result;
}

inline literal literal::operator^(bool other) const {
    literal result;
    result.repr = repr ^ other;
    return result;
}

inline const literal literal::undef = literal(0);

inline bool literal::operator==(const literal& other) const {
    return repr == other.repr;
}

inline bool literal::operator!=(const literal &other) const {
    return !(*this == other);
}

inline bool literal::operator<(const literal &other) const {
    return repr < other.repr;
}

namespace std {
    template<>
    struct hash<literal> {
        size_t operator()(const literal& key) const {
            return hash<int>()(key.repr);
        }
    };
}

inline bool clause::is_learnt() const {
    return stat.lbd != clause_stat::invalid_lbd;
}

inline uint32_t clause::size() const {
    return (uint32_t) literals.size();
}

#endif //SATSOLVER_SOLVER_TYPES_H
