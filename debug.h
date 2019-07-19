#ifndef SATSOLVER_DEBUG_H
#define SATSOLVER_DEBUG_H

#define DEBUG
//#define TRACE

#ifdef DEBUG

#include <iostream>
#include <sstream>

#define debug(x) {x}
#define debug_def(x) x

#ifdef TRACE
#define trace(x) { std::cout << "TRACE\t" << x << std::endl; }
#else
#define trace(x) {}
#endif

#define info(x) { std::cout << "INFO\t" << x << std::endl; }

#define debug_logic_error(x) {\
    std::stringstream ss;\
    ss << x;\
    throw std::logic_error(ss.str());\
}

template <typename LiteralType>
std::string debug_print_literals(const std::vector<LiteralType> vec, const std::string &separator = " ") {
    std::stringstream ss;
    for (auto i = 0; i < vec.size(); i++) {
        ss << (vec[i].sign() ? "" : "-") << vec[i].var();
        if (i < vec.size() - 1)
            ss << separator;
    }
    return ss.str();
}

#else

#define debug(x) {}
#define debug_def(x)
#define trace(x) {}
#define info(x) {}

#endif

#endif //SATSOLVER_DEBUG_H
