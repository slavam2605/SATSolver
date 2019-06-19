#ifndef SATSOLVER_DEBUG_H
#define SATSOLVER_DEBUG_H

#define DEBUG

#ifdef DEBUG

#include <iostream>
#include <sstream>
#define debug(x) {x}
#define trace(x) { std::cout << "TRACE\t" << x << std::endl; }
#define debug_logic_error(x) {\
    std::stringstream ss;\
    ss << x;\
    throw std::logic_error(ss.str());\
}

#else

#define debug(x) {}
#define trace(x) {}

#endif

#endif //SATSOLVER_DEBUG_H
