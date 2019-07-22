cmake_minimum_required(VERSION 3.12)
project(SATSolver)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "-O3")
#set(CMAKE_CXX_FLAGS "-O0 -g -fno-omit-frame-pointer -gdwarf-2")

add_executable(SATSolver main.cpp dimacs.cpp dimacs.h solver.cpp solver.h debug.h sat_preprocessor.cpp sat_preprocessor.h sat_remapper.cpp sat_remapper.h solver_runner.cpp solver_runner.h sat_utils.cpp sat_utils.h min_heap.h vsids_picker.h solver_types.h)
add_executable(SATSolverBenchmark dimacs.cpp dimacs.h solver.cpp solver.h debug.h sat_preprocessor.cpp sat_preprocessor.h sat_remapper.cpp sat_remapper.h benchmark_runner.cpp solver_runner.cpp solver_runner.h sat_utils.cpp sat_utils.h min_heap.h vsids_picker.h solver_types.h)