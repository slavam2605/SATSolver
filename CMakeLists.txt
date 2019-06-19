cmake_minimum_required(VERSION 3.12)
project(SATSolver)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "-O3")
#set(CMAKE_CXX_FLAGS "-O0 -g -fno-omit-frame-pointer -gdwarf-2")

add_executable(SATSolver main.cpp dimacs.cpp dimacs.h solver.cpp solver.h debug.h)