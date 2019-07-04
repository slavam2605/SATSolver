# SATSolver

A simple implementation of SAT solver using CDCL algorithm.

## Usage
SATSolver.exe [dimacs-file]

## Implemented features
* Non-chronological backtrace
* Conflict analysis and deduction of a UIP-clauses
* Unit propagation (boolean constraint propagation)
* 2-watch literals lazy data structure
* VSIDS branching heuristics
* Random branching
* Search restarts (based on learnt clause count)
* Literals Blocks Distance (LBD) as a measure of quality for learnt clauses
* Clause deletion (on restart)
* SAT formula basic preprocessing (eliminate variables with BCP)