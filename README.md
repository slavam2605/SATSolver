# SATSolver

A simple implementation of SAT solver using CDCL algorithm.

## Usage
SATSolver.exe [dimacs-file]

## Implemented features
* Non-chronological backtrace [1]
* Conflict analysis and deduction of a 1-UIP-clauses [1]
* Unit propagation (boolean constraint propagation) [1]
* 2-watch literals lazy data structure [1]
* VSIDS branching heuristics [2] + random branching (from MiniSAT)
* Search restarts (based on learnt clause count, [1]) + clause deletion
* Literals Blocks Distance (LBD) as a measure of quality for learnt clauses [3]
* SAT formula preprocessing:
    * Boolean constraint propagation
    * Bounded variable elimination (NiVER algorithm, [4])
    * Binary hyper-resolution [5]
    * Equality reduction [5]
* Polarity mode: value of decision variable is true, false or random

## References:
1. Biere, Armin, et al. "Conflict-driven clause learning sat solvers." Handbook of Satisfiability, Frontiers in Artificial Intelligence and Applications (2009): 131-153.
2. Moskewicz, Matthew W., et al. "Chaff: Engineering an efficient SAT solver." Proceedings of the 38th annual Design Automation Conference. ACM, 2001.
3. Audemard, Gilles, and Laurent Simon. "Predicting learnt clauses quality in modern SAT solvers." Twenty-first International Joint Conference on Artificial Intelligence. 2009.
4. Subbarayan, Sathiamoorthy, and Dhiraj K. Pradhan. "NiVER: Non-increasing variable elimination resolution for preprocessing SAT instances." International conference on theory and applications of satisfiability testing. Springer, Berlin, Heidelberg, 2004.
5. Bacchus, Fahiem, and Jonathan Winter. "Effective preprocessing with hyper-resolution and equality reduction." International conference on theory and applications of satisfiability testing. Springer, Berlin, Heidelberg, 2003.