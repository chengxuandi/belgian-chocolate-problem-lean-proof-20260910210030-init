# Manuscript status

This repository preserves a Lean formalization and a manuscript that were originally presented as an “Exact Algorithmic Solution of the Belgian Chocolate Problem.” That description is withdrawn.

## Current interpretation

The classical Generalized Belgian Chocolate Problem has a threshold \(\delta^*\): parameters below the threshold are admissible and parameters above it are inadmissible. Determining the value of \(\delta^*\) remains the substantive problem. This repository does not determine that value and does not constitute a complete solution.

The preserved work is best understood as an experimental computability-oriented and formalization study. Its independently useful material includes finite semialgebraic constructions, endpoint analysis, Lean formalization of selected statements, and reproducibility tooling.

## Claim status

- The historical manuscript's complete-solution wording is withdrawn.
- Historical PDFs, Lean files, and commit history are retained for transparency; they have not been rewritten or deleted.
- Formalization and build claims should be read with the coverage boundary and caveats in the current README.
- Numerical, quasi-admissible, or experimental observations in the historical materials are not certified lower-bound claims unless separately supported by an explicit exact witness and independent exact verifiers.

## Separate certified lower-bound project

The explicit finite lower-bound certificate is maintained separately at:

https://github.com/chengxuandi/belgian-chocolate-certified-lower-bound

That project is logically independent. It does not determine \(\delta^*\), solve the complete GBCP, or establish a global optimum.

## Related work

The threshold and simultaneous-stabilization background includes Blondel's monograph and earlier work by Blondel, Gevers, Mortini and Rupp; surveys include Li Wang, Long Wang and Wensheng Yu, “Some Open Problems on Simultaneous Stabilization of Linear Systems.” The published algebraic lower-bound comparison is Charles and Boston (2018). See [REFERENCES.md](REFERENCES.md) for the project bibliography and links.
