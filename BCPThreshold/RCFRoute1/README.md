# E08 route 1: compact-semialgebraic infeasibility

`ROUTE1_APPLICABILITY = YES`.

For rational `q`, the manuscript's actual `H_N(q)` contains exactly
`4 * (N + 1)` real variables and `3 * (N + 1)` polynomial equations.
Every variable has the explicit rational bound `C_j`. There are no strict
inequalities, variable denominators, square roots, transcendental constants,
or hidden analytic predicates. Dividing the four coefficients at index `j`
by the strictly positive `C_j` is a bijection from the manuscript box to the
unit cube.

`CompactSemialgebraic.lean` defines an executable rational-polynomial syntax,
its exact rational evaluator, a certified syntactic Lipschitz bound, the
sum-of-squares violation polynomial, and a finite rational-grid verifier.
Compactness proves that infeasibility gives a positive minimum violation;
the Lipschitz estimate proves that a sufficiently fine grid detects it.

`TrueHierarchy.lean` defines the manuscript constants `R`, `d`, `J`, `B`,
`M(r)`, `r_m`, `M_m`, and `C_j`, expands the real coefficient system, compiles
its equations to the finite syntax, and proves exact normalization. The main
exported declarations are:

- `BelgianChocolate.Route1.TrueHierarchy.H`
- `BelgianChocolate.Route1.TrueHierarchy.H_iff_equationSystem`
- `BelgianChocolate.Route1.TrueHierarchy.negative`
- `BelgianChocolate.Route1.TrueHierarchy.negative_sound`
- `BelgianChocolate.Route1.TrueHierarchy.negative_complete`
- `BelgianChocolate.Route1.TrueHierarchy.hierarchyNegative`
- `BelgianChocolate.Route1.TrueHierarchy.hierarchyNegative_sound`
- `BelgianChocolate.Route1.TrueHierarchy.hierarchyNegative_complete`

`hierarchyNegative stage q` is the finite fair scan over both hierarchy level
and grid depth, so it has the same operational `Nat -> Rat -> Bool` shape as
the negative field of `CertificateInterface`. Its conversion from “some
finite layer is infeasible” to “the rational parameter is below the analytic
threshold” remains, correctly, a theorem of the frozen all-orders analytic
interface rather than part of E08.

The published coefficient bound is intentionally enormous. The verifier is a
total finite exact algorithm and its termination/completeness are proved, but
direct evaluation of even tiny examples may be computationally infeasible.
No practical complexity claim is made.
