# BCP certified-threshold formalization

The concrete final theorem is
`BelgianChocolate.belgianChocolate_exact_algorithmic_solution` in `FinalMain.lean`.
It combines the all-orders analytic hierarchy, concrete finite certificate searches,
certified threshold intervals, strict-slack polynomial realization, and independent
endpoint exclusion. Its statement has no pending mathematical-interface hypotheses.

## Modules

- `Definitions.lean`: strict Hurwitz stability, the original polynomial problem, parameter maps,
  rational intervals, and isolated heavy-analysis / endpoint interfaces.
- `CertificateInterface.lean`: Boolean finite-certificate searches, their soundness/completeness
  contract, the four-way two-trisection update, and an executable finite-prefix fair scan.
- `CertifiedAlgorithm.lean`: distinct trisection points, finite parallel-search termination,
  update soundness, strict bracket preservation, interval nesting, `2/3` width contraction,
  total iteration, and a strict `2^-m` error bound.
- `PolynomialToAnalytic.lean`: the concrete Cayley-transform witness proving the valid forward
  implication `PolynomialFeasible q -> AnalyticFeasible q`.
- `AnalyticPolynomialApproximation.lean`: local uniform Taylor approximation of one given
  holomorphic symmetric function and finite rational coefficient approximation.
- `AnalyticStrictFactors.lean`: strict-slack dilation, exact analytic factors, zero-free margins,
  and the one-free-factor parameterization used for rationalization.
- `RationalPositiveCertificate.lean`: construction of an exact finite rational certificate and
  its connection to the frozen executable positive search.
- `StrictSlackRealization.lean`: Module 3 reuse, finite Cayley homogenization,
  exact `OriginalWitness` construction, stability, and actual-degree control.
- `AdmissibleBounds.lean`: `Admissible δ → δ < 1` from the original identity,
  independent of the threshold and endpoint machinery.
- `AnalyticThreshold.lean`, `EndpointFormalization.lean`: the concrete analytic
  threshold and the separation of analytic versus polynomial endpoints.
- `ConcreteAnalyticCertificates.lean`: the instantiated algorithm interface.
- `Main.lean`: reusable abstract interface bundle and generic algorithm exports.
- `FinalMain.lean`: fully proved concrete implementations of that bundle and the
  unconditional original-polynomial main theorem.
- `FinalAudit.lean`: required-theorem checks and a fail-closed transitive axiom audit.

## Formalization boundary

The reusable structures `HeavyAnalysisInterface`, `CertificateInterface`, and
`PolynomialInterface` have concrete implementations, combined in
`concreteFinalInterfaceBundle`. Their proof fields are filled by proved theorems;
none is an assumption of the final result.

For `0 < q < 1`, analytic feasibility is `analyticQ ≤ q`, while original
polynomial feasibility is `analyticQ < q`. The all-orders hierarchy equivalence
is exported on its proved coefficient-bound domain `0 < q ≤ 9/16`.
For every real `δ`, original admissibility is exactly
`0 < δ ∧ δ < (1 - analyticQ) / (1 + analyticQ)`.

The operational search is `CertificateInterface.scanThrough`: at fuel `n` it checks every finite
stage from `0` through `n`. `finite_parallel_scan_terminates` proves that some finite fuel succeeds.
The total mathematical iterator packages the least successful stage with `Nat.find` and therefore
is marked `noncomputable`; the finite scans themselves are executable.

## Build and checks

From the repository root:

```bash
./verify_bcp.sh
```

Use Git Bash on Windows. The script first builds every BCP Lean file serially
in dependency order (including standalone audit files), checks the root, runs the final
audit, and scans all BCP source for proof holes and axiom declarations. Logs are
saved to `.lake/bcp-verification/`. Transitive axiom dependencies must be limited
to `propext`, `Classical.choice`, and `Quot.sound`; an unexpected axiom is fatal.

## Primary exported results

- `strictSlackRealization`
- `positiveCertificate_polynomialFeasible`
- `realClosedDiscFactors_originalWitness`
- `admissible_lt_one`
- `endpoint_not_polynomialFeasible`
- `endpoint_separation`
- `polynomialFeasible_iff_strict_side`
- `original_feasible_iff_strict_side`
- `analyticFeasible_iff_real_all_levels`
- `certified_analyticQ_interval`
- `belgianChocolate_exact_algorithmic_solution`
- `parallel_search_terminates`
- `finite_parallel_scan_terminates`
- `updateAt_sound`
- `updateAt_nested`
- `ThresholdData.intervals_invariant`
- `ThresholdData.intervals_nested_of_le`
- `ThresholdData.intervals_width_bound`
- `ThresholdData.precisionInterval_correct`
- `ThresholdData.certified_interval_exists`
- `FinalInterfaceBundle.certified_interval_exists`
- `polynomialFeasible_implies_analyticFeasible`
- `polynomialToAnalyticStatement`
- `exists_real_polynomial_uniform_approx`
- `exists_rat_polynomial_uniform_approx`
- `strictAnalyticFeasible_positiveCertificate`
- `strictAnalyticFeasible_executable_positive`
