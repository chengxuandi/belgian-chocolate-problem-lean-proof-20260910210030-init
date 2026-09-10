# BCP certified-threshold formalization

This library freezes the Belgian Chocolate Problem definitions and formalizes the certified
threshold algorithm without formalizing the complex-analytic core.

## Modules

- `Definitions.lean`: strict Hurwitz stability, the original polynomial problem, parameter maps,
  rational intervals, and isolated heavy-analysis / endpoint interfaces.
- `CertificateInterface.lean`: Boolean finite-certificate searches, their soundness/completeness
  contract, the four-way two-trisection update, and an executable finite-prefix fair scan.
- `CertifiedAlgorithm.lean`: distinct trisection points, finite parallel-search termination,
  update soundness, strict bracket preservation, interval nesting, `2/3` width contraction,
  total iteration, and a strict `2^-m` error bound.
- `Main.lean`: the final interface bundle and exported theorem statements.

## Formalization boundary

`HeavyAnalysisInterface`, `CertificateInterface`, and `PolynomialInterface` are structures that a
future analytic development must construct. They are not declarations of global axioms. Every
algorithmic theorem is universally quantified over a concrete certificate implementation.

The operational search is `CertificateInterface.scanThrough`: at fuel `n` it checks every finite
stage from `0` through `n`. `finite_parallel_scan_terminates` proves that some finite fuel succeeds.
The total mathematical iterator packages the least successful stage with `Nat.find` and therefore
is marked `noncomputable`; the finite scans themselves are executable.

## Build and checks

From `D:\ai4math\lean_mathlib_check`:

```powershell
& 'C:\Users\ASUS\.elan\bin\lake.exe' build BCPThreshold
rg -n '\bsorry\b|\badmit\b' BCPThreshold.lean BCPThreshold -g '*.lean'
```

`Main.lean` contains `#print axioms` checks for the main algorithmic results. Expected output is
limited to Lean/Mathlib foundational principles such as `propext`, `Classical.choice`, and
`Quot.sound`; there are no project-specific axioms and no `sorry` declarations.

## Primary exported results

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
