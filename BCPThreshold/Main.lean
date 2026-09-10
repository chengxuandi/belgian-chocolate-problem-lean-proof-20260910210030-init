/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.CertifiedAlgorithm

/-!
# Certified Belgian Chocolate threshold: exported interfaces and algorithmic theorems

The complex-analytic and endpoint implementations are intentionally not supplied in this round.
The algorithmic results below are fully proved for every concrete implementation of the isolated
certificate interface.
-/

namespace BelgianChocolate

/-- The complete handoff object expected from the future analytic and endpoint formalization.
Its proof fields are assumptions of a concrete implementation, never global axioms. -/
structure FinalInterfaceBundle where
  core : HeavyAnalysisInterface
  certificates : CertificateInterface core.analyticThreshold
  polynomial : PolynomialInterface core

/-- Forget the heavy mathematical content and expose exactly the data consumed by the certified
threshold algorithm. -/
def FinalInterfaceBundle.thresholdData (B : FinalInterfaceBundle) : ThresholdData where
  Q := B.core.analyticThreshold
  Q_pos := B.core.threshold_pos
  Q_lt_half := B.core.threshold_lt_half
  certificates := B.certificates

/-- Final theorem statement to be discharged after implementing both isolated mathematical
interfaces. Keeping it as a proposition does not assume it. -/
def BelgianChocolateMainStatement (core : HeavyAnalysisInterface) : Prop :=
  ∀ δ : ℝ, Admissible δ ↔
    0 < δ ∧ δ < deltaOfQ core.analyticThreshold

theorem main_statement_of_polynomial_interface (core : HeavyAnalysisInterface)
    (poly : PolynomialInterface core) : BelgianChocolateMainStatement core := by
  exact poly.delta_characterization

/-- Exported arbitrary-precision theorem for any completed implementation of the isolated
interfaces. -/
theorem FinalInterfaceBundle.certified_interval_exists (B : FinalInterfaceBundle) (m : ℕ) :
    ∃ L R : ℚ, (L : ℝ) < B.core.analyticThreshold ∧
      B.core.analyticThreshold < (R : ℝ) ∧ R - L < 1 / 2 ^ m := by
  exact B.thresholdData.certified_interval_exists m

/-- Exported original-polynomial conclusion, conditional only on implementing the isolated
endpoint interface. -/
theorem FinalInterfaceBundle.original_problem (B : FinalInterfaceBundle) :
    BelgianChocolateMainStatement B.core :=
  main_statement_of_polynomial_interface B.core B.polynomial

#print axioms parallel_search_terminates
#print axioms finite_parallel_scan_terminates
#print axioms updateAt_sound
#print axioms ThresholdData.intervals_invariant
#print axioms ThresholdData.intervals_nested
#print axioms ThresholdData.intervals_width_bound
#print axioms ThresholdData.precisionInterval_correct
#print axioms ThresholdData.certified_interval_exists

end BelgianChocolate
