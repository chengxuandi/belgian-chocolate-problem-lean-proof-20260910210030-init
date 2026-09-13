import BCPThreshold.Main
import BCPThreshold.StrictSlackRealization
import BCPThreshold.AdmissibleBounds
import BCPThreshold.EndpointFormalization
import BCPThreshold.ConcreteAnalyticCertificates

/-!
# Concrete Belgian Chocolate main theorem

All analytic, certificate, and polynomial interfaces are implemented here by
proved declarations. The analytic endpoint is included; the original strict
polynomial endpoint is excluded. No realization hypothesis is a parameter of
the final theorem.
-/

namespace BelgianChocolate

noncomputable section

theorem polynomialFeasible_iff_strict_side {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    PolynomialFeasible q ↔ analyticQ < q := by
  constructor
  · intro hP
    have hle := analyticQ_le_of_feasible
      (polynomialFeasible_implies_analyticFeasible hq0 hq1 hP)
    apply lt_of_le_of_ne hle
    intro he
    exact endpoint_not_polynomialFeasible (he ▸ hP)
  · intro hQq
    exact strictSlackRealization analyticQ q analyticQ_pos hQq hq1
      analytic_endpoint_feasible

theorem original_feasible_iff_strict_side (δ : ℝ) :
    Admissible δ ↔ 0 < δ ∧ δ < deltaOfQ analyticQ := by
  constructor
  · intro h
    have hδ0 := h.1
    have hδ1 := admissible_lt_one h
    have hq := StrictImprovement.qOfDelta_mem hδ0 hδ1
    have hinv := deltaOfQ_qOfDelta (δ := δ) (by linarith)
    have hP : PolynomialFeasible (qOfDelta δ) := by
      simpa only [PolynomialFeasible, hinv] using h
    have hQq := (polynomialFeasible_iff_strict_side hq.1 hq.2).mp hP
    have hlt := parameter_antitone analyticQ_pos hQq hq.2
    exact ⟨hδ0, by simpa only [hinv] using hlt⟩
  · rintro ⟨hδ0, hδQ⟩
    have hδ1 := hδQ.trans (deltaOfQ_lt_one analyticQ_pos)
    have hq := StrictImprovement.qOfDelta_mem hδ0 hδ1
    have hlt := qOfDelta_antitone hδ0 hδQ
    have hQq : analyticQ < qOfDelta δ := by
      simpa only [qOfDelta_deltaOfQ (q := analyticQ) (by linarith [analyticQ_pos])]
        using hlt
    have hP := (polynomialFeasible_iff_strict_side hq.1 hq.2).mpr hQq
    simpa only [PolynomialFeasible, deltaOfQ_qOfDelta (δ := δ) (by linarith)] using hP

theorem analyticFeasible_iff_real_all_levels {q : ℝ}
    (hq0 : 0 < q) (hqb : q ≤ (9 : ℝ) / 16) :
    AnalyticFeasible q ↔ ∀ N, Route1.RealHierarchy.H N q := by
  constructor
  · exact Route1.RealAllOrders.analyticFeasible_all_levels hq0 (by nlinarith)
  · exact Route1.RealAllOrders.allOrders_realization hq0 (by linarith)

/-- The former abstract core, now fully instantiated. -/
def concreteHeavyAnalysisInterface : HeavyAnalysisInterface where
  analyticFeasible := AnalyticFeasible
  finiteLevel := Route1.RealHierarchy.H
  analyticThreshold := analyticQ
  threshold_pos := analyticQ_pos
  threshold_lt_half := analyticQ_lt_half
  analytic_characterization := fun _ _ hq1 => analyticFeasible_iff_threshold hq1
  all_orders := fun _ hq0 hqb => analyticFeasible_iff_real_all_levels hq0 hqb

/-- The former polynomial interface, with no unproved fields. -/
theorem concretePolynomialInterface : PolynomialInterface concreteHeavyAnalysisInterface where
  polynomial_characterization := fun _ hq0 hq1 => polynomialFeasible_iff_strict_side hq0 hq1
  endpoint_not_polynomial := endpoint_not_polynomialFeasible
  delta_characterization := original_feasible_iff_strict_side

def concreteFinalInterfaceBundle : FinalInterfaceBundle where
  core := concreteHeavyAnalysisInterface
  certificates := concreteAnalyticCertificateInterface
  polynomial := concretePolynomialInterface

theorem certified_analyticQ_interval (m : ℕ) :
    ∃ L R : ℚ, (L : ℝ) < analyticQ ∧ analyticQ < (R : ℝ) ∧
      (R : ℝ) - (L : ℝ) < 1 / (2 : ℝ)^m := by
  obtain ⟨L, R, hL, hR, hw⟩ := analyticQ_certified_interval_exists m
  refine ⟨L, R, hL, hR, ?_⟩
  have hc : ((R - L : ℚ) : ℝ) < ((1 / 2^m : ℚ) : ℝ) := Rat.cast_lt.mpr hw
  simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hc

/-- The exact original feasible interval, endpoint separation, concrete
all-orders criterion, and certified arbitrary-precision threshold theorem.
There are no pending mathematical-interface hypotheses. -/
theorem belgianChocolate_exact_algorithmic_solution :
    0 < analyticQ ∧ analyticQ < (1 : ℝ) / 2 ∧
    (∀ q : ℝ, 0 < q → q < 1 → (AnalyticFeasible q ↔ analyticQ ≤ q)) ∧
    (∀ q : ℝ, 0 < q → q ≤ (9 : ℝ) / 16 →
      (AnalyticFeasible q ↔ ∀ N, Route1.RealHierarchy.H N q)) ∧
    (AnalyticFeasible analyticQ ∧ ¬ PolynomialFeasible analyticQ) ∧
    (∀ q : ℝ, 0 < q → q < 1 → (PolynomialFeasible q ↔ analyticQ < q)) ∧
    (∀ δ : ℝ, Admissible δ ↔ 0 < δ ∧ δ < deltaOfQ analyticQ) ∧
    (∀ m : ℕ, ∃ L R : ℚ, (L : ℝ) < analyticQ ∧ analyticQ < (R : ℝ) ∧
      (R : ℝ) - (L : ℝ) < 1 / (2 : ℝ)^m) := by
  exact ⟨analyticQ_pos, analyticQ_lt_half,
    fun _ _ hq1 => analyticFeasible_iff_threshold hq1,
    fun _ hq0 hqb => analyticFeasible_iff_real_all_levels hq0 hqb,
    endpoint_separation,
    fun _ hq0 hq1 => polynomialFeasible_iff_strict_side hq0 hq1,
    original_feasible_iff_strict_side, certified_analyticQ_interval⟩

end

end BelgianChocolate
