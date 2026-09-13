import BCPThreshold.PositiveCertificateSoundness
import BCPThreshold.CertifiedAlgorithm

/-!
# Concrete certificates and certified intervals for `analyticQ`
-/

namespace BelgianChocolate

noncomputable section

def analyticNegative (stage : ℕ) (q : ℚ) : Bool :=
  decide (0 < q ∧ q < (1 : ℚ) / 2) &&
    Route1.TrueHierarchy.hierarchyNegative stage q

def analyticPositive (stage : ℕ) (q : ℚ) : Bool :=
  decide (0 < q ∧ q < (1 : ℚ) / 2) &&
    FinitePositiveVerifier.positive stage q

theorem analyticNegative_sound {stage : ℕ} {q : ℚ}
    (h : analyticNegative stage q = true) : (q : ℝ) < analyticQ := by
  simp only [analyticNegative, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨N, hN⟩ := Route1.TrueHierarchy.hierarchyNegative_sound h.2
  by_contra hnot
  have hQq : analyticQ ≤ (q : ℝ) := le_of_not_gt hnot
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast h.1.2.trans (by norm_num)
  have hA : AnalyticFeasible (q : ℝ) :=
    (analyticFeasible_iff_threshold hq1).2 hQq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast h.1.1
  have hqb : (q : ℝ) ≤ (9 : ℝ) / 16 := by
    have hh : (q : ℝ) < 1 / 2 := by
      have ht : (q : ℝ) < (((1 : ℚ) / 2 : ℚ) : ℝ) := by
        exact Rat.cast_lt.mpr h.1.2
      norm_num at ht ⊢
      exact ht
    exact hh.le.trans (by norm_num)
  exact hN ((Route1.AllOrders.analyticFeasible_iff_allOrders hq0 hqb).1 hA N)

theorem analyticPositive_sound {stage : ℕ} {q : ℚ}
    (h : analyticPositive stage q = true) : analyticQ < (q : ℝ) := by
  simp only [analyticPositive, Bool.and_eq_true, decide_eq_true_eq] at h
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast h.1.2.trans (by norm_num)
  obtain ⟨r, hrq, hA⟩ := executable_positive_strict_analytic hq1 h.2
  exact (analyticQ_le_of_feasible hA).trans_lt hrq

theorem analyticNegative_complete {q : ℚ}
    (hq0 : 0 < q) (hqhalf : q < (1 : ℚ) / 2) (hqQ : (q : ℝ) < analyticQ) :
    ∃ stage, analyticNegative stage q = true := by
  obtain ⟨stage, hs⟩ := negative_complete_at_analyticQ (by exact_mod_cast hq0) hqQ
  refine ⟨stage, ?_⟩
  rw [analyticNegative, Bool.and_eq_true]
  exact ⟨decide_eq_true_eq.mpr ⟨hq0, hqhalf⟩, hs⟩

theorem analyticPositive_complete {q : ℚ}
    (hq0 : 0 < q) (hqhalf : q < (1 : ℚ) / 2) (hQq : analyticQ < (q : ℝ)) :
    ∃ stage, analyticPositive stage q = true := by
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast hqhalf.trans (by norm_num)
  obtain ⟨stage, hs⟩ := positive_complete_at_analyticQ hQq hq1
  refine ⟨stage, ?_⟩
  rw [analyticPositive, Bool.and_eq_true]
  exact ⟨decide_eq_true_eq.mpr ⟨hq0, hqhalf⟩, hs⟩

def concreteAnalyticCertificateInterface : CertificateInterface analyticQ where
  negative := analyticNegative
  positive := analyticPositive
  negative_sound := analyticNegative_sound
  positive_sound := analyticPositive_sound
  negative_complete := analyticNegative_complete
  positive_complete := analyticPositive_complete

def analyticThresholdData : ThresholdData where
  Q := analyticQ
  Q_pos := analyticQ_pos
  Q_lt_half := analyticQ_lt_half
  certificates := concreteAnalyticCertificateInterface

theorem analyticQ_certified_interval_exists (m : ℕ) :
    ∃ L R : ℚ, (L : ℝ) < analyticQ ∧ analyticQ < (R : ℝ) ∧
      R - L < 1 / 2 ^ m := by
  exact analyticThresholdData.certified_interval_exists m

end

end BelgianChocolate
