import BCPThreshold.FourFactorsHierarchy

/-!
# All-orders analytic realization

The nontrivial direction passes through the common compact coefficient box,
constructs the four convergent power series, and then packages their exact
identities as a normalized disc function.
-/

namespace BelgianChocolate.Route1.AllOrders

open BelgianChocolate
open TrueHierarchy

noncomputable section

/-- Every compatible family of finite hierarchy levels at an interior rational
parameter realizes an analytic feasible disc function. -/
theorem allOrders_realization {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (hH : ∀ N, TrueHierarchy.H N q) :
    AnalyticFeasible (q : ℝ) := by
  obtain ⟨c, hc⟩ := infiniteCoefficients_of_all_levels hH
  refine ⟨hq0, hq1, factorMap (infiniteCoefficientsToFourFactors hc), ?_⟩
  exact fourFactors_to_discFunction hq0 hq1
    (infiniteCoefficientsToFourFactors hc)

/-- In the parameter range used by the threshold layer, analytic feasibility is
equivalent to feasibility of every exact finite hierarchy level. -/
theorem analyticFeasible_iff_allOrders {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hqb : (q : ℝ) ≤ (9 : ℝ) / 16) :
    AnalyticFeasible (q : ℝ) ↔ ∀ N, TrueHierarchy.H N q := by
  constructor
  · intro hA
    have hbound : (q : ℝ) ≤ (3 / 4 : ℝ) ^ 2 := by norm_num at hqb ⊢; exact hqb
    exact analyticFeasible_all_levels hq0 hbound hA
  · intro hH
    have hq1 : (q : ℝ) < 1 := lt_of_le_of_lt hqb (by norm_num)
    exact allOrders_realization hq0 hq1 hH

end

end BelgianChocolate.Route1.AllOrders
