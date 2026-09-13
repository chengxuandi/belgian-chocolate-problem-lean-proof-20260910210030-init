import BCPThreshold.AnalyticThreshold
import BCPThreshold.PolynomialStrictImprovement

/-!
# Separation of the analytic and polynomial endpoints

The analytic threshold is attained by an analytic witness, but strict polynomial
feasibility is not attained there.  The exclusion proof uses the independently
proved polynomial strict-improvement theorem and the polynomial-to-analytic map.
-/

namespace BelgianChocolate

noncomputable section

theorem endpoint_not_polynomialFeasible :
    ¬ PolynomialFeasible analyticQ := by
  intro hP
  obtain ⟨q', hq'0, hq'Q, hP'⟩ :=
    polynomialFeasible_strict_improvement analyticQ_pos
      (analyticQ_lt_half.trans (by norm_num)) hP
  have hA' : AnalyticFeasible q' :=
    polynomialFeasible_implies_analyticFeasible hq'0
      (hq'Q.trans (analyticQ_lt_half.trans (by norm_num))) hP'
  exact (not_lt_of_ge (analyticQ_le_of_feasible hA')) hq'Q

theorem endpoint_separation :
    AnalyticFeasible analyticQ ∧ ¬ PolynomialFeasible analyticQ :=
  ⟨analytic_endpoint_feasible, endpoint_not_polynomialFeasible⟩

end

end BelgianChocolate
