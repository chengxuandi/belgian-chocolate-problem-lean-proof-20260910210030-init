import BCPThreshold.RealAllOrdersRealization
import BCPThreshold.PolynomialToAnalytic
import BCPThreshold.RationalPositiveCertificate

/-!
# The concrete analytic infimum

The feasible predicate already includes `0 < q` and `q < 1`. Thus the set
below uses precisely the original analytic parameter domain.
-/

namespace BelgianChocolate

open Set Polynomial

noncomputable section

def analyticFeasibleSet : Set ℝ := {q | AnalyticFeasible q}

def analyticQ : ℝ := sInf analyticFeasibleSet

theorem analyticFeasibleSet_bddBelow : BddBelow analyticFeasibleSet :=
  ⟨0, fun _ h => h.1.le⟩

theorem analyticQ_le_of_feasible {q : ℝ} (h : AnalyticFeasible q) :
    analyticQ ≤ q :=
  csInf_le analyticFeasibleSet_bddBelow h

theorem not_analyticFeasible_of_lt_analyticQ {q : ℝ} (h : q < analyticQ) :
    ¬ AnalyticFeasible q :=
  fun hA => (not_lt_of_ge (analyticQ_le_of_feasible hA)) h

private theorem stable_linear {a b : ℝ} (ha : a ≠ 0) (hb : 0 < b) :
    HurwitzStable (C a * (X + C b)) := by
  constructor
  · intro h
    have he := congrArg (fun p : Polynomial ℝ => p.coeff 1) h
    simp at he
    exact ha he
  · intro z hz
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hz' : z + (b : ℂ) = 0 := by
      simpa [evalC, haC] using hz
    have hre := congrArg Complex.re hz'
    simp at hre
    linarith

/-- An explicit stable polynomial seed at δ = 1/2, hence q = 1/3. -/
theorem analyticFeasible_one_third : AnalyticFeasible (1 / 3 : ℝ) := by
  apply polynomialFeasible_implies_analyticFeasible (by norm_num) (by norm_num)
  change Admissible (deltaOfQ (1 / 3))
  have hd : deltaOfQ (1 / 3) = (1 / 2 : ℝ) := by norm_num [deltaOfQ]
  rw [hd]
  refine ⟨by norm_num, C 1 * (X + C (3 / 2)),
    C (-1) * (X + C (1 / 2)), C (1 / 2) * (X + C 4), ?_⟩
  refine ⟨stable_linear (by norm_num) (by norm_num),
    stable_linear (by norm_num) (by norm_num),
    stable_linear (by norm_num) (by norm_num), ?_, ?_⟩
  · simp only [C_1, one_mul,
      natDegree_C_mul (by norm_num : (-1 : ℝ) ≠ 0), natDegree_X_add_C]
    exact le_rfl
  · apply Polynomial.funext
    intro s
    simp [aPoly, bPoly]
    ring

theorem analyticFeasibleSet_nonempty : analyticFeasibleSet.Nonempty :=
  ⟨1 / 3, analyticFeasible_one_third⟩

theorem analyticQ_nonneg : 0 ≤ analyticQ :=
  le_csInf analyticFeasibleSet_nonempty (fun _ h => h.1.le)

theorem analyticQ_lt_half : analyticQ < (1 : ℝ) / 2 :=
  (analyticQ_le_of_feasible analyticFeasible_one_third).trans_lt (by norm_num)

theorem exists_feasible_lt_of_analyticQ_lt {b : ℝ} (hb : analyticQ < b) :
    ∃ q, AnalyticFeasible q ∧ analyticQ ≤ q ∧ q < b := by
  obtain ⟨q, hq, hqb⟩ := exists_lt_of_csInf_lt analyticFeasibleSet_nonempty hb
  exact ⟨q, hq, analyticQ_le_of_feasible hq, hqb⟩

theorem analyticQ_approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ q, AnalyticFeasible q ∧ analyticQ ≤ q ∧ q < analyticQ + ε :=
  exists_feasible_lt_of_analyticQ_lt (by linarith)

/-- A fixed explicit positive lower bound; the large integer is never evaluated. -/
def analyticLowerBound : ℝ :=
  min (1 / 2) (1 / (Route1.PaperBounds.coefficientBound 0 : ℝ))

theorem analyticLowerBound_pos : 0 < analyticLowerBound := by
  have hC : (0 : ℝ) < Route1.PaperBounds.coefficientBound 0 :=
    Rat.cast_pos.mpr (Route1.PaperBounds.coefficientBound_pos 0)
  exact lt_min (by norm_num) (one_div_pos.mpr hC)

theorem analyticLowerBound_le_of_feasible {q : ℝ} (hA : AnalyticFeasible q) :
    analyticLowerBound ≤ q := by
  by_cases hhalf : (1 : ℝ) / 2 ≤ q
  · exact (min_le_left _ _).trans hhalf
  have hq := hA.1
  obtain ⟨_, hq1, f, hf⟩ := hA
  let F := discFunctionToFourFactors hq hq1 hf
  have hv := Schottky.coefficientBound hq (by linarith) F Route1.TrueHierarchy.vFamily 0
  have hv' : ‖F.v 0‖ ≤ (Route1.PaperBounds.coefficientBound 0 : ℝ) := by
    simpa [Schottky.taylorCoefficient, Schottky.factorFunction,
      Route1.TrueHierarchy.vFamily] using hv
  have hlinear := F.linear 0 (by simp [unitDisc])
  have hmul : (q : ℂ) * F.v 0 = 1 := by simpa using hlinear
  have hnorm := congrArg norm hmul
  have hnorm' : q * ‖F.v 0‖ = 1 := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using hnorm
  have hC : (0 : ℝ) < Route1.PaperBounds.coefficientBound 0 :=
    Rat.cast_pos.mpr (Route1.PaperBounds.coefficientBound_pos 0)
  have hbound : 1 / (Route1.PaperBounds.coefficientBound 0 : ℝ) ≤ q := by
    apply (div_le_iff₀ hC).2
    nlinarith
  exact (min_le_right _ _).trans hbound

theorem analyticQ_pos : 0 < analyticQ :=
  analyticLowerBound_pos.trans_le
    (le_csInf analyticFeasibleSet_nonempty (fun _ h => analyticLowerBound_le_of_feasible h))

/-- A rational parameter strictly below the concrete infimum has a finite obstruction. -/
theorem below_threshold_has_finite_obstruction {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hqQ : (q : ℝ) < analyticQ) :
    ∃ N, ¬ Route1.TrueHierarchy.H N q := by
  by_contra h
  push_neg at h
  have hq1 : (q : ℝ) < 1 :=
    (hqQ.trans analyticQ_lt_half).trans (by norm_num)
  exact not_analyticFeasible_of_lt_analyticQ hqQ
    (Route1.AllOrders.allOrders_realization hq0 hq1 h)

theorem negative_complete_at_analyticQ {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hqQ : (q : ℝ) < analyticQ) :
    ∃ s, Route1.TrueHierarchy.hierarchyNegative s q = true :=
  Route1.TrueHierarchy.hierarchyNegative_complete
    (below_threshold_has_finite_obstruction hq0 hqQ)

/-- Infimum approximation suffices for positive completeness. Endpoint attainment
is not assumed by this theorem. -/
theorem positive_complete_at_analyticQ {q : ℚ}
    (hQq : analyticQ < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    ∃ s, FinitePositiveVerifier.positive s q = true := by
  obtain ⟨r, hr, _, hrq⟩ := exists_feasible_lt_of_analyticQ_lt hQq
  exact strictAnalyticFeasible_executable_positive hrq hq1 hr

/-- The analytic infimum is attained.  The proof first puts the infimum in the
closure of a small-parameter part of the feasible set.  Each finite real
hierarchy level is closed in the parameter, so all levels hold at the
infimum; the real all-orders theorem then realizes them analytically. -/
theorem analytic_endpoint_feasible : AnalyticFeasible analyticQ := by
  have hclosure : analyticQ ∈ closure analyticFeasibleSet :=
    csInf_mem_closure analyticFeasibleSet_nonempty analyticFeasibleSet_bddBelow
  let U : Set ℝ := Set.Iio ((9 : ℝ) / 16)
  have hUopen : IsOpen U := isOpen_Iio
  have hQU : analyticQ ∈ U := by
    dsimp [U]
    exact analyticQ_lt_half.trans_le (by norm_num)
  have hrestricted : analyticQ ∈ closure (U ∩ analyticFeasibleSet) :=
    hUopen.inter_closure ⟨hQU, hclosure⟩
  have hlevels : ∀ N, Route1.RealHierarchy.H N analyticQ := by
    intro N
    have hsub : U ∩ analyticFeasibleSet ⊆
        {q : ℝ | Route1.RealHierarchy.H N q} := by
      intro q hq
      rcases hq with ⟨hqU, hA⟩
      change q < (9 : ℝ) / 16 at hqU
      have hqb : q ≤ (3 / 4 : ℝ) ^ 2 := by
        norm_num at hqU ⊢
        exact hqU.le
      exact Route1.RealAllOrders.analyticFeasible_all_levels hA.1
        hqb hA N
    have hcl : analyticQ ∈ closure {q : ℝ | Route1.RealHierarchy.H N q} :=
      closure_mono hsub hrestricted
    exact (Route1.RealHierarchy.H_parameter_closed N).closure_subset hcl
  exact Route1.RealAllOrders.allOrders_realization analyticQ_pos
    (analyticQ_lt_half.trans (by norm_num)) hlevels

/-- Analytic feasibility is upward closed in the disc parameter. -/
theorem analyticFeasible_mono {r q : ℝ} (hrq : r < q) (hq1 : q < 1)
    (hA : AnalyticFeasible r) : AnalyticFeasible q := by
  rcases hA with ⟨hr0, _, f, hf⟩
  refine ⟨hr0.trans hrq, hq1, dilateDiscFunction f r q, ?_⟩
  have hsub : unitDisc ⊆ Metric.ball (0 : ℂ) (strictRadius r q) :=
    Metric.ball_subset_ball (le_of_lt (strictRadius_gt_one hr0 hrq))
  have hhol : HolSymmOn 1 (dilateDiscFunction f r q) :=
    ⟨(dilated_holSymm hr0 hrq hf).1.mono hsub,
      fun z hz => (dilated_holSymm hr0 hrq hf).2 z (hsub hz)⟩
  refine ⟨hhol, ?_,
    dilated_deriv_zero_ne hr0 hrq hf, ?_, ?_, ?_⟩
  · intro z hz
    exact dilated_zero_iff hr0 hrq hf (hsub hz)
  · intro z hz
    exact dilated_one_iff hr0 hrq hq1 hf (hsub hz)
  · exact dilated_deriv_root_ne hr0 hrq hq1 hf (Or.inl rfl)
  · exact dilated_deriv_root_ne hr0 hrq hq1 hf (Or.inr rfl)

theorem analyticFeasible_iff_threshold {q : ℝ} (hq1 : q < 1) :
    AnalyticFeasible q ↔ analyticQ ≤ q := by
  constructor
  · exact analyticQ_le_of_feasible
  · intro hQq
    rcases hQq.eq_or_lt with rfl | hlt
    · exact analytic_endpoint_feasible
    · exact analyticFeasible_mono hlt hq1 analytic_endpoint_feasible

end

end BelgianChocolate
