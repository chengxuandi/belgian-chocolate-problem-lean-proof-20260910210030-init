/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.AnalyticStrictFactors
import BCPThreshold.FinitePositiveBridge

/-! # Rational positive certificates from strict analytic slack -/

namespace BelgianChocolate

open Set Metric Polynomial Complex

noncomputable section

def approximantV (q : ℚ) (w : Polynomial ℚ) : Polynomial ℚ :=
  C (1 / q) + X * w

def approximantU (q : ℚ) (w : Polynomial ℚ) : Polynomial ℚ :=
  -C (1 / q) * X - (X ^ 2 + C q) * w

theorem approximants_exact_identity {q : ℚ} (hq : q ≠ 0) (w : Polynomial ℚ) :
    X * approximantU q w + (X ^ 2 + C q) * approximantV q w = 1 := by
  rw [approximantU, approximantV]
  field_simp [hq]
  ring_nf
  rw [← C_mul]
  simp [hq]

theorem evalRatC_approximantV (q : ℚ) (w : Polynomial ℚ) (z : ℂ) :
    evalRatC (approximantV q w) z = (1 / (q : ℚ) : ℚ) + z * evalRatC w z := by
  simp [approximantV, evalRatC]

theorem evalRatC_approximantU (q : ℚ) (w : Polynomial ℚ) (z : ℂ) :
    evalRatC (approximantU q w) z =
      -(z / (q : ℚ)) - (z ^ 2 + (q : ℂ)) * evalRatC w z := by
  simp [approximantU, evalRatC]
  ring

theorem closedUnit_norm_le_one {z : ℂ} (hz : z ∈ closedUnitDisc) : ‖z‖ ≤ 1 := by
  simpa [closedUnitDisc, dist_eq_norm] using hz

theorem quadratic_norm_le {q : ℚ} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1)
    {z : ℂ} (hz : z ∈ closedUnitDisc) :
    ‖z ^ 2 + (q : ℂ)‖ ≤ 1 + (q : ℝ) := by
  calc
    ‖z ^ 2 + (q : ℂ)‖ ≤ ‖z ^ 2‖ + ‖(q : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + (q : ℝ) := by
      have hnormq : ‖(q : ℂ)‖ = (q : ℝ) := by
        rw [Complex.norm_ratCast]
        norm_cast
        exact abs_of_pos hq0
      rw [norm_pow, hnormq]
      exact add_le_add (pow_le_one₀ (norm_nonneg z) (closedUnit_norm_le_one hz)) le_rfl

theorem norm_target_lt_of_approxV
    {f : ℂ → ℂ} {r : ℝ} {q : ℚ} {w : Polynomial ℚ} {η : ℝ}
    (hr : 0 < r) (hrq : r < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hf : DiscFunction r f)
    (hw : ∀ z ∈ closedUnitDisc, ‖evalRatC w z - strictW f r q z‖ < η)
    {z : ℂ} (hz : z ∈ closedUnitDisc) :
    ‖strictV f r q z - evalRatC (approximantV q w) z‖ < η := by
  have hzball := closedUnitDisc_subset_strictBall hr hrq hz
  rw [strictV_decompose hr hrq hq1 hf hzball, evalRatC_approximantV]
  have hcast : ((((1 / (q : ℚ) : ℚ) : ℚ) : ℂ)) = (((1 / (q : ℝ) : ℝ) : ℂ)) := by
    norm_cast
  rw [hcast]
  have heq : ((1 / q : ℝ) : ℂ) + z * strictW f r q z -
      (((1 / q : ℝ) : ℂ) + z * evalRatC w z) =
      z * (strictW f r q z - evalRatC w z) := by ring
  rw [heq, norm_mul]
  have hw' : ‖strictW f r q z - evalRatC w z‖ < η := by
    simpa [norm_sub_rev] using hw z hz
  exact (mul_le_of_le_one_left (norm_nonneg _) (closedUnit_norm_le_one hz)).trans_lt hw'

theorem norm_target_lt_of_approxU
    {f : ℂ → ℂ} {r : ℝ} {q : ℚ} {w : Polynomial ℚ} {η : ℝ}
    (hr : 0 < r) (hrq : r < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hf : DiscFunction r f)
    (hw : ∀ z ∈ closedUnitDisc, ‖evalRatC w z - strictW f r q z‖ < η)
    {z : ℂ} (hz : z ∈ closedUnitDisc) :
    ‖strictU f r q z - evalRatC (approximantU q w) z‖ <
      (1 + (q : ℝ)) * η := by
  have hzball := closedUnitDisc_subset_strictBall hr hrq hz
  rw [strictU_decompose hr hrq hq1 hf hzball, evalRatC_approximantU]
  have hqcast : (((q : ℚ) : ℂ)) = (((q : ℝ) : ℂ)) := by norm_cast
  rw [hqcast]
  have heq : (-(z / (q : ℝ)) - (z ^ 2 + ((q : ℝ) : ℂ)) * strictW f r q z) -
      (-(z / (q : ℝ)) - (z ^ 2 + ((q : ℝ) : ℂ)) * evalRatC w z) =
      -(z ^ 2 + ((q : ℝ) : ℂ)) * (strictW f r q z - evalRatC w z) := by ring
  rw [heq, norm_mul, norm_neg]
  have hw' : ‖strictW f r q z - evalRatC w z‖ < η := by
    simpa [norm_sub_rev] using hw z hz
  have hη0 : 0 < η := by
    have hz0 : (0 : ℂ) ∈ closedUnitDisc := by simp [closedUnitDisc]
    exact (norm_nonneg (evalRatC w 0 - strictW f r q 0)).trans_lt (hw 0 hz0)
  have hbound := quadratic_norm_le (show 0 < q by exact_mod_cast hr.trans hrq) hq1 hz
  by_cases hfac0 : ‖z ^ 2 + (((q : ℝ) : ℂ))‖ = 0
  · rw [hfac0, zero_mul]
    exact mul_pos (by linarith [hr.trans hrq]) hη0
  · have hfacpos : 0 < ‖z ^ 2 + (((q : ℝ) : ℂ))‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfac0)
    exact (mul_lt_mul_of_pos_left hw' hfacpos).trans_le
      (mul_le_mul_of_nonneg_right (by simpa using hbound) hη0.le)

theorem zeroFree_approximantV
    {f : ℂ → ℂ} {r : ℝ} {q : ℚ} {w : Polynomial ℚ} {η m : ℝ}
    (hr : 0 < r) (hrq : r < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hf : DiscFunction r f)
    (hm : ∀ z ∈ closedUnitDisc, m ≤ ‖strictV f r q z‖)
    (hηm : η < m)
    (hw : ∀ z ∈ closedUnitDisc, ‖evalRatC w z - strictW f r q z‖ < η) :
    RatClosedDiscZeroFree (approximantV q w) := by
  intro z hz hzero
  have happ := norm_target_lt_of_approxV hr hrq hq1 hf hw hz
  rw [hzero, sub_zero] at happ
  exact (not_lt_of_ge (hm z hz)) (happ.trans hηm)

theorem zeroFree_approximantU
    {f : ℂ → ℂ} {r : ℝ} {q : ℚ} {w : Polynomial ℚ} {η m : ℝ}
    (hr : 0 < r) (hrq : r < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hf : DiscFunction r f)
    (hm : ∀ z ∈ closedUnitDisc, m ≤ ‖strictU f r q z‖)
    (hηm : (1 + (q : ℝ)) * η < m)
    (hw : ∀ z ∈ closedUnitDisc, ‖evalRatC w z - strictW f r q z‖ < η) :
    RatClosedDiscZeroFree (approximantU q w) := by
  intro z hz hzero
  have happ := norm_target_lt_of_approxU hr hrq hq1 hf hw hz
  rw [hzero, sub_zero] at happ
  exact (not_lt_of_ge (hm z hz)) (happ.trans hηm)

/-- Strict analytic slack yields an actual finite rational positive certificate. -/
theorem strictAnalyticFeasible_positiveCertificate {r : ℝ} {q : ℚ}
    (hrq : r < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hA : AnalyticFeasible r) :
    ∃ v : Polynomial ℚ, PositiveCertificate q v := by
  rcases hA with ⟨hr, _, f, hf⟩
  have hq0 : 0 < q := by exact_mod_cast hr.trans hrq
  have hUcont : ContinuousOn (strictU f r q) closedUnitDisc :=
    ((strictU_holSymm hr hrq hf).1.continuousOn).mono
      (closedUnitDisc_subset_strictBall hr hrq)
  have hVcont : ContinuousOn (strictV f r q) closedUnitDisc :=
    ((strictV_holSymm hr hrq hq1 hf).1.continuousOn).mono
      (closedUnitDisc_subset_strictBall hr hrq)
  obtain ⟨mU, hmU0, hmU⟩ := exists_pos_le_norm_on_closedUnitDisc hUcont
    (strictU_zero_free hr hrq hf)
  obtain ⟨mV, hmV0, hmV⟩ := exists_pos_le_norm_on_closedUnitDisc hVcont
    (strictV_zero_free hr hrq hq1 hf)
  let η : ℝ := min (mV / 2) (mU / (2 * (1 + (q : ℝ))))
  have hden : 0 < 2 * (1 + (q : ℝ)) := by positivity
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min (half_pos hmV0) (div_pos hmU0 hden)
  have hηV : η < mV :=
    (min_le_left _ _).trans_lt (half_lt_self hmV0)
  have hηU : (1 + (q : ℝ)) * η < mU := by
    have hle := min_le_right (mV / 2) (mU / (2 * (1 + (q : ℝ))))
    have hpos : 0 < 1 + (q : ℝ) := by positivity
    calc
      (1 + (q : ℝ)) * η ≤
          (1 + (q : ℝ)) * (mU / (2 * (1 + (q : ℝ)))) :=
            mul_le_mul_of_nonneg_left hle hpos.le
      _ = mU / 2 := by field_simp
      _ < mU := half_lt_self hmU0
  obtain ⟨w, hw⟩ := exists_rat_polynomial_uniform_approx
    (strictRadius_gt_one hr hrq) hη0 (strictW_holSymm hr hrq hq1 hf)
  let u := approximantU q w
  let v := approximantV q w
  have hfac : RatClosedDiscFactors q u v := by
    refine ⟨zeroFree_approximantU hr hrq hq1 hf hmU hηU hw,
      zeroFree_approximantV hr hrq hq1 hf hmV hηV hw, ?_⟩
    exact approximants_exact_identity (ne_of_gt hq0) w
  exact ⟨v, positiveCertificate_of_ratFactors hq0 hfac⟩

/-- The frozen executable search eventually accepts the certificate produced above. -/
theorem strictAnalyticFeasible_executable_positive {r : ℝ} {q : ℚ}
    (hrq : r < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hA : AnalyticFeasible r) :
    ∃ stage, FinitePositiveVerifier.positive stage q = true := by
  apply executable_positive_complete
  exact strictAnalyticFeasible_positiveCertificate hrq hq1 hA

end

end BelgianChocolate
