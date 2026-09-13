import BCPThreshold.Definitions
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A necessary parameter bound from the original polynomial identity

Only real evaluation, the intermediate value theorem and a quadratic root
are used. There is no dependency on analytic feasibility or a threshold.
-/

namespace BelgianChocolate

open Polynomial

theorem stable_real_eval_ne_zero {f : Polynomial ℝ} (hf : HurwitzStable f)
    {t : ℝ} (ht : 0 ≤ t) : f.eval t ≠ 0 := by
  intro he
  have heC : evalC f (t : ℂ) = 0 := by
    unfold evalC
    rw [Polynomial.eval_map]
    change f.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) t) = 0
    rw [Polynomial.eval₂_at_apply]
    simp [he]
  have hneg := hf.2 (t : ℂ) heC
  simp only [Complex.ofReal_re] at hneg
  exact (not_lt_of_ge ht) hneg

theorem stable_real_eval_pos_iff {f : Polynomial ℝ} (hf : HurwitzStable f)
    {t : ℝ} (ht : 0 ≤ t) : 0 < f.eval t ↔ 0 < f.eval 0 := by
  constructor
  · intro hpos
    by_contra hn
    have hnonpos : f.eval 0 ≤ 0 := le_of_not_gt hn
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht f.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f.eval 0) (f.eval t) from ⟨hnonpos, hpos.le⟩)
    exact stable_real_eval_ne_zero hf hs.1 he
  · intro hpos
    by_contra hn
    have hnonpos : f.eval t ≤ 0 := le_of_not_gt hn
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc' ht f.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f.eval t) (f.eval 0) from ⟨hnonpos, hpos.le⟩)
    exact stable_real_eval_ne_zero hf hs.1 he

theorem stable_real_eval_neg_iff {f : Polynomial ℝ} (hf : HurwitzStable f)
    {t : ℝ} (ht : 0 ≤ t) : f.eval t < 0 ↔ f.eval 0 < 0 := by
  have hn0 := stable_real_eval_ne_zero hf (le_refl (0 : ℝ))
  have hnt := stable_real_eval_ne_zero hf ht
  have hp := stable_real_eval_pos_iff hf ht
  constructor
  · intro h
    by_contra hn
    have h0 : 0 < f.eval 0 := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hn0)
    exact (not_lt_of_ge h.le) (hp.mpr h0)
  · intro h
    by_contra hn
    have ht' : 0 < f.eval t := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hnt)
    exact (not_lt_of_ge h.le) (hp.mp ht')

theorem originalWitness_delta_lt_one {δ : ℝ} {x y p : Polynomial ℝ}
    (hW : OriginalWitness δ x y p) : δ < 1 := by
  rcases hW with ⟨hx, hy, hp, _, hid⟩
  by_contra hnot
  have hd : 1 ≤ δ := le_of_not_gt hnot
  have h0 : p.eval 0 = x.eval 0 - y.eval 0 := by
    rw [hid]
    simp [aPoly, bPoly, sub_eq_add_neg]
  have h1 : p.eval 1 = (2 - 2 * δ) * x.eval 1 := by
    rw [hid]
    simp only [aPoly, bPoly, eval_add, eval_sub, eval_mul, eval_pow,
      eval_X, eval_C, eval_one]
    ring
  have hdne : δ ≠ 1 := by
    intro he
    have := stable_real_eval_ne_zero hp (by norm_num : (0 : ℝ) ≤ 1)
    apply this
    simpa [he] using h1
  have hdgt : 1 < δ := lt_of_le_of_ne hd (Ne.symm hdne)
  let R : ℝ := δ + Real.sqrt (δ ^ 2 - 1)
  have hsq : (Real.sqrt (δ ^ 2 - 1)) ^ 2 = δ ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith)
  have hR : 1 < R := by
    dsimp [R]
    linarith [Real.sqrt_nonneg (δ ^ 2 - 1)]
  have haR : R ^ 2 - 2 * δ * R + 1 = 0 := by
    dsimp [R]
    nlinarith
  have hpR : p.eval R = (R ^ 2 - 1) * y.eval R := by
    rw [hid]
    simp only [eval_add, eval_mul, aPoly, bPoly, eval_sub, eval_pow,
      eval_X, eval_C, eval_one]
    rw [haR, zero_mul, zero_add]
  rcases lt_or_gt_of_ne (stable_real_eval_ne_zero hx (le_refl (0 : ℝ))) with hx0 | hx0
  · have hx1 : x.eval 1 < 0 := (stable_real_eval_neg_iff hx (by norm_num)).mpr hx0
    have hp1 : 0 < p.eval 1 := by rw [h1]; nlinarith
    have hp0 : 0 < p.eval 0 := (stable_real_eval_pos_iff hp (by norm_num)).mp hp1
    have hy0 : y.eval 0 < 0 := by linarith
    have hyR : y.eval R < 0 := (stable_real_eval_neg_iff hy (by linarith)).mpr hy0
    have hpRpos : 0 < p.eval R := (stable_real_eval_pos_iff hp (by linarith)).mpr hp0
    have hpRneg : p.eval R < 0 := by
      rw [hpR]
      exact mul_neg_of_pos_of_neg (by nlinarith) hyR
    linarith
  · have hx1 : 0 < x.eval 1 := (stable_real_eval_pos_iff hx (by norm_num)).mpr hx0
    have hp1 : p.eval 1 < 0 := by rw [h1]; nlinarith
    have hp0 : p.eval 0 < 0 := (stable_real_eval_neg_iff hp (by norm_num)).mp hp1
    have hy0 : 0 < y.eval 0 := by linarith
    have hyR : 0 < y.eval R := (stable_real_eval_pos_iff hy (by linarith)).mpr hy0
    have hpRneg : p.eval R < 0 := (stable_real_eval_neg_iff hp (by linarith)).mpr hp0
    have hpRpos : 0 < p.eval R := by
      rw [hpR]
      exact mul_pos (by nlinarith) hyR
    linarith

theorem admissible_lt_one {δ : ℝ} (h : Admissible δ) : δ < 1 := by
  rcases h with ⟨_, x, y, p, hW⟩
  exact originalWitness_delta_lt_one hW

end BelgianChocolate
