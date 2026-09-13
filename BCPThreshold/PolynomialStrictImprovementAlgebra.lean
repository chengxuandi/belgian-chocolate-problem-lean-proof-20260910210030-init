import BCPThreshold.Definitions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Checked algebra for the strict-improvement construction

This file proves the parameter direction and the exact witness identities.
It does not yet prove preservation of Hurwitz stability or the final
`polynomialFeasible_strict_improvement` theorem. The complete mathematical
proof and the remaining finite-root/coefficient work are documented in
`STRICT_IMPROVEMENT_MATHEMATICAL_PROOF.md` and its Lean handoff.
-/

namespace BelgianChocolate.StrictImprovement

open Polynomial

noncomputable section

def scale (δ t : ℝ) : ℝ := Real.sqrt (1 + 2 * t + δ ^ 2 * t ^ 2)

def denominator (δ t : ℝ) : ℝ := 1 + δ ^ 2 * t

def improvedDelta (δ t : ℝ) : ℝ := δ * scale δ t / denominator δ t

def affine (δ t α : ℝ) : Polynomial ℝ := C α * X - C (δ * t)

def mixedX (t : ℝ) (x y : Polynomial ℝ) : Polynomial ℝ :=
  x + C t * (x + y)

def mixedY (δ t : ℝ) (x y : Polynomial ℝ) : Polynomial ℝ :=
  y + C t * (C (1 - δ ^ 2) * x + y)

def transformedX (δ t α : ℝ) (x y : Polynomial ℝ) : Polynomial ℝ :=
  C (denominator δ t) * (mixedX t x y).comp (affine δ t α)

def transformedY (δ t α : ℝ) (x y : Polynomial ℝ) : Polynomial ℝ :=
  (mixedY δ t x y).comp (affine δ t α)

theorem scale_pos {δ t : ℝ} (ht : 0 < t) : 0 < scale δ t := by
  unfold scale
  apply Real.sqrt_pos.2
  positivity

theorem scale_sq {δ t : ℝ} (ht : 0 ≤ t) :
    scale δ t ^ 2 = 1 + 2 * t + δ ^ 2 * t ^ 2 := by
  exact Real.sq_sqrt (by positivity)

theorem denominator_pos {δ t : ℝ} (ht : 0 ≤ t) : 0 < denominator δ t := by
  unfold denominator
  positivity

theorem improvedDelta_mul_denominator {δ t : ℝ} (ht : 0 ≤ t) :
    improvedDelta δ t * denominator δ t = δ * scale δ t := by
  unfold improvedDelta
  exact div_mul_cancel₀ _ (ne_of_gt (denominator_pos ht))

theorem parameter_improves {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ht : 0 < t) : δ < improvedDelta δ t ∧ improvedDelta δ t < 1 := by
  have ha := scale_pos (δ := δ) ht
  have hD := denominator_pos (δ := δ) ht.le
  have ha2 := scale_sq (δ := δ) ht.le
  have hfac : 0 < 1 - δ ^ 2 := by nlinarith
  have hgap : 0 < (1 - δ ^ 2) * t * (2 + δ ^ 2 * t) := by positivity
  have hidentity : scale δ t ^ 2 - denominator δ t ^ 2 =
      (1 - δ ^ 2) * t * (2 + δ ^ 2 * t) := by
    rw [ha2]
    unfold denominator
    ring
  have hDa : denominator δ t < scale δ t := by nlinarith
  have hidentity2 : denominator δ t ^ 2 - (δ * scale δ t) ^ 2 =
      1 - δ ^ 2 := by
    rw [mul_pow, ha2]
    unfold denominator
    ring
  have hdaD : δ * scale δ t < denominator δ t := by
    nlinarith [mul_pos hδ0 ha]
  constructor
  · unfold improvedDelta
    exact (lt_div_iff₀ hD).2 (mul_lt_mul_of_pos_left hDa hδ0)
  · unfold improvedDelta
    exact (div_lt_one hD).2 hdaD

theorem a_comp_affine {δ t α d : ℝ}
    (ha : α ^ 2 = 1 + 2 * t + δ ^ 2 * t ^ 2)
    (hd : d * (1 + δ ^ 2 * t) = δ * α) :
    (aPoly δ).comp (affine δ t α) =
      C ((1 + t) * (1 + δ ^ 2 * t)) * aPoly d +
      C ((1 - δ ^ 2) * t) * bPoly := by
  apply Polynomial.funext
  intro s
  simp only [eval_comp, aPoly, bPoly, affine, eval_add, eval_sub,
    eval_mul, eval_pow, eval_X, eval_C, eval_one]
  linear_combination s ^ 2 * ha + 2 * s * (1 + t) * hd

theorem b_comp_affine {δ t α d : ℝ}
    (ha : α ^ 2 = 1 + 2 * t + δ ^ 2 * t ^ 2)
    (hd : d * (1 + δ ^ 2 * t) = δ * α) :
    bPoly.comp (affine δ t α) =
      C (t * (1 + δ ^ 2 * t)) * aPoly d + C (1 + t) * bPoly := by
  apply Polynomial.funext
  intro s
  simp only [eval_comp, aPoly, bPoly, affine, eval_add, eval_sub,
    eval_mul, eval_pow, eval_X, eval_C, eval_one]
  linear_combination s ^ 2 * ha + 2 * s * t * hd

theorem transformed_identity {δ t : ℝ} {x y p : Polynomial ℝ}
    (ht : 0 ≤ t) (hp : p = aPoly δ * x + bPoly * y) :
    p.comp (affine δ t (scale δ t)) =
      aPoly (improvedDelta δ t) * transformedX δ t (scale δ t) x y +
      bPoly * transformedY δ t (scale δ t) x y := by
  have hd := improvedDelta_mul_denominator (δ := δ) ht
  change improvedDelta δ t * (1 + δ ^ 2 * t) = δ * scale δ t at hd
  rw [hp, add_comp, mul_comp, mul_comp, a_comp_affine (scale_sq ht) hd,
    b_comp_affine (scale_sq ht) hd]
  simp only [transformedX, transformedY, mixedX, mixedY, denominator,
    add_comp, mul_comp, sub_comp, pow_comp, one_comp, C_comp,
    map_add, map_mul, map_sub, map_one, map_pow]
  ring

theorem direct_identity (δ ε : ℝ) (x y : Polynomial ℝ) :
    aPoly δ * x + bPoly * y - C (2 * ε) * X * x =
      aPoly (δ + ε) * x + bPoly * y := by
  simp only [aPoly, map_mul, map_add]
  ring

theorem affine_natDegree {δ t α : ℝ} (hα : α ≠ 0) :
    (affine δ t α).natDegree = 1 := by
  rw [affine, sub_eq_add_neg, ← map_neg, natDegree_add_C,
    natDegree_C_mul_X α hα]

theorem affine_comp_natDegree {δ t α : ℝ} (hα : α ≠ 0)
    (p : Polynomial ℝ) : (p.comp (affine δ t α)).natDegree = p.natDegree := by
  rw [natDegree_comp, affine_natDegree hα, mul_one]

theorem mixedX_cancellation_coeff (t : ℝ) {x y : Polynomial ℝ} {n : ℕ}
    (hcancel : y.coeff n = -x.coeff n) :
    (mixedX t x y).coeff n = x.coeff n := by
  simp [mixedX, coeff_add, coeff_C_mul, hcancel]

theorem mixedY_cancellation_coeff (δ t : ℝ) {x y : Polynomial ℝ} {n : ℕ}
    (hcancel : y.coeff n = -x.coeff n) :
    (mixedY δ t x y).coeff n = -denominator δ t * x.coeff n := by
  simp only [mixedY, coeff_add, coeff_C_mul, hcancel, denominator]
  ring

theorem qOfDelta_strictAnti {δ d : ℝ} (hδ : 0 < δ) (h : δ < d) :
    qOfDelta d < qOfDelta δ := by
  have hden1 : 0 < 1 + δ := by linarith
  have hden2 : 0 < 1 + d := by linarith
  unfold qOfDelta
  apply (div_lt_div_iff₀ hden2 hden1).2
  nlinarith

theorem qOfDelta_mem {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < qOfDelta δ ∧ qOfDelta δ < 1 := by
  have hden : 0 < 1 + δ := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · exact (div_lt_one hden).2 (by linarith)

theorem deltaOfQ_qOfDelta {δ : ℝ} (hδ : 0 < δ) :
    deltaOfQ (qOfDelta δ) = δ := by
  unfold deltaOfQ qOfDelta
  have hden : 1 + δ ≠ 0 := by positivity
  field_simp
  ring

end

end BelgianChocolate.StrictImprovement
