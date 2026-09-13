/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.PolynomialAnalyticInterface
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.RCLike.Lemmas

/-!
# The polynomial-to-analytic Cayley construction

This file contains only the valid forward implication.  No reverse implication at the
analytic endpoint is stated.
-/

namespace BelgianChocolate

open Set Metric Polynomial Complex

noncomputable section

def cayley (w : ℂ) : ℂ := (1 + w) / (1 - w)

def liftedEval (p : Polynomial ℝ) (w : ℂ) : ℂ := evalC p (cayley w)

theorem one_sub_ne_zero_of_mem_unitDisc {w : ℂ} (hw : w ∈ unitDisc) : 1 - w ≠ 0 := by
  intro h
  have hw1 : w = 1 := (sub_eq_zero.mp h).symm
  subst w
  simpa [unitDisc] using hw

theorem cayley_re_pos {w : ℂ} (hw : w ∈ unitDisc) : 0 < (cayley w).re := by
  have hnorm : ‖w‖ < 1 := by simpa [unitDisc] using hw
  have hden : 0 < Complex.normSq (1 - w) :=
    Complex.normSq_pos.mpr (one_sub_ne_zero_of_mem_unitDisc hw)
  rw [cayley, Complex.div_re]
  simp only [map_add, map_one, Complex.add_re, Complex.one_re, Complex.sub_re,
    Complex.one_im, Complex.sub_im, Complex.add_im, zero_add, zero_sub]
  have hsq : w.re ^ 2 + w.im ^ 2 < 1 := by
    have hs : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
    rw [Complex.sq_norm, Complex.normSq_apply] at hs
    simpa [pow_two] using hs
  rw [← add_div]
  apply div_pos
  · nlinarith
  · exact hden

theorem stable_eval_ne_zero_of_nonneg_re {p : Polynomial ℝ}
    (hp : HurwitzStable p) {z : ℂ} (hz : 0 ≤ z.re) : evalC p z ≠ 0 := by
  intro hzero
  exact (not_lt_of_ge hz) (hp.2 z hzero)

theorem stable_liftedEval_ne_zero {p : Polynomial ℝ}
    (hp : HurwitzStable p) {w : ℂ} (hw : w ∈ unitDisc) : liftedEval p w ≠ 0 :=
  stable_eval_ne_zero_of_nonneg_re hp (cayley_re_pos hw).le

theorem cayley_add_one {w : ℂ} (hw : 1 - w ≠ 0) :
    cayley w + 1 = 2 / (1 - w) := by
  rw [cayley]
  field_simp
  ring

theorem cayley_b_identity {w : ℂ} (hw : 1 - w ≠ 0) :
    (cayley w + 1) ^ 2 * w = cayley w ^ 2 - 1 := by
  rw [cayley]
  field_simp
  ring

theorem cayley_a_identity {q : ℝ} {w : ℂ} (hq : q ≠ -1) (hw : 1 - w ≠ 0) :
    (cayley w + 1) ^ 2 * (w ^ 2 + (q : ℂ)) =
      (1 + (q : ℂ)) *
        (cayley w ^ 2 - 2 * (deltaOfQ q : ℂ) * cayley w + 1) := by
  have hqden : 1 + q ≠ 0 := by
    intro hzero
    apply hq
    linarith
  have hqdenC : (1 : ℂ) + (q : ℂ) ≠ 0 := by exact_mod_cast hqden
  have hd : ((deltaOfQ q : ℝ) : ℂ) =
      (1 - (q : ℂ)) / (1 + (q : ℂ)) := by
    simp [deltaOfQ]
  rw [cayley, hd]
  field_simp [hw, hqdenC]
  ring

theorem evalC_bPoly (s : ℂ) : evalC bPoly s = s ^ 2 - 1 := by
  simp [evalC, bPoly]

theorem evalC_aPoly (δ : ℝ) (s : ℂ) :
    evalC (aPoly δ) s = s ^ 2 - 2 * (δ : ℂ) * s + 1 := by
  simp [evalC, aPoly]

theorem evalC_original_identity {δ : ℝ} {x y p : Polynomial ℝ}
    (h : p = aPoly δ * x + bPoly * y) (s : ℂ) :
    evalC p s = evalC (aPoly δ) s * evalC x s + evalC bPoly s * evalC y s := by
  subst p
  simp [evalC]

def forwardG (y p : Polynomial ℝ) (w : ℂ) : ℂ :=
  (cayley w + 1) ^ 2 * liftedEval y w / liftedEval p w

def forwardH (q : ℝ) (x p : Polynomial ℝ) (w : ℂ) : ℂ :=
  (cayley w + 1) ^ 2 / (1 + (q : ℂ)) * liftedEval x w / liftedEval p w

def forwardF (y p : Polynomial ℝ) (w : ℂ) : ℂ := w * forwardG y p w

theorem evalC_star (p : Polynomial ℝ) (z : ℂ) :
    evalC p (star z) = star (evalC p z) := by
  simpa [evalC, aeval_def] using (Polynomial.aeval_conj p z)

theorem cayley_star (w : ℂ) : cayley (star w) = star (cayley w) := by
  simp [cayley, map_div₀]

theorem liftedEval_star (p : Polynomial ℝ) (w : ℂ) :
    liftedEval p (star w) = star (liftedEval p w) := by
  unfold liftedEval
  rw [cayley_star, evalC_star]

theorem forwardG_star (y p : Polynomial ℝ) (w : ℂ) :
    forwardG y p (star w) = star (forwardG y p w) := by
  unfold forwardG
  rw [cayley_star, liftedEval_star, liftedEval_star]
  simp

theorem forwardH_star (q : ℝ) (x p : Polynomial ℝ) (w : ℂ) :
    forwardH q x p (star w) = star (forwardH q x p w) := by
  unfold forwardH
  rw [cayley_star, liftedEval_star, liftedEval_star]
  simp

theorem forwardF_star (y p : Polynomial ℝ) (w : ℂ) :
    forwardF y p (star w) = star (forwardF y p w) := by
  unfold forwardF
  rw [forwardG_star]
  simp

theorem differentiableAt_cayley {w : ℂ} (hw : 1 - w ≠ 0) :
    DifferentiableAt ℂ cayley w := by
  unfold cayley
  fun_prop

theorem differentiableAt_liftedEval (p : Polynomial ℝ) {w : ℂ}
    (hw : 1 - w ≠ 0) : DifferentiableAt ℂ (liftedEval p) w := by
  apply (p.map (algebraMap ℝ ℂ)).differentiableAt.comp w
  exact differentiableAt_cayley hw

theorem differentiableAt_forwardG {y p : Polynomial ℝ} {w : ℂ}
    (hw : 1 - w ≠ 0) (hp : liftedEval p w ≠ 0) :
    DifferentiableAt ℂ (forwardG y p) w := by
  unfold forwardG
  exact ((((differentiableAt_cayley hw).add (differentiableAt_const (1 : ℂ))).pow 2).mul
    (differentiableAt_liftedEval y hw)).div (differentiableAt_liftedEval p hw) hp

theorem differentiableAt_forwardH {q : ℝ} {x p : Polynomial ℝ} {w : ℂ}
    (hw : 1 - w ≠ 0) (hq : (1 : ℂ) + (q : ℂ) ≠ 0)
    (hp : liftedEval p w ≠ 0) :
    DifferentiableAt ℂ (forwardH q x p) w := by
  unfold forwardH
  exact (((((differentiableAt_cayley hw).add (differentiableAt_const (1 : ℂ))).pow 2).div_const _).mul
    (differentiableAt_liftedEval x hw)).div (differentiableAt_liftedEval p hw) hp

theorem differentiableAt_forwardF {y p : Polynomial ℝ} {w : ℂ}
    (hw : 1 - w ≠ 0) (hp : liftedEval p w ≠ 0) :
    DifferentiableAt ℂ (forwardF y p) w := by
  exact differentiableAt_id.mul (differentiableAt_forwardG hw hp)

theorem forward_factor_identity {q : ℝ} {x y p : Polynomial ℝ}
    (hq0 : 0 < q) (hp : HurwitzStable p)
    (hidentity : p = aPoly (deltaOfQ q) * x + bPoly * y)
    {w : ℂ} (hw : w ∈ unitDisc) :
    forwardF y p w + (w ^ 2 + (q : ℂ)) * forwardH q x p w = 1 := by
  have hwden := one_sub_ne_zero_of_mem_unitDisc hw
  have hpden : liftedEval p w ≠ 0 := stable_liftedEval_ne_zero hp hw
  have hqden : (1 : ℂ) + (q : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + q ≠ 0 by positivity)
  have hid := evalC_original_identity hidentity (cayley w)
  rw [evalC_aPoly, evalC_bPoly] at hid
  have hb := cayley_b_identity hwden
  have ha := cayley_a_identity (by linarith) hwden
  change evalC p (cayley w) ≠ 0 at hpden
  have hb' : w * ((cayley w + 1) ^ 2 * evalC y (cayley w)) =
      (cayley w ^ 2 - 1) * evalC y (cayley w) := by
    calc
      _ = ((cayley w + 1) ^ 2 * w) * evalC y (cayley w) := by ring
      _ = _ := by rw [hb]
  have ha' : (w ^ 2 + (q : ℂ)) *
      ((cayley w + 1) ^ 2 / (1 + (q : ℂ)) * evalC x (cayley w)) =
      (cayley w ^ 2 - 2 * (deltaOfQ q : ℂ) * cayley w + 1) *
        evalC x (cayley w) := by
    calc
      _ = ((cayley w + 1) ^ 2 * (w ^ 2 + (q : ℂ))) /
          (1 + (q : ℂ)) * evalC x (cayley w) := by ring
      _ = _ := by rw [ha]; field_simp [hqden]
  have hnum : w * ((cayley w + 1) ^ 2 * evalC y (cayley w)) +
      (w ^ 2 + (q : ℂ)) *
        ((cayley w + 1) ^ 2 / (1 + (q : ℂ)) * evalC x (cayley w)) =
      evalC p (cayley w) := by
    rw [hb', ha', hid]
    ring
  unfold forwardF forwardG forwardH liftedEval
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    w * ((cayley w + 1) ^ 2 * evalC y (cayley w) *
          (evalC p (cayley w))⁻¹) +
        (w ^ 2 + (q : ℂ)) *
          ((cayley w + 1) ^ 2 * (1 + (q : ℂ))⁻¹ *
            evalC x (cayley w) * (evalC p (cayley w))⁻¹) =
      (w * ((cayley w + 1) ^ 2 * evalC y (cayley w)) +
        (w ^ 2 + (q : ℂ)) *
          ((cayley w + 1) ^ 2 / (1 + (q : ℂ)) * evalC x (cayley w))) *
            (evalC p (cayley w))⁻¹ := by rw [div_eq_mul_inv]; ring
    _ = evalC p (cayley w) * (evalC p (cayley w))⁻¹ := by rw [hnum]
    _ = 1 := mul_inv_cancel₀ hpden

theorem forwardG_ne_zero {y p : Polynomial ℝ} (hy : HurwitzStable y)
    (hp : HurwitzStable p) {w : ℂ} (hw : w ∈ unitDisc) : forwardG y p w ≠ 0 := by
  have hwden := one_sub_ne_zero_of_mem_unitDisc hw
  have hs1 : cayley w + 1 ≠ 0 := by
    rw [cayley_add_one hwden]
    exact div_ne_zero (by norm_num) hwden
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hs1)
    (stable_liftedEval_ne_zero hy hw)) (stable_liftedEval_ne_zero hp hw)

theorem forwardH_ne_zero {q : ℝ} {x p : Polynomial ℝ} (hq : 0 < q)
    (hx : HurwitzStable x) (hp : HurwitzStable p) {w : ℂ} (hw : w ∈ unitDisc) :
    forwardH q x p w ≠ 0 := by
  have hwden := one_sub_ne_zero_of_mem_unitDisc hw
  have hs1 : cayley w + 1 ≠ 0 := by
    rw [cayley_add_one hwden]
    exact div_ne_zero (by norm_num) hwden
  have hqden : (1 : ℂ) + (q : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + q ≠ 0 by positivity)
  exact div_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero 2 hs1) hqden)
    (stable_liftedEval_ne_zero hx hw)) (stable_liftedEval_ne_zero hp hw)

theorem holSymm_forwardF {y p : Polynomial ℝ} (hp : HurwitzStable p) :
    HolSymmOn 1 (forwardF y p) := by
  constructor
  · intro w hw
    exact (differentiableAt_forwardF (one_sub_ne_zero_of_mem_unitDisc hw)
      (stable_liftedEval_ne_zero hp hw)).differentiableWithinAt
  · intro w hw
    exact forwardF_star y p w

theorem sq_add_real_eq_zero_iff {q : ℝ} (hq : 0 ≤ q) (w : ℂ) :
    w ^ 2 + (q : ℂ) = 0 ↔
      w = Complex.I * (Real.sqrt q : ℂ) ∨ w = -(Complex.I * (Real.sqrt q : ℂ)) := by
  have hsqrt : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq
  have hfactor :
      (w - Complex.I * (Real.sqrt q : ℂ)) *
          (w + Complex.I * (Real.sqrt q : ℂ)) = w ^ 2 + (q : ℂ) := by
    calc
      _ = w ^ 2 - (Complex.I * (Real.sqrt q : ℂ)) ^ 2 := by ring
      _ = w ^ 2 + (q : ℂ) := by rw [mul_pow, Complex.I_sq, hsqrt]; ring
  constructor
  · intro h
    rw [← hfactor] at h
    rcases mul_eq_zero.mp h with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  · rintro (rfl | rfl)
    · rw [← hfactor]
      ring
    · rw [← hfactor]
      ring

theorem forwardF_zero_iff {y p : Polynomial ℝ} (hy : HurwitzStable y)
    (hp : HurwitzStable p) {w : ℂ} (hw : w ∈ unitDisc) :
    forwardF y p w = 0 ↔ w = 0 := by
  rw [forwardF, mul_eq_zero]
  exact or_iff_left (forwardG_ne_zero hy hp hw)

theorem deriv_forwardF_zero_ne {y p : Polynomial ℝ} (hy : HurwitzStable y)
    (hp : HurwitzStable p) : deriv (forwardF y p) 0 ≠ 0 := by
  have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hdiffG := differentiableAt_forwardG (y := y) (p := p)
    (one_sub_ne_zero_of_mem_unitDisc hzero)
    (stable_liftedEval_ne_zero hp hzero)
  have hd := (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul hdiffG.hasDerivAt
  have hevent : forwardF y p =ᶠ[nhds (0 : ℂ)] (id * forwardG y p) := by
    filter_upwards [] with z
    rfl
  have heq : deriv (forwardF y p) 0 = forwardG y p 0 := by
    rw [hevent.deriv_eq, hd.deriv]
    simp
  rw [heq]
  exact forwardG_ne_zero hy hp hzero

theorem specialPoint_mem_unitDisc {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Complex.I * (Real.sqrt q : ℂ) ∈ unitDisc ∧
      -(Complex.I * (Real.sqrt q : ℂ)) ∈ unitDisc := by
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0.le
  have hs1 : Real.sqrt q < 1 := by nlinarith
  constructor <;> simp [unitDisc, abs_of_nonneg hs0, hs1]

theorem forwardF_one_iff {q : ℝ} {x y p : Polynomial ℝ}
    (hq0 : 0 < q) (hx : HurwitzStable x) (hp : HurwitzStable p)
    (hidentity : p = aPoly (deltaOfQ q) * x + bPoly * y)
    {w : ℂ} (hw : w ∈ unitDisc) :
    forwardF y p w = 1 ↔
      w = Complex.I * (Real.sqrt q : ℂ) ∨
        w = -(Complex.I * (Real.sqrt q : ℂ)) := by
  have hid := forward_factor_identity hq0 hp hidentity hw
  have hh := forwardH_ne_zero hq0 hx hp hw
  rw [← sq_add_real_eq_zero_iff hq0.le]
  constructor
  · intro hf
    rw [hf] at hid
    have hm : (w ^ 2 + (q : ℂ)) * forwardH q x p w = 0 := by
      linear_combination hid
    exact (mul_eq_zero.mp hm).resolve_right hh
  · intro hz
    rw [hz, zero_mul, add_zero] at hid
    exact hid

theorem deriv_forwardF_special_ne {q : ℝ} {x y p : Polynomial ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hx : HurwitzStable x) (hp : HurwitzStable p)
    (hidentity : p = aPoly (deltaOfQ q) * x + bPoly * y)
    {w : ℂ} (hw : w = Complex.I * (Real.sqrt q : ℂ) ∨
      w = -(Complex.I * (Real.sqrt q : ℂ))) : deriv (forwardF y p) w ≠ 0 := by
  have hmems := specialPoint_mem_unitDisc hq0 hq1
  have hwmem : w ∈ unitDisc := hw.elim (fun h => h ▸ hmems.1) (fun h => h ▸ hmems.2)
  have hwden := one_sub_ne_zero_of_mem_unitDisc hwmem
  have hpden := stable_liftedEval_ne_zero hp hwmem
  have hqden : (1 : ℂ) + (q : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + q ≠ 0 by positivity)
  have hdiffF := differentiableAt_forwardF (y := y) (p := p) hwden hpden
  have hdiffH := differentiableAt_forwardH (q := q) (x := x) (p := p) hwden hqden hpden
  have hfactor : w ^ 2 + (q : ℂ) = 0 :=
    (sq_add_real_eq_zero_iff hq0.le w).2 hw
  have hevent : (fun z => 1 - forwardF y p z) =ᶠ[nhds w]
      (fun z => (z ^ 2 + (q : ℂ)) * forwardH q x p z) := by
    filter_upwards [isOpen_ball.mem_nhds hwmem] with z hz
    have hid := forward_factor_identity hq0 hp hidentity hz
    rw [← hid]
    ring
  have hrightDeriv : deriv (fun z => (z ^ 2 + (q : ℂ)) * forwardH q x p z) w =
      2 * w * forwardH q x p w := by
    change deriv ((fun z : ℂ => z ^ 2 + (q : ℂ)) * forwardH q x p) w =
      2 * w * forwardH q x p w
    have hd := (((hasDerivAt_id (𝕜 := ℂ) w).pow 2).add_const (q : ℂ)).mul
      hdiffH.hasDerivAt
    simpa [hfactor] using hd.deriv
  have hdeq := hevent.deriv_eq
  rw [deriv_const_sub, hrightDeriv] at hdeq
  have hwne : w ≠ 0 := by
    rintro rfl
    have hqzeroC : (q : ℂ) = 0 := by simpa using hfactor
    have hqzero : q = 0 := by exact_mod_cast hqzeroC
    linarith
  have hh := forwardH_ne_zero hq0 hx hp hwmem
  intro hzero
  rw [hzero] at hdeq
  have htwo : (2 : ℂ) * (w * forwardH q x p w) = 0 := by
    simpa [mul_assoc] using hdeq.symm
  exact (mul_ne_zero (by norm_num) (mul_ne_zero hwne hh)) htwo

/-- Every strict Hurwitz-stable polynomial witness gives the concrete disc function obtained by
the Cayley transform.  This is only the forward interface; in particular it makes no assertion
that analytic feasibility at the threshold has a polynomial realization. -/
theorem polynomialFeasible_implies_analyticFeasible {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hP : PolynomialFeasible q) :
    AnalyticFeasible q := by
  rcases hP with ⟨_, x, y, p, hx, hy, hp, _, hidentity⟩
  refine ⟨hq0, hq1, forwardF y p, ?_⟩
  refine ⟨holSymm_forwardF hp, ?_, deriv_forwardF_zero_ne hy hp, ?_, ?_, ?_⟩
  · intro z hz
    exact forwardF_zero_iff hy hp hz
  · intro z hz
    exact forwardF_one_iff hq0 hx hp hidentity hz
  · exact deriv_forwardF_special_ne hq0 hq1 hx hp hidentity (Or.inl rfl)
  · exact deriv_forwardF_special_ne hq0 hq1 hx hp hidentity (Or.inr rfl)

theorem polynomialToAnalyticStatement : PolynomialToAnalyticStatement := by
  intro q hq0 hq1 hP
  exact polynomialFeasible_implies_analyticFeasible hq0 hq1 hP

end

end BelgianChocolate
