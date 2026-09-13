/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.AnalyticPolynomialApproximation
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Strict-slack analytic factors -/

namespace BelgianChocolate

open Set Metric Polynomial Complex Filter
open scoped Topology

noncomputable section

def strictScale (r q : ℝ) : ℝ := Real.sqrt (r / q)
def strictRadius (r q : ℝ) : ℝ := 1 / strictScale r q
def rootPlus (q : ℝ) : ℂ := Complex.I * (Real.sqrt q : ℂ)
def rootMinus (q : ℝ) : ℂ := -rootPlus q
def dilateDiscFunction (f : ℂ → ℂ) (r q : ℝ) (z : ℂ) : ℂ :=
  f ((strictScale r q : ℝ) * z)

def symmetrize (f : ℂ → ℂ) : ℂ → ℂ :=
  (f + (star ∘ f ∘ star)) / (fun _ => 2)

def strictRawU (f : ℂ → ℂ) (r q : ℝ) : ℂ → ℂ :=
  dslope (dilateDiscFunction f r q) 0

def strictRawV (f : ℂ → ℂ) (r q : ℝ) : ℂ → ℂ :=
  let g := dilateDiscFunction f r q
  let h := fun z => 1 - g z
  dslope (dslope h (rootPlus q)) (rootMinus q)

def strictU (f : ℂ → ℂ) (r q : ℝ) : ℂ → ℂ :=
  symmetrize (strictRawU f r q)

def strictV (f : ℂ → ℂ) (r q : ℝ) : ℂ → ℂ :=
  symmetrize (strictRawV f r q)

theorem strictScale_pos {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    0 < strictScale r q := by
  exact Real.sqrt_pos.2 (div_pos hr hq)

theorem strictScale_lt_one {r q : ℝ} (hr : 0 < r) (hrq : r < q) :
    strictScale r q < 1 := by
  rw [strictScale, Real.sqrt_lt' zero_lt_one]
  have hq : 0 < q := hr.trans hrq
  rw [one_pow, div_lt_one hq]
  exact hrq

theorem strictRadius_gt_one {r q : ℝ} (hr : 0 < r) (hrq : r < q) :
    1 < strictRadius r q := by
  rw [strictRadius, one_div]
  exact (one_lt_inv₀ (strictScale_pos hr (hr.trans hrq))).2 (strictScale_lt_one hr hrq)

theorem strictScale_mul_sqrt {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    strictScale r q * Real.sqrt q = Real.sqrt r := by
  rw [strictScale, Real.sqrt_div hr]
  exact div_mul_cancel₀ (Real.sqrt r) (Real.sqrt_ne_zero'.2 hq)

theorem strictScale_ne_zero {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    strictScale r q ≠ 0 := ne_of_gt (strictScale_pos hr hq)

theorem dilated_mem_unitDisc {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    ((strictScale r q : ℝ) * z) ∈ unitDisc := by
  have hc := strictScale_pos hr hq
  have hz' : ‖z‖ < 1 / strictScale r q := by
    simpa [strictRadius, dist_eq_norm] using hz
  have : strictScale r q * ‖z‖ < 1 := by
    calc
      strictScale r q * ‖z‖ < strictScale r q * (1 / strictScale r q) :=
        mul_lt_mul_of_pos_left hz' hc
      _ = 1 := by field_simp
  simpa [unitDisc, dist_eq_norm, norm_mul, abs_of_pos hc] using this

theorem star_mem_ball_iff (R : ℝ) (z : ℂ) :
    star z ∈ Metric.ball (0 : ℂ) R ↔ z ∈ Metric.ball (0 : ℂ) R := by
  simp [dist_eq_norm]

theorem root_scale {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    (strictScale r q : ℂ) * rootPlus q = rootPlus r := by
  calc
    (strictScale r q : ℂ) * rootPlus q =
        Complex.I * ((strictScale r q * Real.sqrt q : ℝ) : ℂ) := by
          rw [rootPlus]
          push_cast
          ring
    _ = rootPlus r := by rw [strictScale_mul_sqrt hr hq]; rfl

theorem rootPlus_ne_rootMinus {q : ℝ} (hq : 0 < q) : rootPlus q ≠ rootMinus q := by
  intro h
  rw [rootPlus, rootMinus, rootPlus] at h
  have hprod : (2 : ℂ) * (Complex.I * (Real.sqrt q : ℂ)) = 0 := by
    linear_combination h
  have hI : Complex.I * (Real.sqrt q : ℂ) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  have hs : (Real.sqrt q : ℂ) = 0 := by
    exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
  have : Real.sqrt q = 0 := by exact_mod_cast hs
  exact (Real.sqrt_ne_zero'.2 hq) this

theorem rootPlus_mem_strictBall {r q : ℝ} (hr : 0 < r) (hrq : r < q)
    (hq1 : q < 1) : rootPlus q ∈ Metric.ball (0 : ℂ) (strictRadius r q) := by
  have hc := strictScale_pos hr (hr.trans hrq)
  have hsr : Real.sqrt r < 1 := (Real.sqrt_lt' zero_lt_one).2 (by
    rw [one_pow]
    exact hrq.trans hq1)
  have hm : strictScale r q * Real.sqrt q < 1 := by
    rw [strictScale_mul_sqrt hr.le (hr.trans hrq)]
    exact hsr
  have hs : Real.sqrt q < 1 / strictScale r q := (lt_div_iff₀ hc).2 (by
    simpa [mul_comm] using hm)
  simpa [strictRadius, rootPlus, dist_eq_norm, abs_of_nonneg (Real.sqrt_nonneg q)] using hs

theorem rootMinus_mem_strictBall {r q : ℝ} (hr : 0 < r) (hrq : r < q)
    (hq1 : q < 1) : rootMinus q ∈ Metric.ball (0 : ℂ) (strictRadius r q) := by
  simpa [rootMinus, dist_eq_norm] using rootPlus_mem_strictBall hr hrq hq1

theorem dilated_holSymm {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f) :
    HolSymmOn (strictRadius r q) (dilateDiscFunction f r q) := by
  constructor
  · intro z hz
    have hmem := dilated_mem_unitDisc hr (hr.trans hrq) hz
    have hfAt := (hf.1.1 _ hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    have hlin : DifferentiableAt ℂ (fun z : ℂ => (strictScale r q : ℂ) * z) z :=
      (differentiableAt_const (c := (strictScale r q : ℂ))).mul differentiableAt_id
    exact (hfAt.comp z hlin).differentiableWithinAt
  · intro z hz
    have hmem := dilated_mem_unitDisc hr (hr.trans hrq) hz
    have hstar : star z ∈ Metric.ball (0 : ℂ) (strictRadius r q) :=
      (star_mem_ball_iff _ _).2 hz
    have hmemstar := dilated_mem_unitDisc hr (hr.trans hrq) hstar
    rw [dilateDiscFunction, dilateDiscFunction]
    have hc : star ((strictScale r q : ℂ) * z) =
        (strictScale r q : ℂ) * star z := by simp
    rw [← hc, hf.1.2 _ hmem]

theorem dilated_zero {f : ℂ → ℂ} {r q : ℝ} (hf : DiscFunction r f) :
    dilateDiscFunction f r q 0 = 0 := by
  simpa [dilateDiscFunction] using (hf.2.1 0 (by simp [unitDisc])).2 rfl

theorem dilated_zero_iff {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    dilateDiscFunction f r q z = 0 ↔ z = 0 := by
  have hmem := dilated_mem_unitDisc hr (hr.trans hrq) hz
  rw [dilateDiscFunction, hf.2.1 _ hmem]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast strictScale_ne_zero hr (hr.trans hrq))
  · rintro rfl
    simp

theorem dilated_one_iff {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    dilateDiscFunction f r q z = 1 ↔ z = rootPlus q ∨ z = rootMinus q := by
  have hmem := dilated_mem_unitDisc hr (hr.trans hrq) hz
  rw [dilateDiscFunction, hf.2.2.2.1 _ hmem]
  have hc : (strictScale r q : ℂ) ≠ 0 := by exact_mod_cast strictScale_ne_zero hr (hr.trans hrq)
  have hp := root_scale hr.le (hr.trans hrq)
  have hm : (strictScale r q : ℂ) * rootMinus q = rootMinus r := by
    simpa [rootMinus] using congrArg Neg.neg hp
  constructor
  · rintro (h | h)
    · left
      change (strictScale r q : ℂ) * z = rootPlus r at h
      apply mul_left_cancel₀ hc
      rw [h, hp]
    · right
      change (strictScale r q : ℂ) * z = rootMinus r at h
      apply mul_left_cancel₀ hc
      rw [h, hm]
  · rintro (rfl | rfl)
    · left; exact hp
    · right; exact hm

theorem symmetrize_symm (f : ℂ → ℂ) (z : ℂ) :
    symmetrize f (star z) = star (symmetrize f z) := by
  simp [symmetrize, Function.comp_def, star_add]
  ring

theorem differentiableOn_symmetrize {f : ℂ → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) :
    DifferentiableOn ℂ (symmetrize f) (Metric.ball 0 R) := by
  intro z hz
  have hzstar : star z ∈ Metric.ball (0 : ℂ) R := (star_mem_ball_iff R z).2 hz
  have hfz := (hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hfs := (hf (star z) hzstar).differentiableAt (Metric.isOpen_ball.mem_nhds hzstar)
  have href : DifferentiableAt ℂ (star ∘ f ∘ star) z := by
    simpa using hfs.star_conj
  have havg := (hfz.add href).div_const (2 : ℂ)
  exact havg.differentiableWithinAt

theorem holSymm_symmetrize {f : ℂ → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) :
    HolSymmOn R (symmetrize f) :=
  ⟨differentiableOn_symmetrize hf, fun z _ => symmetrize_symm f z⟩

theorem strictRawU_differentiable {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f) :
    DifferentiableOn ℂ (strictRawU f r q) (Metric.ball 0 (strictRadius r q)) := by
  rw [strictRawU, Complex.differentiableOn_dslope
    (Metric.isOpen_ball.mem_nhds (by
      have := strictRadius_gt_one hr hrq
      have hpos : 0 < strictRadius r q := zero_lt_one.trans this
      simpa using hpos))]
  exact (dilated_holSymm hr hrq hf).1

theorem strictRawV_differentiable {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) :
    DifferentiableOn ℂ (strictRawV f r q) (Metric.ball 0 (strictRadius r q)) := by
  let g := dilateDiscFunction f r q
  let h : ℂ → ℂ := fun z => 1 - g z
  have hg := (dilated_holSymm hr hrq hf).1
  have hh : DifferentiableOn ℂ h (Metric.ball 0 (strictRadius r q)) := by
    intro z hz
    exact ((differentiableAt_const (c := (1 : ℂ))).sub
      ((hg z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have ha := rootPlus_mem_strictBall hr hrq hq1
  have hb := rootMinus_mem_strictBall hr hrq hq1
  change DifferentiableOn ℂ
    (dslope (dslope h (rootPlus q)) (rootMinus q))
    (Metric.ball 0 (strictRadius r q))
  rw [Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hb)]
  rw [Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds ha)]
  exact hh

theorem strictRawU_factor {f : ℂ → ℂ} {r q : ℝ} (hf : DiscFunction r f) (z : ℂ) :
    z * strictRawU f r q z = dilateDiscFunction f r q z := by
  simpa [strictRawU] using
    (sub_smul_dslope_of_zero (dilated_zero (q := q) hf) z)

theorem quadratic_root_factor {q : ℝ} (hq : 0 ≤ q) (z : ℂ) :
    (z - rootPlus q) * (z - rootMinus q) = z ^ 2 + (q : ℂ) := by
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq
  rw [rootPlus, rootMinus, rootPlus]
  calc
    (z - Complex.I * (Real.sqrt q : ℂ)) *
        (z - -(Complex.I * (Real.sqrt q : ℂ))) =
        z ^ 2 - (Complex.I * (Real.sqrt q : ℂ)) ^ 2 := by ring
    _ = z ^ 2 + (q : ℂ) := by rw [mul_pow, Complex.I_sq, hs]; ring

theorem strictRawV_factor {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) (z : ℂ) :
    (z ^ 2 + (q : ℂ)) * strictRawV f r q z =
      1 - dilateDiscFunction f r q z := by
  let g := dilateDiscFunction f r q
  let h : ℂ → ℂ := fun z => 1 - g z
  let d := dslope h (rootPlus q)
  have ha_mem := rootPlus_mem_strictBall hr hrq hq1
  have hb_mem := rootMinus_mem_strictBall hr hrq hq1
  have hga : g (rootPlus q) = 1 :=
    (dilated_one_iff hr hrq hq1 hf ha_mem).2 (Or.inl rfl)
  have hgb : g (rootMinus q) = 1 :=
    (dilated_one_iff hr hrq hq1 hf hb_mem).2 (Or.inr rfl)
  have hha : h (rootPlus q) = 0 := by simp [h, hga]
  have hhb : h (rootMinus q) = 0 := by simp [h, hgb]
  have hfirst (w : ℂ) : (w - rootPlus q) * d w = h w := by
    simpa [d, smul_eq_mul] using sub_smul_dslope_of_zero hha w
  have hd_b : d (rootMinus q) = 0 := by
    have hb := hfirst (rootMinus q)
    rw [hhb] at hb
    exact (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr
      (rootPlus_ne_rootMinus (hr.trans hrq)).symm)
  have hsecond : (z - rootMinus q) * dslope d (rootMinus q) z = d z := by
    simpa [smul_eq_mul] using sub_smul_dslope_of_zero hd_b z
  rw [← quadratic_root_factor (hr.trans hrq).le]
  change (z - rootPlus q) * (z - rootMinus q) *
      dslope d (rootMinus q) z = h z
  rw [mul_assoc, hsecond, hfirst]

theorem symmetrize_linear_factor {g u : ℂ → ℂ} {R : ℝ}
    (hg : ∀ z ∈ Metric.ball (0 : ℂ) R, g (star z) = star (g z))
    (hu : ∀ z ∈ Metric.ball (0 : ℂ) R, z * u z = g z)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    z * symmetrize u z = g z := by
  have hzstar := (star_mem_ball_iff R z).2 hz
  have hs := congrArg star (hu (star z) hzstar)
  have href : z * star (u (star z)) = g z := by
    calc
      z * star (u (star z)) = star (u (star z)) * z := mul_comm _ _
      _ = g z := by simpa only [star_mul, star_star, hg z hz] using hs
  rw [symmetrize]
  change z * ((u z + star (u (star z))) / 2) = g z
  rw [show z * ((u z + star (u (star z))) / 2) =
      (z * u z + z * star (u (star z))) / 2 by ring, hu z hz, href]
  ring

theorem symmetrize_quadratic_factor {q R : ℝ} {g v : ℂ → ℂ}
    (hg : ∀ z ∈ Metric.ball (0 : ℂ) R, g (star z) = star (g z))
    (hv : ∀ z ∈ Metric.ball (0 : ℂ) R,
      (z ^ 2 + (q : ℂ)) * v z = 1 - g z)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    (z ^ 2 + (q : ℂ)) * symmetrize v z = 1 - g z := by
  have hzstar := (star_mem_ball_iff R z).2 hz
  have hs := congrArg star (hv (star z) hzstar)
  have href : (z ^ 2 + (q : ℂ)) * star (v (star z)) = 1 - g z := by
    have hgs : star (g (star z)) = g z := by
      have ht := congrArg star (hg z hz)
      simpa using ht
    have hs' : (z ^ 2 + (q : ℂ)) * star (v (star z)) =
        1 - star (g (star z)) := by
      simpa using hs
    rw [hgs] at hs'
    exact hs'
  rw [symmetrize]
  change (z ^ 2 + (q : ℂ)) * ((v z + star (v (star z))) / 2) = 1 - g z
  rw [show (z ^ 2 + (q : ℂ)) * ((v z + star (v (star z))) / 2) =
      ((z ^ 2 + (q : ℂ)) * v z +
        (z ^ 2 + (q : ℂ)) * star (v (star z))) / 2 by ring,
    hv z hz, href]
  ring

theorem strictU_factor {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    z * strictU f r q z = dilateDiscFunction f r q z := by
  exact symmetrize_linear_factor (dilated_holSymm hr hrq hf).2
    (fun w _ => strictRawU_factor hf w) hz

theorem strictV_factor {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    (z ^ 2 + (q : ℂ)) * strictV f r q z = 1 - dilateDiscFunction f r q z := by
  exact symmetrize_quadratic_factor (dilated_holSymm hr hrq hf).2
    (fun w _ => strictRawV_factor hr hrq hq1 hf w) hz

theorem strict_bezout {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    z * strictU f r q z + (z ^ 2 + (q : ℂ)) * strictV f r q z = 1 := by
  rw [strictU_factor hr hrq hf hz, strictV_factor hr hrq hq1 hf hz]
  ring

theorem strictU_holSymm {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f) :
    HolSymmOn (strictRadius r q) (strictU f r q) := by
  exact holSymm_symmetrize (strictRawU_differentiable hr hrq hf)

theorem strictV_holSymm {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) :
    HolSymmOn (strictRadius r q) (strictV f r q) := by
  exact holSymm_symmetrize (strictRawV_differentiable hr hrq hq1 hf)

theorem closedUnitDisc_subset_strictBall {r q : ℝ} (hr : 0 < r) (hrq : r < q) :
    closedUnitDisc ⊆ Metric.ball (0 : ℂ) (strictRadius r q) := by
  exact Metric.closedBall_subset_ball (strictRadius_gt_one hr hrq)

theorem dilated_deriv_zero_ne {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f) :
    deriv (dilateDiscFunction f r q) 0 ≠ 0 := by
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hf0 := (hf.1.1 0 h0mem).differentiableAt (Metric.isOpen_ball.mem_nhds h0mem)
  have hc : (strictScale r q : ℂ) ≠ 0 := by
    exact_mod_cast strictScale_ne_zero hr (hr.trans hrq)
  have hlin : HasDerivAt (fun z : ℂ => (strictScale r q : ℂ) * z)
      (strictScale r q : ℂ) 0 := hasDerivAt_const_mul _
  have hf0' : DifferentiableAt ℂ f ((strictScale r q : ℂ) * (0 : ℂ)) := by
    simpa using hf0
  have hd := hf0'.hasDerivAt.comp 0 hlin
  have hevent : dilateDiscFunction f r q =ᶠ[nhds (0 : ℂ)]
      (f ∘ fun z : ℂ => (strictScale r q : ℂ) * z) := by
    filter_upwards [] with z
    rfl
  have heq : deriv (dilateDiscFunction f r q) 0 =
      deriv f 0 * (strictScale r q : ℂ) := by
    rw [hevent.deriv_eq, hd.deriv]
    simp
  rw [heq]
  exact mul_ne_zero hf.2.2.1 hc

theorem dilated_deriv_root_ne {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z = rootPlus q ∨ z = rootMinus q) :
    deriv (dilateDiscFunction f r q) z ≠ 0 := by
  have hzmem : z ∈ Metric.ball (0 : ℂ) (strictRadius r q) :=
    hz.elim (fun h => h ▸ rootPlus_mem_strictBall hr hrq hq1)
      (fun h => h ▸ rootMinus_mem_strictBall hr hrq hq1)
  have hargmem := dilated_mem_unitDisc hr (hr.trans hrq) hzmem
  have hfAt := (hf.1.1 _ hargmem).differentiableAt (Metric.isOpen_ball.mem_nhds hargmem)
  have hc : (strictScale r q : ℂ) ≠ 0 := by
    exact_mod_cast strictScale_ne_zero hr (hr.trans hrq)
  have hd := hfAt.hasDerivAt.comp z (hasDerivAt_const_mul (strictScale r q : ℂ))
  have heq : deriv (dilateDiscFunction f r q) z =
      deriv f ((strictScale r q : ℂ) * z) * (strictScale r q : ℂ) := by
    change deriv (fun w : ℂ => f ((strictScale r q : ℂ) * w)) z = _
    exact hd.deriv
  rw [heq]
  apply mul_ne_zero _ hc
  rcases hz with rfl | rfl
  · rw [root_scale hr.le (hr.trans hrq)]
    exact hf.2.2.2.2.1
  · have hm : (strictScale r q : ℂ) * rootMinus q = rootMinus r := by
      simpa [rootMinus] using congrArg Neg.neg (root_scale hr.le (hr.trans hrq))
    rw [hm]
    exact hf.2.2.2.2.2

theorem strictU_zero_free {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hf : DiscFunction r f) :
    ∀ z ∈ closedUnitDisc, strictU f r q z ≠ 0 := by
  intro z hz hzero
  have hzball := closedUnitDisc_subset_strictBall hr hrq hz
  by_cases hz0 : z = 0
  · subst z
    have h0ball : (0 : ℂ) ∈ Metric.ball 0 (strictRadius r q) := by
      have hp : 0 < strictRadius r q := zero_lt_one.trans (strictRadius_gt_one hr hrq)
      simpa using hp
    have hUdiff := (strictU_holSymm hr hrq hf).1
    have hUAt := (hUdiff 0 h0ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds h0ball)
    have hevent : (fun w => w * strictU f r q w) =ᶠ[nhds (0 : ℂ)]
        dilateDiscFunction f r q := by
      filter_upwards [Metric.isOpen_ball.mem_nhds h0ball] with w hw
      exact strictU_factor hr hrq hf hw
    have hd := (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul hUAt.hasDerivAt
    have hleft : deriv (fun w => w * strictU f r q w) 0 = strictU f r q 0 := by
      change deriv ((id : ℂ → ℂ) * strictU f r q) 0 = _
      simpa using hd.deriv
    have hdeq := hevent.deriv_eq
    rw [hleft, hzero] at hdeq
    exact dilated_deriv_zero_ne hr hrq hf hdeq.symm
  · have hfac := strictU_factor hr hrq hf hzball
    rw [hzero, mul_zero] at hfac
    have := (dilated_zero_iff hr hrq hf hzball).1 hfac.symm
    exact hz0 this

theorem strictV_zero_free {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) :
    ∀ z ∈ closedUnitDisc, strictV f r q z ≠ 0 := by
  intro z hz hzero
  have hzball := closedUnitDisc_subset_strictBall hr hrq hz
  by_cases hroot : z = rootPlus q ∨ z = rootMinus q
  · have hfactor : z ^ 2 + (q : ℂ) = 0 := by
      have hquad := quadratic_root_factor (hr.trans hrq).le z
      rcases hroot with h | h
      · rw [h]
        rw [h] at hquad
        simpa using hquad.symm
      · rw [h]
        rw [h] at hquad
        simpa using hquad.symm
    have hVdiff := (strictV_holSymm hr hrq hq1 hf).1
    have hVAt := (hVdiff z hzball).differentiableAt
      (Metric.isOpen_ball.mem_nhds hzball)
    have hevent : (fun w => (w ^ 2 + (q : ℂ)) * strictV f r q w) =ᶠ[nhds z]
        (fun w => 1 - dilateDiscFunction f r q w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with w hw
      exact strictV_factor hr hrq hq1 hf hw
    have hpoly : DifferentiableAt ℂ (fun w : ℂ => w ^ 2 + (q : ℂ)) z :=
      (differentiableAt_id.pow 2).add_const _
    have hd := hpoly.hasDerivAt.mul hVAt.hasDerivAt
    have hleft : deriv (fun w => (w ^ 2 + (q : ℂ)) * strictV f r q w) z =
        2 * z * strictV f r q z := by
      change deriv ((fun w : ℂ => w ^ 2 + (q : ℂ)) * strictV f r q) z = _
      rw [hd.deriv]
      simp [hfactor]
    have hdeq := hevent.deriv_eq
    rw [hleft, deriv_const_sub, hzero] at hdeq
    simp only [mul_zero, neg_eq_zero] at hdeq
    exact dilated_deriv_root_ne hr hrq hq1 hf hroot (neg_eq_zero.mp hdeq.symm)
  · have hfac := strictV_factor hr hrq hq1 hf hzball
    rw [hzero, mul_zero] at hfac
    have hone : dilateDiscFunction f r q z = 1 := by linear_combination hfac
    exact hroot ((dilated_one_iff hr hrq hq1 hf hzball).1 hone)

/-- Positive lower modulus on a compact disk. -/
theorem exists_pos_le_norm_on_closedUnitDisc {f : ℂ → ℂ}
    (hf : ContinuousOn f closedUnitDisc)
    (hz : ∀ z ∈ closedUnitDisc, f z ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ closedUnitDisc, m ≤ ‖f z‖ := by
  exact (isCompact_closedBall (0 : ℂ) 1).exists_forall_le' hf.norm
    (fun z hzmem => norm_pos_iff.mpr (hz z hzmem))

def strictW (f : ℂ → ℂ) (r q : ℝ) : ℂ → ℂ :=
  symmetrize (dslope (strictV f r q) 0)

theorem strictV_zero_value {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) :
    strictV f r q 0 = (1 / q : ℝ) := by
  have h0ball : (0 : ℂ) ∈ Metric.ball 0 (strictRadius r q) := by
    have hp : 0 < strictRadius r q := zero_lt_one.trans (strictRadius_gt_one hr hrq)
    simpa using hp
  have hb := strict_bezout hr hrq hq1 hf h0ball
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hr.trans hrq)
  norm_num at hb
  have hvC : strictV f r q 0 = (1 : ℂ) / (q : ℂ) := by
    apply (eq_div_iff hq).2
    simpa [mul_comm] using hb
  calc
    strictV f r q 0 = (1 : ℂ) / (q : ℂ) := hvC
    _ = ((1 / q : ℝ) : ℂ) := by norm_cast

theorem strictW_holSymm {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) :
    HolSymmOn (strictRadius r q) (strictW f r q) := by
  apply holSymm_symmetrize
  rw [Complex.differentiableOn_dslope
    (Metric.isOpen_ball.mem_nhds (by
      have hp : 0 < strictRadius r q := zero_lt_one.trans (strictRadius_gt_one hr hrq)
      simpa using hp))]
  exact (strictV_holSymm hr hrq hq1 hf).1

theorem strictW_factor {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    z * strictW f r q z = strictV f r q z - strictV f r q 0 := by
  let g : ℂ → ℂ := fun w => strictV f r q w - strictV f r q 0
  have hvSym := (strictV_holSymm hr hrq hq1 hf).2
  have hzeroSym : star (strictV f r q 0) = strictV f r q 0 := by
    have hs := hvSym 0 (by
      have hp : 0 < strictRadius r q := zero_lt_one.trans (strictRadius_gt_one hr hrq)
      simpa using hp)
    simpa using hs.symm
  have hgSym : ∀ w ∈ Metric.ball (0 : ℂ) (strictRadius r q),
      g (star w) = star (g w) := by
    intro w hw
    change strictV f r q (star w) - strictV f r q 0 =
      star (strictV f r q w - strictV f r q 0)
    rw [hvSym w hw, star_sub, hzeroSym]
  have hraw : ∀ w ∈ Metric.ball (0 : ℂ) (strictRadius r q),
      w * dslope (strictV f r q) 0 w = g w := by
    intro w _
    simpa [g, smul_eq_mul] using sub_smul_dslope (strictV f r q) 0 w
  exact symmetrize_linear_factor hgSym hraw hz

theorem strictV_decompose {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    strictV f r q z = (1 / q : ℝ) + z * strictW f r q z := by
  rw [strictW_factor hr hrq hq1 hf hz, strictV_zero_value hr hrq hq1 hf]
  ring

theorem strictW_zero_eq_derivV {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f) :
    strictW f r q 0 = deriv (strictV f r q) 0 := by
  have h0ball : (0 : ℂ) ∈ Metric.ball 0 (strictRadius r q) := by
    have hp : 0 < strictRadius r q := zero_lt_one.trans (strictRadius_gt_one hr hrq)
    simpa using hp
  have hWAt := ((strictW_holSymm hr hrq hq1 hf).1 0 h0ball).differentiableAt
    (Metric.isOpen_ball.mem_nhds h0ball)
  have hevent : (fun z => z * strictW f r q z) =ᶠ[nhds (0 : ℂ)]
      (fun z => strictV f r q z - strictV f r q 0) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0ball] with z hz
    exact strictW_factor hr hrq hq1 hf hz
  have hd := (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul hWAt.hasDerivAt
  have hleft : deriv (fun z => z * strictW f r q z) 0 = strictW f r q 0 := by
    change deriv ((id : ℂ → ℂ) * strictW f r q) 0 = _
    simpa using hd.deriv
  have hdeq := hevent.deriv_eq
  rw [hleft, deriv_sub_const] at hdeq
  exact hdeq

theorem strictU_decompose {f : ℂ → ℂ} {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq1 : q < 1) (hf : DiscFunction r f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (strictRadius r q)) :
    strictU f r q z = -(z / q) - (z ^ 2 + (q : ℂ)) * strictW f r q z := by
  by_cases hz0 : z = 0
  · subst z
    have h0ball := hz
    have hUAt := ((strictU_holSymm hr hrq hf).1 0 h0ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds h0ball)
    have hVAt := ((strictV_holSymm hr hrq hq1 hf).1 0 h0ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds h0ball)
    have hevent : (fun z => z * strictU f r q z +
        (z ^ 2 + (q : ℂ)) * strictV f r q z) =ᶠ[nhds (0 : ℂ)]
        (fun _ => (1 : ℂ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds h0ball] with z hz
      exact strict_bezout hr hrq hq1 hf hz
    have hdu := (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul hUAt.hasDerivAt
    have hpoly : DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + (q : ℂ)) 0 :=
      (differentiableAt_id.pow 2).add_const _
    have hdv := hpoly.hasDerivAt.mul hVAt.hasDerivAt
    have hleft : deriv (fun z => z * strictU f r q z +
        (z ^ 2 + (q : ℂ)) * strictV f r q z) 0 =
        strictU f r q 0 + (q : ℂ) * deriv (strictV f r q) 0 := by
      have hsum := hdu.add hdv
      change deriv ((id * strictU f r q) +
        ((fun z : ℂ => z ^ 2 + (q : ℂ)) * strictV f r q)) 0 = _
      simpa using hsum.deriv
    have hdeq := hevent.deriv_eq
    rw [hleft, deriv_const] at hdeq
    rw [strictW_zero_eq_derivV hr hrq hq1 hf]
    norm_num
    linear_combination hdeq
  · have hb := strict_bezout hr hrq hq1 hf hz
    rw [strictV_decompose hr hrq hq1 hf hz] at hb
    have hqcast : (((1 / q : ℝ) : ℂ)) = (1 : ℂ) / (q : ℂ) := by norm_cast
    rw [hqcast] at hb
    have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hr.trans hrq)
    have hzmul : z * (strictU f r q z -
        (-(z / q) - (z ^ 2 + (q : ℂ)) * strictW f r q z)) = 0 := by
      field_simp [hqne] at hb ⊢
      linear_combination hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzmul).resolve_left hz0)

end

end BelgianChocolate
