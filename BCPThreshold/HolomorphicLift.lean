import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.ToIntervalMod

open Set Filter Topology

namespace BelgianChocolate
namespace HolomorphicLift

/-! A continuous lift through the complex exponential of a holomorphic map is
holomorphic.  The proof uses the local inverse supplied by the strict inverse
function theorem, so it needs no global covering-space uniqueness theorem. -/
theorem differentiableOn_of_continuousOn_exp_comp
    {S : Set ℂ} {L g : ℂ → ℂ}
    (hL : ContinuousOn L S)
    (hg : DifferentiableOn ℂ g S)
    (hexp : EqOn (Complex.exp ∘ L) g S) :
    DifferentiableOn ℂ L S := by
  intro x hx
  let hE := Complex.hasStrictDerivAt_exp (L x)
  let r : ℂ → ℂ :=
    hE.localInverse Complex.exp (Complex.exp (L x)) (L x) (Complex.exp_ne_zero (L x))
  have hr : DifferentiableAt ℂ r (Complex.exp (L x)) := by
    exact (hE.to_localInverse (Complex.exp_ne_zero (L x))).hasDerivAt.differentiableAt
  have hleft : ∀ᶠ y in nhds (L x), r (Complex.exp y) = y := by
    exact hE.eventually_left_inverse (Complex.exp_ne_zero (L x))
  have hleftL : ∀ᶠ y in nhdsWithin x S, r (Complex.exp (L y)) = L y :=
    (hL x hx).eventually hleft
  have heq : L =ᶠ[nhdsWithin x S] r ∘ g := by
    filter_upwards [hleftL, self_mem_nhdsWithin] with y hy hyS
    change L y = r (g y)
    rw [← hexp hyS]
    exact hy.symm
  have hr' : DifferentiableAt ℂ r (g x) := by
    rw [← hexp hx]
    exact hr
  have hcomp : DifferentiableWithinAt ℂ (r ∘ g) S x :=
    hr'.comp_differentiableWithinAt x (hg x hx)
  exact hcomp.congr_of_eventuallyEq heq (by
    change L x = r (g x)
    rw [← hexp hx]
    exact (mem_of_mem_nhds hleft).symm)

theorem exists_differentiableOn_log
    {S : Set ℂ} (hSopen : IsOpen S) (hSsc : IsSimplyConnected S)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g S)
    (hg0 : ∀ z ∈ S, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L S ∧ EqOn (Complex.exp ∘ L) g S := by
  have hzero : 0 ∉ g '' S := by
    rintro ⟨z, hz, hgz⟩
    exact hg0 z hz hgz
  obtain ⟨L, hLc, hLexp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hSsc hSopen hg.continuousOn hzero
  exact ⟨L, differentiableOn_of_continuousOn_exp_comp hLc hg hLexp, hLexp⟩

/-- A holomorphic map omitting `±1` has a global holomorphic cosine lift on a
simply connected open set.  This is the unnormalised form of the lift used by
the coarse Schottky argument. -/
theorem cosine_lift_exists
    {S : Set ℂ} (hSopen : IsOpen S) (hSsc : IsSimplyConnected S)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S)
    (homit : ∀ z ∈ S, f z ≠ 1 ∧ f z ≠ -1) :
    ∃ v : ℂ → ℂ, DifferentiableOn ℂ v S ∧
      ∀ z ∈ S, f z = Complex.cos (v z) := by
  let q : ℂ → ℂ := fun z ↦ 1 - f z ^ 2
  have hq : DifferentiableOn ℂ q S := by
    have hc : DifferentiableOn ℂ (fun _ : ℂ ↦ (1 : ℂ)) S := differentiableOn_const 1
    exact hc.sub (hf.pow 2)
  have hq0 : ∀ z ∈ S, q z ≠ 0 := by
    intro z hz
    change 1 - f z ^ 2 ≠ 0
    rw [sub_ne_zero]
    intro hone
    have hsq : f z ^ 2 = 1 := hone.symm
    exact (sq_ne_one_iff.mpr (homit z hz)) hsq
  obtain ⟨A, hA, hAexp⟩ := exists_differentiableOn_log hSopen hSsc hq hq0
  let s : ℂ → ℂ := fun z ↦ Complex.exp (A z / 2)
  have hs : DifferentiableOn ℂ s S := by
    exact (hA.div_const 2).cexp
  have hs_sq : ∀ z ∈ S, s z ^ 2 = q z := by
    intro z hz
    change Complex.exp (A z / 2) ^ 2 = q z
    rw [← Complex.exp_nat_mul]
    calc
      Complex.exp ((2 : ℂ) * (A z / 2)) = Complex.exp (A z) := by
        congr 1
        ring
      _ = q z := hAexp hz
  let w : ℂ → ℂ := fun z ↦ f z + Complex.I * s z
  have hw : DifferentiableOn ℂ w S := hf.add (hs.const_mul Complex.I)
  have hw0 : ∀ z ∈ S, w z ≠ 0 := by
    intro z hz hwz
    have hprod : w z * (f z - Complex.I * s z) = 1 := by
      change (f z + Complex.I * s z) * (f z - Complex.I * s z) = 1
      have hsq : s z ^ 2 = 1 - f z ^ 2 := hs_sq z hz
      calc
        (f z + Complex.I * s z) * (f z - Complex.I * s z) =
            f z ^ 2 + s z ^ 2 := by
          ring_nf
          rw [Complex.I_sq]
          ring
        _ = 1 := by rw [hsq]; ring
    rw [hwz, zero_mul] at hprod
    exact zero_ne_one hprod
  obtain ⟨L, hL, hLexp⟩ := exists_differentiableOn_log hSopen hSsc hw hw0
  let v : ℂ → ℂ := fun z ↦ -Complex.I * L z
  refine ⟨v, hL.const_mul (-Complex.I), ?_⟩
  intro z hz
  rw [eq_comm, Complex.cos_eq_iff_quadratic]
  have hexp_arg : Complex.exp (v z * Complex.I) = w z := by
    change Complex.exp ((-Complex.I * L z) * Complex.I) = w z
    rw [show (-Complex.I * L z) * Complex.I = L z by
      calc
        (-Complex.I * L z) * Complex.I = -(Complex.I * Complex.I) * L z := by ring
        _ = L z := by rw [Complex.I_mul_I]; ring]
    exact hLexp hz
  rw [hexp_arg]
  change (f z + Complex.I * s z) ^ 2 - 2 * f z * (f z + Complex.I * s z) + 1 = 0
  have hsq := hs_sq z hz
  simp only [q] at hsq
  rw [show (f z + Complex.I * s z) ^ 2 - 2 * f z * (f z + Complex.I * s z) + 1 =
      1 - f z ^ 2 - s z ^ 2 by
    ring_nf
    rw [Complex.I_sq]
    ring]
  rw [hsq]
  ring

theorem norm_cos_sq_eq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.cos_eq]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_mul, zero_sub, add_zero]
  ring_nf
  rw [show Real.cosh z.im ^ 2 = 1 + Real.sinh z.im ^ 2 by
    nlinarith [Real.cosh_sq_sub_sinh_sq z.im]]
  nlinarith [Real.sin_sq_add_cos_sq z.re]

theorem sinh_abs_im_le_norm_cos (z : ℂ) :
    Real.sinh |z.im| ≤ ‖Complex.cos z‖ := by
  have hsq : Real.sinh |z.im| ^ 2 ≤ ‖Complex.cos z‖ ^ 2 := by
    rw [← Real.abs_sinh, sq_abs, norm_cos_sq_eq]
    exact le_add_of_nonneg_left (sq_nonneg (Real.cos z.re))
  have hsnonneg : 0 ≤ Real.sinh |z.im| :=
    Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  nlinarith [norm_nonneg (Complex.cos z)]

theorem abs_im_le_norm_cos (z : ℂ) : |z.im| ≤ ‖Complex.cos z‖ :=
  (Real.self_le_sinh_iff.mpr (abs_nonneg z.im)).trans (sinh_abs_im_le_norm_cos z)

theorem cosine_lift_basepoint_normalize
    {S : Set ℂ} {f v : ℂ → ℂ}
    (hv : DifferentiableOn ℂ v S)
    {a : ℂ} (ha : a ∈ S)
    (hcos : ∀ z ∈ S, f z = Complex.cos (v z)) :
    ∃ u : ℂ → ℂ,
      DifferentiableOn ℂ u S ∧
      ‖u a‖ ≤ 1 + ‖f a‖ / 3 ∧
      ∀ z ∈ S, f z = Complex.cos (Real.pi * u z) := by
  let n : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) (v a).re
  let v₀ : ℂ → ℂ := fun z ↦ v z - (n : ℂ) * (2 * Real.pi)
  let u : ℂ → ℂ := fun z ↦ v₀ z / Real.pi
  have hv₀ : DifferentiableOn ℂ v₀ S := hv.sub_const _
  have hu : DifferentiableOn ℂ u S := hv₀.div_const _
  have hperiod : ∀ z ∈ S, Complex.cos (v₀ z) = Complex.cos (v z) := by
    intro z hz
    change Complex.cos (v z - (n : ℂ) * (2 * Real.pi)) = Complex.cos (v z)
    exact Complex.cos_sub_int_mul_two_pi (v z) n
  have hreIoc : (v₀ a).re ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hI : (v a).re - n • (2 * Real.pi) ∈
        Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simpa [n] using
        (sub_toIocDiv_zsmul_mem_Ioc Real.two_pi_pos (-Real.pi) (v a).re)
    have hre_eq : (v₀ a).re = (v a).re - n • (2 * Real.pi) := by
      simp [v₀, smul_eq_mul]
    rw [hre_eq]
    exact ⟨hI.1, by nlinarith [hI.2]⟩
  have hre : |(v₀ a).re| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨hreIoc.1.le, hreIoc.2⟩
  have him_eq : (v₀ a).im = (v a).im := by simp [v₀]
  have him : |(v₀ a).im| ≤ ‖f a‖ := by
    rw [him_eq]
    calc
      |(v a).im| ≤ ‖Complex.cos (v a)‖ := abs_im_le_norm_cos (v a)
      _ = ‖f a‖ := by rw [hcos a ha]
  have hv₀norm : ‖v₀ a‖ ≤ Real.pi + ‖f a‖ := by
    exact (Complex.norm_le_abs_re_add_abs_im (v₀ a)).trans (add_le_add hre him)
  refine ⟨u, hu, ?_, ?_⟩
  · change ‖v₀ a / (Real.pi : ℂ)‖ ≤ 1 + ‖f a‖ / 3
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ Real.pi_pos).2
    calc
      ‖v₀ a‖ ≤ Real.pi + ‖f a‖ := hv₀norm
      _ ≤ (1 + ‖f a‖ / 3) * Real.pi := by
        have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
        have hn : 0 ≤ ‖f a‖ := norm_nonneg _
        nlinarith
  · intro z hz
    calc
      f z = Complex.cos (v z) := hcos z hz
      _ = Complex.cos (v₀ z) := (hperiod z hz).symm
      _ = Complex.cos (Real.pi * u z) := by
        congr 1
        change v₀ z = (Real.pi : ℂ) * (v₀ z / Real.pi)
        field_simp

/-- The bounded holomorphic cosine lift used in the coarse Schottky proof. -/
theorem holomorphic_cosine_lift_bounded
    {S : Set ℂ}
    (hSopen : IsOpen S)
    (hSsc : IsSimplyConnected S)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f S)
    {a : ℂ}
    (ha : a ∈ S)
    (homit : ∀ z ∈ S, f z ≠ 1 ∧ f z ≠ -1) :
    ∃ u : ℂ → ℂ,
      DifferentiableOn ℂ u S ∧
      ‖u a‖ ≤ 1 + ‖f a‖ / 3 ∧
      ∀ z ∈ S, f z = Complex.cos (Real.pi * u z) := by
  obtain ⟨v, hv, hcos⟩ := cosine_lift_exists hSopen hSsc hf homit
  exact cosine_lift_basepoint_normalize hv ha hcos

end HolomorphicLift
end BelgianChocolate
