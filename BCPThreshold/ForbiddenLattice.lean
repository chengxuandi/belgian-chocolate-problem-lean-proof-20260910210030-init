import BCPThreshold.HolomorphicLift
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semifield

open Metric Set

namespace BelgianChocolate
namespace ForbiddenLattice

noncomputable section

def step : ℝ := Real.arcosh 2 / Real.pi

def chebInt (k : ℕ) : ℤ :=
  (Polynomial.Chebyshev.T ℤ (k : ℤ)).eval 2

def lattice : Set ℂ :=
  {z | ∃ (m : ℤ) (k : ℕ),
    z = (m : ℂ) + Complex.I * ((k : ℝ) * step) ∨
    z = (m : ℂ) - Complex.I * ((k : ℝ) * step)}

theorem step_pos : 0 < step := by
  exact div_pos (Real.arcosh_pos (by norm_num)) Real.pi_pos

theorem arcosh_two_lt_two : Real.arcosh 2 < 2 := by
  rw [Real.arcosh]
  have hsqrt : Real.sqrt 3 < 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg 3]
  have harg : (0 : ℝ) < 2 + Real.sqrt 3 := by positivity
  have hlt : 2 + Real.sqrt 3 < 4 := by linarith
  calc
    Real.log (2 + Real.sqrt (2 ^ 2 - 1)) = Real.log (2 + Real.sqrt 3) := by norm_num
    _ < Real.log 4 := Real.log_lt_log harg hlt
    _ = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul] <;> norm_num
      ring
    _ < 2 := by nlinarith [Real.log_two_lt_d9]

theorem step_lt_two_thirds : step < (2 / 3 : ℝ) := by
  rw [step, div_lt_iff₀ Real.pi_pos]
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ha := arcosh_two_lt_two
  nlinarith

theorem chebInt_cast (k : ℕ) :
    (chebInt k : ℝ) = Real.cosh ((k : ℝ) * Real.arcosh 2) := by
  have hmap := Polynomial.Chebyshev.algebraMap_eval_T (R := ℤ) (R' := ℝ)
    (2 : ℤ) (k : ℤ)
  have hcosh := Polynomial.Chebyshev.T_real_cosh (Real.arcosh 2) (k : ℤ)
  simp only [Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 2)] at hcosh
  calc
    (((Polynomial.Chebyshev.T ℤ (k : ℤ)).eval 2 : ℤ) : ℝ) =
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval 2 := by simpa using hmap
    _ = Real.cosh (((k : ℤ) : ℝ) * Real.arcosh 2) := hcosh
    _ = Real.cosh ((k : ℝ) * Real.arcosh 2) := by norm_num

theorem cos_pi_plus_integer (m : ℤ) (k : ℕ) :
    Complex.cos (Real.pi *
      ((m : ℂ) + Complex.I * ((k : ℝ) * step))) =
      (((m.negOnePow * chebInt k : ℤ) : ℂ)) := by
  have harg : (Real.pi : ℂ) *
      ((m : ℂ) + Complex.I * ((k : ℝ) * step)) =
      (m : ℂ) * Real.pi + ((k : ℝ) * Real.arcosh 2 : ℂ) * Complex.I := by
    have hcstep : (Real.pi : ℂ) * (step : ℂ) = (Real.arcosh 2 : ℂ) := by
      norm_cast
      rw [step]
      field_simp [Real.pi_ne_zero]
    calc
      (Real.pi : ℂ) * ((m : ℂ) + Complex.I * ((k : ℝ) * step)) =
          (m : ℂ) * Real.pi + Complex.I * (k : ℂ) *
            ((Real.pi : ℂ) * step) := by
        push_cast
        ring
      _ = (m : ℂ) * Real.pi + ((k : ℝ) * Real.arcosh 2 : ℂ) * Complex.I := by
        rw [hcstep]
        push_cast
        ring
  rw [harg, Complex.cos_add_mul_I]
  have hcosm : Complex.cos ((m : ℂ) * Real.pi) = (m.negOnePow : ℂ) := by
    simpa using (Complex.cos_antiperiodic.add_int_mul_eq (x := 0) m)
  have hsinm : Complex.sin ((m : ℂ) * Real.pi) = 0 := by
    exact_mod_cast Real.sin_int_mul_pi m
  have hcoshk : Complex.cosh (((k : ℝ) * Real.arcosh 2 : ℂ)) =
      (chebInt k : ℂ) := by
    have hmap := Polynomial.Chebyshev.algebraMap_eval_T (R := ℤ) (R' := ℂ)
      (2 : ℤ) (k : ℤ)
    have hcosh := Polynomial.Chebyshev.T_complex_cosh (Real.arcosh 2 : ℂ) (k : ℤ)
    have hbase : Complex.cosh (Real.arcosh 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_cosh]
      norm_cast
      exact Real.cosh_arcosh (by norm_num)
    rw [hbase] at hcosh
    calc
      Complex.cosh (((k : ℝ) * Real.arcosh 2 : ℂ)) =
          (Polynomial.Chebyshev.T ℂ (k : ℤ)).eval 2 := hcosh.symm
      _ = (chebInt k : ℂ) := by simpa [chebInt] using hmap.symm
  rw [hcosm, hsinm]
  rw [hcoshk]
  simp

theorem cos_pi_minus_integer (m : ℤ) (k : ℕ) :
    Complex.cos (Real.pi *
      ((m : ℂ) - Complex.I * ((k : ℝ) * step))) =
      (((m.negOnePow * chebInt k : ℤ) : ℂ)) := by
  have hpoint : (m : ℂ) - Complex.I * ((k : ℝ) * step) =
      - (((-m : ℤ) : ℂ) + Complex.I * ((k : ℝ) * step)) := by
    push_cast
    ring
  rw [hpoint, mul_neg, Complex.cos_neg, cos_pi_plus_integer (-m) k]
  simp

theorem lattice_inner_integer {z : ℂ} (hz : z ∈ lattice) :
    ∃ j : ℤ, Complex.cos (Real.pi * z) = (j : ℂ) := by
  rcases hz with ⟨m, k, rfl | rfl⟩
  · exact ⟨m.negOnePow * chebInt k, cos_pi_plus_integer m k⟩
  · exact ⟨m.negOnePow * chebInt k, cos_pi_minus_integer m k⟩

theorem lattice_forbidden {z : ℂ} (hz : z ∈ lattice) :
    Complex.cos (Real.pi * Complex.cos (Real.pi * z)) = 1 ∨
      Complex.cos (Real.pi * Complex.cos (Real.pi * z)) = -1 := by
  obtain ⟨j, hj⟩ := lattice_inner_integer hz
  rw [hj]
  have hc : Complex.cos ((j : ℂ) * Real.pi) = (j.negOnePow : ℂ) := by
    simpa using (Complex.cos_antiperiodic.add_int_mul_eq (x := 0) j)
  rw [show (Real.pi : ℂ) * (j : ℂ) = (j : ℂ) * Real.pi by ring, hc]
  rcases Int.even_or_odd j with he | ho
  · left
    rw [(Int.negOnePow_eq_one_iff j).2 he]
    norm_num
  · right
    rw [(Int.negOnePow_eq_neg_one_iff j).2 ho]
    norm_num

/-- Every open unit disc meets the forbidden lattice. -/
theorem exists_mem_lattice_ball (z : ℂ) :
    ∃ w ∈ lattice, w ∈ Metric.ball z 1 := by
  let m : ℤ := toIocDiv (by norm_num : (0 : ℝ) < 1) (-1 / 2) z.re
  have hmI : z.re - m • (1 : ℝ) ∈ Set.Ioc (-1 / 2) (-1 / 2 + 1) := by
    simpa [m] using
      (sub_toIocDiv_zsmul_mem_Ioc (by norm_num : (0 : ℝ) < 1) (-1 / 2) z.re)
  norm_num at hmI
  have hm : |(m : ℝ) - z.re| ≤ (1 / 2 : ℝ) := by
    rw [abs_sub_comm, abs_le]
    constructor
    · linarith [hmI.1]
    · linarith [hmI.2]
  let y : ℝ := |z.im|
  let k : ℕ := ⌊y / step⌋₊
  have hy : 0 ≤ y := abs_nonneg _
  have hdiv : 0 ≤ y / step := div_nonneg hy step_pos.le
  have hk_le : (k : ℝ) ≤ y / step := by
    simpa [k] using Nat.floor_le hdiv
  have hy_lt : y / step < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one (y / step)
  have hkstep : (k : ℝ) * step ≤ y := by
    exact (le_div_iff₀ step_pos).mp hk_le
  have hy_step : y < ((k : ℝ) + 1) * step :=
    (div_lt_iff₀ step_pos).mp hy_lt
  have hgap_nonneg : 0 ≤ y - (k : ℝ) * step := sub_nonneg.mpr hkstep
  have hgap : y - (k : ℝ) * step < (2 / 3 : ℝ) := by
    have hs := step_lt_two_thirds
    nlinarith
  have hm_sq : ((m : ℝ) - z.re) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg ((m : ℝ) - z.re))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hm
    simpa [sq_abs] using hs
  by_cases hzIm : 0 ≤ z.im
  · let w : ℂ := (m : ℂ) + Complex.I * ((k : ℝ) * step)
    refine ⟨w, ⟨m, k, Or.inl rfl⟩, ?_⟩
    rw [mem_ball, dist_eq_norm]
    apply (sq_lt_sq₀ (norm_nonneg (w - z)) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [one_pow, Complex.sq_norm, Complex.normSq_apply]
    have hy_eq : z.im = y := by simp [y, abs_of_nonneg hzIm]
    have hre : (w - z).re = (m : ℝ) - z.re := by simp [w]
    have him : (w - z).im = (k : ℝ) * step - y := by
      simp [w, hy_eq]
    rw [hre, him]
    have him_abs : |(k : ℝ) * step - y| < (2 / 3 : ℝ) := by
      rw [abs_sub_comm, abs_of_nonneg hgap_nonneg]
      exact hgap
    have him_sq : ((k : ℝ) * step - y) ^ 2 < (2 / 3 : ℝ) ^ 2 := by
      have hs := (sq_lt_sq₀ (abs_nonneg ((k : ℝ) * step - y))
        (by norm_num : (0 : ℝ) ≤ 2 / 3)).2 him_abs
      simpa [sq_abs] using hs
    nlinarith
  · let w : ℂ := (m : ℂ) - Complex.I * ((k : ℝ) * step)
    refine ⟨w, ⟨m, k, Or.inr rfl⟩, ?_⟩
    rw [mem_ball, dist_eq_norm]
    apply (sq_lt_sq₀ (norm_nonneg (w - z)) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [one_pow, Complex.sq_norm, Complex.normSq_apply]
    have hzneg : z.im < 0 := lt_of_not_ge hzIm
    have hy_eq : -z.im = y := by simp [y, abs_of_neg hzneg]
    have hre : (w - z).re = (m : ℝ) - z.re := by simp [w]
    have him : (w - z).im = y - (k : ℝ) * step := by
      simp [w]
      linarith
    rw [hre, him]
    have him_abs : |y - (k : ℝ) * step| < (2 / 3 : ℝ) := by
      rw [abs_of_nonneg hgap_nonneg]
      exact hgap
    have him_sq : (y - (k : ℝ) * step) ^ 2 < (2 / 3 : ℝ) ^ 2 := by
      have hs := (sq_lt_sq₀ (abs_nonneg (y - (k : ℝ) * step))
        (by norm_num : (0 : ℝ) ≤ 2 / 3)).2 him_abs
      simpa [sq_abs] using hs
    nlinarith

end

end ForbiddenLattice
end BelgianChocolate
