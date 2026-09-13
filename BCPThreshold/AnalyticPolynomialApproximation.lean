/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.PositiveCertificate
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Local polynomial approximation used by strict positive certificates

Only one already-given holomorphic witness is approximated here.  No uniform all-orders bound is
asserted or used.
-/

namespace BelgianChocolate

open Set Metric Polynomial Filter
open scoped Topology NNReal ENNReal

noncomputable section

/-- The polynomial whose evaluation is a finite partial sum of a one-dimensional formal
multilinear series. -/
def partialSumPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n, Polynomial.monomial k (p.coeff k)

theorem eval_partialSumPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (z : ℂ) :
    (partialSumPolynomial p n).eval z = p.partialSum n z := by
  rw [partialSumPolynomial, Polynomial.eval_finsetSum]
  simp [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Coefficientwise real part of a complex polynomial. -/
def realPartPolynomial (p : Polynomial ℂ) : Polynomial ℝ :=
  p.sum fun n c => Polynomial.monomial n c.re

theorem evalC_realPartPolynomial (p : Polynomial ℂ) (z : ℂ) :
    evalC (realPartPolynomial p) z =
      (p.eval z + star (p.eval (star z))) / 2 := by
  classical
  rw [evalC, realPartPolynomial, Polynomial.sum_def, Polynomial.map_sum,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.map_monomial, map_natCast, Polynomial.eval_monomial]
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def,
    Polynomial.sum_def]
  rw [star_sum]
  simp_rw [star_mul, star_pow, star_star]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  change ((p.coeff n).re : ℂ) * z ^ n = _
  rw [Complex.re_eq_add_conj]
  change ((p.coeff n + (starRingEnd ℂ) (p.coeff n)) / 2) * z ^ n =
    (p.coeff n * z ^ n + z ^ n * (starRingEnd ℂ) (p.coeff n)) / 2
  ring

/-- A holomorphic conjugation-symmetric function on a disk is uniformly approximable on the
closed unit disk by a real-coefficient polynomial. -/
theorem exists_real_polynomial_uniform_approx
    {f : ℂ → ℂ} {R ε : ℝ} (hR : 1 < R) (hε : 0 < ε)
    (hhol : HolSymmOn R f) :
    ∃ p : Polynomial ℝ, ∀ z ∈ closedUnitDisc, ‖evalC p z - f z‖ < ε := by
  let ρr : ℝ := (R + 1) / 2
  have hρ1 : 1 < ρr := by dsimp [ρr]; linarith
  have hρR : ρr < R := by dsimp [ρr]; linarith
  let ρ : ℝ≥0 := ⟨ρr, by linarith⟩
  have hρcoe : (ρ : ℝ) = ρr := rfl
  have hdclosed : DifferentiableOn ℂ f (Metric.closedBall 0 (ρ : ℝ)) :=
    hhol.1.mono (Metric.closedBall_subset_ball (by simpa [hρcoe] using hρR))
  let ps := cauchyPowerSeries f 0 (ρ : ℝ)
  have hps : HasFPowerSeriesOnBall f ps 0 (ρ : ℝ≥0∞) := by
    exact hdclosed.hasFPowerSeriesOnBall (by exact_mod_cast hρ1.trans' zero_lt_one)
  let σr : ℝ := (ρr + 1) / 2
  have hσ1 : 1 < σr := by dsimp [σr]; linarith
  have hσρ : σr < ρr := by dsimp [σr]; linarith
  let σ : ℝ≥0 := ⟨σr, by linarith⟩
  have hσcoe : (σ : ℝ) = σr := rfl
  have hσρe : (σ : ℝ≥0∞) < (ρ : ℝ≥0∞) := by
    exact_mod_cast hσρ
  have ht := hps.tendstoUniformlyOn hσρe
  have hev := (Metric.tendstoUniformlyOn_iff.mp ht) ε hε
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
  let P := partialSumPolynomial ps n
  refine ⟨realPartPolynomial P, ?_⟩
  intro z hz
  have hzσ : z ∈ Metric.ball (0 : ℂ) (σ : ℝ) :=
    Metric.closedBall_subset_ball (by simpa [hσcoe] using hσ1) hz
  have hzstar : star z ∈ closedUnitDisc := by
    simpa [closedUnitDisc, dist_eq_norm] using hz
  have hzstarσ : star z ∈ Metric.ball (0 : ℂ) (σ : ℝ) :=
    Metric.closedBall_subset_ball (by simpa [hσcoe] using hσ1) hzstar
  have hPz := hn n le_rfl z hzσ
  have hPstar := hn n le_rfl (star z) hzstarσ
  rw [dist_eq_norm, zero_add, ← eval_partialSumPolynomial] at hPz hPstar
  rw [evalC_realPartPolynomial]
  have hsym' : star (f (star z)) = f z := by
    have hs := congrArg star (hhol.2 z (Metric.closedBall_subset_ball hR hz))
    simpa using hs
  have hPz' : ‖P.eval z - f z‖ < ε := by
    rw [norm_sub_rev]
    exact hPz
  have hPstar' : ‖star (P.eval (star z) - f (star z))‖ < ε := by
    rw [norm_star, norm_sub_rev]
    exact hPstar
  have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  calc
    ‖(P.eval z + star (P.eval (star z))) / 2 - f z‖ =
        ‖((P.eval z - f z) + star (P.eval (star z) - f (star z))) / 2‖ := by
          rw [star_sub, hsym']
          apply congrArg norm
          ring
    _ ≤ (‖P.eval z - f z‖ + ‖star (P.eval (star z) - f (star z))‖) / ‖(2 : ℂ)‖ := by
          rw [norm_div]
          exact div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ < (ε + ε) / ‖(2 : ℂ)‖ := by
          exact div_lt_div_of_pos_right
            (add_lt_add hPz' hPstar') (norm_pos_iff.mpr (by norm_num))
    _ = ε := by rw [hnormTwo]; ring

/-- A finite real polynomial can be perturbed coefficientwise to rational coefficients while
remaining uniformly close on the closed unit disk. -/
theorem exists_rat_polynomial_uniform_approx_real
    (p : Polynomial ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : Polynomial ℚ, ∀ z ∈ closedUnitDisc, ‖evalRatC r z - evalC p z‖ < ε := by
  classical
  let n := p.natDegree + 1
  have hn0 : 0 < n := by dsimp [n]; omega
  let η : ℝ := ε / (2 * n)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hchoice : ∀ i : Fin n, ∃ a : ℚ, |p.coeff i - (a : ℝ)| < η := by
    intro i
    exact exists_rat_near (p.coeff i) hη
  choose a ha using hchoice
  let r : Polynomial ℚ := Polynomial.ofFn n a
  refine ⟨r, ?_⟩
  intro z hz
  have hznorm : ‖z‖ ≤ 1 := by simpa [closedUnitDisc, dist_eq_norm] using hz
  have hpdeg : p.natDegree < n := by dsimp [n]; omega
  have hrdeg : r.natDegree < n := by
    exact Polynomial.ofFn_natDegree_lt (by omega) a
  have hmaprdeg : (r.map (algebraMap ℚ ℂ)).natDegree < n :=
    Polynomial.natDegree_map_le.trans_lt hrdeg
  have hmappdeg : (p.map (algebraMap ℝ ℂ)).natDegree < n :=
    Polynomial.natDegree_map_le.trans_lt hpdeg
  rw [evalRatC, evalC, Polynomial.eval_eq_sum_range' hmaprdeg,
    Polynomial.eval_eq_sum_range' hmappdeg, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range n,
        ((r.map (algebraMap ℚ ℂ)).coeff k * z ^ k -
          (p.map (algebraMap ℝ ℂ)).coeff k * z ^ k)‖ ≤
        ∑ k ∈ Finset.range n,
          ‖(r.map (algebraMap ℚ ℂ)).coeff k * z ^ k -
            (p.map (algebraMap ℝ ℂ)).coeff k * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, η := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      rw [Polynomial.coeff_map, Polynomial.coeff_map,
        Polynomial.ofFn_coeff_eq_val_of_lt a hkn]
      have hcoeff : ‖((a ⟨k, hkn⟩ : ℚ) : ℂ) - (p.coeff k : ℂ)‖ ≤ η := by
        rw [show ((a ⟨k, hkn⟩ : ℚ) : ℂ) = (((a ⟨k, hkn⟩ : ℚ) : ℝ) : ℂ) by norm_cast,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        exact (ha ⟨k, hkn⟩).le
      rw [← sub_mul, norm_mul]
      have hpow : ‖z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg z) hznorm
      rw [norm_pow]
      simpa using mul_le_mul hcoeff hpow (pow_nonneg (norm_nonneg z) k) hη.le
    _ = n * η := by simp
    _ < ε := by
      dsimp [η]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      field_simp
      linarith

/-- Combined local Taylor approximation and finite rationalization. -/
theorem exists_rat_polynomial_uniform_approx
    {f : ℂ → ℂ} {R ε : ℝ} (hR : 1 < R) (hε : 0 < ε)
    (hhol : HolSymmOn R f) :
    ∃ p : Polynomial ℚ, ∀ z ∈ closedUnitDisc, ‖evalRatC p z - f z‖ < ε := by
  obtain ⟨p, hp⟩ := exists_real_polynomial_uniform_approx hR (half_pos hε) hhol
  obtain ⟨r, hr⟩ := exists_rat_polynomial_uniform_approx_real p (half_pos hε)
  refine ⟨r, fun z hz => ?_⟩
  calc
    ‖evalRatC r z - f z‖ ≤
        ‖evalRatC r z - evalC p z‖ + ‖evalC p z - f z‖ := by
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hr z hz) (hp z hz)
    _ = ε := by ring

end

end BelgianChocolate
