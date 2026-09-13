import BCPThreshold.CoefficientBounds

open Filter Complex

namespace BelgianChocolate.Schottky

noncomputable section

open Route1.PaperBounds

theorem cast_coeffRadius (m : ℕ) :
    (coeffRadius m : ℝ) = 1 - (1 / 2 : ℝ) ^ m := by
  rw [coeffRadius]
  norm_num [div_pow]

theorem exists_lt_coeffRadius {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ ρ < (coeffRadius m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (K := ℝ)
    (x := 1 - ρ) (y := (1 / 2 : ℝ)) (sub_pos.mpr hρ1) (by norm_num)
  have hm0 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    subst m
    norm_num at hm
    linarith
  refine ⟨m, hm0, ?_⟩
  rw [cast_coeffRadius]
  linarith

/-- Module 6 convergence handoff: every infinite coefficient sequence in the
paper boxes defines an absolutely convergent power series at every point of
the open unit disc. No inverse-limit realization is asserted here. -/
theorem coefficientBound_summable
    {a : ℕ → ℂ}
    (ha : ∀ j : ℕ, ‖a j‖ ≤ (Route1.PaperBounds.coefficientBound j : ℝ))
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun j : ℕ => a j * z ^ j) := by
  let ρ : ℝ := ‖z‖
  obtain ⟨m, hm0, hρm⟩ := exists_lt_coeffRadius (norm_nonneg z) hz
  let R : ℝ := (coeffRadius m : ℝ)
  let A : ℝ := (max 1 (factorBound (coeffRadius m)) : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact Rat.cast_pos.mpr (coeffRadius_pos hm0)
  have hratio0 : 0 ≤ ρ / R := div_nonneg (norm_nonneg z) hR0.le
  have hratio1 : ρ / R < 1 := (div_lt_one hR0).2 (by simpa [ρ, R] using hρm)
  have hgeom : Summable (fun j : ℕ => A * (ρ / R) ^ j) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left A
  apply Summable.of_norm_bounded_eventually_nat hgeom
  filter_upwards [eventually_ge_atTop (m - 1)] with j hj
  have hmj : m ≤ j + 1 := by omega
  have hbox : (Route1.PaperBounds.coefficientBound j : ℝ) ≤
      (localCoeffBound m j : ℝ) := by
    exact_mod_cast coefficientBound_le_localCoeffBound j m hm0 hmj
  have hpow0 : 0 ≤ ρ ^ j := pow_nonneg (norm_nonneg z) _
  calc
    ‖a j * z ^ j‖ = ‖a j‖ * ρ ^ j := by simp [norm_mul, norm_pow, ρ]
    _ ≤ (Route1.PaperBounds.coefficientBound j : ℝ) * ρ ^ j :=
      mul_le_mul_of_nonneg_right (ha j) hpow0
    _ ≤ (localCoeffBound m j : ℝ) * ρ ^ j :=
      mul_le_mul_of_nonneg_right hbox hpow0
    _ = A * (ρ / R) ^ j := by
      simp [localCoeffBound, A, R, div_pow]
      ring

/-- Absolute-convergence form of `coefficientBound_summable`.  Module 6 uses
this statement for Cauchy products; the majorant is the same geometric series
as in the preceding theorem. -/
theorem coefficientBound_norm_summable
    {a : ℕ → ℂ}
    (ha : ∀ j : ℕ, ‖a j‖ ≤ (Route1.PaperBounds.coefficientBound j : ℝ))
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun j : ℕ => ‖a j * z ^ j‖) := by
  let ρ : ℝ := ‖z‖
  obtain ⟨m, hm0, hρm⟩ := exists_lt_coeffRadius (norm_nonneg z) hz
  let R : ℝ := (coeffRadius m : ℝ)
  let A : ℝ := (max 1 (factorBound (coeffRadius m)) : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact Rat.cast_pos.mpr (coeffRadius_pos hm0)
  have hratio0 : 0 ≤ ρ / R := div_nonneg (norm_nonneg z) hR0.le
  have hratio1 : ρ / R < 1 := (div_lt_one hR0).2 (by simpa [ρ, R] using hρm)
  have hgeom : Summable (fun j : ℕ => A * (ρ / R) ^ j) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left A
  apply Summable.of_norm_bounded_eventually_nat hgeom
  filter_upwards [eventually_ge_atTop (m - 1)] with j hj
  have hmj : m ≤ j + 1 := by omega
  have hbox : (Route1.PaperBounds.coefficientBound j : ℝ) ≤
      (localCoeffBound m j : ℝ) := by
    exact_mod_cast coefficientBound_le_localCoeffBound j m hm0 hmj
  have hpow0 : 0 ≤ ρ ^ j := pow_nonneg (norm_nonneg z) _
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a j * z ^ j))]
  calc
    ‖a j * z ^ j‖ = ‖a j‖ * ρ ^ j := by simp [norm_mul, norm_pow, ρ]
    _ ≤ (Route1.PaperBounds.coefficientBound j : ℝ) * ρ ^ j :=
      mul_le_mul_of_nonneg_right (ha j) hpow0
    _ ≤ (localCoeffBound m j : ℝ) * ρ ^ j :=
      mul_le_mul_of_nonneg_right hbox hpow0
    _ = A * (ρ / R) ^ j := by
      simp [localCoeffBound, A, R, div_pow]
      ring

end

end BelgianChocolate.Schottky
