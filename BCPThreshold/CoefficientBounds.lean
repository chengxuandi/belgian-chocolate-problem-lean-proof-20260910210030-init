import BCPThreshold.FourFactorsSchottky
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecificLimits.Normed

open Metric Set Complex Filter

namespace BelgianChocolate.Schottky

noncomputable section

open Route1.PaperBounds

def factorFunction {q : ℝ} (F : FourFactors q) : Fin 4 → ℂ → ℂ
  | 0 => F.u
  | 1 => F.v
  | 2 => F.uInv
  | 3 => F.vInv

theorem factorFunction_differentiableOn {q : ℝ} (F : FourFactors q) (i : Fin 4) :
    DifferentiableOn ℂ (factorFunction F i) unitDisc := by
  fin_cases i
  · exact F.holSymm_u.1
  · exact F.holSymm_v.1
  · exact F.holSymm_uInv.1
  · exact F.holSymm_vInv.1

theorem factorFunction_schottky_bound
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) (i : Fin 4)
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ (r : ℝ)) :
    ‖factorFunction F i z‖ ≤ (factorBound r : ℝ) := by
  have h := fourFactors_schottky_bound hq hqb F hr0 hr1 hz
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

def taylorCoefficient {q : ℝ} (F : FourFactors q) (i : Fin 4) (j : ℕ) : ℂ :=
  (j.factorial : ℂ)⁻¹ * iteratedDeriv j (factorFunction F i) 0

theorem coeffRadius_lt_one (m : ℕ) : coeffRadius m < 1 := by
  rw [coeffRadius]
  have hp : (0 : ℚ) < (2 : ℚ) ^ m := pow_pos (by norm_num) _
  have hi : 0 < 1 / (2 : ℚ) ^ m := one_div_pos.mpr hp
  linarith

theorem local_taylorCoefficient_bound
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) (i : Fin 4) {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    ‖taylorCoefficient F i j‖ ≤ (localCoeffBound m j : ℝ) := by
  let R : ℝ := (coeffRadius m : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact Rat.cast_pos.mpr (coeffRadius_pos hm)
  have hR1 : R < 1 := by
    dsimp [R]
    have hcast : ((coeffRadius m : ℚ) : ℝ) < ((1 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr (coeffRadius_lt_one m)
    norm_num at hcast ⊢
    exact hcast
  have hclosed : closedBall (0 : ℂ) R ⊆ unitDisc := by
    intro z hz
    rw [unitDisc, mem_ball, dist_zero_right]
    have hzR : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz
    exact hzR.trans_lt hR1
  have hdc : DiffContOnCl ℂ (factorFunction F i) (ball (0 : ℂ) R) :=
    (factorFunction_differentiableOn F i).diffContOnCl_ball hclosed
  have hcircle : ∀ z ∈ sphere (0 : ℂ) R,
      ‖factorFunction F i z‖ ≤ (factorBound (coeffRadius m) : ℝ) := by
    intro z hz
    apply factorFunction_schottky_bound hq hqb F i (coeffRadius_pos hm).le
      (coeffRadius_lt_one m)
    simpa [mem_sphere, dist_zero_right, R] using hz.le
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j hR0 hdc hcircle
  have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hscaled := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hfac.le)
  have hbase :
      ‖taylorCoefficient F i j‖ ≤
        (factorBound (coeffRadius m) : ℝ) / R ^ j := by
    rw [taylorCoefficient, norm_mul, norm_inv]
    norm_num at hscaled ⊢
    calc
      (j.factorial : ℝ)⁻¹ * ‖iteratedDeriv j (factorFunction F i) 0‖ ≤
          (j.factorial : ℝ)⁻¹ *
            ((j.factorial : ℝ) * (factorBound (coeffRadius m) : ℝ) / R ^ j) :=
        hscaled
      _ = (factorBound (coeffRadius m) : ℝ) / R ^ j := by
        field_simp
  have hfactor : (factorBound (coeffRadius m) : ℝ) ≤
      (max 1 (factorBound (coeffRadius m)) : ℝ) := by exact_mod_cast le_max_right 1 _
  calc
    ‖taylorCoefficient F i j‖ ≤
        (factorBound (coeffRadius m) : ℝ) / R ^ j := hbase
    _ ≤ (max 1 (factorBound (coeffRadius m)) : ℝ) / R ^ j :=
      div_le_div_of_nonneg_right hfactor (pow_nonneg hR0.le _)
    _ = (localCoeffBound m j : ℝ) := by
      simp [localCoeffBound, R]

theorem coefficientBoundAux_le_localCoeffBound
    (j k m : ℕ) (hm0 : 1 ≤ m) (hmk : m ≤ k + 1) :
    coefficientBoundAux j k ≤ localCoeffBound m j := by
  induction k generalizing m with
  | zero =>
      have : m = 1 := by omega
      subst m
      simp [coefficientBoundAux]
  | succ k ih =>
      rw [coefficientBoundAux]
      by_cases hm : m ≤ k + 1
      · exact (min_le_left _ _).trans (ih m hm0 hm)
      · have heq : m = k + 2 := by omega
        subst m
        exact min_le_right _ _

theorem coefficientBound_le_localCoeffBound
    (j m : ℕ) (hm0 : 1 ≤ m) (hmj : m ≤ j + 1) :
    coefficientBound j ≤ localCoeffBound m j :=
  coefficientBoundAux_le_localCoeffBound j j m hm0 hmj

/-- The manuscript's single coefficient box bounds every Taylor coefficient
of each of the four factors, independently of the witness and of truncation. -/
theorem coefficientBound
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) (i : Fin 4) (j : ℕ) :
    ‖taylorCoefficient F i j‖ ≤
      (Route1.PaperBounds.coefficientBound j : ℝ) := by
  have haux : ∀ k : ℕ, ‖taylorCoefficient F i j‖ ≤
      (coefficientBoundAux j k : ℝ) := by
    intro k
    induction k with
    | zero =>
        simpa [coefficientBoundAux] using
          local_taylorCoefficient_bound hq hqb F i (m := 1) (by norm_num) j
    | succ k ih =>
        rw [coefficientBoundAux]
        simpa only [Rat.cast_min] using le_min ih
          (local_taylorCoefficient_bound hq hqb F i (m := k + 2) (by omega) j)
  exact haux j

end

end BelgianChocolate.Schottky
