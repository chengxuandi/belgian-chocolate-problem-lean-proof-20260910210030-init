import BCPThreshold.AnalyticThreshold
import BCPThreshold.FinitePositiveBridge
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.DenselyOrdered

/-!
# Strict soundness of finite positive certificates

A certificate zero-free on the closed unit disc is automatically zero-free
on a slightly larger disc because a nonzero polynomial has finitely many
roots.  Rescaling that larger disc realizes a strictly smaller analytic
parameter.
-/

namespace BelgianChocolate

open Set Metric Polynomial Complex

noncomputable section

theorem ratClosedDiscZeroFree_mul {u v : Polynomial ℚ}
    (hu : RatClosedDiscZeroFree u) (hv : RatClosedDiscZeroFree v) :
    RatClosedDiscZeroFree (u * v) := by
  intro z hz
  rw [evalRatC_mul]
  exact mul_ne_zero (hu z hz) (hv z hz)

theorem exists_gt_one_zeroFree {p : Polynomial ℚ}
    (hp : RatClosedDiscZeroFree p) :
    ∃ R : ℝ, 1 < R ∧ ∀ z : ℂ, ‖z‖ ≤ R → evalRatC p z ≠ 0 := by
  let pC : Polynomial ℂ := p.map (algebraMap ℚ ℂ)
  have hpCne : pC ≠ 0 := by
    intro hzero
    have heval : evalRatC p 0 = 0 := by simp [evalRatC, pC, hzero]
    exact hp 0 (by simp [closedUnitDisc]) heval
  let Z : Set ℂ := {z | evalRatC p z = 0}
  have hZfinite : Z.Finite := by
    have hf := Polynomial.finite_setOf_isRoot hpCne
    simpa [Z, pC, evalRatC, Polynomial.IsRoot] using hf
  let T : Set ℝ := norm '' Z
  have hTfinite : T.Finite := hZfinite.image norm
  have hsep : ∀ x ∈ ({1} : Set ℝ), ∀ y ∈ T, x < y := by
    intro x hx y hy
    simp only [mem_singleton_iff] at hx
    subst x
    rcases hy with ⟨z, hzZ, rfl⟩
    change evalRatC p z = 0 at hzZ
    by_contra hnot
    have hzclosed : z ∈ closedUnitDisc := by
      simpa [closedUnitDisc, dist_eq_norm] using le_of_not_gt hnot
    exact hp z hzclosed hzZ
  obtain ⟨R, hR, hRT⟩ := Set.Finite.exists_between'
    (Set.finite_singleton (1 : ℝ)) hTfinite hsep
  refine ⟨R, hR 1 (by simp), ?_⟩
  intro z hz hzero
  have hzT : ‖z‖ ∈ T := ⟨z, hzero, rfl⟩
  exact (not_lt_of_ge hz) (hRT ‖z‖ hzT)

theorem exists_gt_one_twoFactors_zeroFree {q : ℚ} {u v : Polynomial ℚ}
    (h : RatClosedDiscFactors q u v) :
    ∃ R : ℝ, 1 < R ∧
      (∀ z : ℂ, ‖z‖ ≤ R → evalRatC u z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ ≤ R → evalRatC v z ≠ 0) := by
  obtain ⟨R, hR, hp⟩ := exists_gt_one_zeroFree
    (ratClosedDiscZeroFree_mul h.1 h.2.1)
  refine ⟨R, hR, ?_, ?_⟩
  · intro z hz hu
    exact hp z hz (by rw [evalRatC_mul, hu, zero_mul])
  · intro z hz hv
    exact hp z hz (by rw [evalRatC_mul, hv, mul_zero])

def scaledFactor (R : ℝ) (power : ℕ) (p : Polynomial ℚ) (z : ℂ) : ℂ :=
  (R : ℂ) ^ power * evalRatC p ((R : ℂ) * z)

theorem scaledFactor_star (R : ℝ) (power : ℕ) (p : Polynomial ℚ) (z : ℂ) :
    scaledFactor R power p (star z) = star (scaledFactor R power p z) := by
  have heval : evalRatC p (star ((R : ℂ) * z)) = star (evalRatC p ((R : ℂ) * z)) := by
    rw [← evalC_ratToReal, evalC_star, evalC_ratToReal]
  unfold scaledFactor
  rw [show (R : ℂ) * star z = star ((R : ℂ) * z) by simp, heval]
  simp

theorem scaledFactor_differentiableOn (R : ℝ) (power : ℕ) (p : Polynomial ℚ) :
    DifferentiableOn ℂ (scaledFactor R power p) unitDisc := by
  intro z hz
  have hlin : DifferentiableAt ℂ (fun w : ℂ => (R : ℂ) * w) z :=
    (differentiableAt_const (c := (R : ℂ))).mul differentiableAt_id
  have heval : DifferentiableAt ℂ (fun w : ℂ => evalRatC p w) ((R : ℂ) * z) := by
    exact (p.map (algebraMap ℚ ℂ)).differentiableAt
  exact ((differentiableAt_const (c := (R : ℂ) ^ power)).mul
    (heval.comp z hlin)).differentiableWithinAt

theorem scaledFactor_ne_zero {R : ℝ} {power : ℕ} {p : Polynomial ℚ}
    (hR : 1 < R) (hp : ∀ z : ℂ, ‖z‖ ≤ R → evalRatC p z ≠ 0)
    {z : ℂ} (hz : z ∈ unitDisc) : scaledFactor R power p z ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast ne_of_gt (zero_lt_one.trans hR))
  · apply hp
    have hz' : ‖z‖ < 1 := by simpa [unitDisc, dist_eq_norm] using hz
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hR)]
    nlinarith

theorem scaledFactor_holSymm (R : ℝ) (power : ℕ) (p : Polynomial ℚ) :
    HolSymmOn 1 (scaledFactor R power p) :=
  ⟨scaledFactor_differentiableOn R power p, fun z _ => scaledFactor_star R power p z⟩

theorem scaledFactor_inverse_holSymm {R : ℝ} {power : ℕ} {p : Polynomial ℚ}
    (hR : 1 < R) (hp : ∀ z : ℂ, ‖z‖ ≤ R → evalRatC p z ≠ 0) :
    HolSymmOn 1 (fun z => (scaledFactor R power p z)⁻¹) := by
  constructor
  · intro z hz
    exact ((scaledFactor_differentiableOn R power p z hz).differentiableAt
      (Metric.isOpen_ball.mem_nhds hz)).inv
        (scaledFactor_ne_zero hR hp hz) |>.differentiableWithinAt
  · intro z _
    change (scaledFactor R power p (star z))⁻¹ = star ((scaledFactor R power p z)⁻¹)
    rw [scaledFactor_star]
    simp

theorem scaled_factors_linear {q : ℚ} {u v : Polynomial ℚ}
    (hid : X * u + (X ^ 2 + C q) * v = 1) {R : ℝ} (hR0 : R ≠ 0) (z : ℂ) :
    z * scaledFactor R 1 u z +
      (z ^ 2 + ((q : ℝ) / R ^ 2 : ℂ)) * scaledFactor R 2 v z = 1 := by
  have heval0 := congrArg (fun p : Polynomial ℚ => evalRatC p ((R : ℂ) * z)) hid
  have heval : (R : ℂ) * z * evalRatC u ((R : ℂ) * z) +
      (((R : ℂ) * z) ^ 2 + (q : ℂ)) * evalRatC v ((R : ℂ) * z) = 1 := by
    simpa [evalRatC] using heval0
  have hR0C : (R : ℂ) ≠ 0 := by exact_mod_cast hR0
  have hRC : (R : ℂ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ hR0C
  simp only [scaledFactor, pow_one]
  calc
    z * ((R : ℂ) * evalRatC u ((R : ℂ) * z)) +
        (z ^ 2 + (((q : ℝ) : ℂ)) / (R : ℂ) ^ 2) *
          ((R : ℂ) ^ 2 * evalRatC v ((R : ℂ) * z)) =
      (R : ℂ) * z * evalRatC u ((R : ℂ) * z) +
        (((R : ℂ) * z) ^ 2 + (((q : ℝ) : ℂ))) * evalRatC v ((R : ℂ) * z) := by
          field_simp [hRC]
    _ = (R : ℂ) * z * evalRatC u ((R : ℂ) * z) +
        (((R : ℂ) * z) ^ 2 + (q : ℂ)) * evalRatC v ((R : ℂ) * z) := by
          norm_cast
    _ = 1 := heval

theorem ratFactors_strict_analytic {q : ℚ} {u v : Polynomial ℚ}
    (hq : 0 < q) (hq1 : (q : ℝ) < 1) (h : RatClosedDiscFactors q u v) :
    ∃ r : ℝ, 0 < r ∧ r < (q : ℝ) ∧ AnalyticFeasible r := by
  obtain ⟨R, hR, hu, hv⟩ := exists_gt_one_twoFactors_zeroFree h
  let r : ℝ := (q : ℝ) / R ^ 2
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hr0 : 0 < r := div_pos (by exact_mod_cast hq) (sq_pos_of_pos hR0)
  have hrq : r < (q : ℝ) := by
    rw [div_lt_iff₀ (sq_pos_of_pos hR0)]
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hqR : (q : ℝ) < (q : ℝ) * R ^ 2 :=
      (lt_mul_iff_one_lt_right (by exact_mod_cast hq)).2 hR2
    exact hqR
  let F : FourFactors r := {
    u := scaledFactor R 1 u
    v := scaledFactor R 2 v
    uInv := fun z => (scaledFactor R 1 u z)⁻¹
    vInv := fun z => (scaledFactor R 2 v z)⁻¹
    holSymm_u := scaledFactor_holSymm R 1 u
    holSymm_v := scaledFactor_holSymm R 2 v
    holSymm_uInv := scaledFactor_inverse_holSymm hR hu
    holSymm_vInv := scaledFactor_inverse_holSymm hR hv
    linear := fun z _ => by
      dsimp [r]
      have ht := scaled_factors_linear h.2.2 (ne_of_gt hR0) z
      norm_cast at ht ⊢
    inverse_u := fun z hz => mul_inv_cancel₀ (scaledFactor_ne_zero hR hu hz)
    inverse_v := fun z hz => mul_inv_cancel₀ (scaledFactor_ne_zero hR hv hz)
  }
  refine ⟨r, hr0, hrq, hr0, hrq.trans hq1,
    factorMap F, fourFactors_to_discFunction hr0 (hrq.trans hq1) F⟩

theorem executable_positive_strict_analytic {stage : ℕ} {q : ℚ}
    (hq1 : (q : ℝ) < 1) (h : FinitePositiveVerifier.positive stage q = true) :
    ∃ r : ℝ, r < (q : ℝ) ∧ AnalyticFeasible r := by
  obtain ⟨v, hv⟩ := executable_positive_sound h
  obtain ⟨r, _, hrq, hrA⟩ := ratFactors_strict_analytic hv.1 hq1
    ⟨hv.2.2.2, hv.2.2.1, positiveCertificate_exact_identity hv⟩
  exact ⟨r, hrq, hrA⟩

end

end BelgianChocolate
