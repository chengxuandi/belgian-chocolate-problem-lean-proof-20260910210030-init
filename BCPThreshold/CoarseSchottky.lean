import BCPThreshold.FourFactorsBound
import BCPThreshold.HolomorphicLift
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open Metric Set Filter Topology

namespace BelgianChocolate
namespace CoarseSchottky

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
      ∀ z ∈ S, f z = Complex.cos (Real.pi * u z) :=
  HolomorphicLift.holomorphic_cosine_lift_bounded hSopen hSsc hf ha homit

/-!
This file contains kernel-checked pieces of a coarse Bloch--Schottky route.
It deliberately does not state the final Schottky theorem until the analytic
lifting and Bloch image-disc arguments have been formalized.
-/

/-- A Schwarz-lemma estimate for the variation of the derivative. -/
theorem deriv_sub_center_bound
    {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖deriv G z‖ ≤ 2 * ‖deriv G 0‖)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv G z - deriv G 0‖ ≤ 3 * ‖deriv G 0‖ * ‖z‖ := by
  let D : ℂ → ℂ := fun w ↦ deriv G w - deriv G 0
  have hD : DifferentiableOn ℂ D (ball (0 : ℂ) 1) := by
    exact (hG.deriv isOpen_ball).sub_const _
  have hmaps : MapsTo D (ball (0 : ℂ) 1)
      (closedBall (D 0) (3 * ‖deriv G 0‖)) := by
    intro w hw
    rw [mem_closedBall]
    simp only [D, sub_self, dist_zero_right]
    calc
      ‖deriv G w - deriv G 0‖ ≤ ‖deriv G w‖ + ‖deriv G 0‖ := norm_sub_le _ _
      _ ≤ 2 * ‖deriv G 0‖ + ‖deriv G 0‖ := by nlinarith [hbound w hw]
      _ = 3 * ‖deriv G 0‖ := by ring
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hD hmaps hz
  simpa [D, dist_eq_norm] using hs

/--
If the derivative on the unit disc is at most twice its value at the
centre, the image contains a completely explicit disc.  The deliberately
weak constant `1/32` makes the proof depend only on Schwarz's lemma, the
mean-value inequality, and Mathlib's maximum-principle image-disc lemma.
-/
theorem local_image_disc_of_deriv_bound
    {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖deriv G z‖ ≤ 2 * ‖deriv G 0‖) :
    ball (G 0) (‖deriv G 0‖ / 32) ⊆ G '' ball (0 : ℂ) 1 := by
  by_cases hd : deriv G 0 = 0
  · simp [hd]
  have hsmall : DiffContOnCl ℂ G (ball (0 : ℂ) (1 / 4 : ℝ)) := by
    exact hG.mono (ball_subset_ball (by norm_num))
  have hdiffAt : ∀ w ∈ closedBall (0 : ℂ) (1 / 4 : ℝ), DifferentiableAt ℂ G w := by
    intro w hw
    have hn : ‖w‖ ≤ (1 / 4 : ℝ) := by simpa [mem_closedBall] using hw
    have hwball : w ∈ ball (0 : ℂ) 1 := by
      simpa [mem_ball] using lt_of_le_of_lt hn (by norm_num : (1 / 4 : ℝ) < 1)
    exact hG.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hwball)
  let E : ℂ → ℂ := fun w ↦ G w - G 0 - deriv G 0 * w
  have hEderiv : ∀ w ∈ closedBall (0 : ℂ) (1 / 4 : ℝ),
      HasDerivAt E (deriv G w - deriv G 0) w := by
    intro w hw
    dsimp [E]
    exact ((hdiffAt w hw).hasDerivAt.sub_const _).sub (hasDerivAt_const_mul (deriv G 0))
  have hEbound : ∀ w ∈ closedBall (0 : ℂ) (1 / 4 : ℝ),
      ‖fderiv ℂ E w‖ ≤ (3 / 4 : ℝ) * ‖deriv G 0‖ := by
    intro w hw
    have hwball : w ∈ ball (0 : ℂ) 1 := by
      have hn : ‖w‖ ≤ (1 / 4 : ℝ) := by simpa [mem_closedBall] using hw
      simpa [mem_ball] using lt_of_le_of_lt hn (by norm_num : (1 / 4 : ℝ) < 1)
    have hv := deriv_sub_center_bound hG.differentiableOn hbound hwball
    have hn : ‖w‖ ≤ (1 / 4 : ℝ) := by simpa [mem_closedBall] using hw
    rw [← norm_deriv_eq_norm_fderiv, (hEderiv w hw).deriv]
    calc
      ‖deriv G w - deriv G 0‖ ≤ 3 * ‖deriv G 0‖ * ‖w‖ := hv
      _ ≤ (3 / 4 : ℝ) * ‖deriv G 0‖ := by nlinarith [norm_nonneg (deriv G 0)]
  have hElip : ∀ w ∈ closedBall (0 : ℂ) (1 / 4 : ℝ),
      ‖E w - E 0‖ ≤ ((3 / 4 : ℝ) * ‖deriv G 0‖) * ‖w - 0‖ := by
    intro w hw
    exact (convex_closedBall (0 : ℂ) (1 / 4 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun x hx ↦ (hEderiv x hx).differentiableAt) hEbound
      (mem_closedBall_self (by norm_num)) hw
  have hsphere : ∀ w ∈ sphere (0 : ℂ) (1 / 4 : ℝ),
      ‖deriv G 0‖ / 16 ≤ ‖G w - G 0‖ := by
    intro w hw
    have hwc : w ∈ closedBall (0 : ℂ) (1 / 4 : ℝ) := sphere_subset_closedBall hw
    have hw_norm : ‖w‖ = (1 / 4 : ℝ) := by simpa [mem_sphere] using hw
    have he0 : E 0 = 0 := by simp [E]
    have he : ‖E w‖ ≤ (3 / 16 : ℝ) * ‖deriv G 0‖ := by
      have := hElip w hwc
      rw [he0, sub_zero, sub_zero, hw_norm] at this
      nlinarith [norm_nonneg (deriv G 0)]
    have htri : ‖deriv G 0 * w‖ - ‖E w‖ ≤ ‖G w - G 0‖ := by
      have hid : deriv G 0 * w = (G w - G 0) - E w := by simp [E]
      have hh : ‖deriv G 0 * w‖ ≤ ‖G w - G 0‖ + ‖E w‖ := by
        rw [hid]
        exact norm_sub_le _ _
      linarith
    rw [norm_mul, hw_norm] at htri
    nlinarith [norm_nonneg (deriv G 0)]
  have hfreq : ∃ᶠ w in 𝓝 (0 : ℂ), G w ≠ G 0 := by
    rw [← Filter.not_eventually]
    intro hevent
    have heq : G =ᶠ[𝓝 (0 : ℂ)] (fun _ ↦ G 0) := by
      change ∀ᶠ x in 𝓝 (0 : ℂ), G x = (fun _ ↦ G 0) x
      simpa only [not_ne_iff] using hevent
    have hdeq := heq.deriv_eq
    simp only [deriv_const] at hdeq
    exact hd hdeq
  have himage := hsmall.ball_subset_image_closedBall (by norm_num : (0 : ℝ) < 1 / 4)
    hsphere hfreq
  intro y hy
  have hy' : y ∈ ball (G 0) ((‖deriv G 0‖ / 16) / 2) := by
    convert hy using 1 <;> ring_nf
  rcases himage hy' with ⟨w, hw, rfl⟩
  exact ⟨w, by
    have hn : ‖w‖ ≤ (1 / 4 : ℝ) := by simpa [mem_closedBall] using hw
    simpa [mem_ball] using lt_of_le_of_lt hn (by norm_num : (1 / 4 : ℝ) < 1), rfl⟩

/-- Rescaled form of the local image-disc theorem. -/
theorem local_image_disc_at
    {F : ℂ → ℂ} {p : ℂ} {t : ℝ}
    (ht : 0 < t)
    (hF : DiffContOnCl ℂ F (ball p t))
    (hbound : ∀ z ∈ ball p t, ‖deriv F z‖ ≤ 2 * ‖deriv F p‖) :
    ball (F p) (t * ‖deriv F p‖ / 32) ⊆ F '' ball p t := by
  let A : ℂ → ℂ := fun z ↦ p + (t : ℂ) * z
  let G : ℂ → ℂ := F ∘ A
  have hA : DiffContOnCl ℂ A (ball (0 : ℂ) 1) := by
    apply Differentiable.diffContOnCl
    fun_prop
  have hAmap : MapsTo A (ball (0 : ℂ) 1) (ball p t) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    simp only [sub_zero] at hz
    simp only [A, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le]
    nlinarith
  have hG : DiffContOnCl ℂ G (ball (0 : ℂ) 1) :=
    hF.comp hA hAmap
  have hAderiv (z : ℂ) : HasDerivAt A (t : ℂ) z := by
    change HasDerivAt (fun x : ℂ ↦ p + (t : ℂ) * x) (t : ℂ) z
    exact (hasDerivAt_const_mul (t : ℂ)).const_add p
  have hGderiv (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      deriv G z = deriv F (A z) * (t : ℂ) := by
    have hFA : DifferentiableAt ℂ F (A z) :=
      hF.differentiableOn.differentiableAt (isOpen_ball.mem_nhds (hAmap hz))
    exact (hFA.hasDerivAt.comp z (hAderiv z)).deriv
  have hGderiv0 : deriv G 0 = deriv F p * (t : ℂ) := by
    have hz : (0 : ℂ) ∈ ball 0 1 := by simp
    simpa [A] using hGderiv 0 hz
  have hGbound : ∀ z ∈ ball (0 : ℂ) 1,
      ‖deriv G z‖ ≤ 2 * ‖deriv G 0‖ := by
    intro z hz
    rw [hGderiv z hz, hGderiv0, norm_mul, norm_mul]
    have hb := hbound (A z) (hAmap hz)
    have ht0 : 0 ≤ ‖(t : ℂ)‖ := norm_nonneg _
    nlinarith
  have himage := local_image_disc_of_deriv_bound hG hGbound
  intro y hy
  have hyG : y ∈ ball (G 0) (‖deriv G 0‖ / 32) := by
    rw [show G 0 = F p by simp [G, A]]
    rw [hGderiv0, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    convert hy using 1 <;> ring_nf
  obtain ⟨z, hz, rfl⟩ := himage hyG
  exact ⟨A z, hAmap hz, rfl⟩

/-- A deliberately coarse Bloch theorem, with an explicit image-disc radius. -/
theorem coarse_bloch_image_disc
    {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    ∃ b : ℂ, ball b (‖deriv F 0‖ / 128) ⊆ F '' ball (0 : ℂ) 1 := by
  by_cases hd : deriv F 0 = 0
  · refine ⟨F 0, ?_⟩
    simp [hd]
  let M : ℂ → ℝ := fun z ↦ (1 / 2 - ‖z‖) * ‖deriv F z‖
  have hhalf : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    linarith
  have hMcont : ContinuousOn M (closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
    have hfirst : ContinuousOn (fun z : ℂ ↦ (1 / 2 : ℝ) - ‖z‖)
        (closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
      continuousOn_const.sub continuous_norm.continuousOn
    have hsecond : ContinuousOn (fun z : ℂ ↦ ‖deriv F z‖)
        (closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
      ((hF.deriv isOpen_ball).continuousOn.mono hhalf).norm
    exact hfirst.mul hsecond
  obtain ⟨p, hp, hpmax⟩ :=
    (isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ)).exists_isMaxOn
      ⟨0, by simp⟩ hMcont
  have hM0 : M 0 = (1 / 2 : ℝ) * ‖deriv F 0‖ := by simp [M]
  have hdpos : 0 < ‖deriv F 0‖ := norm_pos_iff.mpr hd
  have hMp_lower : (1 / 2 : ℝ) * ‖deriv F 0‖ ≤ M p := by
    rw [← hM0]
    exact hpmax (by simp)
  have hMp_pos : 0 < M p :=
    lt_of_lt_of_le (mul_pos (by norm_num) hdpos) hMp_lower
  have hp_norm : ‖p‖ ≤ (1 / 2 : ℝ) := by
    simpa [mem_closedBall, dist_zero_left] using hp
  have hp_lt : ‖p‖ < (1 / 2 : ℝ) := by
    by_contra hnot
    have heq : ‖p‖ = (1 / 2 : ℝ) := le_antisymm hp_norm (not_lt.mp hnot)
    simp [M, heq] at hMp_pos
  let t : ℝ := (1 / 2 - ‖p‖) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hclosed : closedBall p t ⊆ ball (0 : ℂ) 1 := by
    intro y hy
    have hyd : dist y p ≤ t := by simpa [dist_comm] using hy
    have hyn : ‖y‖ ≤ ‖p‖ + t := by
      have htri : ‖y‖ ≤ ‖y - p‖ + ‖p‖ := by
        calc
          ‖y‖ = ‖(y - p) + p‖ := by ring_nf
          _ ≤ ‖y - p‖ + ‖p‖ := norm_add_le _ _
      rw [← dist_eq_norm] at htri
      nlinarith
    rw [mem_ball, dist_zero_right]
    dsimp [t] at hyn ⊢
    nlinarith
  have hFp : DiffContOnCl ℂ F (ball p t) :=
    hF.diffContOnCl_ball hclosed
  have hbound : ∀ y ∈ ball p t, ‖deriv F y‖ ≤ 2 * ‖deriv F p‖ := by
    intro y hy
    have hyd : dist y p < t := by simpa [mem_ball] using hy
    have hyn : ‖y‖ ≤ ‖p‖ + dist y p := by
      have htri : ‖y‖ ≤ ‖y - p‖ + ‖p‖ := by
        calc
          ‖y‖ = ‖(y - p) + p‖ := by ring_nf
          _ ≤ ‖y - p‖ + ‖p‖ := norm_add_le _ _
      rw [← dist_eq_norm] at htri
      linarith
    have hyhalf : y ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) := by
      rw [mem_closedBall, dist_zero_right]
      dsimp [t] at hyd hyn
      nlinarith
    have hMy := hpmax hyhalf
    have hclear : t ≤ (1 / 2 : ℝ) - ‖y‖ := by
      dsimp [t] at hyd ⊢
      nlinarith [hyn]
    have hnonneg : 0 ≤ ‖deriv F y‖ := norm_nonneg _
    have hscaled : t * ‖deriv F y‖ ≤ M y := by
      dsimp [M]
      exact mul_le_mul_of_nonneg_right hclear hnonneg
    have hMp_eq : M p = 2 * t * ‖deriv F p‖ := by
      dsimp [M, t]
      ring
    rw [hMp_eq] at hMy
    have hmul : t * ‖deriv F y‖ ≤ t * (2 * ‖deriv F p‖) := by
      calc
        t * ‖deriv F y‖ ≤ M y := hscaled
        _ ≤ 2 * t * ‖deriv F p‖ := hMy
        _ = t * (2 * ‖deriv F p‖) := by ring
    exact le_of_mul_le_mul_left hmul ht
  have himage := local_image_disc_at ht hFp hbound
  have hMp_eq : M p = 2 * t * ‖deriv F p‖ := by
    dsimp [M, t]
    ring
  have hradius : ‖deriv F 0‖ / 128 ≤ t * ‖deriv F p‖ / 32 := by
    rw [hMp_eq] at hMp_lower
    nlinarith
  refine ⟨F p, ?_⟩
  intro y hy
  have hy' : y ∈ ball (F p) (t * ‖deriv F p‖ / 32) :=
    (ball_subset_ball hradius) hy
  obtain ⟨x, hx, rfl⟩ := himage hy'
  exact ⟨x, hclosed (ball_subset_closedBall hx), rfl⟩

end CoarseSchottky
end BelgianChocolate
