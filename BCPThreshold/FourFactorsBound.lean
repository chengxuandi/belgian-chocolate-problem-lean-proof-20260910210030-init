import BCPThreshold.PolynomialAnalyticInterface
import BCPThreshold.QuantitativeSchottky
import Mathlib.Topology.Order.IntermediateValue

/-!
# Real-axis anchors for the four-factor bound

These lemmas use the actual FourFactors definition. They do not assume a
uniform bound and do not assert the as-yet-unformalized Schottky theorem.
-/

namespace BelgianChocolate.Schottky

open Set Metric Complex

theorem holSymm_real {h : ℂ → ℂ} (hh : HolSymmOn 1 h)
    {x : ℝ} (hx : |x| < 1) : (h (x : ℂ)).im = 0 := by
  have hz : (x : ℂ) ∈ Metric.ball 0 1 := by simpa using hx
  have hs := hh.2 (x : ℂ) hz
  have hc : star (h (x : ℂ)) = h (x : ℂ) := by simpa using hs.symm
  exact Complex.conj_eq_iff_im.mp hc

theorem positive_on_preconnected {S : Set ℝ} (hS : IsPreconnected S)
    {g : ℝ → ℝ} (hg : ContinuousOn g S)
    (hne : ∀ x ∈ S, g x ≠ 0) {a : ℝ} (ha : a ∈ S) (hga : 0 < g a) :
    ∀ x ∈ S, 0 < g x := by
  intro x hx
  by_contra h
  have hz : (0 : ℝ) ∈ Icc (g x) (g a) := ⟨le_of_not_gt h, hga.le⟩
  obtain ⟨y, hy, he⟩ := hS.intermediate_value hx ha hg hz
  exact hne y hy he

theorem fourFactors_v_real_pos {q : ℝ} (hq : 0 < q) (F : FourFactors q)
    {x : ℝ} (hx : |x| < 1) : 0 < (F.v (x : ℂ)).re := by
  have mem_disc : ∀ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → (y : ℂ) ∈ unitDisc := by
    intro y hy
    simpa [unitDisc, abs_lt] using hy
  have hv : ContinuousOn (fun y : ℝ => (F.v (y : ℂ)).re) (Ioo (-1) 1) :=
    Complex.continuous_re.continuousOn.comp
      (F.holSymm_v.1.continuousOn.comp Complex.continuous_ofReal.continuousOn mem_disc)
      (fun _ _ => Set.mem_univ _)
  have hn : ∀ y ∈ Ioo (-1 : ℝ) 1, (F.v (y : ℂ)).re ≠ 0 := by
    intro y hy he
    have hi := holSymm_real F.holSymm_v (abs_lt.mpr hy)
    have hz : F.v (y : ℂ) = 0 := Complex.ext he hi
    have hp := F.inverse_v (y : ℂ) (mem_disc y hy)
    simp [hz] at hp
  have hzero := congrArg Complex.re (F.linear 0 (by simp [unitDisc]))
  have hp : 0 < (F.v (0 : ℂ)).re := by
    simp at hzero
    nlinarith
  exact positive_on_preconnected isPreconnected_Ioo hv hn
    (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) (by simpa using hp) x (abs_lt.mp hx)

end BelgianChocolate.Schottky
