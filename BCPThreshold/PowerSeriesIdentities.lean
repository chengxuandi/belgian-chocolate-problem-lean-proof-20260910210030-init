import BCPThreshold.AllOrdersCompactness
import BCPThreshold.CoefficientConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Power-series realization of infinite coefficient arrays
-/

namespace BelgianChocolate.Route1.AllOrders

open Set Metric Complex
open TrueHierarchy

noncomputable section

def complexCoeff (c : InfiniteCoefficients) (f : TrueHierarchy.Family) (n : ℕ) : ℂ :=
  (c f n : ℂ)

def seriesFun (c : InfiniteCoefficients) (f : TrueHierarchy.Family) (z : ℂ) : ℂ :=
  ∑' n : ℕ, complexCoeff c f n * z ^ n

theorem complexCoeff_bound {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) (n : ℕ) :
    ‖complexCoeff c f n‖ ≤ (PaperBounds.coefficientBound n : ℝ) := by
  have h := hc f n
  rw [mem_Icc] at h
  simpa [complexCoeff, Complex.norm_real, Real.norm_eq_abs, abs_le] using h

theorem seriesFun_summable {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => complexCoeff c f n * z ^ n) :=
  Schottky.coefficientBound_summable (complexCoeff_bound hc f) hz

theorem seriesFun_norm_summable {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖complexCoeff c f n * z ^ n‖) :=
  Schottky.coefficientBound_norm_summable (complexCoeff_bound hc f) hz

theorem seriesFun_uniform_majorant {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => ‖complexCoeff c f n * (ρ : ℂ) ^ n‖) ∧
      ∀ z : ℂ, ‖z‖ ≤ ρ → ∀ n : ℕ,
        ‖complexCoeff c f n * z ^ n‖ ≤
          ‖complexCoeff c f n * (ρ : ℂ) ^ n‖ := by
  constructor
  · exact seriesFun_norm_summable hc f
      (by simpa [abs_of_nonneg hρ0] using hρ1)
  · intro z hz n
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n)
      (norm_nonneg _)

theorem seriesFun_differentiableOn {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) :
    DifferentiableOn ℂ (seriesFun c f) unitDisc := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
  let ρ : ℝ := (‖z‖ + 1) / 2
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hzρ : ‖z‖ < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  obtain ⟨hsum, hmajor⟩ := seriesFun_uniform_majorant hc f hρ0 hρ1
  have hdiff : DifferentiableOn ℂ (seriesFun c f) (Metric.ball 0 ρ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
    · intro n
      exact (differentiableOn_const (c := complexCoeff c f n)).mul
        (differentiableOn_id.pow n)
    · exact Metric.isOpen_ball
    · intro n w hw
      apply hmajor w
      exact (le_of_lt (by simpa [mem_ball, dist_zero_right] using hw))
  have hzball : z ∈ Metric.ball (0 : ℂ) ρ := by
    simpa [mem_ball, dist_zero_right] using hzρ
  exact (hdiff z hzball).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzball) |>.differentiableWithinAt

theorem seriesFun_star (c : InfiniteCoefficients) (f : TrueHierarchy.Family)
    (z : ℂ) :
    seriesFun c f (star z) = star (seriesFun c f z) := by
  rw [seriesFun, seriesFun]
  change (∑' n : ℕ, complexCoeff c f n * star z ^ n) =
    (starRingEnd ℂ) (∑' n : ℕ, complexCoeff c f n * z ^ n)
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp [complexCoeff]

theorem list_sum_map_range_eq_finset {R : Type} [AddCommMonoid R]
    (h : ℕ → R) (n : ℕ) :
    ((List.range n).map h).sum = ∑ i ∈ Finset.range n, h i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp

theorem convolution_eq_finset (c : InfiniteCoefficients)
    (f g : TrueHierarchy.Family) (n : ℕ) :
    convolution c f g n = ∑ i ∈ Finset.range (n + 1), c f i * c g (n - i) := by
  exact list_sum_map_range_eq_finset (fun i => c f i * c g (n - i)) (n + 1)

theorem seriesFun_mul {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f g : TrueHierarchy.Family) {z : ℂ} (hz : ‖z‖ < 1) :
    seriesFun c f z * seriesFun c g z =
      ∑' n : ℕ, (convolution c f g n : ℂ) * z ^ n := by
  have hfNorm := seriesFun_norm_summable hc f hz
  have hgNorm := seriesFun_norm_summable hc g hz
  rw [seriesFun, seriesFun]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfNorm hgNorm]
  apply tsum_congr
  intro n
  rw [convolution_eq_finset]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [show z ^ n = z ^ i * z ^ (n - i) by
    rw [← pow_add, Nat.add_sub_of_le hin]]
  simp [complexCoeff]
  ring

theorem seriesFun_eq_of_coeff_eq {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) {d : ℕ → ℝ}
    (hd : ∀ n, c f n = d n) {z : ℂ} (hz : ‖z‖ < 1) :
    seriesFun c f z = ∑' n : ℕ, (d n : ℂ) * z ^ n := by
  rw [seriesFun]
  apply tsum_congr
  intro n
  simp [complexCoeff, hd n]

theorem tsum_deltaZero (z : ℂ) :
    (∑' n : ℕ, (TrueHierarchy.deltaZero n : ℂ) * z ^ n) = 1 := by
  rw [tsum_eq_single 0]
  · simp [TrueHierarchy.deltaZero]
  · intro b hb
    simp [TrueHierarchy.deltaZero, hb]

theorem series_convolution_eq_one {q : ℚ} {c : InfiniteCoefficients}
    (hc : InfiniteConstraints q c) (f g : TrueHierarchy.Family)
    (hconv : ∀ n, convolution c f g n = TrueHierarchy.deltaZero n)
    {z : ℂ} (hz : ‖z‖ < 1) :
    seriesFun c f z * seriesFun c g z = 1 := by
  rw [seriesFun_mul hc.1 f g hz]
  calc
    (∑' n : ℕ, (convolution c f g n : ℂ) * z ^ n) =
        ∑' n : ℕ, (TrueHierarchy.deltaZero n : ℂ) * z ^ n := by
          apply tsum_congr
          intro n
          rw [hconv n]
    _ = 1 := tsum_deltaZero z

theorem shifted_seriesFun {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) (shift : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (shiftedCoeff c f n shift : ℂ) * z ^ n) =
      z ^ shift * seriesFun c f z := by
  let S : ℕ → ℂ := fun n => (shiftedCoeff c f n shift : ℂ) * z ^ n
  have htail : Summable (fun n => S (n + shift)) := by
    have hs := (seriesFun_summable hc f hz).mul_left (z ^ shift)
    refine hs.congr ?_
    intro n
    simp [S, shiftedCoeff, complexCoeff, Nat.add_sub_cancel, pow_add]
    ring
  have hS : Summable S := (summable_nat_add_iff shift).mp htail
  calc
    (∑' n : ℕ, (shiftedCoeff c f n shift : ℂ) * z ^ n) = ∑' n, S n := rfl
    _ = (∑ n ∈ Finset.range shift, S n) + ∑' n, S (n + shift) :=
      (hS.sum_add_tsum_nat_add shift).symm
    _ = 0 + ∑' n, S (n + shift) := by
      congr 1
      apply Finset.sum_eq_zero
      intro n hn
      have hns : ¬ shift ≤ n := Nat.not_le_of_lt (Finset.mem_range.mp hn)
      simp [S, shiftedCoeff, hns]
    _ = z ^ shift * ∑' n, complexCoeff c f n * z ^ n := by
      rw [zero_add, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp [S, shiftedCoeff, complexCoeff, Nat.add_sub_cancel, pow_add]
      ring
    _ = z ^ shift * seriesFun c f z := by rw [seriesFun]

theorem shifted_seriesFun_summable {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) (shift : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => (shiftedCoeff c f n shift : ℂ) * z ^ n) := by
  let S : ℕ → ℂ := fun n => (shiftedCoeff c f n shift : ℂ) * z ^ n
  have htail : Summable (fun n => S (n + shift)) := by
    have hs := (seriesFun_summable hc f hz).mul_left (z ^ shift)
    refine hs.congr ?_
    intro n
    simp [S, shiftedCoeff, complexCoeff, Nat.add_sub_cancel, pow_add]
    ring
  exact (summable_nat_add_iff shift).mp htail

theorem seriesFun_linear_identity {q : ℚ} {c : InfiniteCoefficients}
    (hc : InfiniteConstraints q c) {z : ℂ} (hz : ‖z‖ < 1) :
    z * seriesFun c uFamily z + (z ^ 2 + (q : ℂ)) * seriesFun c vFamily z = 1 := by
  let d : ℕ → ℂ := fun n =>
    (shiftedCoeff c uFamily n 1 : ℂ) +
      (shiftedCoeff c vFamily n 2 : ℂ) +
      (q : ℂ) * (c vFamily n : ℂ)
  have hd : ∀ n, d n = (TrueHierarchy.deltaZero n : ℂ) := by
    intro n
    simpa [d] using congrArg (fun x : ℝ => (x : ℂ)) (hc.2.1 n)
  have hu := seriesFun_summable hc.1 uFamily hz
  have hv := seriesFun_summable hc.1 vFamily hz
  have hsu := (hu.mul_left z)
  have hsv2 := (hv.mul_left (z ^ 2))
  have hqv := (hv.mul_left (q : ℂ))
  have hsuShift := shifted_seriesFun_summable hc.1 uFamily 1 hz
  have hsvShift := shifted_seriesFun_summable hc.1 vFamily 2 hz
  have hqv' : Summable (fun n => ((q : ℂ) * (c vFamily n : ℂ)) * z ^ n) := by
    refine hqv.congr ?_
    intro n
    simp [complexCoeff]
    ring
  calc
    z * seriesFun c uFamily z + (z ^ 2 + (q : ℂ)) * seriesFun c vFamily z =
        z * seriesFun c uFamily z + z ^ 2 * seriesFun c vFamily z +
          (q : ℂ) * seriesFun c vFamily z := by ring
    _ = (∑' n, (shiftedCoeff c uFamily n 1 : ℂ) * z ^ n) +
          (∑' n, (shiftedCoeff c vFamily n 2 : ℂ) * z ^ n) +
          ∑' n, ((q : ℂ) * (c vFamily n : ℂ)) * z ^ n := by
      rw [shifted_seriesFun hc.1 uFamily 1 hz,
        shifted_seriesFun hc.1 vFamily 2 hz]
      simp only [pow_one]
      have hqeq : (q : ℂ) * seriesFun c vFamily z =
          ∑' n, ((q : ℂ) * (c vFamily n : ℂ)) * z ^ n := by
        rw [seriesFun, ← tsum_mul_left]
        apply tsum_congr
        intro n
        simp [complexCoeff]
        ring
      rw [hqeq]
    _ = ∑' n, d n * z ^ n := by
      rw [← hsuShift.tsum_add hsvShift,
        ← (hsuShift.add hsvShift).tsum_add hqv']
      apply tsum_congr
      intro n
      simp [d]
      ring
    _ = ∑' n, (TrueHierarchy.deltaZero n : ℂ) * z ^ n := by
      apply tsum_congr
      intro n
      rw [hd n]
    _ = 1 := tsum_deltaZero z

end

end BelgianChocolate.Route1.AllOrders
