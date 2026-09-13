import BCPThreshold.InfiniteFourFactors
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Four factors produce the normalized disc function
-/

namespace BelgianChocolate

open Set Metric Complex Filter

noncomputable section

def factorMap {q : ℝ} (F : FourFactors q) (z : ℂ) : ℂ := z * F.u z

def plusRoot (q : ℝ) : ℂ := Complex.I * (Real.sqrt q : ℂ)

theorem plusRoot_sq {q : ℝ} (hq : 0 ≤ q) : plusRoot q ^ 2 = -(q : ℂ) := by
  rw [plusRoot, mul_pow, Complex.I_sq]
  calc
    (-1 : ℂ) * (Real.sqrt q : ℂ) ^ 2 = -((Real.sqrt q : ℂ) ^ 2) := by ring
    _ = -(q : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hq]

theorem sq_add_real_eq_zero_iff_fourFactors {q : ℝ} (hq : 0 ≤ q) (z : ℂ) :
    z ^ 2 + (q : ℂ) = 0 ↔
      z = plusRoot q ∨ z = -(plusRoot q) := by
  rw [show z ^ 2 + (q : ℂ) = 0 ↔ z ^ 2 = plusRoot q ^ 2 by
    rw [plusRoot_sq hq]
    constructor <;> intro h <;> linear_combination h]
  exact sq_eq_sq_iff_eq_or_eq_neg

theorem plusRoot_mem_unitDisc {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    plusRoot q ∈ unitDisc := by
  have hs : Real.sqrt q < 1 := by
    rw [Real.sqrt_lt' zero_lt_one, one_pow]
    exact hq1
  simpa [plusRoot, unitDisc, mem_ball, dist_zero_right,
    abs_of_nonneg (Real.sqrt_nonneg q)] using hs

theorem neg_plusRoot_mem_unitDisc {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    -(plusRoot q) ∈ unitDisc := by
  simpa [unitDisc, mem_ball, dist_zero_right] using plusRoot_mem_unitDisc hq0 hq1

theorem fourFactors_u_ne_zero' {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : F.u z ≠ 0 := by
  intro h
  have hi := F.inverse_u z hz
  simp [h] at hi

theorem fourFactors_v_ne_zero' {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : F.v z ≠ 0 := by
  intro h
  have hi := F.inverse_v z hz
  simp [h] at hi

theorem factorMap_holSymm {q : ℝ} (F : FourFactors q) :
    HolSymmOn 1 (factorMap F) := by
  constructor
  · exact differentiableOn_id.mul F.holSymm_u.1
  · intro z hz
    simp only [factorMap, map_mul, F.holSymm_u.2 z hz]
    rw [star_mul]
    exact mul_comm _ _

theorem factorMap_zero_iff {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : factorMap F z = 0 ↔ z = 0 := by
  rw [factorMap, mul_eq_zero]
  exact or_iff_left (fourFactors_u_ne_zero' F hz)

theorem factorMap_one_iff {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : factorMap F z = 1 ↔ z ^ 2 + (q : ℂ) = 0 := by
  have hlin := F.linear z hz
  constructor
  · intro hf
    rw [factorMap] at hf
    have hp : (z ^ 2 + (q : ℂ)) * F.v z = 0 := by
      calc
        (z ^ 2 + (q : ℂ)) * F.v z = 1 - z * F.u z := by
          linear_combination hlin
        _ = 0 := by rw [hf]; ring
    exact (mul_eq_zero.mp hp).resolve_right (fourFactors_v_ne_zero' F hz)
  · intro hp
    rw [hp] at hlin
    simpa [factorMap] using hlin

theorem factorMap_deriv_zero_ne {q : ℝ} (F : FourFactors q) :
    deriv (factorMap F) 0 ≠ 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have huAt : DifferentiableAt ℂ F.u 0 :=
    (F.holSymm_u.1 0 h0).differentiableAt (Metric.isOpen_ball.mem_nhds h0)
  change deriv (id * F.u) 0 ≠ 0
  rw [deriv_mul differentiableAt_id huAt]
  simpa using fourFactors_u_ne_zero' F h0

theorem factorMap_deriv_root_ne {q : ℝ} (F : FourFactors q)
    {p : ℂ} (hp : p ∈ unitDisc) (hroot : p ^ 2 + (q : ℂ) = 0)
    (hp0 : p ≠ 0) : deriv (factorMap F) p ≠ 0 := by
  have hvAt : DifferentiableAt ℂ F.v p :=
    (F.holSymm_v.1 p hp).differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hpoly : HasDerivAt (fun z : ℂ => z ^ 2 + (q : ℂ)) (2 * p) p := by
    simpa [id, mul_assoc] using ((hasDerivAt_id p).pow 2).add_const (q : ℂ)
  have heq : factorMap F =ᶠ[nhds p]
      (fun z : ℂ => 1 - (z ^ 2 + (q : ℂ)) * F.v z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with z hz
    have hlin := F.linear z hz
    rw [factorMap]
    linear_combination hlin
  have hder : deriv (factorMap F) p = -(2 * p * F.v p) := by
    rw [heq.deriv_eq]
    rw [show (fun z : ℂ => 1 - (z ^ 2 + (q : ℂ)) * F.v z) =
        (fun _ : ℂ => (1 : ℂ)) - (fun z : ℂ => z ^ 2 + (q : ℂ)) * F.v by
      funext z
      rfl]
    rw [deriv_sub (differentiableAt_const (c := (1 : ℂ)))
      (hpoly.differentiableAt.mul hvAt)]
    rw [deriv_const, deriv_mul hpoly.differentiableAt hvAt, hpoly.deriv, hroot]
    ring
  rw [hder]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hp0)
    (fourFactors_v_ne_zero' F hp))

theorem plusRoot_ne_zero {q : ℝ} (hq : 0 < q) : plusRoot q ≠ 0 := by
  rw [plusRoot]
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.sqrt_ne_zero'.2 hq)

theorem fourFactors_to_discFunction {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (F : FourFactors q) : DiscFunction q (factorMap F) := by
  have hpMem := plusRoot_mem_unitDisc hq0.le hq1
  have hmMem := neg_plusRoot_mem_unitDisc hq0.le hq1
  refine ⟨factorMap_holSymm F, ?_, factorMap_deriv_zero_ne F, ?_, ?_, ?_⟩
  · intro z hz
    exact factorMap_zero_iff F hz
  · intro z hz
    rw [factorMap_one_iff F hz, sq_add_real_eq_zero_iff_fourFactors hq0.le]
    rfl
  · have hplus : plusRoot q ^ 2 + (q : ℂ) = 0 := by
      rw [plusRoot_sq hq0.le]
      ring
    exact factorMap_deriv_root_ne F hpMem hplus (plusRoot_ne_zero hq0)
  · have hminus : (-plusRoot q) ^ 2 + (q : ℂ) = 0 := by
      rw [show (-plusRoot q) ^ 2 = plusRoot q ^ 2 by ring, plusRoot_sq hq0.le]
      ring
    exact factorMap_deriv_root_ne F hmMem hminus
      (neg_ne_zero.mpr (plusRoot_ne_zero hq0))

end

end BelgianChocolate
