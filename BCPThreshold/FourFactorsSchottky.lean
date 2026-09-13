import BCPThreshold.CirclePropagation
import Mathlib.Analysis.Complex.AbsMax

open Metric Set Complex

namespace BelgianChocolate
namespace Schottky

noncomputable section

open Route1.PaperBounds

def fourFactorMap {q : ℝ} (F : FourFactors q) (z : ℂ) : ℂ := z * F.u z

theorem fourFactors_u_ne_zero {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : F.u z ≠ 0 := by
  intro he
  have hi := F.inverse_u z hz
  simp [he] at hi

theorem fourFactors_v_ne_zero {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : F.v z ≠ 0 := by
  intro he
  have hi := F.inverse_v z hz
  simp [he] at hi

theorem fourFactors_uInv_ne_zero {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : F.uInv z ≠ 0 := by
  intro he
  have hi := F.inverse_u z hz
  simp [he] at hi

theorem fourFactors_vInv_ne_zero {q : ℝ} (F : FourFactors q) {z : ℂ}
    (hz : z ∈ unitDisc) : F.vInv z ≠ 0 := by
  intro he
  have hi := F.inverse_v z hz
  simp [he] at hi

theorem fourFactorMap_ne_zero_on_annulus {q : ℝ} (F : FourFactors q)
    {z : ℂ} (hzβ : (3 / 4 : ℝ) < ‖z‖) (hz1 : ‖z‖ < 1) :
    fourFactorMap F z ≠ 0 := by
  apply mul_ne_zero
  · exact norm_ne_zero_iff.mp (by nlinarith)
  · exact fourFactors_u_ne_zero F (by simpa [unitDisc, mem_ball, dist_zero_right])

theorem fourFactorMap_ne_one_on_annulus
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) {z : ℂ}
    (hzβ : (3 / 4 : ℝ) < ‖z‖) (hz1 : ‖z‖ < 1) :
    fourFactorMap F z ≠ 1 := by
  intro he
  have hzD : z ∈ unitDisc := by simpa [unitDisc, mem_ball, dist_zero_right]
  have hlin := F.linear z hzD
  have hv0 := fourFactors_v_ne_zero F hzD
  have hprod : (z ^ 2 + (q : ℂ)) * F.v z = 0 := by
    calc
      (z ^ 2 + (q : ℂ)) * F.v z = 1 - fourFactorMap F z := by
        rw [fourFactorMap]
        linear_combination hlin
      _ = 0 := by simp [he]
  have hzq : z ^ 2 + (q : ℂ) = 0 := (mul_eq_zero.mp hprod).resolve_right hv0
  have hnorm : ‖z‖ ^ 2 = q := by
    have heq : z ^ 2 = -(q : ℂ) := by linear_combination hzq
    have hn := congrArg norm heq
    simpa [norm_pow, Real.norm_eq_abs, abs_of_pos hq] using hn
  nlinarith

def transformedF {q : ℝ} (F : FourFactors q) : Fin 4 → ℂ → ℂ
  | 0 => fourFactorMap F
  | 1 => fun z => 1 - fourFactorMap F z
  | 2 => fun z => (fourFactorMap F z)⁻¹
  | 3 => fun z => (1 - fourFactorMap F z)⁻¹

theorem transformedF_differentiableOn_annulus
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) (i : Fin 4) :
    DifferentiableOn ℂ (transformedF F i)
      {z : ℂ | (3 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 1} := by
  have hf : DifferentiableOn ℂ (fourFactorMap F)
      {z : ℂ | (3 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 1} := by
    intro z hz
    have hu : DifferentiableAt ℂ F.u z :=
      F.holSymm_u.1.differentiableAt
        (isOpen_ball.mem_nhds
          (by simpa [unitDisc, mem_ball, dist_zero_right] using hz.2))
    have hm : DifferentiableWithinAt ℂ (fun w : ℂ => w * F.u w)
        {z : ℂ | (3 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 1} z :=
      ((differentiableAt_fun_id : DifferentiableAt ℂ (fun w : ℂ => w) z).mul hu).differentiableWithinAt
    exact hm
  fin_cases i
  · exact hf
  · simpa [transformedF] using hf.const_sub (1 : ℂ)
  · apply hf.fun_inv
    intro z hz
    exact fourFactorMap_ne_zero_on_annulus F hz.1 hz.2
  · apply (hf.const_sub (1 : ℂ)).fun_inv
    intro z hz he
    apply fourFactorMap_ne_one_on_annulus hq hqb F hz.1 hz.2
    exact (sub_eq_zero.mp he).symm

theorem transformedF_omits_on_annulus
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) (i : Fin 4) {z : ℂ}
    (hzβ : (3 / 4 : ℝ) < ‖z‖) (hz1 : ‖z‖ < 1) :
    transformedF F i z ≠ 0 ∧ transformedF F i z ≠ 1 := by
  have hf0 := fourFactorMap_ne_zero_on_annulus F hzβ hz1
  have hf1 := fourFactorMap_ne_one_on_annulus hq hqb F hzβ hz1
  fin_cases i
  · exact ⟨hf0, hf1⟩
  · constructor
    · intro he
      simp only [transformedF] at he
      apply hf1
      exact (sub_eq_zero.mp he).symm
    · intro he
      simp only [transformedF] at he
      apply hf0
      calc
        fourFactorMap F z = 1 - (1 - fourFactorMap F z) := by ring
        _ = 0 := by rw [he]; ring
  · constructor
    · simpa [transformedF] using inv_ne_zero hf0
    · simpa [transformedF, inv_eq_one] using hf1
  · constructor
    · exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hf1))
    · intro he
      simp only [transformedF] at he
      have hone : 1 - fourFactorMap F z = 1 := inv_eq_one.mp he
      apply hf0
      calc
        fourFactorMap F z = 1 - (1 - fourFactorMap F z) := by ring
        _ = 0 := by rw [hone]; ring

theorem fourFactorMap_differentiableOn_unitDisc {q : ℝ} (F : FourFactors q) :
    DifferentiableOn ℂ (fourFactorMap F) unitDisc := by
  intro z hz
  have hu : DifferentiableAt ℂ F.u z :=
    F.holSymm_u.1.differentiableAt (isOpen_ball.mem_nhds hz)
  have hm : DifferentiableWithinAt ℂ (fun w : ℂ => w * F.u w) unitDisc z :=
    ((differentiableAt_fun_id : DifferentiableAt ℂ (fun w : ℂ => w) z).mul hu).differentiableWithinAt
  exact hm

theorem fourFactors_u_real_ne_zero {q : ℝ} (F : FourFactors q)
    {x : ℝ} (hx : |x| < 1) : (F.u (x : ℂ)).re ≠ 0 := by
  intro hre
  have him := holSymm_real F.holSymm_u hx
  have hz : F.u (x : ℂ) = 0 := Complex.ext hre him
  exact fourFactors_u_ne_zero F (by simpa [unitDisc] using hx) hz

theorem fourFactors_u_pos_of_u_zero_pos {q : ℝ} (F : FourFactors q)
    (hzero : 0 < (F.u 0).re) {x : ℝ} (hx : |x| < 1) :
    0 < (F.u (x : ℂ)).re := by
  have mem_disc : ∀ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → (y : ℂ) ∈ unitDisc := by
    intro y hy
    simpa [unitDisc, abs_lt] using hy
  have hu : ContinuousOn (fun y : ℝ => (F.u (y : ℂ)).re) (Ioo (-1) 1) :=
    Complex.continuous_re.continuousOn.comp
      (F.holSymm_u.1.continuousOn.comp Complex.continuous_ofReal.continuousOn mem_disc)
      (fun _ _ => Set.mem_univ _)
  exact positive_on_preconnected isPreconnected_Ioo hu
    (fun y hy => fourFactors_u_real_ne_zero F (abs_lt.mpr hy))
    (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) (by simpa using hzero)
    x (abs_lt.mp hx)

theorem fourFactors_u_neg_of_u_zero_neg {q : ℝ} (F : FourFactors q)
    (hzero : (F.u 0).re < 0) {x : ℝ} (hx : |x| < 1) :
    (F.u (x : ℂ)).re < 0 := by
  have mem_disc : ∀ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → (y : ℂ) ∈ unitDisc := by
    intro y hy
    simpa [unitDisc, abs_lt] using hy
  have hu : ContinuousOn (fun y : ℝ => -(F.u (y : ℂ)).re) (Ioo (-1) 1) :=
    (Complex.continuous_re.continuousOn.comp
      (F.holSymm_u.1.continuousOn.comp Complex.continuous_ofReal.continuousOn mem_disc)
      (fun _ _ => Set.mem_univ _)).neg
  have hp := positive_on_preconnected isPreconnected_Ioo hu
    (fun y hy h => fourFactors_u_real_ne_zero F (abs_lt.mpr hy) (by linarith))
    (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) (by simpa using neg_pos.mpr hzero)
    x (abs_lt.mp hx)
  linarith

/-- Two antipodal real points supply the first three small anchors. -/
theorem fourFactorMap_real_anchors
    {q R : ℝ} (hq : 0 < q) (hR0 : 0 < R) (hR1 : R < 1)
    (F : FourFactors q) :
    ∃ a b : ℂ,
      ‖a‖ = R ∧ ‖b‖ = R ∧
      0 < (fourFactorMap F a).re ∧ (fourFactorMap F a).re < 1 ∧
      (fourFactorMap F a).im = 0 ∧
      (fourFactorMap F b).re < 0 ∧ (fourFactorMap F b).im = 0 := by
  have hu0 : (F.u 0).re ≠ 0 := fourFactors_u_real_ne_zero F (by norm_num)
  rcases lt_or_gt_of_ne hu0 with hu0neg | hu0pos
  · refine ⟨(-R : ℝ), (R : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [abs_of_pos hR0]
    · simp [abs_of_pos hR0]
    · have hu := fourFactors_u_neg_of_u_zero_neg F hu0neg (show |-R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hp : 0 < (-R) * (F.u ((-R : ℝ) : ℂ)).re :=
        mul_pos_of_neg_of_neg (neg_lt_zero.mpr hR0) hu
      simpa [fourFactorMap] using hp
    · have hzD : ((-R : ℝ) : ℂ) ∈ unitDisc := by
        simpa [unitDisc, abs_of_pos hR0] using hR1
      have hlin := congrArg Complex.re (F.linear ((-R : ℝ) : ℂ) hzD)
      have hv := fourFactors_v_real_pos hq F (show |-R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hvim := holSymm_real F.holSymm_v
        (show |-R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hc : 0 < (R ^ 2 + q) * (F.v ((-R : ℝ) : ℂ)).re :=
        mul_pos (by nlinarith [sq_nonneg R]) hv
      have hc' : 0 < (R ^ 2 + q) * (F.v (-(R : ℂ))).re := by simpa using hc
      simp [fourFactorMap, pow_two, hvim] at hlin
      simp [fourFactorMap]
      nlinarith [hc']
    · have huim := holSymm_real F.holSymm_u
        (show |-R| < 1 by simpa [abs_of_pos hR0] using hR1)
      calc
        (fourFactorMap F ((-R : ℝ) : ℂ)).im =
            (-R) * (F.u ((-R : ℝ) : ℂ)).im := by simp [fourFactorMap]
        _ = 0 := by rw [huim]; ring

    · have hu := fourFactors_u_neg_of_u_zero_neg F hu0neg (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hn : R * (F.u (R : ℂ)).re < 0 := mul_neg_of_pos_of_neg hR0 hu
      simpa [fourFactorMap] using hn
    · have huim := holSymm_real F.holSymm_u
        (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)
      calc
        (fourFactorMap F (R : ℂ)).im = R * (F.u (R : ℂ)).im := by simp [fourFactorMap]
        _ = 0 := by rw [huim]; ring
  · refine ⟨(R : ℝ), (-R : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [abs_of_pos hR0]
    · simp [abs_of_pos hR0]
    · have hu := fourFactors_u_pos_of_u_zero_pos F hu0pos (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)
      simp [fourFactorMap]
      nlinarith
    · have hzD : ((R : ℝ) : ℂ) ∈ unitDisc := by
        simpa [unitDisc, abs_of_pos hR0] using hR1
      have hlin := congrArg Complex.re (F.linear ((R : ℝ) : ℂ) hzD)
      have hv := fourFactors_v_real_pos hq F (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hvim := holSymm_real F.holSymm_v
        (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hc : 0 < (R ^ 2 + q) * (F.v (R : ℂ)).re :=
        mul_pos (by nlinarith [sq_nonneg R]) hv
      simp [fourFactorMap, pow_two, hvim] at hlin
      simp [fourFactorMap]
      nlinarith [hc]
    · have huim := holSymm_real F.holSymm_u
        (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)
      calc
        (fourFactorMap F (R : ℂ)).im = R * (F.u (R : ℂ)).im := by simp [fourFactorMap]
        _ = 0 := by rw [huim]; ring
    · have hu := fourFactors_u_pos_of_u_zero_pos F hu0pos (show |-R| < 1 by simpa [abs_of_pos hR0] using hR1)
      have hn : (-R) * (F.u ((-R : ℝ) : ℂ)).re < 0 :=
        mul_neg_of_neg_of_pos (neg_lt_zero.mpr hR0) hu
      simpa [fourFactorMap] using hn
    · have huim := holSymm_real F.holSymm_u
        (show |-R| < 1 by simpa [abs_of_pos hR0] using hR1)
      calc
        (fourFactorMap F ((-R : ℝ) : ℂ)).im =
            (-R) * (F.u ((-R : ℝ) : ℂ)).im := by simp [fourFactorMap]
        _ = 0 := by rw [huim]; ring

theorem fourFactorMap_at_sqrt_q
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) :
    fourFactorMap F (Complex.I * (Real.sqrt q : ℂ)) = 1 := by
  let p : ℂ := Complex.I * (Real.sqrt q : ℂ)
  have hp_norm : ‖p‖ = Real.sqrt q := by
    dsimp [p]
    simp [abs_of_nonneg (Real.sqrt_nonneg q)]
  have hp_mem : p ∈ unitDisc := by
    have hsqrt : Real.sqrt q ≤ 3 / 4 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · norm_num at hqb ⊢
        exact hqb
    rw [unitDisc, mem_ball, dist_zero_right, hp_norm]
    linarith
  have hlin := F.linear p hp_mem
  have hpq : p ^ 2 + (q : ℂ) = 0 := by
    dsimp [p]
    rw [mul_pow]
    simp only [Complex.I_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]
    ring
  rw [hpq, zero_mul, add_zero] at hlin
  change p * F.u p = 1
  exact hlin

/-- Maximum modulus supplies the small anchor for the reciprocal transform. -/
theorem fourFactorMap_inverse_anchor
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ c : ℂ, ‖c‖ = (radius r : ℝ) ∧ ‖(fourFactorMap F c)⁻¹‖ ≤ 1 := by
  let R : ℝ := (radius r : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 7 / 8)
      (CoarseSchottky.paper_radius_ge hr0 hr1)
  have hR1 : R < 1 := by
    dsimp [R]
    exact_mod_cast CoarseSchottky.paper_radius_lt hr1
  have hclosed : closedBall (0 : ℂ) R ⊆ unitDisc := by
    intro z hz
    rw [unitDisc, mem_ball, dist_zero_right]
    have hzR : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz
    exact hzR.trans_lt hR1
  have hdc : DiffContOnCl ℂ (fourFactorMap F) (ball (0 : ℂ) R) :=
    (fourFactorMap_differentiableOn_unitDisc F).diffContOnCl_ball hclosed
  obtain ⟨c, hcfront, hcmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
      (nonempty_ball.mpr hR0) hdc
  refine ⟨c, ?_, ?_⟩
  · rw [frontier_ball 0 hR0.ne'] at hcfront
    simpa [mem_sphere, dist_zero_right, R] using hcfront
  · let p : ℂ := Complex.I * (Real.sqrt q : ℂ)
    have hp_norm : ‖p‖ = Real.sqrt q := by
      dsimp [p]
      simp [abs_of_nonneg (Real.sqrt_nonneg q)]
    have hsqrt : Real.sqrt q ≤ 3 / 4 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · norm_num at hqb ⊢
        exact hqb
    have hpR : p ∈ closure (ball (0 : ℂ) R) := by
      rw [closure_ball 0 hR0.ne']
      rw [mem_closedBall, dist_zero_right, hp_norm]
      have hβR : (3 / 4 : ℝ) < R := by
        have hge : (7 / 8 : ℝ) ≤ R := by
          dsimp [R]
          have hqge := CoarseSchottky.paper_radius_ge hr0 hr1
          have hcast : (((7 / 8 : ℚ) : ℝ)) ≤ ((radius r : ℚ) : ℝ) :=
            Rat.cast_le.mpr hqge
          norm_num at hcast ⊢
          exact hcast
        linarith
      exact hsqrt.trans hβR.le
    have hpc : ‖fourFactorMap F p‖ ≤ ‖fourFactorMap F c‖ := hcmax hpR
    have hpval : fourFactorMap F p = 1 := by
      simpa [p] using fourFactorMap_at_sqrt_q hq hqb F
    have hone : (1 : ℝ) ≤ ‖fourFactorMap F c‖ := by
      simpa [hpval] using hpc
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hone

/-- The four transformed functions are uniformly bounded on the manuscript circle. -/
theorem fourFactors_circle_bound
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = (radius r : ℝ)) :
    ‖fourFactorMap F z‖ ≤ (largeBound r : ℝ) ∧
    ‖1 - fourFactorMap F z‖ ≤ (largeBound r : ℝ) ∧
    ‖(fourFactorMap F z)⁻¹‖ ≤ (largeBound r : ℝ) ∧
    ‖(1 - fourFactorMap F z)⁻¹‖ ≤ (largeBound r : ℝ) := by
  let R : ℝ := (radius r : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 7 / 8)
      (CoarseSchottky.paper_radius_ge hr0 hr1)
  have hR1 : R < 1 := by
    dsimp [R]
    exact_mod_cast CoarseSchottky.paper_radius_lt hr1
  obtain ⟨a, b, haR, hbR, hfa0, hfa1, hfaim, hfb0, hfbim⟩ :=
    fourFactorMap_real_anchors hq hR0 hR1 F
  obtain ⟨c, hcR, hcinv⟩ := fourFactorMap_inverse_anchor hq hqb F hr0 hr1
  have hfa_norm : ‖fourFactorMap F a‖ ≤ 1 := by
    rw [← Complex.abs_re_eq_norm.mpr hfaim, abs_of_pos hfa0]
    exact hfa1.le
  have hOneFaIm : (1 - fourFactorMap F a).im = 0 := by simp [hfaim]
  have hOneFaRe : 0 ≤ (1 - fourFactorMap F a).re := by simp; linarith
  have hOneFaNorm : ‖1 - fourFactorMap F a‖ ≤ 1 := by
    rw [← Complex.abs_re_eq_norm.mpr hOneFaIm, abs_of_nonneg hOneFaRe]
    simp
    exact hfa0.le
  have hOneFbIm : (1 - fourFactorMap F b).im = 0 := by simp [hfbim]
  have hOneFbRe : 1 ≤ (1 - fourFactorMap F b).re := by simp; linarith
  have hOneFbNorm : 1 ≤ ‖1 - fourFactorMap F b‖ := by
    rw [← Complex.abs_re_eq_norm.mpr hOneFbIm,
      abs_of_nonneg (le_trans (by norm_num) hOneFbRe)]
    exact hOneFbRe
  have hOneFbInv : ‖(1 - fourFactorMap F b)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hOneFbNorm
  have hdiff := transformedF_differentiableOn_annulus hq hqb F
  have homit := transformedF_omits_on_annulus hq hqb F
  have h0 := CoarseSchottky.omitted_values_chain_bound
    (hdiff (0 : Fin 4)) (fun w hwβ hw1 => homit (0 : Fin 4) hwβ hw1)
    hr0 hr1 haR hfa_norm hz
  have h1 := CoarseSchottky.omitted_values_chain_bound
    (hdiff (1 : Fin 4)) (fun w hwβ hw1 => homit (1 : Fin 4) hwβ hw1)
    hr0 hr1 haR hOneFaNorm hz
  have h2 := CoarseSchottky.omitted_values_chain_bound
    (hdiff (2 : Fin 4)) (fun w hwβ hw1 => homit (2 : Fin 4) hwβ hw1)
    hr0 hr1 hcR hcinv hz
  have h3 := CoarseSchottky.omitted_values_chain_bound
    (hdiff (3 : Fin 4)) (fun w hwβ hw1 => homit (3 : Fin 4) hwβ hw1)
    hr0 hr1 hbR hOneFbInv hz
  simpa [transformedF] using And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem factorEnvelope_le_factorBound (r : ℚ) :
    (((largeBound r : ℚ) *
      (1 / radius r + 1 / (radius r ^ 2 - Route1.PaperBounds.beta ^ 2) +
        radius r + radius r ^ 2 + Route1.PaperBounds.beta ^ 2) : ℚ) : ℝ) ≤
      (factorBound r : ℝ) := by
  have hq :
      (largeBound r : ℚ) *
        (1 / radius r + 1 / (radius r ^ 2 - Route1.PaperBounds.beta ^ 2) +
          radius r + radius r ^ 2 + Route1.PaperBounds.beta ^ 2) ≤
        (factorBound r : ℕ) := by
    exact Nat.le_ceil _
  have hcast :
      (((largeBound r : ℚ) *
        (1 / radius r + 1 / (radius r ^ 2 - Route1.PaperBounds.beta ^ 2) +
          radius r + radius r ^ 2 + Route1.PaperBounds.beta ^ 2) : ℚ) : ℝ) ≤
        (((factorBound r : ℕ) : ℚ) : ℝ) := Rat.cast_le.mpr hq
  norm_num at hcast ⊢
  exact hcast

theorem fourFactors_circle_factorBound
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = (radius r : ℝ)) :
    ‖F.u z‖ ≤ (factorBound r : ℝ) ∧
    ‖F.v z‖ ≤ (factorBound r : ℝ) ∧
    ‖F.uInv z‖ ≤ (factorBound r : ℝ) ∧
    ‖F.vInv z‖ ≤ (factorBound r : ℝ) := by
  let R : ℝ := (radius r : ℝ)
  let M : ℝ := (largeBound r : ℝ)
  let B : ℝ := (factorBound r : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 7 / 8)
      (CoarseSchottky.paper_radius_ge hr0 hr1)
  have hR1 : R < 1 := by
    dsimp [R]
    exact_mod_cast CoarseSchottky.paper_radius_lt hr1
  have hβR : (3 / 4 : ℝ) < R := by
    have hge : (7 / 8 : ℝ) ≤ R := by
      dsimp [R]
      have hqge := CoarseSchottky.paper_radius_ge hr0 hr1
      have hcast : (((7 / 8 : ℚ) : ℝ)) ≤ ((radius r : ℚ) : ℝ) :=
        Rat.cast_le.mpr hqge
      norm_num at hcast ⊢
      exact hcast
    linarith
  have hd0 : 0 < R ^ 2 - (3 / 4 : ℝ) ^ 2 := by nlinarith
  have hM0 : 0 ≤ M := by positivity
  have hsum :
      M * (1 / R + 1 / (R ^ 2 - (3 / 4 : ℝ) ^ 2) + R + R ^ 2 +
        (3 / 4 : ℝ) ^ 2) ≤ B := by
    have he := factorEnvelope_le_factorBound r
    norm_num [R, M, B, Route1.PaperBounds.beta] at he ⊢
    exact he
  have hzD : z ∈ unitDisc := by
    rw [unitDisc, mem_ball, dist_zero_right, hz]
    exact hR1
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact hR0.ne')
  obtain ⟨hf, hOneF, hfInv, hOneFInv⟩ :=
    fourFactors_circle_bound hq hqb F hr0 hr1 hz
  have huTerm : ‖F.u z‖ ≤ M * (1 / R) := by
    rw [fourFactorMap, norm_mul, hz] at hf
    have ht : ‖F.u z‖ * R ≤ M := by simpa [R, M, mul_comm] using hf
    have hdiv : ‖F.u z‖ ≤ M / R := (le_div_iff₀ hR0).2 ht
    simpa [div_eq_mul_inv] using hdiv
  have hdenLower : R ^ 2 - q ≤ ‖z ^ 2 + (q : ℂ)‖ := by
    have ht := norm_sub_le (z ^ 2 + (q : ℂ)) (q : ℂ)
    have hqnorm : ‖(q : ℂ)‖ = q := by simp [abs_of_pos hq]
    rw [add_sub_cancel_right, norm_pow, hz, hqnorm] at ht
    linarith
  have hdenPos : 0 < ‖z ^ 2 + (q : ℂ)‖ := by
    have : 0 < R ^ 2 - q := by nlinarith
    linarith
  have hden0 : z ^ 2 + (q : ℂ) ≠ 0 := norm_ne_zero_iff.mp hdenPos.ne'
  have hvTerm : ‖F.v z‖ ≤ M * (1 / (R ^ 2 - (3 / 4 : ℝ) ^ 2)) := by
    have hlin := F.linear z hzD
    have hrel : (z ^ 2 + (q : ℂ)) * F.v z = 1 - fourFactorMap F z := by
      rw [fourFactorMap]
      linear_combination hlin
    have hprod : ‖z ^ 2 + (q : ℂ)‖ * ‖F.v z‖ ≤ M := by
      rw [← norm_mul, hrel]
      exact hOneF
    have hlower : R ^ 2 - (3 / 4 : ℝ) ^ 2 ≤ ‖z ^ 2 + (q : ℂ)‖ := by
      norm_num at hqb
      exact le_trans (by nlinarith) hdenLower
    have hmul : ‖F.v z‖ * (R ^ 2 - (3 / 4 : ℝ) ^ 2) ≤ M := by
      calc
      ‖F.v z‖ * (R ^ 2 - (3 / 4 : ℝ) ^ 2) ≤
          ‖F.v z‖ * ‖z ^ 2 + (q : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hlower (norm_nonneg _)
      _ ≤ M := by simpa [mul_comm] using hprod
    have hdiv : ‖F.v z‖ ≤ M / (R ^ 2 - (3 / 4 : ℝ) ^ 2) :=
      (le_div_iff₀ hd0).2 hmul
    simpa [div_eq_mul_inv] using hdiv
  have huInvId : F.uInv z = z * (fourFactorMap F z)⁻¹ := by
    have hu0 := fourFactors_u_ne_zero F hzD
    have hi := F.inverse_u z hzD
    have hiu : F.uInv z = (F.u z)⁻¹ :=
      ((mul_eq_one_iff_inv_eq₀ hu0).mp hi).symm
    rw [hiu, fourFactorMap, mul_inv_rev]
    field_simp
  have huInvTerm : ‖F.uInv z‖ ≤ M * R := by
    rw [huInvId, norm_mul, hz]
    nlinarith
  have hdenUpper : ‖z ^ 2 + (q : ℂ)‖ ≤ R ^ 2 + (3 / 4 : ℝ) ^ 2 := by
    calc
      ‖z ^ 2 + (q : ℂ)‖ ≤ ‖z ^ 2‖ + ‖(q : ℂ)‖ := norm_add_le _ _
      _ = R ^ 2 + q := by simp [norm_pow, hz, abs_of_pos hq, R]
      _ ≤ R ^ 2 + (3 / 4 : ℝ) ^ 2 := by nlinarith
  have hvInvId : F.vInv z = (z ^ 2 + (q : ℂ)) * (1 - fourFactorMap F z)⁻¹ := by
    have hv0 := fourFactors_v_ne_zero F hzD
    have hi := F.inverse_v z hzD
    have hiv : F.vInv z = (F.v z)⁻¹ :=
      ((mul_eq_one_iff_inv_eq₀ hv0).mp hi).symm
    have hlin := F.linear z hzD
    have hrel : 1 - fourFactorMap F z = (z ^ 2 + (q : ℂ)) * F.v z := by
      have hrel' : (z ^ 2 + (q : ℂ)) * F.v z = 1 - fourFactorMap F z := by
        rw [fourFactorMap]
        linear_combination hlin
      exact hrel'.symm
    rw [hiv, hrel, mul_inv_rev]
    field_simp [hden0]
  have hvInvTerm : ‖F.vInv z‖ ≤ M * (R ^ 2 + (3 / 4 : ℝ) ^ 2) := by
    rw [hvInvId, norm_mul]
    calc
      ‖z ^ 2 + (q : ℂ)‖ * ‖(1 - fourFactorMap F z)⁻¹‖ ≤
          (R ^ 2 + (3 / 4 : ℝ) ^ 2) * M :=
        mul_le_mul hdenUpper hOneFInv (norm_nonneg _) (by positivity)
      _ = M * (R ^ 2 + (3 / 4 : ℝ) ^ 2) := by ring
  have hInvR0 : 0 ≤ 1 / R := (one_div_pos.mpr hR0).le
  have hInvD0 : 0 ≤ 1 / (R ^ 2 - (3 / 4 : ℝ) ^ 2) :=
    (one_div_pos.mpr hd0).le
  have hRnonneg : 0 ≤ R := hR0.le
  have hsqnonneg : 0 ≤ R ^ 2 := sq_nonneg R
  have hβsqnonneg : 0 ≤ (3 / 4 : ℝ) ^ 2 := sq_nonneg _
  constructor
  · exact huTerm.trans ((mul_le_mul_of_nonneg_left (by nlinarith) hM0).trans hsum)
  constructor
  · exact hvTerm.trans ((mul_le_mul_of_nonneg_left (by nlinarith) hM0).trans hsum)
  constructor
  · exact huInvTerm.trans ((mul_le_mul_of_nonneg_left (by nlinarith) hM0).trans hsum)
  · exact hvInvTerm.trans ((mul_le_mul_of_nonneg_left (by nlinarith) hM0).trans hsum)

/-- The explicit witness-independent and truncation-independent four-factor bound. -/
theorem fourFactors_schottky_bound
    {q : ℝ} (hq : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ (r : ℝ)) :
    ‖F.u z‖ ≤ (factorBound r : ℝ) ∧
    ‖F.v z‖ ≤ (factorBound r : ℝ) ∧
    ‖F.uInv z‖ ≤ (factorBound r : ℝ) ∧
    ‖F.vInv z‖ ≤ (factorBound r : ℝ) := by
  let R : ℝ := (radius r : ℝ)
  have hR0 : 0 < R := by
    dsimp [R]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 7 / 8)
      (CoarseSchottky.paper_radius_ge hr0 hr1)
  have hR1 : R < 1 := by
    dsimp [R]
    exact_mod_cast CoarseSchottky.paper_radius_lt hr1
  have hrR_q : r ≤ radius r := by
    rw [radius]
    have hm : r ≤ max r Route1.PaperBounds.beta := le_max_left _ _
    linarith
  have hrR : (r : ℝ) ≤ R := by
    dsimp [R]
    exact_mod_cast hrR_q
  have hclosed : closedBall (0 : ℂ) R ⊆ unitDisc := by
    intro w hw
    rw [unitDisc, mem_ball, dist_zero_right]
    have hwR : ‖w‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hw
    exact hwR.trans_lt hR1
  have hzcl : z ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR0.ne', mem_closedBall, dist_zero_right]
    exact hz.trans hrR
  have hboundary (G : ℂ → ℂ)
      (hG : DifferentiableOn ℂ G unitDisc)
      (hcircle : ∀ w : ℂ, ‖w‖ = R → ‖G w‖ ≤ (factorBound r : ℝ)) :
      ‖G z‖ ≤ (factorBound r : ℝ) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hG.diffContOnCl_ball hclosed) _ hzcl
    intro w hw
    rw [frontier_ball 0 hR0.ne'] at hw
    apply hcircle w
    simpa [mem_sphere, dist_zero_right] using hw
  have hcu (w : ℂ) (hw : ‖w‖ = R) : ‖F.u w‖ ≤ (factorBound r : ℝ) :=
    (fourFactors_circle_factorBound hq hqb F hr0 hr1 (by simpa [R] using hw)).1
  have hcv (w : ℂ) (hw : ‖w‖ = R) : ‖F.v w‖ ≤ (factorBound r : ℝ) :=
    (fourFactors_circle_factorBound hq hqb F hr0 hr1 (by simpa [R] using hw)).2.1
  have hcuInv (w : ℂ) (hw : ‖w‖ = R) : ‖F.uInv w‖ ≤ (factorBound r : ℝ) :=
    (fourFactors_circle_factorBound hq hqb F hr0 hr1 (by simpa [R] using hw)).2.2.1
  have hcvInv (w : ℂ) (hw : ‖w‖ = R) : ‖F.vInv w‖ ≤ (factorBound r : ℝ) :=
    (fourFactors_circle_factorBound hq hqb F hr0 hr1 (by simpa [R] using hw)).2.2.2
  exact ⟨hboundary F.u F.holSymm_u.1 hcu,
    hboundary F.v F.holSymm_v.1 hcv,
    hboundary F.uInv F.holSymm_uInv.1 hcuInv,
    hboundary F.vInv F.holSymm_vInv.1 hcvInv⟩

end
end Schottky
end BelgianChocolate
