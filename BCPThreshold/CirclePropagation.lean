import BCPThreshold.CoarseSchottkyBound
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Metric Set

namespace BelgianChocolate
namespace CoarseSchottky

noncomputable section

/-- The normalized second cosine lift is uniformly bounded on the closed
`12/31`-disc.  This is the smaller-radius version needed by the moving-anchor
argument. -/
theorem second_lift_norm_le_1574_div_19
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hg0 : ‖g 0‖ < 2)
    (hgderiv : ∀ w ∈ ball (0 : ℂ) 1,
      ‖deriv g w‖ ≤ 128 / (1 - ‖w‖))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (12 / 31 : ℝ)) :
    ‖g z‖ ≤ (1574 / 19 : ℝ) := by
  have hsub : closedBall (0 : ℂ) (12 / 31 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    rw [mem_ball, dist_zero_right]
    norm_num at hw ⊢
    linarith
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) (12 / 31 : ℝ),
      DifferentiableAt ℂ g w := by
    intro w hw
    exact hg.differentiableAt (isOpen_ball.mem_nhds (hsub hw))
  have hfderiv : ∀ w ∈ closedBall (0 : ℂ) (12 / 31 : ℝ),
      ‖fderiv ℂ g w‖ ≤ (3968 / 19 : ℝ) := by
    intro w hw
    have hwnorm : ‖w‖ ≤ (12 / 31 : ℝ) := by
      simpa [mem_closedBall, dist_zero_right] using hw
    have hd := hgderiv w (hsub hw)
    rw [← norm_deriv_eq_norm_fderiv]
    have hden : (19 / 31 : ℝ) ≤ 1 - ‖w‖ := by linarith
    have hdenpos : 0 < 1 - ‖w‖ := lt_of_lt_of_le (by norm_num) hden
    calc
      ‖deriv g w‖ ≤ 128 / (1 - ‖w‖) := hd
      _ ≤ 3968 / 19 := by
        apply (div_le_iff₀ hdenpos).2
        nlinarith
  have hmv :=
    (convex_closedBall (0 : ℂ) (12 / 31 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      hdiff hfderiv (mem_closedBall_self (by norm_num)) hz
  have hzNorm : ‖z‖ ≤ (12 / 31 : ℝ) := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hgzsub : ‖g z - g 0‖ ≤ (1536 / 19 : ℝ) := by
    calc
      ‖g z - g 0‖ ≤ (3968 / 19 : ℝ) * ‖z - 0‖ := hmv
      _ ≤ 1536 / 19 := by
        rw [sub_zero]
        nlinarith
  calc
    ‖g z‖ ≤ ‖g z - g 0‖ + ‖g 0‖ := by
      have := norm_add_le (g z - g 0) (g 0)
      simpa using this
    _ ≤ 1574 / 19 := by linarith

/-- Direct transcendental form of the small-disc estimate. -/
theorem coarse_schottky_twelve_thirtyone_exp
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (homit : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ f z ≠ 1)
    (hf0 : ‖f 0‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ (12 / 31 : ℝ)) :
    ‖f z‖ ≤ Real.exp (Real.pi * Real.exp (Real.pi * (1574 / 19))) := by
  obtain ⟨h, g, hh, hg, hg0, hfh, hhg, hgderiv⟩ :=
    exists_double_cosine_lift_with_deriv_bound hf homit hf0
  have hzClosed : z ∈ closedBall (0 : ℂ) (12 / 31 : ℝ) := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hgBound : ‖g z‖ ≤ (1574 / 19 : ℝ) :=
    second_lift_norm_le_1574_div_19 hg hg0 hgderiv hzClosed
  have hzBall : z ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_zero_right] using lt_of_le_of_lt hz (by norm_num)
  have hhNorm : ‖h z‖ ≤ Real.exp (Real.pi * (1574 / 19)) := by
    rw [hhg z hzBall]
    calc
      ‖Complex.cos ((Real.pi : ℂ) * g z)‖ ≤
          Real.exp ‖(Real.pi : ℂ) * g z‖ := norm_cos_le_exp_norm _
      _ ≤ Real.exp (Real.pi * (1574 / 19)) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        exact mul_le_mul_of_nonneg_left hgBound Real.pi_pos.le
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * h z)‖ ≤
      Real.exp (Real.pi * Real.exp (Real.pi * (1574 / 19))) := by
    calc
      ‖Complex.cos ((Real.pi : ℂ) * h z)‖ ≤
          Real.exp ‖(Real.pi : ℂ) * h z‖ := norm_cos_le_exp_norm _
      _ ≤ Real.exp (Real.pi * Real.exp (Real.pi * (1574 / 19))) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        exact mul_le_mul_of_nonneg_left hhNorm Real.pi_pos.le
  have hfFormula : f z = (Complex.cos ((Real.pi : ℂ) * h z) + 1) / 2 := by
    have hr := hfh z hzBall
    apply_fun (fun w : ℂ ↦ (w + 1) / 2) at hr
    simpa using hr
  rw [hfFormula, norm_div]
  norm_num
  have hEone : 1 ≤ Real.exp (Real.pi * Real.exp (Real.pi * (1574 / 19))) :=
    Real.one_le_exp (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
  calc
    ‖Complex.cos ((Real.pi : ℂ) * h z) + 1‖ / 2 ≤
        (‖Complex.cos ((Real.pi : ℂ) * h z)‖ + 1) / 2 := by
      gcongr
      simpa using norm_add_le (Complex.cos ((Real.pi : ℂ) * h z)) 1
    _ ≤ Real.exp (Real.pi * Real.exp (Real.pi * (1574 / 19))) := by
      nlinarith

/-- Explicit absolute Schottky bound on the radius `12/31` disc. -/
theorem coarse_schottky_twelve_thirtyone
    {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) 1))
    (homit : ∀ w ∈ ball (0 : ℂ) 1, H w ≠ 0 ∧ H w ≠ 1)
    (h0 : ‖H 0‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ (12 / 31 : ℝ)) :
    ‖H z‖ ≤ (3 : ℝ) ^ (4 * 3 ^ 261 : ℕ) := by
  have htrans := coarse_schottky_twelve_thirtyone_exp hH homit h0 hz
  have hpi : Real.pi < (63 / 20 : ℝ) := by
    have hp := Real.pi_lt_d2
    norm_num at hp ⊢
    exact hp
  have hinnerArg : Real.pi * (1574 / 19) < (261 : ℝ) := by
    nlinarith
  have hinner : Real.exp (Real.pi * (1574 / 19)) < (3 : ℝ) ^ (261 : ℕ) :=
    exp_lt_three_pow_of_lt_nat hinnerArg
  have houterArg :
      Real.pi * Real.exp (Real.pi * (1574 / 19)) < (4 * 3 ^ 261 : ℕ) := by
    have hp4 : Real.pi < 4 := Real.pi_lt_four
    have hm := mul_lt_mul hp4 hinner.le (Real.exp_pos _)
      (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at hm ⊢
    exact hm
  exact htrans.trans (exp_lt_three_pow_of_lt_nat houterArg).le

/-- The elementary automorphism of the unit disc that sends `0` to `p`. -/
def discMove (p ξ : ℂ) : ℂ := (p + ξ) / (1 + star p * ξ)

/-- The parameter whose image under `discMove p` is `q`. -/
def discMoveParameter (p q : ℂ) : ℂ := (q - p) / (1 - star p * q)

theorem discMove_mapsTo_ball {p : ℂ} (hp : ‖p‖ ≤ (1 / 4 : ℝ)) :
    MapsTo (discMove p) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro ξ hξ
  have hξn : ‖ξ‖ < 1 := by simpa [mem_ball, dist_zero_right] using hξ
  have hpid :
      Complex.normSq (1 + star p * ξ) - Complex.normSq (p + ξ) =
        (1 - Complex.normSq p) * (1 - Complex.normSq ξ) := by
    simp [Complex.normSq_add, Complex.normSq_mul]
    ring
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hpid
  have hpSq : ‖p‖ ^ 2 < 1 := by nlinarith [norm_nonneg p]
  have hξSq : ‖ξ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ξ]
  have hsq : ‖p + ξ‖ ^ 2 < ‖1 + star p * ξ‖ ^ 2 := by nlinarith
  have hnorm : ‖p + ξ‖ < ‖1 + star p * ξ‖ := by
    nlinarith [norm_nonneg (p + ξ), norm_nonneg (1 + star p * ξ)]
  have hden : 1 + star p * ξ ≠ 0 := by
    intro he
    rw [he, norm_zero] at hnorm
    exact (not_lt_of_ge (norm_nonneg _)) hnorm
  rw [mem_ball, dist_zero_right, discMove, norm_div,
    div_lt_one (norm_pos_iff.mpr hden)]
  exact hnorm

theorem differentiableOn_discMove {p : ℂ} (hp : ‖p‖ ≤ (1 / 4 : ℝ)) :
    DifferentiableOn ℂ (discMove p) (ball (0 : ℂ) 1) := by
  have hne : ∀ ξ ∈ ball (0 : ℂ) 1, 1 + star p * ξ ≠ 0 := by
    intro ξ hξ he
    have hξn : ‖ξ‖ < 1 := by simpa [mem_ball, dist_zero_right] using hξ
    have hm : ‖star p * ξ‖ < 1 := by
      rw [norm_mul, norm_star]
      nlinarith [norm_nonneg p, norm_nonneg ξ]
    have he' : star p * ξ = -1 := by linear_combination he
    rw [he', norm_neg, norm_one] at hm
    exact (lt_irrefl 1) hm
  change DifferentiableOn ℂ (fun ξ : ℂ => (p + ξ) / (1 + star p * ξ))
    (ball (0 : ℂ) 1)
  fun_prop

@[simp] theorem discMove_zero (p : ℂ) : discMove p 0 = p := by
  simp [discMove]

theorem discMoveParameter_norm_le
    {p q : ℂ} (hp : ‖p‖ ≤ (1 / 4 : ℝ)) (hq : ‖q‖ ≤ (1 / 8 : ℝ)) :
    ‖discMoveParameter p q‖ ≤ (12 / 31 : ℝ) := by
  have hnum : ‖q - p‖ ≤ (3 / 8 : ℝ) := by
    calc
      ‖q - p‖ ≤ ‖q‖ + ‖p‖ := norm_sub_le q p
      _ ≤ 3 / 8 := by linarith
  have hprod : ‖star p * q‖ ≤ (1 / 32 : ℝ) := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg p, norm_nonneg q]
  rw [norm_mul, norm_star] at hprod
  have hdenLower : (31 / 32 : ℝ) ≤ ‖1 - star p * q‖ := by
    have ht := norm_add_le (1 - star p * q) (star p * q)
    have hone : ‖(1 : ℂ)‖ ≤ ‖1 - star p * q‖ + ‖star p * q‖ := by
      simpa using ht
    norm_num only [norm_one] at hone
    rw [norm_mul, norm_star] at hone
    linarith
  have hdenPos : 0 < ‖1 - star p * q‖ := lt_of_lt_of_le (by norm_num) hdenLower
  rw [discMoveParameter, norm_div]
  calc
    ‖q - p‖ / ‖1 - star p * q‖ ≤ (3 / 8 : ℝ) / (31 / 32) := by
      gcongr
    _ = 12 / 31 := by norm_num

theorem discMove_parameter_image
    {p q : ℂ} (hp : ‖p‖ ≤ (1 / 4 : ℝ)) (hq : ‖q‖ ≤ (1 / 8 : ℝ)) :
    discMove p (discMoveParameter p q) = q := by
  have hprod : ‖star p * q‖ < 1 := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg p, norm_nonneg q]
  have hden : 1 - star p * q ≠ 0 := by
    intro he
    have he' : star p * q = 1 := (sub_eq_zero.mp he).symm
    rw [he', norm_one] at hprod
    exact (lt_irrefl 1) hprod
  have hnormSq : Complex.normSq p < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg p]
  have hdenFormula :
      1 + star p * discMoveParameter p q =
        ((1 - Complex.normSq p : ℝ) : ℂ) / (1 - star p * q) := by
    rw [discMoveParameter]
    push_cast
    field_simp
    rw [Complex.normSq_eq_conj_mul_self]
    ring_nf
    simp [mul_comm]
  have hden2 : 1 + star p * discMoveParameter p q ≠ 0 := by
    rw [hdenFormula]
    exact div_ne_zero (by
      exact_mod_cast (sub_ne_zero.mpr (ne_of_lt hnormSq).symm)) hden
  have hden' : 1 - q * star p ≠ 0 := by simpa [mul_comm] using hden
  rw [discMove, div_eq_iff hden2, discMoveParameter]
  field_simp [hden']
  ring

/-- A small anchor anywhere in the quarter-disc controls every point of the
eighth-disc by the absolute Schottky constant. -/
theorem omitted_values_near_anchor
    {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (homit : ∀ w ∈ ball (0 : ℂ) 1, F w ≠ 0 ∧ F w ≠ 1)
    {p q : ℂ}
    (hp : ‖p‖ ≤ (1 / 4 : ℝ))
    (hq : ‖q‖ ≤ (1 / 8 : ℝ))
    (hFp : ‖F p‖ ≤ 1) :
    ‖F q‖ ≤ (3 : ℝ) ^ (4 * 3 ^ 261 : ℕ) := by
  let T : ℂ → ℂ := discMove p
  let G : ℂ → ℂ := F ∘ T
  have hTmap := discMove_mapsTo_ball hp
  have hTdiff := differentiableOn_discMove hp
  have hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := hF.comp hTdiff hTmap
  have hGomit : ∀ ξ ∈ ball (0 : ℂ) 1, G ξ ≠ 0 ∧ G ξ ≠ 1 := by
    intro ξ hξ
    exact homit (T ξ) (hTmap hξ)
  have hG0 : ‖G 0‖ ≤ 1 := by simpa [G, T] using hFp
  let η := discMoveParameter p q
  have hη : ‖η‖ ≤ (12 / 31 : ℝ) := discMoveParameter_norm_le hp hq
  have hbound := coarse_schottky_twelve_thirtyone hG hGomit hG0 hη
  have himage : T η = q := by
    simpa [T, η] using discMove_parameter_image hp hq
  simpa [G, himage] using hbound

/-- A positive-real-part holomorphic function on a disc satisfies the coarse
Harnack estimate needed here.  The proof is the Schwarz lemma applied to its
Cayley transform. -/
theorem re_le_three_mul_re_center
    {U : ℂ → ℂ} {c : ℂ} {s : ℝ}
    (hs : 0 < s)
    (hU : DifferentiableOn ℂ U (ball c s))
    (hpos : ∀ w ∈ ball c s, 0 < (U w).re)
    (hcenter : (U c).im = 0)
    {z : ℂ} (hz : ‖z - c‖ ≤ s / 2) :
    (U z).re ≤ 3 * (U c).re := by
  let a : ℝ := (U c).re
  have hc : c ∈ ball c s := mem_ball_self hs
  have ha : 0 < a := hpos c hc
  have hUc : U c = (a : ℂ) := by
    apply Complex.ext
    · simp [a]
    · simpa [a] using hcenter
  let W : ℂ → ℂ := fun w => (U w - (a : ℂ)) / (U w + (a : ℂ))
  have hden : ∀ w ∈ ball c s, U w + (a : ℂ) ≠ 0 := by
    intro w hw he
    have hre := congrArg Complex.re he
    simp only [map_add, Complex.add_re, Complex.ofReal_re, map_zero,
      Complex.zero_re] at hre
    nlinarith [hpos w hw]
  have hW : DifferentiableOn ℂ W (ball c s) := by
    dsimp [W]
    fun_prop
  have hWc : W c = 0 := by simp [W, hUc, ha.ne']
  have hWmap : MapsTo W (ball c s) (closedBall (W c) 1) := by
    intro w hw
    have hident :
        Complex.normSq (U w + (a : ℂ)) - Complex.normSq (U w - (a : ℂ)) =
          4 * a * (U w).re := by
      simp [Complex.normSq_add, Complex.normSq_sub]
      ring
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hident
    have hsquare : ‖U w - (a : ℂ)‖ ^ 2 < ‖U w + (a : ℂ)‖ ^ 2 := by
      nlinarith [hpos w hw]
    have hnorm : ‖U w - (a : ℂ)‖ < ‖U w + (a : ℂ)‖ := by
      nlinarith [norm_nonneg (U w - (a : ℂ)), norm_nonneg (U w + (a : ℂ))]
    have hdpos : 0 < ‖U w + (a : ℂ)‖ := norm_pos_iff.mpr (hden w hw)
    rw [mem_closedBall, hWc, dist_zero_right]
    change ‖(U w - (a : ℂ)) / (U w + (a : ℂ))‖ ≤ 1
    rw [norm_div]
    exact (div_lt_one hdpos).mpr hnorm |>.le
  have hzBall : z ∈ ball c s := by
    rw [mem_ball, dist_eq_norm]
    nlinarith
  have hschwarz :=
    Complex.dist_le_div_mul_dist_of_mapsTo_ball hW hWmap hzBall
  rw [hWc, dist_zero_right] at hschwarz
  change ‖(U z - (a : ℂ)) / (U z + (a : ℂ))‖ ≤
    1 / s * dist z c at hschwarz
  rw [norm_div, div_eq_mul_inv] at hschwarz
  have hWz : ‖U z - (a : ℂ)‖ / ‖U z + (a : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    rw [div_eq_mul_inv]
    calc
      ‖U z - (a : ℂ)‖ * ‖U z + (a : ℂ)‖⁻¹ ≤
          1 * s⁻¹ * ‖z - c‖ := by simpa [dist_eq_norm] using hschwarz
      _ ≤ 1 / 2 := by
        rw [one_mul]
        have hsne : s ≠ 0 := ne_of_gt hs
        rw [inv_mul_eq_div, div_le_iff₀ hs]
        nlinarith
  have hzden : U z + (a : ℂ) ≠ 0 := hden z hzBall
  have hzdenPos : 0 < ‖U z + (a : ℂ)‖ := norm_pos_iff.mpr hzden
  have hsub : ‖U z - (a : ℂ)‖ ≤ (1 / 2 : ℝ) * ‖U z + (a : ℂ)‖ := by
    exact (div_le_iff₀ hzdenPos).mp hWz
  have hplus : ‖U z + (a : ℂ)‖ ≤ ‖U z - (a : ℂ)‖ + 2 * a := by
    have ht := norm_add_le (U z - (a : ℂ)) ((2 * a : ℝ) : ℂ)
    have heq : U z - (a : ℂ) + ((2 * a : ℝ) : ℂ) = U z + (a : ℂ) := by
      push_cast
      ring
    rw [heq] at ht
    simpa [Real.norm_eq_abs, abs_of_pos ha, abs_of_nonneg ha.le] using ht
  have hdist : ‖U z - (a : ℂ)‖ ≤ 2 * a := by nlinarith
  have hre : (U z).re - a ≤ ‖U z - (a : ℂ)‖ := by
    have := Complex.re_le_norm (U z - (a : ℂ))
    simpa using this
  dsimp [a] at ha ⊢
  nlinarith

/-- If the modulus is everywhere greater than one on a disc, a holomorphic
logarithm and the preceding Schwarz estimate give cubic growth from the
centre. -/
theorem norm_le_center_cube_of_one_lt
    {H : ℂ → ℂ} {c : ℂ} {s : ℝ}
    (hs : 0 < s)
    (hH : DifferentiableOn ℂ H (ball c s))
    (hlarge : ∀ w ∈ ball c s, 1 < ‖H w‖)
    {z : ℂ} (hz : ‖z - c‖ ≤ s / 2) :
    ‖H z‖ ≤ ‖H c‖ ^ 3 := by
  let S : Set ℂ := ball c s
  have hSne : S.Nonempty := ⟨c, by simp [S, hs]⟩
  have hSconv : Convex ℝ S := convex_ball c s
  letI : ContractibleSpace S := hSconv.contractibleSpace hSne
  have hSsc : IsSimplyConnected S := by
    change SimplyConnectedSpace S
    infer_instance
  have hzero : ∀ w ∈ S, H w ≠ 0 := by
    intro w hw he
    have := hlarge w hw
    simp [he] at this
    linarith
  obtain ⟨ell, hell, hexp⟩ :=
    HolomorphicLift.exists_differentiableOn_log isOpen_ball hSsc hH hzero
  let U : ℂ → ℂ := fun w => ell w - (ell c).im * Complex.I
  have hU : DifferentiableOn ℂ U S := by
    dsimp [U]
    fun_prop
  have hUpos : ∀ w ∈ S, 0 < (U w).re := by
    intro w hw
    have hwlarge := hlarge w hw
    have hwe := hexp hw
    have hnorm : ‖H w‖ = Real.exp (ell w).re := by
      rw [← hwe]
      exact Complex.norm_exp _
    rw [hnorm] at hwlarge
    have hellpos : 0 < (ell w).re := Real.one_lt_exp_iff.mp hwlarge
    simpa [U] using hellpos
  have hUcenter : (U c).im = 0 := by simp [U]
  have hzU : (U z).re ≤ 3 * (U c).re :=
    re_le_three_mul_re_center hs hU hUpos hUcenter hz
  have hzBall : z ∈ S := by
    change z ∈ ball c s
    rw [mem_ball, dist_eq_norm]
    nlinarith
  have hcBall : c ∈ S := by simp [S, hs]
  have hzexp : Complex.exp (ell z) = H z := by simpa using hexp hzBall
  have hcexp : Complex.exp (ell c) = H c := by simpa using hexp hcBall
  rw [← hzexp, ← hcexp, Complex.norm_exp, Complex.norm_exp]
  have hre : (ell z).re ≤ 3 * (ell c).re := by simpa [U] using hzU
  calc
    Real.exp (ell z).re ≤ Real.exp (3 * (ell c).re) := Real.exp_le_exp.mpr hre
    _ = Real.exp (ell c).re ^ 3 := by
      simpa [mul_comm] using Real.exp_nat_mul (ell c).re 3

/-- The local recurrence used by the circle chain.  It is uniform in the
function and uses an absolute bound only when a nearby small-value anchor
exists; otherwise the logarithmic Schwarz estimate gives cubic growth. -/
theorem omitted_values_collar_step
    {H : ℂ → ℂ} {c z : ℂ} {d : ℝ}
    (hd : 0 < d)
    (hH : DifferentiableOn ℂ H (ball c (2 * d)))
    (homit : ∀ w ∈ ball c (2 * d), H w ≠ 0 ∧ H w ≠ 1)
    (hz : ‖z - c‖ ≤ d / 4) :
    ‖H z‖ ≤ max ((3 : ℝ) ^ (4 * 3 ^ 261 : ℕ))
      ((max 1 ‖H c‖) ^ 3) := by
  by_cases hsmall : ∃ w ∈ ball c (d / 2), ‖H w‖ ≤ 1
  · obtain ⟨w, hw, hHw⟩ := hsmall
    let F : ℂ → ℂ := fun ξ => H (c + (2 * d : ℝ) * ξ)
    let p : ℂ := (w - c) / (2 * d : ℝ)
    let q : ℂ := (z - c) / (2 * d : ℝ)
    have hmap : MapsTo (fun ξ : ℂ => c + (2 * d : ℝ) * ξ)
        (ball (0 : ℂ) 1) (ball c (2 * d)) := by
      intro ξ hξ
      have hξn : ‖ξ‖ < 1 := by simpa [mem_ball, dist_zero_right] using hξ
      rw [mem_ball, dist_eq_norm]
      have h2d : (0 : ℝ) < 2 * d := by positivity
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h2d.le]
      nlinarith
    have hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
      apply hH.comp
      · fun_prop
      · exact hmap
    have hFomit : ∀ ξ ∈ ball (0 : ℂ) 1, F ξ ≠ 0 ∧ F ξ ≠ 1 := by
      intro ξ hξ
      exact homit _ (hmap hξ)
    have hp : ‖p‖ ≤ (1 / 4 : ℝ) := by
      have hwn : ‖w - c‖ < d / 2 := by simpa [mem_ball, dist_eq_norm] using hw
      have h2d : (0 : ℝ) < 2 * d := by positivity
      dsimp [p]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h2d.le]
      apply le_of_lt
      rw [div_lt_iff₀ h2d]
      nlinarith
    have hq : ‖q‖ ≤ (1 / 8 : ℝ) := by
      have h2d : (0 : ℝ) < 2 * d := by positivity
      dsimp [q]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h2d.le]
      rw [div_le_iff₀ h2d]
      nlinarith
    have hFp : F p = H w := by
      dsimp [F, p]
      push_cast
      have hd' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
      field_simp [hd']
      ring
    have hFq : F q = H z := by
      dsimp [F, q]
      push_cast
      have hd' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
      field_simp [hd']
      ring
    have habs := omitted_values_near_anchor hF hFomit hp hq (by simpa [hFp] using hHw)
    rw [hFq] at habs
    exact habs.trans (le_max_left _ _)
  · have hlarge : ∀ w ∈ ball c (d / 2), 1 < ‖H w‖ := by
      intro w hw
      have hnle : ¬ ‖H w‖ ≤ 1 := by
        intro hle
        exact hsmall ⟨w, hw, hle⟩
      exact lt_of_not_ge hnle
    have hcube : ‖H z‖ ≤ ‖H c‖ ^ 3 := by
      have hHsmall : DifferentiableOn ℂ H (ball c (d / 2)) := hH.mono (by
        intro w hw
        have hwn : ‖w - c‖ < d / 2 := by simpa [mem_ball, dist_eq_norm] using hw
        rw [mem_ball, dist_eq_norm]
        nlinarith)
      exact norm_le_center_cube_of_one_lt (s := d / 2) (by positivity)
        hHsmall hlarge (by convert hz using 1 <;> ring)
    calc
      ‖H z‖ ≤ ‖H c‖ ^ 3 := hcube
      _ ≤ (max 1 ‖H c‖) ^ 3 := by
        gcongr
        exact le_max_right _ _
      _ ≤ max ((3 : ℝ) ^ (4 * 3 ^ 261 : ℕ)) ((max 1 ‖H c‖) ^ 3) :=
        le_max_right _ _

/-- The absolute constant and a deliberately loose closed-form envelope for
the max-cubic recurrence. -/
def propagationConstant : ℝ := (3 : ℝ) ^ (4 * 3 ^ 261 : ℕ)

def propagationEnvelope (k : ℕ) : ℝ :=
  (3 : ℝ) ^ (4 * 3 ^ (261 + k) : ℕ)

theorem propagationEnvelope_one_le (k : ℕ) : 1 ≤ propagationEnvelope k := by
  exact one_le_pow₀ (by norm_num)

theorem propagationConstant_le_envelope (k : ℕ) :
    propagationConstant ≤ propagationEnvelope k := by
  unfold propagationConstant propagationEnvelope
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) (by omega))

theorem propagationEnvelope_cube (k : ℕ) :
    propagationEnvelope k ^ 3 = propagationEnvelope (k + 1) := by
  unfold propagationEnvelope
  rw [← pow_mul]
  congr 1
  have he : 261 + (k + 1) = (261 + k) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem propagationEnvelope_step (k : ℕ) :
    max propagationConstant ((max 1 (propagationEnvelope k)) ^ 3) ≤
      propagationEnvelope (k + 1) := by
  rw [max_eq_right (propagationEnvelope_one_le k), propagationEnvelope_cube]
  exact max_le (propagationConstant_le_envelope (k + 1)) le_rfl

/-- Finite induction for values satisfying the new local recurrence. -/
theorem max_cubic_chain_bound (x : ℕ → ℝ) {K : ℕ} (h0 : x 0 ≤ 1)
    (hs : ∀ k < K, x (k + 1) ≤
      max propagationConstant ((max 1 (x k)) ^ 3)) :
    x K ≤ propagationEnvelope K := by
  have haux : ∀ k ≤ K, x k ≤ propagationEnvelope k := by
    intro k hk
    induction k with
    | zero => exact h0.trans (propagationEnvelope_one_le 0)
    | succ k ih =>
        apply (hs k (by omega)).trans
        apply le_trans _ (propagationEnvelope_step k)
        exact max_le_max le_rfl (pow_le_pow_left₀ (by positivity)
          (max_le_max le_rfl (ih (by omega))) _)
  exact haux K le_rfl

/-- Auxiliary number of shortest-arc steps.  The manuscript's `chainLength`
is unchanged. -/
def propagationSteps (r : ℚ) : ℕ :=
  Nat.ceil (13 * Route1.PaperBounds.radius r / Route1.PaperBounds.clearance r)

open Route1.PaperBounds

theorem paper_radius_ge {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (7 / 8 : ℚ) ≤ radius r := by
  have hm : (3 / 4 : ℚ) ≤ max r beta := by
    simpa [beta] using le_max_right r (3 / 4 : ℚ)
  rw [radius]
  linarith

theorem paper_radius_lt {r : ℚ} (hr1 : r < 1) : radius r < (1 : ℚ) := by
  have hm : max r beta < (1 : ℚ) := max_lt hr1 (by norm_num [beta])
  rw [radius]
  linarith

theorem paper_clearance_pos {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < clearance r := by
  have hRge := paper_radius_ge hr0 hr1
  have hRlt := paper_radius_lt hr1
  rw [clearance]
  apply div_pos
  · apply lt_min
    · norm_num [beta] at hRge ⊢
      linarith
    · linarith
  · norm_num

theorem paper_clearance_le {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    clearance r ≤ (1 / 16 : ℚ) := by
  have hRge := paper_radius_ge hr0 hr1
  have hm : min (radius r - beta) (1 - radius r) ≤ 1 - radius r :=
    min_le_right _ _
  have hgap : 1 - radius r ≤ (1 / 8 : ℚ) := by linarith
  have hm' : min (radius r - beta) (1 - radius r) ≤ (1 / 8 : ℚ) :=
    hm.trans hgap
  rw [clearance]
  norm_num at hm' ⊢
  nlinarith

theorem paper_two_clearance_le_left {r : ℚ} :
    2 * clearance r ≤ radius r - beta := by
  rw [clearance]
  have hm := min_le_left (radius r - beta) (1 - radius r)
  linarith

theorem paper_two_clearance_le_right {r : ℚ} :
    2 * clearance r ≤ 1 - radius r := by
  rw [clearance]
  have hm := min_le_right (radius r - beta) (1 - radius r)
  linarith

theorem paper_chainLength_ge_general {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    225 ≤ chainLength r := by
  have hRge := paper_radius_ge hr0 hr1
  have hdPos := paper_clearance_pos hr0 hr1
  have hdLe := paper_clearance_le hr0 hr1
  have hquot : (224 : ℚ) ≤ 16 * radius r / clearance r := by
    apply (le_div_iff₀ hdPos).2
    nlinarith
  have hceilQ : (224 : ℚ) ≤
      (Nat.ceil (16 * radius r / clearance r) : ℚ) :=
    hquot.trans (Nat.le_ceil _)
  have hceil : 224 ≤ Nat.ceil (16 * radius r / clearance r) := by
    exact_mod_cast hceilQ
  rw [chainLength]
  omega

theorem propagationSteps_ge {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    182 ≤ propagationSteps r := by
  have hRge := paper_radius_ge hr0 hr1
  have hdPos := paper_clearance_pos hr0 hr1
  have hdLe := paper_clearance_le hr0 hr1
  have hquot : (182 : ℚ) ≤ 13 * radius r / clearance r := by
    apply (le_div_iff₀ hdPos).2
    nlinarith
  have hceilQ : (182 : ℚ) ≤
      (Nat.ceil (13 * radius r / clearance r) : ℚ) :=
    hquot.trans (Nat.le_ceil _)
  exact_mod_cast hceilQ

theorem propagationSteps_chainLength_relation
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    16 * propagationSteps r ≤ 13 * chainLength r + 2 := by
  have hR0 : 0 ≤ radius r := (paper_radius_ge hr0 hr1).trans' (by norm_num)
  have hdPos := paper_clearance_pos hr0 hr1
  have h13nonneg : 0 ≤ 13 * radius r / clearance r := by positivity
  have hKup : (propagationSteps r : ℚ) <
      13 * radius r / clearance r + 1 := by
    exact Nat.ceil_lt_add_one h13nonneg
  have hLlow : 16 * radius r / clearance r ≤
      (Nat.ceil (16 * radius r / clearance r) : ℚ) := Nat.le_ceil _
  have hKup' : (propagationSteps r : ℚ) <
      13 * (radius r / clearance r) + 1 := by
    convert hKup using 1 <;> ring
  have hLlow' : 16 * (radius r / clearance r) ≤
      (Nat.ceil (16 * radius r / clearance r) : ℚ) := by
    convert hLlow using 1 <;> ring
  have hrat : (16 * propagationSteps r : ℕ) < 13 * chainLength r + 3 := by
    rw [chainLength]
    exact_mod_cast (show (16 : ℚ) * propagationSteps r <
        13 * (Nat.ceil (16 * radius r / clearance r) + 1) + 3 by
      nlinarith [hKup', hLlow'])
  omega

theorem propagationSteps_le_chainLength
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    propagationSteps r ≤ chainLength r := by
  have hrel := propagationSteps_chainLength_relation hr0 hr1
  have hL := paper_chainLength_ge_general hr0 hr1
  omega

theorem propagation_exponent_budget
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    261 + propagationSteps r ≤ 2 * chainLength r := by
  have hrel := propagationSteps_chainLength_relation hr0 hr1
  have hL := paper_chainLength_ge_general hr0 hr1
  omega

/-- Equally spaced points along the shortest argument arc from `a` toward
`z`. -/
def circleChain (a z : ℂ) (K j : ℕ) : ℂ :=
  a * Complex.exp (Complex.I *
    (((j : ℝ) / (K : ℝ) * (z / a).arg : ℝ) : ℂ))

theorem norm_exp_I_sub_exp_I_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ |x - y| := by
  have heq :
      Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y) =
        Complex.exp (Complex.I * y) *
          (Complex.exp (Complex.I * (x - y)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul]
  have hone : ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hone, one_mul]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

theorem circleChain_norm (a z : ℂ) (K j : ℕ) :
    ‖circleChain a z K j‖ = ‖a‖ := by
  rw [circleChain, norm_mul, Complex.norm_exp]
  simp

@[simp] theorem circleChain_zero (a z : ℂ) (K : ℕ) :
    circleChain a z K 0 = a := by simp [circleChain]

theorem circleChain_last {a z : ℂ} {R : ℝ} {K : ℕ}
    (hR : 0 < R) (hK : 0 < K) (ha : ‖a‖ = R) (hz : ‖z‖ = R) :
    circleChain a z K K = z := by
  have ha0 : a ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [ha]; exact ne_of_gt hR)
  have hu : ‖z / a‖ = 1 := by
    rw [norm_div, ha, hz]
    exact div_self (ne_of_gt hR)
  have hpolar :
      Complex.exp (Complex.I * (((z / a).arg : ℝ) : ℂ)) = z / a := by
    simpa [norm_div, ha, hz, hR.ne', mul_comm] using
      Complex.norm_mul_exp_arg_mul_I (z / a)
  rw [circleChain]
  have hcast : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [div_self hcast, one_mul, hpolar]
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ z ha0

theorem circleChain_step {a z : ℂ} {R d : ℝ} {K j : ℕ}
    (hR : 0 < R) (hd : 0 < d) (hK : 0 < K) (ha : ‖a‖ = R)
    (hKlower : 13 * R / d ≤ (K : ℝ)) :
    ‖circleChain a z K (j + 1) - circleChain a z K j‖ < d / 4 := by
  let θ : ℝ := (z / a).arg
  let x : ℝ := ((j + 1 : ℕ) : ℝ) / K * θ
  let y : ℝ := (j : ℝ) / K * θ
  have hdiff : |x - y| = |θ| / K := by
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hxy : x - y = θ / K := by
      dsimp [x, y]
      field_simp [hK0]
      push_cast
      ring
    rw [hxy, abs_div]
    have hKposR : (0 : ℝ) < K := by exact_mod_cast hK
    rw [abs_of_pos hKposR]
  have harg : |θ| ≤ Real.pi := Complex.abs_arg_le_pi _
  have hpi : Real.pi < (13 / 4 : ℝ) := by
    have hp := Real.pi_lt_d2
    norm_num at hp ⊢
    linarith
  have hstep : R * (|θ| / K) < d / 4 := by
    have hKposR : (0 : ℝ) < K := by exact_mod_cast hK
    have hdK : 13 * R ≤ (K : ℝ) * d := (div_le_iff₀ hd).mp hKlower
    have htheta : |θ| < (13 / 4 : ℝ) := harg.trans_lt hpi
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hKposR).2
    nlinarith
  have hnorm :
      ‖circleChain a z K (j + 1) - circleChain a z K j‖ ≤ R * |x - y| := by
    change ‖a * Complex.exp (Complex.I * x) -
      a * Complex.exp (Complex.I * y)‖ ≤ R * |x - y|
    rw [← mul_sub, norm_mul, ha]
    exact mul_le_mul_of_nonneg_left (norm_exp_I_sub_exp_I_le x y) hR.le
  rw [hdiff] at hnorm
  exact hnorm.trans_lt hstep

theorem propagationEnvelope_le_largeBound
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    propagationEnvelope (propagationSteps r) ≤
      (largeBound r : ℝ) := by
  rw [propagationEnvelope, largeBound, Nat.cast_pow, Nat.cast_ofNat]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hbudget := propagation_exponent_budget hr0 hr1
  have hpow : 3 ^ (261 + propagationSteps r) ≤
      3 ^ (2 * chainLength r) := Nat.pow_le_pow_right (by omega) hbudget
  have hpow' : 3 ^ (261 + propagationSteps r) ≤ 9 ^ chainLength r := by
    simpa [show (9 : ℕ) = 3 ^ 2 by norm_num, pow_mul] using hpow
  exact Nat.mul_le_mul (by omega) hpow'

/-- Uniform propagation from one small anchor around the manuscript circle.
This is the analytic statement consumed independently by each of the four
transformed factors. -/
theorem omitted_values_chain_bound
    {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H
      {w : ℂ | (3 / 4 : ℝ) < ‖w‖ ∧ ‖w‖ < 1})
    (homit : ∀ w : ℂ, (3 / 4 : ℝ) < ‖w‖ → ‖w‖ < 1 →
      H w ≠ 0 ∧ H w ≠ 1)
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {a z : ℂ}
    (ha : ‖a‖ = (radius r : ℝ))
    (hanchor : ‖H a‖ ≤ 1)
    (hz : ‖z‖ = (radius r : ℝ)) :
    ‖H z‖ ≤ (largeBound r : ℝ) := by
  let R : ℝ := (radius r : ℝ)
  let d : ℝ := (clearance r : ℝ)
  let K : ℕ := propagationSteps r
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 7 / 8)
      (paper_radius_ge hr0 hr1)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast paper_clearance_pos hr0 hr1
  have hK : 0 < K := by
    dsimp [K]
    have := propagationSteps_ge hr0 hr1
    omega
  have hKlower : 13 * R / d ≤ (K : ℝ) := by
    have hq : 13 * radius r / clearance r ≤ (propagationSteps r : ℚ) :=
      Nat.le_ceil _
    dsimp [R, d, K]
    exact_mod_cast hq
  have hleft : (3 / 4 : ℝ) ≤ R - 2 * d := by
    have hq := paper_two_clearance_le_left (r := r)
    have hq' : (3 / 4 : ℚ) ≤ radius r - 2 * clearance r := by
      norm_num [beta] at hq ⊢
      linarith
    have hqR : ((3 / 4 : ℚ) : ℝ) ≤
        ((radius r - 2 * clearance r : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 hq'
    dsimp [R, d]
    push_cast at hqR
    norm_num at hqR ⊢
    exact hqR
  have hright : R + 2 * d ≤ 1 := by
    have hq := paper_two_clearance_le_right (r := r)
    dsimp [R, d]
    exact_mod_cast (show radius r + 2 * clearance r ≤ (1 : ℚ) by linarith)
  have hball : ∀ j : ℕ, ball (circleChain a z K j) (2 * d) ⊆
      {w : ℂ | (3 / 4 : ℝ) < ‖w‖ ∧ ‖w‖ < 1} := by
    intro j w hw
    have hwc : ‖w - circleChain a z K j‖ < 2 * d := by
      simpa [mem_ball, dist_eq_norm] using hw
    have hcNorm : ‖circleChain a z K j‖ = R := by
      rw [circleChain_norm, ha]
    constructor
    · have ht := norm_add_le (circleChain a z K j - w) w
      have hlower : R ≤ ‖w - circleChain a z K j‖ + ‖w‖ := by
        rw [← norm_neg (w - circleChain a z K j)]
        simpa [hcNorm] using ht
      nlinarith
    · have ht := norm_add_le (w - circleChain a z K j) (circleChain a z K j)
      have hupper : ‖w‖ ≤ ‖w - circleChain a z K j‖ + R := by
        simpa [hcNorm] using ht
      nlinarith
  let x : ℕ → ℝ := fun j => ‖H (circleChain a z K j)‖
  have hx0 : x 0 ≤ 1 := by simpa [x] using hanchor
  have hxstep : ∀ j < K, x (j + 1) ≤
      max propagationConstant ((max 1 (x j)) ^ 3) := by
    intro j hj
    have hlocalH : DifferentiableOn ℂ H
        (ball (circleChain a z K j) (2 * d)) := hH.mono (hball j)
    have hlocalOmit : ∀ w ∈ ball (circleChain a z K j) (2 * d),
        H w ≠ 0 ∧ H w ≠ 1 := by
      intro w hw
      exact homit w (hball j hw).1 (hball j hw).2
    have hstep := circleChain_step (a := a) (z := z) (R := R) (d := d)
      (K := K) (j := j) hR hd hK (by simpa [R] using ha) hKlower
    have hrec := omitted_values_collar_step hd hlocalH hlocalOmit hstep.le
    simpa [x, propagationConstant] using hrec
  have hxK : x K ≤ propagationEnvelope K :=
    max_cubic_chain_bound x hx0 hxstep
  have hlast : circleChain a z K K = z :=
    circleChain_last hR hK (by simpa [R] using ha) (by simpa [R] using hz)
  have henv : propagationEnvelope K ≤ (largeBound r : ℝ) := by
    simpa [K] using propagationEnvelope_le_largeBound hr0 hr1
  simpa [x, hlast] using hxK.trans henv

end
end CoarseSchottky
end BelgianChocolate
