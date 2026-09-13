import BCPThreshold.CoarseSchottky
import BCPThreshold.ForbiddenLattice
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

open Metric Set

namespace BelgianChocolate
namespace CoarseSchottky

noncomputable section

open Route1.PaperBounds

/-- A holomorphic map of the unit disc that omits the forbidden lattice has
an explicit hyperbolic-type derivative bound. -/
theorem deriv_le_of_avoids_lattice
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (havoid : ∀ z ∈ ball (0 : ℂ) 1, g z ∉ ForbiddenLattice.lattice)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖deriv g w‖ ≤ 128 / (1 - ‖w‖) := by
  have hwNorm : ‖w‖ < 1 := by simpa [mem_ball] using hw
  let ρ : ℝ := 1 - ‖w‖
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let A : ℂ → ℂ := fun z ↦ w + (ρ : ℂ) * z
  let G : ℂ → ℂ := g ∘ A
  have hAmap : MapsTo A (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    have htri : ‖w + (ρ : ℂ) * z‖ ≤ ‖w‖ + ‖(ρ : ℂ) * z‖ := norm_add_le _ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le] at htri
    dsimp [A, ρ]
    nlinarith [norm_nonneg w, norm_nonneg z]
  have hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := by
    apply hg.comp
    · dsimp [A]
      fun_prop
    · exact hAmap
  have hAderiv (z : ℂ) : HasDerivAt A (ρ : ℂ) z := by
    change HasDerivAt (fun x : ℂ ↦ w + (ρ : ℂ) * x) (ρ : ℂ) z
    exact (hasDerivAt_const_mul (ρ : ℂ)).const_add w
  have hGderiv0 : deriv G 0 = deriv g w * (ρ : ℂ) := by
    have hgd : DifferentiableAt ℂ g w :=
      hg.differentiableAt (isOpen_ball.mem_nhds hw)
    have hgdA : DifferentiableAt ℂ g (A 0) := by simpa [A] using hgd
    simpa [G, A, Function.comp_def] using (hgdA.hasDerivAt.comp 0 (hAderiv 0)).deriv
  obtain ⟨b, hb⟩ := coarse_bloch_image_disc hG
  by_contra hnot
  have hlarge : 1 < ‖deriv G 0‖ / 128 := by
    rw [hGderiv0, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    dsimp [ρ]
    have hden : 0 < 1 - ‖w‖ := by linarith
    have hgt : 128 / (1 - ‖w‖) < ‖deriv g w‖ := lt_of_not_ge hnot
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2
    have := (div_lt_iff₀ hden).1 hgt
    nlinarith
  obtain ⟨p, hpLattice, hpBall⟩ := ForbiddenLattice.exists_mem_lattice_ball b
  have hpBig : p ∈ ball b (‖deriv G 0‖ / 128) :=
    (ball_subset_ball hlarge.le) hpBall
  obtain ⟨z, hz, hGz⟩ := hb hpBig
  apply (havoid (A z) (hAmap hz))
  have hgAz : g (A z) = p := by simpa [G, Function.comp_def] using hGz
  rw [hgAz]
  exact hpLattice

/-- The two normalized cosine lifts used in the coarse Schottky argument. -/
theorem exists_double_cosine_lift
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (homit : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ f z ≠ 1)
    (hf0 : ‖f 0‖ ≤ 1) :
    ∃ h g : ℂ → ℂ,
      DifferentiableOn ℂ h (ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ g (ball (0 : ℂ) 1) ∧
      ‖g 0‖ < 2 ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        2 * f z - 1 = Complex.cos (Real.pi * h z)) ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        h z = Complex.cos (Real.pi * g z)) ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ∉ ForbiddenLattice.lattice) := by
  let S : Set ℂ := ball (0 : ℂ) 1
  have hSopen : IsOpen S := isOpen_ball
  have hSne : S.Nonempty := ⟨0, by simp [S]⟩
  have hSconv : Convex ℝ S := convex_ball (0 : ℂ) 1
  letI : ContractibleSpace S := hSconv.contractibleSpace hSne
  have hSsc : IsSimplyConnected S := by
    change SimplyConnectedSpace S
    infer_instance
  let f₁ : ℂ → ℂ := fun z ↦ 2 * f z - 1
  have hf₁ : DifferentiableOn ℂ f₁ S := by
    dsimp [f₁, S]
    fun_prop
  have hf₁omit : ∀ z ∈ S, f₁ z ≠ 1 ∧ f₁ z ≠ -1 := by
    intro z hz
    constructor
    · intro heq
      apply (homit z hz).2
      apply_fun (fun w : ℂ ↦ (w + 1) / 2) at heq
      simpa [f₁] using heq
    · intro heq
      apply (homit z hz).1
      apply_fun (fun w : ℂ ↦ (w + 1) / 2) at heq
      simpa [f₁] using heq
  have f_eq_zero_of_f₁_neg : ∀ {z}, f₁ z = -1 → f z = 0 := by
    intro z heq
    apply_fun (fun w : ℂ ↦ (w + 1) / 2) at heq
    simpa [f₁] using heq
  have f_eq_one_of_f₁_one : ∀ {z}, f₁ z = 1 → f z = 1 := by
    intro z heq
    apply_fun (fun w : ℂ ↦ (w + 1) / 2) at heq
    simpa [f₁] using heq
  obtain ⟨h, hh, hh0, hrepr⟩ :=
    holomorphic_cosine_lift_bounded (f := f₁) (a := 0)
      hSopen hSsc hf₁ (by simp [S]) hf₁omit
  have hf₁0 : ‖f₁ 0‖ ≤ 3 := by
    calc
      ‖f₁ 0‖ = ‖2 * f 0 - 1‖ := rfl
      _ ≤ ‖2 * f 0‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 := by rw [norm_mul]; norm_num at *; nlinarith
  have hh0two : ‖h 0‖ ≤ 2 := by nlinarith
  have hhomit : ∀ z ∈ S, h z ≠ 1 ∧ h z ≠ -1 := by
    intro z hz
    constructor
    · intro heq
      have hfzero : f z = 0 := by
        have hr := hrepr z hz
        rw [heq] at hr
        simp only [mul_one, Complex.cos_pi] at hr
        exact f_eq_zero_of_f₁_neg hr
      exact (homit z hz).1 hfzero
    · intro heq
      have hfzero : f z = 0 := by
        have hr := hrepr z hz
        rw [heq] at hr
        rw [mul_neg, mul_one, Complex.cos_neg, Complex.cos_pi] at hr
        exact f_eq_zero_of_f₁_neg hr
      exact (homit z hz).1 hfzero
  obtain ⟨g, hg, hg0, hgrepr⟩ :=
    holomorphic_cosine_lift_bounded (f := h) (a := 0)
      hSopen hSsc hh (by simp [S]) hhomit
  have hg0two : ‖g 0‖ < 2 := by nlinarith
  have hgavoid : ∀ z ∈ S, g z ∉ ForbiddenLattice.lattice := by
    intro z hz hgL
    rcases ForbiddenLattice.lattice_forbidden hgL with hforbid | hforbid
    · apply (homit z hz).2
      have hr₁ := hrepr z hz
      have hr₂ := hgrepr z hz
      rw [hr₂] at hr₁
      rw [hforbid] at hr₁
      exact f_eq_one_of_f₁_one hr₁
    · apply (homit z hz).1
      have hr₁ := hrepr z hz
      have hr₂ := hgrepr z hz
      rw [hr₂] at hr₁
      rw [hforbid] at hr₁
      exact f_eq_zero_of_f₁_neg hr₁
  exact ⟨h, g, hh, hg, hg0two, hrepr, hgrepr, hgavoid⟩

/-- The second cosine lift has the explicit derivative bound used below. -/
theorem exists_double_cosine_lift_with_deriv_bound
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (homit : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ f z ≠ 1)
    (hf0 : ‖f 0‖ ≤ 1) :
    ∃ h g : ℂ → ℂ,
      DifferentiableOn ℂ h (ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ g (ball (0 : ℂ) 1) ∧
      ‖g 0‖ < 2 ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        2 * f z - 1 = Complex.cos (Real.pi * h z)) ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        h z = Complex.cos (Real.pi * g z)) ∧
      (∀ w ∈ ball (0 : ℂ) 1,
        ‖deriv g w‖ ≤ 128 / (1 - ‖w‖)) := by
  obtain ⟨h, g, hh, hg, hg0, hfh, hhg, hgavoid⟩ :=
    exists_double_cosine_lift hf homit hf0
  refine ⟨h, g, hh, hg, hg0, hfh, hhg, ?_⟩
  intro w hw
  exact deriv_le_of_avoids_lattice hg hgavoid hw

/-- On the closed half-disc, the normalized second lift has norm at most `130`. -/
theorem second_lift_norm_le_130
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hg0 : ‖g 0‖ < 2)
    (hgderiv : ∀ w ∈ ball (0 : ℂ) 1,
      ‖deriv g w‖ ≤ 128 / (1 - ‖w‖))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (1 / 2 : ℝ)) :
    ‖g z‖ ≤ 130 := by
  have hhalf : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    rw [mem_ball, dist_zero_right]
    linarith
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) (1 / 2 : ℝ),
      DifferentiableAt ℂ g w := by
    intro w hw
    exact hg.differentiableAt (isOpen_ball.mem_nhds (hhalf hw))
  have hfderiv : ∀ w ∈ closedBall (0 : ℂ) (1 / 2 : ℝ),
      ‖fderiv ℂ g w‖ ≤ 256 := by
    intro w hw
    have hwnorm : ‖w‖ ≤ 1 / 2 := by
      simpa [mem_closedBall, dist_zero_right] using hw
    have hd := hgderiv w (hhalf hw)
    rw [← norm_deriv_eq_norm_fderiv] 
    have hden : 1 / 2 ≤ 1 - ‖w‖ := by linarith
    have hdenpos : 0 < 1 - ‖w‖ := lt_of_lt_of_le (by norm_num) hden
    calc
      ‖deriv g w‖ ≤ 128 / (1 - ‖w‖) := hd
      _ ≤ 256 := by
        apply (div_le_iff₀ hdenpos).2
        nlinarith
  have hsub :=
    (convex_closedBall (0 : ℂ) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      hdiff hfderiv (mem_closedBall_self (by norm_num)) hz
  have hzNorm : ‖z‖ ≤ 1 / 2 := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hgzsub : ‖g z - g 0‖ ≤ 128 := by
    simpa using (hsub.trans (by
      rw [sub_zero]
      nlinarith))
  calc
    ‖g z‖ ≤ ‖g z - g 0‖ + ‖g 0‖ := by
      have := norm_add_le (g z - g 0) (g 0)
      simpa using this
    _ ≤ 130 := by linarith

/-- A deliberately elementary complex-cosine estimate. -/
theorem norm_cos_le_exp_norm (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.cos, norm_div]
  norm_num
  calc
    ‖Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))‖ / 2 ≤
        (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (Real.exp ‖z‖ + Real.exp ‖z‖) / 2 := by
      gcongr
      · simpa using Complex.norm_exp_le_exp_norm (z * Complex.I)
      · simpa using Complex.norm_exp_le_exp_norm (-(z * Complex.I))
    _ = Real.exp ‖z‖ := by ring

/-- The direct transcendental bound before replacing it by a pure integer. -/
theorem coarse_schottky_exp_bound
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (homit : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ f z ≠ 1)
    (hf0 : ‖f 0‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖f z‖ ≤ Real.exp (Real.pi * Real.exp (Real.pi * 130)) := by
  obtain ⟨h, g, hh, hg, hg0, hfh, hhg, hgderiv⟩ :=
    exists_double_cosine_lift_with_deriv_bound hf homit hf0
  have hzClosed : z ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hg130 : ‖g z‖ ≤ 130 := second_lift_norm_le_130 hg hg0 hgderiv hzClosed
  have hhNorm : ‖h z‖ ≤ Real.exp (Real.pi * 130) := by
    rw [hhg z (by simpa [mem_ball, dist_zero_right] using lt_of_le_of_lt hz (by norm_num))]
    calc
      ‖Complex.cos ((Real.pi : ℂ) * g z)‖ ≤
          Real.exp ‖(Real.pi : ℂ) * g z‖ := norm_cos_le_exp_norm _
      _ ≤ Real.exp (Real.pi * 130) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        exact mul_le_mul_of_nonneg_left hg130 Real.pi_pos.le
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * h z)‖ ≤
      Real.exp (Real.pi * Real.exp (Real.pi * 130)) := by
    calc
      ‖Complex.cos ((Real.pi : ℂ) * h z)‖ ≤
          Real.exp ‖(Real.pi : ℂ) * h z‖ := norm_cos_le_exp_norm _
      _ ≤ Real.exp (Real.pi * Real.exp (Real.pi * 130)) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        exact mul_le_mul_of_nonneg_left hhNorm Real.pi_pos.le
  have hfFormula : f z = (Complex.cos ((Real.pi : ℂ) * h z) + 1) / 2 := by
    have hr := hfh z (by
      simpa [mem_ball, dist_zero_right] using lt_of_le_of_lt hz (by norm_num))
    apply_fun (fun w : ℂ ↦ (w + 1) / 2) at hr
    simpa using hr
  rw [hfFormula, norm_div]
  norm_num
  have hEone : 1 ≤ Real.exp (Real.pi * Real.exp (Real.pi * 130)) := by
    exact Real.one_le_exp (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
  calc
    ‖Complex.cos ((Real.pi : ℂ) * h z) + 1‖ / 2 ≤
        (‖Complex.cos ((Real.pi : ℂ) * h z)‖ + 1) / 2 := by
      gcongr
      simpa using norm_add_le (Complex.cos ((Real.pi : ℂ) * h z)) 1
    _ ≤ Real.exp (Real.pi * Real.exp (Real.pi * 130)) := by nlinarith

/-- `exp x` is bounded by an explicit integral power of three whenever
`x` is below the corresponding natural number. -/
theorem exp_lt_three_pow_of_lt_nat {x : ℝ} {n : ℕ} (hx : x < n) :
    Real.exp x < (3 : ℝ) ^ n := by
  cases n with
  | zero =>
      have hx0 : x < 0 := by simpa using hx
      simpa using (Real.exp_lt_one_iff.mpr hx0)
  | succ n =>
      calc
        Real.exp x < Real.exp ((n + 1 : ℕ) : ℝ) := Real.exp_lt_exp.mpr hx
        _ = Real.exp 1 ^ (n + 1) := by simpa using Real.exp_nat_mul 1 (n + 1)
        _ < (3 : ℝ) ^ (n + 1) :=
          pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by omega)

/-- The standalone half-disc Schottky estimate with the pure integer constant
used by the paper. -/
theorem coarse_schottky_half_disc
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (homit : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ f z ≠ 1)
    (hf0 : ‖f 0‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖f z‖ ≤ (3 : ℝ) ^ (4 * 3 ^ 409 : ℕ) := by
  have htrans := coarse_schottky_exp_bound hf homit hf0 hz
  have hpi409 : Real.pi * 130 < (409 : ℝ) := by
    have hp := Real.pi_lt_d4
    nlinarith
  have hinner : Real.exp (Real.pi * 130) < (3 : ℝ) ^ (409 : ℕ) :=
    exp_lt_three_pow_of_lt_nat hpi409
  have houterArg :
      Real.pi * Real.exp (Real.pi * 130) < (4 * 3 ^ 409 : ℕ) := by
    have hp4 : Real.pi < 4 := Real.pi_lt_four
    have hm := mul_lt_mul hp4 hinner.le (Real.exp_pos _)
      (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at hm ⊢
    exact hm
  exact htrans.trans (exp_lt_three_pow_of_lt_nat houterArg).le

/-- The manuscript's propagation chain is long enough to dominate the
standalone Schottky constant. -/
theorem paper_chainLength_ge_225 {m : ℕ} (hm : 1 ≤ m) :
    225 ≤ Route1.PaperBounds.chainLength (Route1.PaperBounds.coeffRadius m) := by
    have hrHalf : (1 / 2 : ℚ) ≤ coeffRadius m := by
      have hp := one_le_two_pow hm
      have hp0 : (0 : ℚ) < 2 ^ m := pow_pos (by norm_num) _
      rw [coeffRadius]
      have : 1 / (2 : ℚ) ^ m ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hp
      linarith
    have hrLt : coeffRadius m < (1 : ℚ) := by
      rw [coeffRadius]
      have hp0 : (0 : ℚ) < 1 / (2 : ℚ) ^ m := by positivity
      linarith
    have hmaxGe : (3 / 4 : ℚ) ≤ max (coeffRadius m) beta := by
      simpa [beta] using (le_max_right (coeffRadius m) (3 / 4 : ℚ))
    have hmaxLt : max (coeffRadius m) beta < (1 : ℚ) := by
      exact max_lt hrLt (by norm_num [beta])
    have hradGe : (7 / 8 : ℚ) ≤ radius (coeffRadius m) := by
      change (7 / 8 : ℚ) ≤ (1 + max (coeffRadius m) beta) / 2
      dsimp [beta] at hmaxGe
      dsimp [beta]
      linarith
    have hradLt : radius (coeffRadius m) < (1 : ℚ) := by
      rw [radius]
      linarith
    have hclearPos : 0 < clearance (coeffRadius m) := by
      rw [clearance]
      apply div_pos
      apply lt_min
      · dsimp [beta]
        linarith
      · linarith
      · norm_num
    have hclearLe : clearance (coeffRadius m) ≤ (1 / 16 : ℚ) := by
      have hmin : min (radius (coeffRadius m) - beta)
          (1 - radius (coeffRadius m)) ≤ 1 - radius (coeffRadius m) := min_le_right _ _
      change min (radius (coeffRadius m) - beta)
          (1 - radius (coeffRadius m)) / 2 ≤ (1 / 16 : ℚ)
      dsimp [beta] at hmin
      dsimp [beta]
      nlinarith
    have hquot : (224 : ℚ) ≤
        16 * radius (coeffRadius m) / clearance (coeffRadius m) := by
      apply (le_div_iff₀ hclearPos).2
      nlinarith
    have hceilQ : (224 : ℚ) ≤
        (Nat.ceil (16 * radius (coeffRadius m) / clearance (coeffRadius m)) : ℚ) :=
      hquot.trans (Nat.le_ceil _)
    have hceil : 224 ≤
        Nat.ceil (16 * radius (coeffRadius m) / clearance (coeffRadius m)) := by
      exact_mod_cast hceilQ
    rw [chainLength]
    omega

theorem coarse_constant_le_largeBound {m : ℕ} (hm : 1 ≤ m) :
    (3 : ℝ) ^ (4 * 3 ^ 409 : ℕ) ≤
      (Route1.PaperBounds.largeBound (Route1.PaperBounds.coeffRadius m) : ℝ) := by
  rw [Route1.PaperBounds.largeBound, Nat.cast_pow, Nat.cast_ofNat]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hk := paper_chainLength_ge_225 hm
  let k := Route1.PaperBounds.chainLength (Route1.PaperBounds.coeffRadius m)
  have hexp : 409 ≤ 2 * k := by dsimp [k]; omega
  have hpow : 3 ^ (409 : ℕ) ≤ 3 ^ (2 * k) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hpow' : 3 ^ (409 : ℕ) ≤ 9 ^ k := by
    simpa [show (9 : ℕ) = 3 ^ 2 by norm_num, pow_mul] using hpow
  exact Nat.mul_le_mul (by omega) hpow'

end

end CoarseSchottky
end BelgianChocolate
