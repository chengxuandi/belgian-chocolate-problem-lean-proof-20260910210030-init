import BCPThreshold.FourFactorsToDiscFunction
import BCPThreshold.AnalyticStrictFactors

/-!
# Exact four-factor representation of a normalized disc function
-/

namespace BelgianChocolate

open Set Metric Complex Filter

noncomputable section

def exactRawU (f : ℂ → ℂ) : ℂ → ℂ := dslope f 0

def exactRawV (f : ℂ → ℂ) (q : ℝ) : ℂ → ℂ :=
  dslope (dslope (fun z => 1 - f z) (rootPlus q)) (rootMinus q)

def exactU (f : ℂ → ℂ) : ℂ → ℂ := symmetrize (exactRawU f)

def exactV (f : ℂ → ℂ) (q : ℝ) : ℂ → ℂ := symmetrize (exactRawV f q)

theorem exactRawU_differentiable {q : ℝ} {f : ℂ → ℂ} (hf : DiscFunction q f) :
    DifferentiableOn ℂ (exactRawU f) unitDisc := by
  rw [unitDisc, exactRawU, Complex.differentiableOn_dslope
    (Metric.isOpen_ball.mem_nhds (by simp [unitDisc]))]
  simpa [unitDisc] using hf.1.1

theorem exactRawV_differentiable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} (hf : DiscFunction q f) :
    DifferentiableOn ℂ (exactRawV f q) unitDisc := by
  have hp := plusRoot_mem_unitDisc hq0.le hq1
  have hm := neg_plusRoot_mem_unitDisc hq0.le hq1
  have hh : DifferentiableOn ℂ (fun z : ℂ => 1 - f z) unitDisc := by
    intro z hz
    exact ((differentiableAt_const (c := (1 : ℂ))).sub
      ((hf.1.1 z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz))).differentiableWithinAt
  change DifferentiableOn ℂ
    (dslope (dslope (fun z : ℂ => 1 - f z) (rootPlus q)) (rootMinus q))
      (Metric.ball 0 1)
  have hp' : rootPlus q ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [unitDisc, rootPlus, plusRoot] using hp
  have hm' : rootMinus q ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [unitDisc, rootMinus, rootPlus, plusRoot] using hm
  rw [Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hm')]
  rw [Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hp')]
  simpa [unitDisc] using hh

theorem exactRawU_factor {q : ℝ} {f : ℂ → ℂ} (hf : DiscFunction q f) (z : ℂ) :
    z * exactRawU f z = f z := by
  have hf0 : f 0 = 0 := (hf.2.1 0 (by simp [unitDisc])).2 rfl
  simpa [exactRawU] using sub_smul_dslope_of_zero hf0 z

theorem exactRawV_factor {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} (hf : DiscFunction q f) (z : ℂ) :
    (z ^ 2 + (q : ℂ)) * exactRawV f q z = 1 - f z := by
  let h : ℂ → ℂ := fun z => 1 - f z
  let d := dslope h (rootPlus q)
  have hp := plusRoot_mem_unitDisc hq0.le hq1
  have hm := neg_plusRoot_mem_unitDisc hq0.le hq1
  have hfp : f (rootPlus q) = 1 :=
    (hf.2.2.2.1 _ hp).2 (Or.inl rfl)
  have hfm : f (rootMinus q) = 1 := by
    have : rootMinus q = -(plusRoot q) := rfl
    exact (hf.2.2.2.1 _ hm).2 (Or.inr this)
  have hhp : h (rootPlus q) = 0 := by simp [h, hfp]
  have hhm : h (rootMinus q) = 0 := by simp [h, hfm]
  have hfirst (w : ℂ) : (w - rootPlus q) * d w = h w := by
    simpa [d, smul_eq_mul] using sub_smul_dslope_of_zero hhp w
  have hd_m : d (rootMinus q) = 0 := by
    have hx := hfirst (rootMinus q)
    rw [hhm] at hx
    exact (mul_eq_zero.mp hx).resolve_left
      (sub_ne_zero.mpr (rootPlus_ne_rootMinus hq0).symm)
  have hsecond : (z - rootMinus q) * dslope d (rootMinus q) z = d z := by
    simpa [smul_eq_mul] using sub_smul_dslope_of_zero hd_m z
  rw [← quadratic_root_factor hq0.le]
  change (z - rootPlus q) * (z - rootMinus q) *
      dslope d (rootMinus q) z = h z
  rw [mul_assoc, hsecond, hfirst]

theorem exactU_holSymm {q : ℝ} {f : ℂ → ℂ} (hf : DiscFunction q f) :
    HolSymmOn 1 (exactU f) := by
  exact holSymm_symmetrize (exactRawU_differentiable hf)

theorem exactV_holSymm {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} (hf : DiscFunction q f) :
    HolSymmOn 1 (exactV f q) := by
  exact holSymm_symmetrize (exactRawV_differentiable hq0 hq1 hf)

theorem exactU_factor {q : ℝ} {f : ℂ → ℂ} (hf : DiscFunction q f)
    {z : ℂ} (hz : z ∈ unitDisc) : z * exactU f z = f z := by
  exact symmetrize_linear_factor hf.1.2 (fun w _ => exactRawU_factor hf w) hz

theorem exactV_factor {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} (hf : DiscFunction q f)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (z ^ 2 + (q : ℂ)) * exactV f q z = 1 - f z := by
  exact symmetrize_quadratic_factor hf.1.2
    (fun w _ => exactRawV_factor hq0 hq1 hf w) hz

theorem exactU_zero_free {q : ℝ} {f : ℂ → ℂ} (hf : DiscFunction q f) :
    ∀ z ∈ unitDisc, exactU f z ≠ 0 := by
  intro z hz hu
  by_cases hz0 : z = 0
  · subst z
    have huAt : DifferentiableAt ℂ (exactU f) 0 :=
      ((exactU_holSymm hf).1 0 hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have heq : (fun w => w * exactU f w) =ᶠ[nhds (0 : ℂ)] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact exactU_factor hf hw
    have hleft : deriv (fun w => w * exactU f w) 0 = exactU f 0 := by
      change deriv (id * exactU f) 0 = _
      simpa using ((hasDerivAt_id (𝕜 := ℂ) 0).mul huAt.hasDerivAt).deriv
    have hd := heq.deriv_eq
    rw [hleft, hu] at hd
    exact hf.2.2.1 hd.symm
  · have hfac := exactU_factor hf hz
    rw [hu, mul_zero] at hfac
    exact hz0 ((hf.2.1 z hz).1 hfac.symm)

theorem exactV_zero_free {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} (hf : DiscFunction q f) :
    ∀ z ∈ unitDisc, exactV f q z ≠ 0 := by
  intro z hz hv
  by_cases hroot : z = rootPlus q ∨ z = rootMinus q
  · have hfactor : z ^ 2 + (q : ℂ) = 0 := by
      rw [sq_add_real_eq_zero_iff_fourFactors hq0.le]
      simpa [rootPlus, rootMinus, plusRoot] using hroot
    have hvAt : DifferentiableAt ℂ (exactV f q) z :=
      ((exactV_holSymm hq0 hq1 hf).1 z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have heq : (fun w => (w ^ 2 + (q : ℂ)) * exactV f q w) =ᶠ[nhds z]
        (fun w => 1 - f w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact exactV_factor hq0 hq1 hf hw
    have hpoly : DifferentiableAt ℂ (fun w : ℂ => w ^ 2 + (q : ℂ)) z :=
      (differentiableAt_id.pow 2).add_const _
    have hleft : deriv (fun w => (w ^ 2 + (q : ℂ)) * exactV f q w) z =
        2 * z * exactV f q z := by
      change deriv ((fun w : ℂ => w ^ 2 + (q : ℂ)) * exactV f q) z = _
      rw [deriv_mul hpoly hvAt]
      simp [hfactor]
    have hd := heq.deriv_eq
    rw [hleft, deriv_const_sub, hv] at hd
    simp only [mul_zero, neg_eq_zero] at hd
    rcases hroot with rfl | rfl
    · exact hf.2.2.2.2.1 (neg_eq_zero.mp hd.symm)
    · simpa [rootMinus, plusRoot] using hf.2.2.2.2.2 (neg_eq_zero.mp hd.symm)
  · have hfac := exactV_factor hq0 hq1 hf hz
    rw [hv, mul_zero] at hfac
    have hone : f z = 1 := by linear_combination hfac
    have hfib := (hf.2.2.2.1 z hz).1 hone
    exact hroot (by simpa [rootPlus, rootMinus, plusRoot] using hfib)

def reciprocal (g : ℂ → ℂ) : ℂ → ℂ := fun z => (g z)⁻¹

theorem reciprocal_holSymm {g : ℂ → ℂ} (hg : HolSymmOn 1 g)
    (hne : ∀ z ∈ unitDisc, g z ≠ 0) : HolSymmOn 1 (reciprocal g) := by
  constructor
  · intro z hz
    exact ((hg.1 z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz) |>.inv
      (hne z hz)).differentiableWithinAt
  · intro z hz
    change (g (star z))⁻¹ = star ((g z)⁻¹)
    rw [hg.2 z hz]
    simpa using (map_inv₀ (starRingEnd ℂ) (g z)).symm

noncomputable def discFunctionToFourFactors {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {f : ℂ → ℂ} (hf : DiscFunction q f) : FourFactors q where
  u := exactU f
  v := exactV f q
  uInv := reciprocal (exactU f)
  vInv := reciprocal (exactV f q)
  holSymm_u := exactU_holSymm hf
  holSymm_v := exactV_holSymm hq0 hq1 hf
  holSymm_uInv := reciprocal_holSymm (exactU_holSymm hf) (exactU_zero_free hf)
  holSymm_vInv := reciprocal_holSymm (exactV_holSymm hq0 hq1 hf)
    (exactV_zero_free hq0 hq1 hf)
  linear := by
    intro z hz
    rw [exactU_factor hf hz, exactV_factor hq0 hq1 hf hz]
    ring
  inverse_u := by
    intro z hz
    exact mul_inv_cancel₀ (exactU_zero_free hf z hz)
  inverse_v := by
    intro z hz
    exact mul_inv_cancel₀ (exactV_zero_free hq0 hq1 hf z hz)

end

end BelgianChocolate
