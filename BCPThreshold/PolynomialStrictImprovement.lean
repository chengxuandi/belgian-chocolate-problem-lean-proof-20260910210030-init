import BCPThreshold.PolynomialStrictImprovementAlgebra
import BCPThreshold.PolynomialAnalyticInterface
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Data.Finset.DenselyOrdered
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BelgianChocolate.StrictImprovement

open Polynomial Finset

noncomputable section

def coeffSize (d : ℕ) (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), |p.coeff k|

theorem evalC_eq_sum_range {p : Polynomial ℝ} {d : ℕ}
    (hp : p.natDegree ≤ d) (z : ℂ) :
    evalC p z = ∑ k ∈ Finset.range (d + 1), (p.coeff k : ℂ) * z ^ k := by
  rw [evalC, ← eval₂_eq_eval_map]
  exact eval₂_eq_sum_range' (algebraMap ℝ ℂ) (Nat.lt_succ_of_le hp) z

theorem coeffSize_nonneg (d : ℕ) (p : Polynomial ℝ) :
    0 ≤ coeffSize d p := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem coeff_abs_le_coeffSize {p : Polynomial ℝ} {d k : ℕ}
    (hk : k < d + 1) : |p.coeff k| ≤ coeffSize d p := by
  unfold coeffSize
  exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (p.coeff i))
    (by simpa [Nat.lt_succ_iff] using hk)

theorem norm_pow_le_one_add_norm_pow {z : ℂ} {k d : ℕ} (hkd : k ≤ d) :
    ‖z‖ ^ k ≤ (1 + ‖z‖) ^ d := by
  exact (pow_le_pow_left₀ (norm_nonneg z) (by linarith : ‖z‖ ≤ 1 + ‖z‖) k).trans
    (pow_le_pow_right₀ (by linarith [norm_nonneg z] : 1 ≤ 1 + ‖z‖) hkd)

theorem evalC_norm_le_coeffSize {p : Polynomial ℝ} {d : ℕ}
    (hp : p.natDegree ≤ d) (z : ℂ) :
    ‖evalC p z‖ ≤ coeffSize d p * (1 + ‖z‖) ^ d := by
  rw [evalC_eq_sum_range hp]
  calc
    ‖∑ k ∈ Finset.range (d + 1), (p.coeff k : ℂ) * z ^ k‖ ≤
        ∑ k ∈ Finset.range (d + 1), ‖(p.coeff k : ℂ) * z ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (d + 1),
        |p.coeff k| * (1 + ‖z‖) ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_pow_le_one_add_norm_pow (by simpa [Nat.lt_succ_iff] using hk)) (abs_nonneg _)
    _ = coeffSize d p * (1 + ‖z‖) ^ d := by
      simp [coeffSize, Finset.sum_mul]

theorem coeffSize_add_le (d : ℕ) (p q : Polynomial ℝ) :
    coeffSize d (p + q) ≤ coeffSize d p + coeffSize d q := by
  unfold coeffSize
  calc
    ∑ k ∈ Finset.range (d + 1), |(p + q).coeff k| ≤
        ∑ k ∈ Finset.range (d + 1), (|p.coeff k| + |q.coeff k|) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [coeff_add] using abs_add_le (p.coeff k) (q.coeff k)
    _ = (∑ k ∈ Finset.range (d + 1), |p.coeff k|) +
        ∑ k ∈ Finset.range (d + 1), |q.coeff k| := by
      simp only [Finset.sum_add_distrib]

theorem coeffSize_C_mul (d : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    coeffSize d (C a * p) = |a| * coeffSize d p := by
  unfold coeffSize
  simp only [coeff_C_mul, abs_mul, Finset.mul_sum]

theorem stable_exists_left_margin {p : Polynomial ℝ}
    (hp : HurwitzStable p) :
    ∃ η : ℝ, 0 < η ∧
      ∀ z : ℂ, evalC p z = 0 → z.re < -η := by
  let pC : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  have hpCne : pC ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff
      (FaithfulSMul.algebraMap_injective ℝ ℂ)).2 hp.1
  let Z : Set ℂ := {z | evalC p z = 0}
  have hZfinite : Z.Finite := by
    have hf := Polynomial.finite_setOf_isRoot hpCne
    simpa [Z, pC, evalC, Polynomial.IsRoot] using hf
  let T : Set ℝ := (fun z : ℂ ↦ -z.re) '' Z
  have hTfinite : T.Finite := hZfinite.image (fun z : ℂ ↦ -z.re)
  have hsep : ∀ x ∈ ({0} : Set ℝ), ∀ y ∈ T, x < y := by
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx
    subst x
    rcases hy with ⟨z, hz, rfl⟩
    exact neg_pos.mpr (hp.2 z hz)
  obtain ⟨η, hη0, hηT⟩ := Set.Finite.exists_between'
    (Set.finite_singleton (0 : ℝ)) hTfinite hsep
  refine ⟨η, hη0 0 (by simp), ?_⟩
  intro z hz
  have hzT : -z.re ∈ T := ⟨z, hz, rfl⟩
  have := hηT (-z.re) hzT
  linarith

def rootWeight (η : ℝ) (w : ℂ) : ℝ :=
  (-η - w.re) / (-η - w.re + 1 + ‖w‖)

theorem rootWeight_pos {η : ℝ} {w : ℂ} (hw : w.re < -η) :
    0 < rootWeight η w := by
  unfold rootWeight
  apply div_pos <;> nlinarith [norm_nonneg w]

theorem rootWeight_le_one {η : ℝ} {w : ℂ} (hw : w.re < -η) :
    rootWeight η w ≤ 1 := by
  unfold rootWeight
  apply (div_le_one (by nlinarith [norm_nonneg w])).2
  nlinarith [norm_nonneg w]

theorem rootWeight_mul_le_norm_sub {η : ℝ} {w z : ℂ}
    (hw : w.re < -η) (hz : -η ≤ z.re) :
    rootWeight η w * (1 + ‖z‖) ≤ ‖z - w‖ := by
  let a : ℝ := -η - w.re
  have ha : 0 < a := by dsimp [a]; linarith
  have hden : 0 < a + 1 + ‖w‖ := by positivity
  have hre : a ≤ (z - w).re := by
    dsimp [a]
    change -η - w.re ≤ z.re - w.re
    linarith
  have hanorm : a ≤ ‖z - w‖ := hre.trans (Complex.re_le_norm (z - w))
  have hznorm : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
    calc
      ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
  change a / (a + 1 + ‖w‖) * (1 + ‖z‖) ≤ ‖z - w‖
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  have hfirst : a * (1 + ‖z‖) ≤ a * (1 + ‖z - w‖ + ‖w‖) := by
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  have hsecond : a * (1 + ‖w‖) ≤ ‖z - w‖ * (1 + ‖w‖) :=
    mul_le_mul_of_nonneg_right hanorm (by positivity)
  calc
    a * (1 + ‖z‖) ≤ a * (1 + ‖z - w‖ + ‖w‖) := hfirst
    _ ≤ ‖z - w‖ * (a + 1 + ‖w‖) := by nlinarith

def complexification (p : Polynomial ℝ) : Polynomial ℂ :=
  p.map (algebraMap ℝ ℂ)

def halfPlaneConstant (p : Polynomial ℝ) (η : ℝ) : ℝ :=
  |p.leadingCoeff| *
    ((complexification p).roots.map (rootWeight η)).prod

theorem complexification_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    complexification p ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective ℝ ℂ)).2 hp

theorem complexification_natDegree (p : Polynomial ℝ) :
    (complexification p).natDegree = p.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective ℝ ℂ) p

theorem complexification_eval (p : Polynomial ℝ) (z : ℂ) :
    (complexification p).eval z = evalC p z := rfl

theorem root_of_mem_complexification_roots {p : Polynomial ℝ} {z : ℂ}
    (hz : z ∈ (complexification p).roots) : evalC p z = 0 := by
  exact (Polynomial.mem_roots (Polynomial.ne_zero_of_mem_roots hz)).mp hz

theorem halfPlaneConstant_pos {p : Polynomial ℝ} {η : ℝ}
    (hp : p ≠ 0)
    (hroots : ∀ z : ℂ, evalC p z = 0 → z.re < -η) :
    0 < halfPlaneConstant p η := by
  unfold halfPlaneConstant
  apply mul_pos
  · exact abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  · apply Multiset.prod_pos
    intro z hz
    simp only [Multiset.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    exact rootWeight_pos (hroots w (root_of_mem_complexification_roots hw))

theorem halfPlaneConstant_le_leadingCoeff {p : Polynomial ℝ} {η : ℝ}
    (hroots : ∀ z : ℂ, evalC p z = 0 → z.re < -η) :
    halfPlaneConstant p η ≤ |p.leadingCoeff| := by
  unfold halfPlaneConstant
  have hprodnonneg : 0 ≤ ((complexification p).roots.map (rootWeight η)).prod := by
    apply Multiset.prod_nonneg
    intro r hr
    simp only [Multiset.mem_map] at hr
    rcases hr with ⟨z, hz, rfl⟩
    exact (rootWeight_pos (hroots z (root_of_mem_complexification_roots hz))).le
  have hprodle : ((complexification p).roots.map (rootWeight η)).prod ≤ 1 := by
    have h := Multiset.prod_map_le_prod_map₀
      (s := (complexification p).roots)
      (rootWeight η) (fun _ : ℂ ↦ (1 : ℝ))
      (fun z hz ↦ (rootWeight_pos
        (hroots z (root_of_mem_complexification_roots hz))).le)
      (fun z hz ↦ rootWeight_le_one
        (hroots z (root_of_mem_complexification_roots hz)))
    simpa using h
  exact mul_le_of_le_one_right (abs_nonneg _) hprodle

theorem halfPlaneConstant_lower_bound {p : Polynomial ℝ} {η : ℝ}
    (hp : p ≠ 0)
    (hroots : ∀ z : ℂ, evalC p z = 0 → z.re < -η)
    {z : ℂ} (hz : -η ≤ z.re) :
    halfPlaneConstant p η * (1 + ‖z‖) ^ p.natDegree ≤ ‖evalC p z‖ := by
  let pc := complexification p
  have hpc0 : pc ≠ 0 := complexification_ne_zero hp
  have hsplits : pc.Splits := IsAlgClosed.splits pc
  have hprod :
      (pc.roots.map (fun w ↦ rootWeight η w * (1 + ‖z‖))).prod ≤
        (pc.roots.map (fun w ↦ ‖z - w‖)).prod := by
    apply Multiset.prod_map_le_prod_map₀
    · intro w hw
      exact mul_nonneg (rootWeight_pos
        (hroots w (root_of_mem_complexification_roots hw))).le (by positivity)
    · intro w hw
      exact rootWeight_mul_le_norm_sub
        (hroots w (root_of_mem_complexification_roots hw)) hz
  have hcard : pc.roots.card = p.natDegree := by
    rw [← hsplits.natDegree_eq_card_roots, show pc.natDegree = p.natDegree by
      exact complexification_natDegree p]
  have heval := hsplits.eval_eq_prod_roots z
  have hnorm : ‖evalC p z‖ =
      |p.leadingCoeff| * (pc.roots.map (fun w ↦ ‖z - w‖)).prod := by
    rw [← complexification_eval] 
    rw [heval, norm_mul]
    change ‖(pc.leadingCoeff)‖ * ‖(pc.roots.map (fun w ↦ z - w)).prod‖ = _
    have hnormprod : ‖(pc.roots.map (fun w : ℂ ↦ z - w)).prod‖ =
        (pc.roots.map (fun w : ℂ ↦ ‖z - w‖)).prod := by
      exact (pc.roots.prod_hom' (NormedField.toMulRingNorm ℂ)
        (fun w : ℂ ↦ z - w)).symm
    have hlc : ‖pc.leadingCoeff‖ = |p.leadingCoeff| := by
      dsimp [pc, complexification]
      rw [Polynomial.leadingCoeff_map_of_injective
        (FaithfulSMul.algebraMap_injective ℝ ℂ)]
      simp
    rw [hlc, hnormprod]
  rw [hnorm, halfPlaneConstant]
  have hprod' :
      ((complexification p).roots.map (rootWeight η)).prod *
          (1 + ‖z‖) ^ p.natDegree ≤
        (pc.roots.map (fun w ↦ ‖z - w‖)).prod := by
    calc
      ((complexification p).roots.map (rootWeight η)).prod *
          (1 + ‖z‖) ^ p.natDegree =
          (pc.roots.map (fun w ↦ rootWeight η w * (1 + ‖z‖))).prod := by
        change ((pc.roots.map (rootWeight η)).prod *
          (1 + ‖z‖) ^ p.natDegree) = _
        rw [Multiset.prod_map_mul]
        simp only [Multiset.map_const', Multiset.prod_replicate]
        rw [hcard]
      _ ≤ (pc.roots.map (fun w ↦ ‖z - w‖)).prod := hprod
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hprod' (abs_nonneg p.leadingCoeff)

theorem degreeSafe_perturbation {p h : Polynomial ℝ} {η c : ℝ}
    (hp : p ≠ 0) (hc0 : 0 < c) (hclead : c ≤ |p.leadingCoeff|)
    (hbound : ∀ z : ℂ, -η ≤ z.re →
      c * (1 + ‖z‖) ^ p.natDegree ≤ ‖evalC p z‖)
    (hdegree : h.natDegree ≤ p.natDegree)
    (hsmall : coeffSize p.natDegree h < c) :
    (p + h).natDegree = p.natDegree ∧ p + h ≠ 0 ∧
      ∀ z : ℂ, -η ≤ z.re → evalC (p + h) z ≠ 0 := by
  have hcoeffle : |h.coeff p.natDegree| ≤ coeffSize p.natDegree h :=
    coeff_abs_le_coeffSize (by simp)
  have hcoefflt : |h.coeff p.natDegree| < |p.leadingCoeff| :=
    hcoeffle.trans_lt (hsmall.trans_le hclead)
  have htop : (p + h).coeff p.natDegree ≠ 0 := by
    rw [coeff_add, coeff_natDegree]
    intro heq
    have he : h.coeff p.natDegree = -p.leadingCoeff := by linarith
    rw [he, abs_neg] at hcoefflt
    exact (lt_irrefl _) hcoefflt
  have hdegreeSum : (p + h).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_add_le_of_degree_le le_rfl hdegree
  have hnat : (p + h).natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegreeSum htop
  have hzeroFree : ∀ z : ℂ, -η ≤ z.re → evalC (p + h) z ≠ 0 := by
    intro z hz hroot
    have heval : evalC p z + evalC h z = 0 := by
      simpa [evalC] using hroot
    have hnormeq : ‖evalC p z‖ = ‖evalC h z‖ := by
      have he : evalC p z = -evalC h z := eq_neg_of_add_eq_zero_left heval
      rw [he, norm_neg]
    have hupper := evalC_norm_le_coeffSize hdegree z
    have hlower := hbound z hz
    have hpow : 0 < (1 + ‖z‖) ^ p.natDegree := by positivity
    have hstrict : coeffSize p.natDegree h * (1 + ‖z‖) ^ p.natDegree <
        c * (1 + ‖z‖) ^ p.natDegree :=
      mul_lt_mul_of_pos_right hsmall hpow
    rw [hnormeq] at hlower
    linarith
  refine ⟨hnat, ?_, hzeroFree⟩
  intro hzero
  apply htop
  rw [hzero, coeff_zero]

theorem stable_small_smul {p h : Polynomial ℝ} {η : ℝ}
    (hp : HurwitzStable p)
    (hη0 : 0 ≤ η)
    (hmargin : ∀ z : ℂ, evalC p z = 0 → z.re < -η)
    (hdegree : h.natDegree ≤ p.natDegree) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      HurwitzStable (p + C t * h) ∧
      (p + C t * h).natDegree = p.natDegree ∧
      (∀ z : ℂ, -η ≤ z.re → evalC (p + C t * h) z ≠ 0) := by
  let c := halfPlaneConstant p η
  let S := coeffSize p.natDegree h
  let e := c / (S + 1)
  have hc : 0 < c := halfPlaneConstant_pos hp.1 hmargin
  have hS : 0 ≤ S := coeffSize_nonneg _ _
  have he : 0 < e := div_pos hc (by positivity)
  refine ⟨e, he, ?_⟩
  intro t ht
  have hdegree' : (C t * h).natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_C_mul_le t h).trans hdegree
  have hsize : coeffSize p.natDegree (C t * h) < c := by
    rw [coeffSize_C_mul]
    have := (mul_lt_mul_of_pos_right ht (by positivity : 0 < S + 1))
    change |t| * S < c
    dsimp [e] at this
    rw [div_mul_cancel₀ c (by positivity : S + 1 ≠ 0)] at this
    nlinarith [mul_nonneg (abs_nonneg t) hS]
  have hpert := degreeSafe_perturbation hp.1 hc
    (halfPlaneConstant_le_leadingCoeff hmargin)
    (fun z hz ↦ halfPlaneConstant_lower_bound hp.1 hmargin hz)
    hdegree' hsize
  refine ⟨⟨hpert.2.1, ?_⟩, hpert.1, hpert.2.2⟩
  intro z hz
  by_contra hnot
  exact hpert.2.2 z (by linarith) hz

theorem hurwitzStable_C_mul {c : ℝ} {p : Polynomial ℝ}
    (hc : c ≠ 0) (hp : HurwitzStable p) : HurwitzStable (C c * p) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hp.1, ?_⟩
  intro z hz
  have hmul : (c : ℂ) * evalC p z = 0 := by
    simpa [evalC] using hz
  have hpz : evalC p z = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (Complex.ofReal_ne_zero.mpr hc)
  exact hp.2 z hpz

theorem evalC_comp_affine (p : Polynomial ℝ) (δ t α : ℝ) (z : ℂ) :
    evalC (p.comp (affine δ t α)) z =
      evalC p ((α : ℂ) * z - (δ * t : ℝ)) := by
  unfold evalC
  rw [Polynomial.map_comp, Polynomial.eval_comp]
  simp [affine]

theorem hurwitzStable_comp_affine_of_strip {p : Polynomial ℝ}
    {δ t α η : ℝ} (hα : 0 < α) (hdt : δ * t < η)
    (hstrip : ∀ w : ℂ, -η ≤ w.re → evalC p w ≠ 0) :
    HurwitzStable (p.comp (affine δ t α)) := by
  let w : ℂ := (α : ℂ) * (0 : ℂ) - (δ * t : ℝ)
  have hwre : -η ≤ w.re := by
    dsimp [w]
    simp
    linarith
  have hzero : evalC (p.comp (affine δ t α)) 0 ≠ 0 := by
    rw [evalC_comp_affine]
    exact hstrip w hwre
  refine ⟨fun hpzero ↦ hzero (by rw [hpzero]; simp [evalC]), ?_⟩
  intro z hz
  by_contra hznot
  have hzre : 0 ≤ z.re := le_of_not_gt hznot
  let wz : ℂ := (α : ℂ) * z - (δ * t : ℝ)
  have hwzre : -η ≤ wz.re := by
    dsimp [wz]
    simp
    have := mul_nonneg hα.le hzre
    linarith
  apply hstrip wz hwzre
  rw [← evalC_comp_affine]
  exact hz

theorem aPoly_natDegree (d : ℝ) : (aPoly d).natDegree = 2 := by
  unfold aPoly
  compute_degree!

theorem bPoly_natDegree : bPoly.natDegree = 2 := by
  unfold bPoly
  compute_degree!

theorem aPoly_ne_zero (d : ℝ) : aPoly d ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  simpa [aPoly_natDegree] using this

theorem bPoly_ne_zero : bPoly ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  simpa [bPoly_natDegree] using this

theorem original_p_natDegree_of_degree_lt {d : ℝ} {x y p : Polynomial ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hdeg : y.natDegree < x.natDegree)
    (hid : p = aPoly d * x + bPoly * y) :
    p.natDegree = x.natDegree + 2 := by
  have hax : (aPoly d * x).natDegree = x.natDegree + 2 := by
    rw [Polynomial.natDegree_mul (aPoly_ne_zero d) hx, aPoly_natDegree]
    exact Nat.add_comm 2 x.natDegree
  have hby : (bPoly * y).natDegree = y.natDegree + 2 := by
    rw [Polynomial.natDegree_mul bPoly_ne_zero hy, bPoly_natDegree]
    exact Nat.add_comm 2 y.natDegree
  rw [hid, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hax
  · rw [hax, hby]
    exact Nat.add_lt_add_right hdeg 2

theorem originalWitness_improve_of_degree_lt {d : ℝ}
    {x y p : Polynomial ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (hW : OriginalWitness d x y p) (hdeg : y.natDegree < x.natDegree) :
    ∃ d' : ℝ, d < d' ∧ d' < 1 ∧
      ∃ x' y' p' : Polynomial ℝ, OriginalWitness d' x' y' p' := by
  rcases hW with ⟨hx, hy, hp, hdegree, hid⟩
  let h : Polynomial ℝ := C (-2) * X * x
  have hpdeg : p.natDegree = x.natDegree + 2 :=
    original_p_natDegree_of_degree_lt hx.1 hy.1 hdeg hid
  have hhdeg : h.natDegree ≤ p.natDegree := by
    have hh : h.natDegree ≤ x.natDegree + 1 := by
      dsimp [h]
      calc
        (C (-2 : ℝ) * X * x).natDegree ≤
            (C (-2 : ℝ) * X).natDegree + x.natDegree :=
          @Polynomial.natDegree_mul_le ℝ _ (C (-2 : ℝ) * X) x
        _ = x.natDegree + 1 := by
          rw [Polynomial.natDegree_C_mul_X (-2) (by norm_num)]
          exact Nat.add_comm 1 x.natDegree
    rw [hpdeg]
    exact hh.trans (Nat.le_succ (x.natDegree + 1))
  have hmargin : ∀ z : ℂ, evalC p z = 0 → z.re < -(0 : ℝ) := by
    intro z hz
    simpa using hp.2 z hz
  obtain ⟨e, he0, he⟩ := stable_small_smul hp (by norm_num : (0 : ℝ) ≤ 0)
    hmargin hhdeg
  let eps : ℝ := min e (1 - d) / 2
  have heps0 : 0 < eps := by
    dsimp [eps]
    exact half_pos (lt_min he0 (sub_pos.mpr hd1))
  have hepse : |eps| < e := by
    rw [abs_of_pos heps0]
    exact (div_lt_self (lt_min he0 (sub_pos.mpr hd1)) (by norm_num)).trans_le
      (min_le_left _ _)
  have hepsd : eps < 1 - d := by
    exact (div_lt_self (lt_min he0 (sub_pos.mpr hd1)) (by norm_num)).trans_le
      (min_le_right _ _)
  obtain ⟨hpstable, hpdegree, hpstrip⟩ := he eps hepse
  let p' := p + C eps * h
  have hp'id : p' = aPoly (d + eps) * x + bPoly * y := by
    apply Polynomial.funext
    intro s
    have hdirect := congrArg (fun r : Polynomial ℝ ↦ r.eval s)
      (direct_identity d eps x y)
    dsimp [p', h]
    rw [hid]
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X] at hdirect ⊢
    convert hdirect using 1 <;> ring
  refine ⟨d + eps, by linarith, by linarith, x, y, p', ?_⟩
  exact ⟨hx, hy, hpstable, hdegree, hp'id⟩

theorem originalWitness_improve_of_degree_eq {d : ℝ}
    {x y p : Polynomial ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (hW : OriginalWitness d x y p) (hdeg : y.natDegree = x.natDegree) :
    ∃ d' : ℝ, d < d' ∧ d' < 1 ∧
      ∃ x' y' p' : Polynomial ℝ, OriginalWitness d' x' y' p' := by
  rcases hW with ⟨hx, hy, hp, hdegree, hid⟩
  obtain ⟨ηx, hηx0, hηx⟩ := stable_exists_left_margin hx
  obtain ⟨ηy, hηy0, hηy⟩ := stable_exists_left_margin hy
  obtain ⟨ηp, hηp0, hηp⟩ := stable_exists_left_margin hp
  let η : ℝ := min ηx (min ηy ηp)
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min hηx0 (lt_min hηy0 hηp0)
  have hηxle : η ≤ ηx := by
    dsimp [η]
    exact min_le_left _ _
  have hηyle : η ≤ ηy := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hηple : η ≤ ηp := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hxmargin : ∀ z : ℂ, evalC x z = 0 → z.re < -η := by
    intro z hz
    exact (hηx z hz).trans_le (neg_le_neg hηxle)
  have hymargin : ∀ z : ℂ, evalC y z = 0 → z.re < -η := by
    intro z hz
    exact (hηy z hz).trans_le (neg_le_neg hηyle)
  have hpmargin : ∀ z : ℂ, evalC p z = 0 → z.re < -η := by
    intro z hz
    exact (hηp z hz).trans_le (neg_le_neg hηple)
  have hxdir : (x + y).natDegree ≤ x.natDegree := by
    apply Polynomial.natDegree_add_le_of_degree_le le_rfl
    exact hdeg.le
  have hydir : (C (1 - d ^ 2) * x + y).natDegree ≤ y.natDegree := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_C_mul_le (1 - d ^ 2) x).trans_eq hdeg.symm
    · exact le_rfl
  obtain ⟨ex, hex0, hex⟩ := stable_small_smul hx hη0.le hxmargin hxdir
  obtain ⟨ey, hey0, hey⟩ := stable_small_smul hy hη0.le hymargin hydir
  let m : ℝ := min ex (min ey (η / (d + 1)))
  let t : ℝ := m / 2
  have hden : 0 < d + 1 := by linarith
  have hm0 : 0 < m := by
    dsimp [m]
    exact lt_min hex0 (lt_min hey0 (div_pos hη0 hden))
  have ht0 : 0 < t := by
    dsimp [t]
    exact half_pos hm0
  have htex : t < ex := by
    exact (div_lt_self hm0 (by norm_num)).trans_le (min_le_left _ _)
  have htey : t < ey := by
    exact (div_lt_self hm0 (by norm_num)).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have htη : t < η / (d + 1) := by
    exact (div_lt_self hm0 (by norm_num)).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hdt : d * t < η := by
    have hsum : t * (d + 1) < η := (lt_div_iff₀ hden).1 htη
    nlinarith [mul_pos ht0 (by norm_num : (0 : ℝ) < 1)]
  obtain ⟨hXtStable, hXtDegree, hXtStrip⟩ := hex t (by simpa [abs_of_pos ht0] using htex)
  obtain ⟨hYtStable, hYtDegree, hYtStrip⟩ := hey t (by simpa [abs_of_pos ht0] using htey)
  change HurwitzStable (mixedX t x y) at hXtStable
  change (mixedX t x y).natDegree = x.natDegree at hXtDegree
  change (∀ z : ℂ, -η ≤ z.re → evalC (mixedX t x y) z ≠ 0) at hXtStrip
  change HurwitzStable (mixedY d t x y) at hYtStable
  change (mixedY d t x y).natDegree = y.natDegree at hYtDegree
  change (∀ z : ℂ, -η ≤ z.re → evalC (mixedY d t x y) z ≠ 0) at hYtStrip
  have hpStrip : ∀ z : ℂ, -η ≤ z.re → evalC p z ≠ 0 := by
    intro z hz hpz
    exact (not_lt_of_ge hz) (hpmargin z hpz)
  let α : ℝ := scale d t
  have hα0 : 0 < α := by
    dsimp [α]
    exact scale_pos ht0
  have hXcomp : HurwitzStable ((mixedX t x y).comp (affine d t α)) :=
    hurwitzStable_comp_affine_of_strip hα0 hdt hXtStrip
  have hYcomp : HurwitzStable ((mixedY d t x y).comp (affine d t α)) :=
    hurwitzStable_comp_affine_of_strip hα0 hdt hYtStrip
  have hpcomp : HurwitzStable (p.comp (affine d t α)) :=
    hurwitzStable_comp_affine_of_strip hα0 hdt hpStrip
  have hD0 : 0 < denominator d t := denominator_pos ht0.le
  have hx' : HurwitzStable (transformedX d t α x y) := by
    unfold transformedX
    exact hurwitzStable_C_mul (ne_of_gt hD0) hXcomp
  have hy' : HurwitzStable (transformedY d t α x y) := by
    exact hYcomp
  have hx'degree : (transformedX d t α x y).natDegree = x.natDegree := by
    unfold transformedX
    rw [Polynomial.natDegree_C_mul (ne_of_gt hD0),
      affine_comp_natDegree (ne_of_gt hα0), hXtDegree]
  have hy'degree : (transformedY d t α x y).natDegree = y.natDegree := by
    unfold transformedY
    rw [affine_comp_natDegree (ne_of_gt hα0), hYtDegree]
  have hparam := parameter_improves hd0 hd1 ht0
  refine ⟨improvedDelta d t, hparam.1, hparam.2,
    transformedX d t α x y, transformedY d t α x y,
    p.comp (affine d t α), ?_⟩
  refine ⟨hx', hy', hpcomp, ?_, ?_⟩
  · rw [hx'degree, hy'degree, hdeg]
  · simpa [α] using transformed_identity (δ := d) (t := t) ht0.le hid

theorem originalWitness_strict_delta_improvement {d : ℝ}
    {x y p : Polynomial ℝ} (hd0 : 0 < d) (hd1 : d < 1)
    (hW : OriginalWitness d x y p) :
    ∃ d' : ℝ, d < d' ∧ d' < 1 ∧
      ∃ x' y' p' : Polynomial ℝ, OriginalWitness d' x' y' p' := by
  rcases lt_or_eq_of_le hW.2.2.2.1 with hdeg | hdeg
  · exact originalWitness_improve_of_degree_lt hd0 hd1 hW hdeg
  · exact originalWitness_improve_of_degree_eq hd0 hd1 hW hdeg

theorem polynomialFeasible_strict_improvement_internal {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hP : PolynomialFeasible q) :
    ∃ q' : ℝ, 0 < q' ∧ q' < q ∧ PolynomialFeasible q' := by
  change Admissible (deltaOfQ q) at hP
  rcases hP with ⟨hd0, x, y, p, hW⟩
  have hd1 : deltaOfQ q < 1 := BelgianChocolate.deltaOfQ_lt_one hq0
  obtain ⟨d', hdd', hd'1, x', y', p', hW'⟩ :=
    originalWitness_strict_delta_improvement hd0 hd1 hW
  have hd'0 : 0 < d' := hd0.trans hdd'
  have hq'mem := qOfDelta_mem hd'0 hd'1
  refine ⟨qOfDelta d', hq'mem.1, ?_, ?_⟩
  · have hanti := qOfDelta_strictAnti hd0 hdd'
    rw [BelgianChocolate.qOfDelta_deltaOfQ (by linarith : q ≠ -1)] at hanti
    exact hanti
  · change Admissible (deltaOfQ (qOfDelta d'))
    rw [StrictImprovement.deltaOfQ_qOfDelta hd'0]
    exact ⟨hd'0, x', y', p', hW'⟩

end


end BelgianChocolate.StrictImprovement

namespace BelgianChocolate

theorem polynomialFeasible_strict_improvement {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hP : PolynomialFeasible q) :
    ∃ q' : ℝ, 0 < q' ∧ q' < q ∧ PolynomialFeasible q' :=
  StrictImprovement.polynomialFeasible_strict_improvement_internal hq0 hq1 hP

end BelgianChocolate
