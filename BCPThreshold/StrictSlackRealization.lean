import BCPThreshold.RationalPositiveCertificate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Strict-slack polynomial realization

This file reuses Module 3 at a rational intermediate parameter and rescales its
finite factors to an arbitrary real target parameter. Finite Cayley
homogenization then constructs an actual `OriginalWitness`, including its
exact identity, strict stability, and actual-degree condition.
-/

namespace BelgianChocolate

open Polynomial

noncomputable section

def rescaleDiscU (lam : ℝ) (u : Polynomial ℝ) : Polynomial ℝ :=
  C lam * u.comp (C lam * X)

def rescaleDiscV (lam : ℝ) (v : Polynomial ℝ) : Polynomial ℝ :=
  C (lam ^ 2) * v.comp (C lam * X)

theorem evalC_comp_scale (f : Polynomial ℝ) (lam : ℝ) (z : ℂ) :
    evalC (f.comp (C lam * X)) z = evalC f ((lam : ℂ) * z) := by
  unfold evalC
  rw [Polynomial.map_comp, Polynomial.eval_comp]
  simp

theorem rescale_mem_closedUnitDisc {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {z : ℂ} (hz : z ∈ closedUnitDisc) : (lam : ℂ) * z ∈ closedUnitDisc := by
  have hz' : ‖z‖ ≤ 1 := by simpa [closedUnitDisc] using hz
  have hn : ‖(lam : ℂ) * z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0]
    exact (mul_le_mul_of_nonneg_left hz' hlam0).trans (by simpa using hlam1)
  simpa [closedUnitDisc] using hn

theorem realClosedDiscFactors_rescale {a q lam : ℝ} {u v : Polynomial ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hrel : lam ^ 2 * q = a)
    (h : RealClosedDiscFactors a u v) :
    RealClosedDiscFactors q (rescaleDiscU lam u) (rescaleDiscV lam v) := by
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam0.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hu := h.1 ((lam : ℂ) * z) (rescale_mem_closedUnitDisc hlam0.le hlam1 hz)
    change evalC (C lam * u.comp (C lam * X)) z ≠ 0
    have he : evalC (C lam * u.comp (C lam * X)) z =
        (lam : ℂ) * evalC u ((lam : ℂ) * z) := by
      rw [show evalC (C lam * u.comp (C lam * X)) z =
        (lam : ℂ) * evalC (u.comp (C lam * X)) z by simp [evalC], evalC_comp_scale]
    rw [he]
    exact mul_ne_zero hlamC hu
  · intro z hz
    have hv := h.2.1 ((lam : ℂ) * z) (rescale_mem_closedUnitDisc hlam0.le hlam1 hz)
    change evalC (C (lam ^ 2) * v.comp (C lam * X)) z ≠ 0
    have he : evalC (C (lam ^ 2) * v.comp (C lam * X)) z =
        (lam : ℂ) ^ 2 * evalC v ((lam : ℂ) * z) := by
      rw [show evalC (C (lam ^ 2) * v.comp (C lam * X)) z =
        (lam : ℂ) ^ 2 * evalC (v.comp (C lam * X)) z by simp [evalC], evalC_comp_scale]
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ hlamC) hv
  · apply Polynomial.funext
    intro s
    have hi := congrArg (fun f : Polynomial ℝ => f.eval (lam * s)) h.2.2
    simp only [rescaleDiscU, rescaleDiscV, eval_add, eval_mul, eval_pow,
      eval_C, eval_X, eval_comp, eval_one] at hi ⊢
    rw [← hrel] at hi
    convert hi using 1 <;> ring

theorem strictSlack_realClosedDiscFactors {r q : ℝ}
    (hr0 : 0 < r) (hrq : r < q) (hq1 : q < 1) (hA : AnalyticFeasible r) :
    ∃ u v : Polynomial ℝ, RealClosedDiscFactors q u v := by
  obtain ⟨a, hra, haq⟩ := exists_rat_btwn hrq
  obtain ⟨v, hv⟩ := strictAnalyticFeasible_positiveCertificate hra (haq.trans hq1) hA
  have ha0 : 0 < (a : ℝ) := hr0.trans hra
  have hq0 : 0 < q := hr0.trans hrq
  let lam : ℝ := Real.sqrt ((a : ℝ) / q)
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos ha0 hq0)
  have hlamsq : lam ^ 2 = (a : ℝ) / q := Real.sq_sqrt (div_pos ha0 hq0).le
  have hlam1 : lam ≤ 1 := by
    have hratio : (a : ℝ) / q < 1 := (div_lt_one hq0).mpr haq
    nlinarith
  have hrel : lam ^ 2 * q = (a : ℝ) := by
    rw [hlamsq, div_mul_cancel₀ _ hq0.ne']
  exact ⟨_, _, realClosedDiscFactors_rescale hlam0 hlam1 hrel
    (positiveCertificate_real_factors hv)⟩

/-- Common-degree inverse-Cayley homogenization: a finite real polynomial. -/
def cayleyHomogenize (n : ℕ) (f : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), C (f.coeff k) * (X - 1) ^ k * (X + 1) ^ (n - k)

def discWitnessDegree (u v : Polynomial ℝ) : ℕ := max u.natDegree v.natDegree

def discWitnessX (q : ℝ) (u v : Polynomial ℝ) : Polynomial ℝ :=
  C (1 + q) * cayleyHomogenize (discWitnessDegree u v) v

def discWitnessY (u v : Polynomial ℝ) : Polynomial ℝ :=
  cayleyHomogenize (discWitnessDegree u v) u

def discWitnessP (u v : Polynomial ℝ) : Polynomial ℝ :=
  (X + 1) ^ (discWitnessDegree u v + 2)

theorem eval₂_cayleyHomogenize {K : Type*} [Field K] (φ : ℝ →+* K)
    {n : ℕ} {f : Polynomial ℝ} (hf : f.natDegree ≤ n)
    {s : K} (hs : s + 1 ≠ 0) :
    (cayleyHomogenize n f).eval₂ φ s =
      (s + 1) ^ n * f.eval₂ φ ((s - 1) / (s + 1)) := by
  rw [Polynomial.eval₂_eq_sum_range' φ (Nat.lt_succ_of_le hf)]
  simp only [cayleyHomogenize, eval₂_finset_sum, eval₂_mul, eval₂_C,
    eval₂_pow, eval₂_sub, eval₂_add, eval₂_X, eval₂_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have he : (s + 1) ^ n = (s + 1) ^ k * (s + 1) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [he, div_pow]
  field_simp

theorem evalC_cayleyHomogenize {n : ℕ} {f : Polynomial ℝ}
    (hf : f.natDegree ≤ n) {s : ℂ} (hs : s + 1 ≠ 0) :
    evalC (cayleyHomogenize n f) s =
      (s + 1) ^ n * evalC f ((s - 1) / (s + 1)) := by
  simpa only [evalC, Polynomial.eval_map] using
    eval₂_cayleyHomogenize (algebraMap ℝ ℂ) hf hs

theorem homogenize_basis_monic (n k : ℕ) :
    (((X : Polynomial ℝ) - 1) ^ k * (X + 1) ^ (n-k)).Monic := by
  have hm : ((X : Polynomial ℝ) - 1).Monic := by simpa using monic_X_sub_C (1 : ℝ)
  have hp : ((X : Polynomial ℝ) + 1).Monic := by simpa using monic_X_add_C (1 : ℝ)
  exact (hm.pow k).mul (hp.pow (n-k))

theorem homogenize_basis_degree {n k : ℕ} (hk : k ≤ n) :
    (((X : Polynomial ℝ) - 1) ^ k * (X + 1) ^ (n-k)).natDegree = n := by
  have hm : ((X : Polynomial ℝ) - 1).Monic := by simpa using monic_X_sub_C (1 : ℝ)
  have hp : ((X : Polynomial ℝ) + 1).Monic := by simpa using monic_X_add_C (1 : ℝ)
  rw [(hm.pow k).natDegree_mul (hp.pow (n-k)), natDegree_pow, natDegree_pow]
  have hd1 : ((X : Polynomial ℝ) - 1).natDegree = 1 := by
    simpa using natDegree_X_sub_C (1 : ℝ)
  have hd2 : ((X : Polynomial ℝ) + 1).natDegree = 1 := by
    simpa using natDegree_X_add_C (1 : ℝ)
  rw [hd1, hd2]
  simpa using Nat.add_sub_of_le hk

theorem cayleyHomogenize_natDegree_le (n : ℕ) (f : Polynomial ℝ) :
    (cayleyHomogenize n f).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  rw [mul_assoc]
  exact (natDegree_C_mul_le _ _).trans_eq
    (homogenize_basis_degree (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

theorem cayleyHomogenize_coeff_top {n : ℕ} {f : Polynomial ℝ}
    (hf : f.natDegree ≤ n) :
    (cayleyHomogenize n f).coeff n = f.eval 1 := by
  have hev := Polynomial.eval₂_eq_sum_range' (RingHom.id ℝ)
    (Nat.lt_succ_of_le hf) (1 : ℝ)
  have he : f.eval 1 = ∑ k ∈ Finset.range (n+1), f.coeff k := by
    simpa using hev
  rw [he]
  simp only [cayleyHomogenize, finset_sum_coeff, mul_assoc, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hd := homogenize_basis_degree (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hc : (((X : Polynomial ℝ) - 1) ^ k * (X + 1) ^ (n-k)).coeff n = 1 := by
    have htop := (homogenize_basis_monic n k)
    have hc' : (((X : Polynomial ℝ) - 1) ^ k * (X + 1) ^ (n-k)).coeff
        (((X : Polynomial ℝ) - 1) ^ k * (X + 1) ^ (n-k)).natDegree = 1 := by
      rw [coeff_natDegree]
      exact htop
    rwa [hd] at hc'
  rw [hc, mul_one]

theorem cayleyHomogenize_natDegree {n : ℕ} {f : Polynomial ℝ}
    (hf : f.natDegree ≤ n) (h1 : f.eval 1 ≠ 0) :
    (cayleyHomogenize n f).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (cayleyHomogenize_natDegree_le n f)
  rwa [cayleyHomogenize_coeff_top hf]

theorem inverseCayley_den_ne_zero {s : ℂ} (hs : 0 ≤ s.re) : s + 1 ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp at this
  linarith

theorem inverseCayley_mem_closedUnitDisc {s : ℂ} (hs : 0 ≤ s.re) :
    (s - 1) / (s + 1) ∈ closedUnitDisc := by
  have hden := inverseCayley_den_ne_zero hs
  have hnorm : ‖s - 1‖ ≤ ‖s + 1‖ := by
    have he1 := Complex.sq_norm (s - 1)
    have he2 := Complex.sq_norm (s + 1)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      sub_zero, add_zero] at he1 he2
    nlinarith [norm_nonneg (s - 1), norm_nonneg (s + 1)]
  have hratio : ‖(s - 1) / (s + 1)‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hden)).mpr hnorm
  simpa [closedUnitDisc] using hratio

theorem cayleyHomogenize_stable {n : ℕ} {f : Polynomial ℝ}
    (hf : f.natDegree ≤ n)
    (hzf : ∀ z : ℂ, z ∈ closedUnitDisc → evalC f z ≠ 0) :
    HurwitzStable (cayleyHomogenize n f) := by
  have hfree : ∀ s : ℂ, 0 ≤ s.re → evalC (cayleyHomogenize n f) s ≠ 0 := by
    intro s hs
    rw [evalC_cayleyHomogenize hf (inverseCayley_den_ne_zero hs)]
    exact mul_ne_zero (pow_ne_zero _ (inverseCayley_den_ne_zero hs))
      (hzf _ (inverseCayley_mem_closedUnitDisc hs))
  refine ⟨?_, ?_⟩
  · intro he
    have hn := hfree 0 (by simp)
    apply hn
    simp [he, evalC]
  · intro s hs
    by_contra hn
    exact hfree s (le_of_not_gt hn) hs

theorem discWitness_identity {q : ℝ} {u v : Polynomial ℝ}
    (hq : 1 + q ≠ 0) (h : RealClosedDiscFactors q u v) :
    discWitnessP u v =
      aPoly (deltaOfQ q) * discWitnessX q u v +
      bPoly * discWitnessY u v := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro s hs
  have hs0 : 0 ≤ s := hs
  have hsne : s + 1 ≠ 0 := by linarith
  let n := discWitnessDegree u v
  let w := (s - 1) / (s + 1)
  have hu : u.natDegree ≤ n := le_max_left _ _
  have hv : v.natDegree ≤ n := le_max_right _ _
  have heu : (cayleyHomogenize n u).eval s = (s + 1) ^ n * u.eval w := by
    simpa only [Polynomial.eval₂_id] using eval₂_cayleyHomogenize (RingHom.id ℝ) hu hsne
  have hev : (cayleyHomogenize n v).eval s = (s + 1) ^ n * v.eval w := by
    simpa only [Polynomial.eval₂_id] using eval₂_cayleyHomogenize (RingHom.id ℝ) hv hsne
  have hi := congrArg (fun f : Polynomial ℝ => f.eval w) h.2.2
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one] at hi
  have hc : (s + 1)^2 = (s^2 - 1) * u.eval w +
      ((s - 1)^2 + q * (s + 1)^2) * v.eval w := by
    dsimp [w] at hi
    field_simp [hsne] at hi
    dsimp [w]
    nlinarith [hi]
  have ha : (s^2 - 2 * deltaOfQ q * s + 1) * (1 + q) =
      (s - 1)^2 + q * (s + 1)^2 := by
    unfold deltaOfQ
    field_simp [hq]
    ring
  change (discWitnessP u v).eval s = _
  simp only [discWitnessP, discWitnessX, discWitnessY, eval_add,
    eval_mul, eval_C, eval_pow, eval_X, eval_one]
  change (s + 1) ^ (n + 2) =
    (aPoly (deltaOfQ q)).eval s * ((1 + q) * (cayleyHomogenize n v).eval s) +
      bPoly.eval s * (cayleyHomogenize n u).eval s
  rw [heu, hev]
  simp only [aPoly, bPoly, eval_add, eval_sub, eval_mul, eval_pow,
    eval_X, eval_C, eval_one]
  calc
    (s + 1) ^ (n + 2) = (s + 1)^n * (s + 1)^2 := pow_add _ _ _
    _ = (s + 1)^n * ((s^2 - 1) * u.eval w +
        ((s - 1)^2 + q * (s + 1)^2) * v.eval w) :=
      congrArg (fun t : ℝ => (s + 1)^n * t) hc
    _ = _ := by rw [← ha]; ring

theorem closedDisc_eval_one_ne_zero {f : Polynomial ℝ}
    (hf : ∀ z : ℂ, z ∈ closedUnitDisc → evalC f z ≠ 0) : f.eval 1 ≠ 0 := by
  intro he
  have hn := hf 1 (by simp [closedUnitDisc])
  apply hn
  unfold evalC
  rw [Polynomial.eval_map]
  change f.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) 1) = 0
  rw [Polynomial.eval₂_at_apply, he, map_zero]

theorem discWitnessP_stable (u v : Polynomial ℝ) : HurwitzStable (discWitnessP u v) := by
  have hm : ((X : Polynomial ℝ) + 1).Monic := by simpa using monic_X_add_C (1 : ℝ)
  refine ⟨(hm.pow _).ne_zero, ?_⟩
  intro s hs
  have he : (s + 1) ^ (discWitnessDegree u v + 2) = 0 := by
    simpa [discWitnessP, evalC] using hs
  have he' : s + 1 = 0 := by
    by_contra hn
    exact (pow_ne_zero _ hn) he
  have hre := congrArg Complex.re he'
  simp at hre
  linarith

theorem realClosedDiscFactors_originalWitness {q : ℝ} {u v : Polynomial ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (h : RealClosedDiscFactors q u v) :
    OriginalWitness (deltaOfQ q)
      (discWitnessX q u v) (discWitnessY u v) (discWitnessP u v) := by
  have hqne : 1 + q ≠ 0 := by positivity
  have hu : u.natDegree ≤ discWitnessDegree u v := le_max_left _ _
  have hv : v.natDegree ≤ discWitnessDegree u v := le_max_right _ _
  have hy : HurwitzStable (discWitnessY u v) := cayleyHomogenize_stable hu h.1
  have hxbase := cayleyHomogenize_stable hv h.2.1
  have hx : HurwitzStable (discWitnessX q u v) := by
    refine ⟨mul_ne_zero (C_ne_zero.mpr hqne) hxbase.1, ?_⟩
    intro s hs
    have hmul : ((1 + q : ℝ) : ℂ) * evalC
        (cayleyHomogenize (discWitnessDegree u v) v) s = 0 := by
      simpa [discWitnessX, evalC] using hs
    exact hxbase.2 s ((mul_eq_zero.mp hmul).resolve_left
      (Complex.ofReal_ne_zero.mpr hqne))
  refine ⟨hx, hy, discWitnessP_stable u v, ?_, discWitness_identity hqne h⟩
  simp only [discWitnessX, discWitnessY, natDegree_C_mul hqne]
  rw [cayleyHomogenize_natDegree hu (closedDisc_eval_one_ne_zero h.1),
    cayleyHomogenize_natDegree hv (closedDisc_eval_one_ne_zero h.2.1)]

theorem realClosedDiscFactors_polynomialFeasible {q : ℝ} {u v : Polynomial ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (h : RealClosedDiscFactors q u v) :
    PolynomialFeasible q :=
  ⟨deltaOfQ_pos hq0 hq1, discWitnessX q u v, discWitnessY u v, discWitnessP u v,
    realClosedDiscFactors_originalWitness hq0 hq1 h⟩

theorem positiveCertificate_polynomialFeasible {q : ℚ} {v : Polynomial ℚ}
    (hq1 : (q : ℝ) < 1) (h : PositiveCertificate q v) :
    PolynomialFeasible (q : ℝ) :=
  realClosedDiscFactors_polynomialFeasible (by exact_mod_cast h.1) hq1
    (positiveCertificate_real_factors h)

theorem strictSlackRealization : StrictSlackRealizationStatement := by
  intro r q hr0 hrq hq1 hA
  obtain ⟨u, v, hfac⟩ := strictSlack_realClosedDiscFactors hr0 hrq hq1 hA
  exact realClosedDiscFactors_polynomialFeasible (hr0.trans hrq) hq1 hfac

end

end BelgianChocolate
