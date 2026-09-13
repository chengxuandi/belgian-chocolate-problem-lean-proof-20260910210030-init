import BCPThreshold.DiscFunctionFourFactors
import BCPThreshold.CoefficientBounds
import BCPThreshold.RCFRoute1.TrueHierarchy
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Taylor coefficients of four factors satisfy every finite hierarchy level
-/

namespace BelgianChocolate.Route1

open Set Metric Complex
open TrueHierarchy

noncomputable section

def analyticCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

theorem analyticCoefficient_factorFunction {q : ℝ} (F : FourFactors q)
    (i : Fin 4) (n : ℕ) :
    analyticCoefficient (Schottky.factorFunction F i) n =
      Schottky.taylorCoefficient F i n := rfl

theorem analyticCoefficient_eq_of_eqOn {f g : ℂ → ℂ}
    (hfg : Set.EqOn f g unitDisc) (n : ℕ) :
    analyticCoefficient f n = analyticCoefficient g n := by
  unfold analyticCoefficient
  rw [hfg.iteratedDeriv_of_isOpen Metric.isOpen_ball n (by simp [unitDisc])]

theorem analyticCoefficient_add {f g : ℂ → ℂ} {n : ℕ}
    (hf : DifferentiableOn ℂ f unitDisc) (hg : DifferentiableOn ℂ g unitDisc) :
    analyticCoefficient (f + g) n = analyticCoefficient f n + analyticCoefficient g n := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hfc : ContDiffAt ℂ n f 0 :=
    (hf.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds h0)
  have hgc : ContDiffAt ℂ n g 0 :=
    (hg.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds h0)
  simp only [analyticCoefficient, iteratedDeriv_add hfc hgc]
  ring

theorem analyticCoefficient_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    analyticCoefficient (fun z => c * f z) n = c * analyticCoefficient f n := by
  simp [analyticCoefficient, iteratedDeriv_const_mul_field]
  ring

theorem analyticCoefficient_mul {f g : ℂ → ℂ} {n : ℕ}
    (hf : DifferentiableOn ℂ f unitDisc) (hg : DifferentiableOn ℂ g unitDisc) :
    analyticCoefficient (f * g) n =
      ∑ i ∈ Finset.range (n + 1), analyticCoefficient f i * analyticCoefficient g (n - i) := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hfc : ContDiffAt ℂ n f 0 :=
    (hf.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds h0)
  have hgc : ContDiffAt ℂ n g 0 :=
    (hg.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds h0)
  rw [analyticCoefficient, iteratedDeriv_mul hfc hgc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [analyticCoefficient, analyticCoefficient]
  have hfac : (n.choose i : ℂ) * (i.factorial : ℂ) *
      ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni0 : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hi0, hni0, hn0]
  linear_combination hfac * iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0

theorem analyticCoefficient_monomial_mul (s n : ℕ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f unitDisc) :
    analyticCoefficient ((fun z : ℂ => z ^ s) * f) n =
      if s ≤ n then analyticCoefficient f (n - s) else 0 := by
  rw [analyticCoefficient_mul
    (f := fun z : ℂ => z ^ s) (g := f) (differentiableOn_id.pow s) hf]
  by_cases hsn : s ≤ n
  · rw [if_pos hsn]
    rw [Finset.sum_eq_single s]
    · simp only [analyticCoefficient, iteratedDeriv_fun_pow_zero, if_pos rfl]
      have hs0 : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
      simp only [if_true]
      field_simp [hs0]
    · intro i hi his
      have hz : iteratedDeriv i (fun z : ℂ => z ^ s) 0 = 0 := by
        rw [iteratedDeriv_fun_pow_zero]
        simp [his]
      simp [analyticCoefficient, hz]
    · simp [hsn]
  · rw [if_neg hsn]
    apply Finset.sum_eq_zero
    intro i hi
    have his : i ≠ s := by
      intro his
      subst i
      exact hsn (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    have hz : iteratedDeriv i (fun z : ℂ => z ^ s) 0 = 0 := by
      rw [iteratedDeriv_fun_pow_zero]
      simp [his]
    simp [analyticCoefficient, hz]

theorem deriv_symm_on_unitDisc {f : ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, f (star z) = star (f z)) :
    ∀ z ∈ unitDisc, deriv f (star z) = star (deriv f z) := by
  intro z hz
  have hzstar : star z ∈ unitDisc := by simpa [unitDisc, dist_eq_norm] using hz
  have heq : f =ᶠ[nhds (star z)] (star ∘ f ∘ star) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzstar] with w hw
    have hsw := hs (star w) (by simpa [unitDisc, dist_eq_norm] using hw)
    simpa using hsw
  calc
    deriv f (star z) = deriv (star ∘ f ∘ star) (star z) := heq.deriv_eq
    _ = star (deriv f z) := by simp

theorem iteratedDeriv_symm_on_unitDisc {f : ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, f (star z) = star (f z)) (n : ℕ) :
    ∀ z ∈ unitDisc, iteratedDeriv n f (star z) = star (iteratedDeriv n f z) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
      simpa only [iteratedDeriv_succ] using deriv_symm_on_unitDisc (ih)

theorem analyticCoefficient_im_eq_zero {f : ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, f (star z) = star (f z)) (n : ℕ) :
    (analyticCoefficient f n).im = 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hi := iteratedDeriv_symm_on_unitDisc hs n 0 h0
  have him : (iteratedDeriv n f 0).im = 0 := by
    have := congrArg Complex.im hi
    simp at this
    linarith
  simp [analyticCoefficient, him]

def factorCoefficients {q : ℝ} (F : FourFactors q) (N : ℕ) : Coefficients N :=
  fun i j => (Schottky.taylorCoefficient F i j).re

theorem factorCoefficient_cast {q : ℝ} (F : FourFactors q) (i : Fin 4) (n : ℕ) :
    ((Schottky.taylorCoefficient F i n).re : ℂ) = Schottky.taylorCoefficient F i n := by
  have hs : ∀ z ∈ unitDisc,
      Schottky.factorFunction F i (star z) = star (Schottky.factorFunction F i z) := by
    fin_cases i
    · exact F.holSymm_u.2
    · exact F.holSymm_v.2
    · exact F.holSymm_uInv.2
    · exact F.holSymm_vInv.2
  apply Complex.ext
  · simp
  · simp [← analyticCoefficient_factorFunction F i n,
      analyticCoefficient_im_eq_zero hs]

theorem analyticCoefficient_const_one (n : ℕ) :
    analyticCoefficient (fun _ : ℂ => (1 : ℂ)) n = (TrueHierarchy.deltaZero n : ℂ) := by
  simp [analyticCoefficient, iteratedDeriv_const, TrueHierarchy.deltaZero]
  split <;> simp_all

theorem fourFactors_product_coefficient {q : ℝ} (F : FourFactors q)
    (a b : Fin 4)
    (hab : ∀ z ∈ unitDisc,
      Schottky.factorFunction F a z * Schottky.factorFunction F b z = 1)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      Schottky.taylorCoefficient F a i *
        Schottky.taylorCoefficient F b (n - i)) =
      (TrueHierarchy.deltaZero n : ℂ) := by
  let fa := Schottky.factorFunction F a
  let fb := Schottky.factorFunction F b
  have heq : Set.EqOn (fa * fb) (fun _ : ℂ => (1 : ℂ)) unitDisc := by
    intro z hz
    exact hab z hz
  have hc := analyticCoefficient_eq_of_eqOn heq n
  rw [analyticCoefficient_mul (Schottky.factorFunction_differentiableOn F a)
    (Schottky.factorFunction_differentiableOn F b)] at hc
  rw [analyticCoefficient_const_one] at hc
  simpa [fa, fb, analyticCoefficient_factorFunction] using hc

theorem fourFactors_linear_coefficient {q : ℝ} (F : FourFactors q) (n : ℕ) :
    (if 1 ≤ n then Schottky.taylorCoefficient F uFamily (n - 1) else 0) +
      (if 2 ≤ n then Schottky.taylorCoefficient F vFamily (n - 2) else 0) +
      (q : ℂ) * Schottky.taylorCoefficient F vFamily n =
        (TrueHierarchy.deltaZero n : ℂ) := by
  let u := Schottky.factorFunction F uFamily
  let v := Schottky.factorFunction F vFamily
  let zu : ℂ → ℂ := (fun z : ℂ => z ^ 1) * u
  let z2v : ℂ → ℂ := (fun z : ℂ => z ^ 2) * v
  let qv : ℂ → ℂ := fun z => (q : ℂ) * v z
  let lhs : ℂ → ℂ := zu + z2v + qv
  have hu : DifferentiableOn ℂ u unitDisc :=
    Schottky.factorFunction_differentiableOn F uFamily
  have hv : DifferentiableOn ℂ v unitDisc :=
    Schottky.factorFunction_differentiableOn F vFamily
  have hzu : DifferentiableOn ℂ zu unitDisc := (differentiableOn_id.pow 1).mul hu
  have hz2v : DifferentiableOn ℂ z2v unitDisc := (differentiableOn_id.pow 2).mul hv
  have hqv : DifferentiableOn ℂ qv unitDisc := by
    intro z hz
    exact ((differentiableAt_const (c := (q : ℂ))).mul
      ((hv z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have heq : Set.EqOn lhs (fun _ : ℂ => (1 : ℂ)) unitDisc := by
    intro z hz
    have h := F.linear z hz
    dsimp [lhs, zu, z2v, qv, u, v, Schottky.factorFunction, uFamily, vFamily]
    linear_combination h
  have hc := analyticCoefficient_eq_of_eqOn heq n
  have hlhs : analyticCoefficient lhs n =
      analyticCoefficient zu n + analyticCoefficient z2v n + analyticCoefficient qv n := by
    change analyticCoefficient (zu + z2v + qv) n = _
    rw [analyticCoefficient_add (hzu.add hz2v) hqv,
      analyticCoefficient_add hzu hz2v]
  rw [hlhs, analyticCoefficient_monomial_mul 1 n u hu,
    analyticCoefficient_monomial_mul 2 n v hv,
    analyticCoefficient_const_mul (q : ℂ) v n,
    analyticCoefficient_const_one] at hc
  simpa [u, v, zu, z2v, qv, analyticCoefficient_factorFunction] using hc

theorem factorCoefficients_coeffAt {q : ℝ} (F : FourFactors q) {N : ℕ}
    (a : Fin 4) {j : ℕ} (hj : j < N + 1) :
    TrueHierarchy.coeffAt (factorCoefficients F N) a j =
      (Schottky.taylorCoefficient F a j).re := by
  simp [TrueHierarchy.coeffAt, factorCoefficients, hj]

theorem factorCoefficients_shiftedCoeff {q : ℝ} (F : FourFactors q) {N : ℕ}
    (a : Fin 4) (k : Fin (N + 1)) (s : ℕ) :
    TrueHierarchy.shiftedCoeff (factorCoefficients F N) a k s =
      if s ≤ (k : ℕ) then (Schottky.taylorCoefficient F a (k - s)).re else 0 := by
  by_cases hs : s ≤ (k : ℕ)
  · rw [if_pos hs]
    rw [TrueHierarchy.shiftedCoeff, if_pos hs]
    exact factorCoefficients_coeffAt F a
      (lt_of_le_of_lt (Nat.sub_le _ _) k.isLt)
  · simp [TrueHierarchy.shiftedCoeff, hs]

theorem factorCoefficients_convolution_cast {q : ℝ} (F : FourFactors q) {N : ℕ}
    (a b : Fin 4) (k : Fin (N + 1)) :
    (TrueHierarchy.convolution (factorCoefficients F N) a b k : ℂ) =
      ∑ i ∈ Finset.range ((k : ℕ) + 1),
        Schottky.taylorCoefficient F a i *
          Schottky.taylorCoefficient F b ((k : ℕ) - i) := by
  rw [TrueHierarchy.convolution]
  rw [AllOrders.list_sum_map_range_eq_finset]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ (k : ℕ) := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [factorCoefficients_coeffAt F a (lt_of_le_of_lt hik k.isLt),
    factorCoefficients_coeffAt F b
      (lt_of_le_of_lt (Nat.sub_le _ _) k.isLt)]
  rw [factorCoefficient_cast F a i, factorCoefficient_cast F b ((k : ℕ) - i)]

theorem factorCoefficients_constraints {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hqb : (q : ℝ) ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors (q : ℝ)) (N : ℕ) :
    TrueHierarchy.Constraints N q (factorCoefficients F N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a j
    exact (abs_re_le_norm (Schottky.taylorCoefficient F a j)).trans
      (Schottky.coefficientBound hq0 hqb F a j)
  · intro k
    have hc := congrArg Complex.re (fourFactors_linear_coefficient F (k : ℕ))
    rw [factorCoefficients_shiftedCoeff F uFamily k 1,
      factorCoefficients_shiftedCoeff F vFamily k 2,
      factorCoefficients_coeffAt F vFamily k.isLt]
    by_cases h1 : 1 ≤ (k : ℕ) <;> by_cases h2 : 2 ≤ (k : ℕ) <;>
      simp [h1, h2, Complex.add_re, Complex.mul_re] at hc ⊢
    all_goals exact hc
  · intro k
    have hc := fourFactors_product_coefficient F uFamily UFamily
      (fun z hz => F.inverse_u z hz) (k : ℕ)
    rw [← factorCoefficients_convolution_cast F uFamily UFamily k] at hc
    exact_mod_cast hc
  · intro k
    have hc := fourFactors_product_coefficient F vFamily VFamily
      (fun z hz => F.inverse_v z hz) (k : ℕ)
    rw [← factorCoefficients_convolution_cast F vFamily VFamily k] at hc
    exact_mod_cast hc

theorem fourFactors_all_levels {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hqb : (q : ℝ) ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors (q : ℝ)) : ∀ N, TrueHierarchy.H N q := by
  intro N
  exact ⟨factorCoefficients F N, factorCoefficients_constraints hq0 hqb F N⟩

theorem analyticFeasible_all_levels {q : ℚ}
    (hq0 : 0 < (q : ℝ)) (hqb : (q : ℝ) ≤ (3 / 4 : ℝ) ^ 2)
    (hA : AnalyticFeasible (q : ℝ)) : ∀ N, TrueHierarchy.H N q := by
  obtain ⟨_, hq1, f, hf⟩ := hA
  exact fourFactors_all_levels hq0 hqb (discFunctionToFourFactors hq0 hq1 hf)

end

end BelgianChocolate.Route1
