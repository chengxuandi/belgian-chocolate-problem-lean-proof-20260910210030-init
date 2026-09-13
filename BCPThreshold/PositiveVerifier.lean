/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.PositiveCertificate

/-!
# Executable closed-disc verifier for positive certificates

A root in the closed unit disc is encoded by three real variables `a,b,t` on the unit cube,
with `a^2+b^2+t^2=1`.  This turns closed-disc root existence into a finite compact rational
polynomial equation system and permits reuse of the E08 grid semidecider.
-/

namespace BelgianChocolate

open Polynomial
open Route1

namespace PositiveVerifier

abbrev P3 := RatPoly 3

structure ComplexSyntax where
  re : P3
  im : P3

def cconst (q : ℚ) : ComplexSyntax := ⟨.const q, .const 0⟩

def cvar : ComplexSyntax :=
  ⟨.var ⟨0, by norm_num⟩, .var ⟨1, by norm_num⟩⟩

def cadd (x y : ComplexSyntax) : ComplexSyntax :=
  ⟨.add x.re y.re, .add x.im y.im⟩

def cmul (x y : ComplexSyntax) : ComplexSyntax :=
  ⟨.add (.mul x.re y.re) (.neg (.mul x.im y.im)),
   .add (.mul x.re y.im) (.mul x.im y.re)⟩

def cpow (x : ComplexSyntax) : ℕ → ComplexSyntax
  | 0 => cconst 1
  | n + 1 => cmul (cpow x n) x

def scale (q : ℚ) (x : ComplexSyntax) : ComplexSyntax :=
  ⟨.mul (.const q) x.re, .mul (.const q) x.im⟩

def csum : List ComplexSyntax → ComplexSyntax
  | [] => cconst 0
  | x :: xs => cadd x (csum xs)

/-- Exact compiler for evaluation of a rational polynomial at `a+bi`. -/
def compileEval (p : Polynomial ℚ) : ComplexSyntax :=
  csum ((List.range (p.natDegree + 1)).map fun n =>
    scale (p.coeff n) (cpow cvar n))

def evalSyntax (p : P3) (x : Fin 3 → ℝ) : ℝ := p.evalR x

def evalComplexSyntax (p : ComplexSyntax) (x : Fin 3 → ℝ) : ℂ :=
  (evalSyntax p.re x : ℂ) + Complex.I * (evalSyntax p.im x : ℂ)

def point (x : Fin 3 → ℝ) : ℂ := (x 0 : ℂ) + Complex.I * (x 1 : ℂ)

@[simp] theorem eval_cconst (q : ℚ) (x : Fin 3 → ℝ) :
    evalComplexSyntax (cconst q) x = q := by
  simp [evalComplexSyntax, evalSyntax, cconst, RatPoly.evalR]

@[simp] theorem eval_cvar (x : Fin 3 → ℝ) :
    evalComplexSyntax cvar x = point x := by
  simp [evalComplexSyntax, evalSyntax, cvar, point, RatPoly.evalR]

theorem eval_cadd (a b : ComplexSyntax) (x : Fin 3 → ℝ) :
    evalComplexSyntax (cadd a b) x = evalComplexSyntax a x + evalComplexSyntax b x := by
  simp [evalComplexSyntax, evalSyntax, cadd, RatPoly.evalR]
  ring

theorem eval_cmul (a b : ComplexSyntax) (x : Fin 3 → ℝ) :
    evalComplexSyntax (cmul a b) x = evalComplexSyntax a x * evalComplexSyntax b x := by
  apply Complex.ext <;>
    simp [evalComplexSyntax, evalSyntax, cmul, RatPoly.evalR] <;> ring

theorem eval_cpow (a : ComplexSyntax) (n : ℕ) (x : Fin 3 → ℝ) :
    evalComplexSyntax (cpow a n) x = evalComplexSyntax a x ^ n := by
  induction n with
  | zero => simp [cpow]
  | succ n ih => simp [cpow, eval_cmul, ih, pow_succ]

theorem eval_scale (q : ℚ) (a : ComplexSyntax) (x : Fin 3 → ℝ) :
    evalComplexSyntax (scale q a) x = (q : ℂ) * evalComplexSyntax a x := by
  simp [evalComplexSyntax, evalSyntax, scale, RatPoly.evalR]
  ring

theorem eval_csum (xs : List ComplexSyntax) (x : Fin 3 → ℝ) :
    evalComplexSyntax (csum xs) x = (xs.map fun a => evalComplexSyntax a x).sum := by
  induction xs with
  | nil => simp [csum]
  | cons a xs ih => simp [csum, eval_cadd, ih]

theorem eval_compileEval (p : Polynomial ℚ) (x : Fin 3 → ℝ) :
    evalComplexSyntax (compileEval p) x = evalRatC p (point x) := by
  have hsum (n : ℕ) :
      ((List.range n).map fun i =>
        (p.coeff i : ℂ) * point x ^ i).sum =
        ∑ i ∈ Finset.range n, (p.coeff i : ℂ) * point x ^ i := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  rw [compileEval, eval_csum, evalRatC, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum_range]
  rw [List.map_map]
  have hmap :
      (List.range (p.natDegree + 1)).map
          ((fun a => evalComplexSyntax a x) ∘ fun n => scale (p.coeff n) (cpow cvar n)) =
        (List.range (p.natDegree + 1)).map fun i =>
          (p.coeff i : ℂ) * point x ^ i := by
    apply List.map_congr_left
    intro i hi
    simp [eval_scale, eval_cpow, eval_cvar]
  rw [hmap]
  exact hsum (p.natDegree + 1)

def sphereEquation : P3 :=
  .add
    (.add (.mul (.var ⟨0, by norm_num⟩) (.var ⟨0, by norm_num⟩))
      (.mul (.var ⟨1, by norm_num⟩) (.var ⟨1, by norm_num⟩)))
    (.add (.mul (.var ⟨2, by norm_num⟩) (.var ⟨2, by norm_num⟩)) (.const (-1)))

def rootEquations (p : Polynomial ℚ) : List P3 :=
  [(compileEval p).re, (compileEval p).im, sphereEquation]

@[simp] theorem eval_sphereEquation (x : Fin 3 → ℝ) :
    sphereEquation.evalR x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 - 1 := by
  simp [sphereEquation, RatPoly.evalR]
  ring

def noRootAtDepth (p : Polynomial ℚ) (depth : ℕ) : Bool :=
  systemInfeasible (rootEquations p) depth

theorem point_mem_closedDisc_of_sphere {x : Fin 3 → ℝ}
    (hx : RatPoly.InCube x) (hsphere : sphereEquation.evalR x = 0) :
    point x ∈ closedUnitDisc := by
  have ht : 0 ≤ (x 2) ^ 2 := sq_nonneg _
  have hs : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 = 1 := by
    simp [sphereEquation, RatPoly.evalR] at hsphere
    nlinarith
  rw [closedUnitDisc, Metric.mem_closedBall, dist_zero_right]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm,
    Complex.normSq_apply]
  simp [point]
  nlinarith

theorem rootEquations_solution_gives_root {p : Polynomial ℚ}
    {x : Fin 3 → ℝ} (hx : RatPoly.InCube x)
    (heq : ∀ e ∈ rootEquations p, e.evalR x = 0) :
    point x ∈ closedUnitDisc ∧ evalRatC p (point x) = 0 := by
  have hre := heq (compileEval p).re (by simp [rootEquations])
  have him := heq (compileEval p).im (by simp [rootEquations])
  have hs := heq sphereEquation (by simp [rootEquations])
  refine ⟨point_mem_closedDisc_of_sphere hx hs, ?_⟩
  rw [← eval_compileEval]
  simp [evalComplexSyntax, evalSyntax, hre, him]

/-- Every point of the closed unit disc has a lift to the rational cube/sphere
encoding used by the finite verifier. -/
theorem exists_cube_sphere_lift {z : ℂ} (hz : z ∈ closedUnitDisc) :
    ∃ x : Fin 3 → ℝ, RatPoly.InCube x ∧ point x = z ∧ sphereEquation.evalR x = 0 := by
  let rad : ℝ := Real.sqrt (1 - Complex.normSq z)
  have hz' : ‖z‖ ≤ 1 := by simpa [closedUnitDisc] using hz
  have hnorm : Complex.normSq z ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  let x : Fin 3 → ℝ := fun i => if i = 0 then z.re else if i = 1 then z.im else rad
  have hx : RatPoly.InCube x := by
    intro i
    fin_cases i
    · simpa [x] using (Complex.abs_re_le_norm z).trans hz'
    · simpa [x] using (Complex.abs_im_le_norm z).trans hz'
    · have hr0 : 0 ≤ 1 - Complex.normSq z := sub_nonneg.mpr hnorm
      change |rad| ≤ 1
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt hr0, Complex.normSq_nonneg z]
  have hpoint : point x = z := by
    apply Complex.ext <;> simp [point, x]
  have hsphere : sphereEquation.evalR x = 0 := by
    have hr0 : 0 ≤ 1 - Complex.normSq z := sub_nonneg.mpr hnorm
    rw [eval_sphereEquation]
    have hx0 : x 0 = z.re := by simp [x]
    have hx1 : x 1 = z.im := by
      simp [x, show (1 : Fin 3) ≠ 0 by decide]
    have hx2 : x 2 = rad := by
      simp [x, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
    rw [hx0, hx1, hx2]
    change z.re * z.re + z.im * z.im +
      Real.sqrt (1 - Complex.normSq z) * Real.sqrt (1 - Complex.normSq z) - 1 = 0
    have hrsq : Real.sqrt (1 - Complex.normSq z) * Real.sqrt (1 - Complex.normSq z) =
        1 - Complex.normSq z := by
      rw [← pow_two, Real.sq_sqrt hr0]
    rw [hrsq]
    simp [Complex.normSq_apply]
  exact ⟨x, hx, hpoint, hsphere⟩

theorem noRootAtDepth_sound {p : Polynomial ℚ} {depth : ℕ}
    (h : noRootAtDepth p depth = true) : RatClosedDiscZeroFree p := by
  intro z hz hroot
  let rad : ℝ := Real.sqrt (1 - Complex.normSq z)
  have hnorm : Complex.normSq z ≤ 1 := by
    have hz' : ‖z‖ ≤ 1 := by simpa [closedUnitDisc] using hz
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  let x : Fin 3 → ℝ := fun i => if i = 0 then z.re else if i = 1 then z.im else rad
  have hx : RatPoly.InCube x := by
    intro i
    have hz' : ‖z‖ ≤ 1 := by simpa [closedUnitDisc] using hz
    fin_cases i
    · simpa [x] using (Complex.abs_re_le_norm z).trans hz'
    · simpa [x] using (Complex.abs_im_le_norm z).trans hz'
    · have hr0 : 0 ≤ 1 - Complex.normSq z := sub_nonneg.mpr hnorm
      have hrsq := Real.sq_sqrt hr0
      change |rad| ≤ 1
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Complex.normSq_nonneg z]
  have hpoint : point x = z := by
    apply Complex.ext <;> simp [point, x]
  have hsphere : sphereEquation.evalR x = 0 := by
    have hr0 : 0 ≤ 1 - Complex.normSq z := sub_nonneg.mpr hnorm
    rw [eval_sphereEquation]
    have hx0 : x 0 = z.re := by simp [x]
    have hx1 : x 1 = z.im := by
      simp [x, show (1 : Fin 3) ≠ 0 by decide]
    have hx2 : x 2 = rad := by
      simp [x, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
    rw [hx0, hx1, hx2]
    change z.re * z.re + z.im * z.im +
      Real.sqrt (1 - Complex.normSq z) * Real.sqrt (1 - Complex.normSq z) - 1 = 0
    have hrsq : Real.sqrt (1 - Complex.normSq z) * Real.sqrt (1 - Complex.normSq z) =
        1 - Complex.normSq z := by
      rw [← pow_two, Real.sq_sqrt hr0]
    rw [hrsq]
    simp [Complex.normSq_apply]
  have hcompile : evalComplexSyntax (compileEval p) x = 0 := by
    rw [eval_compileEval, hpoint, hroot]
  have hre : (compileEval p).re.evalR x = 0 := by
    have := congrArg Complex.re hcompile
    simpa [evalComplexSyntax, evalSyntax] using this
  have him : (compileEval p).im.evalR x = 0 := by
    have := congrArg Complex.im hcompile
    simpa [evalComplexSyntax, evalSyntax] using this
  apply systemInfeasible_sound h
  exact ⟨x, hx, by
    intro e he
    simp [rootEquations] at he
    rcases he with rfl | rfl | rfl
    · exact hre
    · exact him
    · exact hsphere⟩

/-- Conversely, a closed-disc root supplies a cube solution of the three exact
rational equations. -/
theorem root_gives_rootEquations_solution {p : Polynomial ℚ} {z : ℂ}
    (hz : z ∈ closedUnitDisc) (hroot : evalRatC p z = 0) :
    EquationSystemFeasible (rootEquations p) := by
  let rad : ℝ := Real.sqrt (1 - Complex.normSq z)
  have hz' : ‖z‖ ≤ 1 := by simpa [closedUnitDisc] using hz
  have hnorm : Complex.normSq z ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  let x : Fin 3 → ℝ := fun i => if i = 0 then z.re else if i = 1 then z.im else rad
  have hx : RatPoly.InCube x := by
    intro i
    fin_cases i
    · simpa [x] using (Complex.abs_re_le_norm z).trans hz'
    · simpa [x] using (Complex.abs_im_le_norm z).trans hz'
    · have hr0 : 0 ≤ 1 - Complex.normSq z := sub_nonneg.mpr hnorm
      change |rad| ≤ 1
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt hr0, Complex.normSq_nonneg z]
  have hpoint : point x = z := by
    apply Complex.ext <;> simp [point, x]
  have hsphere : sphereEquation.evalR x = 0 := by
    have hr0 : 0 ≤ 1 - Complex.normSq z := sub_nonneg.mpr hnorm
    rw [eval_sphereEquation]
    have hx0 : x 0 = z.re := by simp [x]
    have hx1 : x 1 = z.im := by
      simp [x, show (1 : Fin 3) ≠ 0 by decide]
    have hx2 : x 2 = rad := by
      simp [x, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
    rw [hx0, hx1, hx2]
    change z.re * z.re + z.im * z.im +
      Real.sqrt (1 - Complex.normSq z) * Real.sqrt (1 - Complex.normSq z) - 1 = 0
    have hrsq : Real.sqrt (1 - Complex.normSq z) * Real.sqrt (1 - Complex.normSq z) =
        1 - Complex.normSq z := by
      rw [← pow_two, Real.sq_sqrt hr0]
    rw [hrsq]
    simp [Complex.normSq_apply]
  have hcompile : evalComplexSyntax (compileEval p) x = 0 := by
    rw [eval_compileEval, hpoint, hroot]
  have hre : (compileEval p).re.evalR x = 0 := by
    have h := congrArg Complex.re hcompile
    simpa [evalComplexSyntax, evalSyntax] using h
  have him : (compileEval p).im.evalR x = 0 := by
    have h := congrArg Complex.im hcompile
    simpa [evalComplexSyntax, evalSyntax] using h
  refine ⟨x, hx, ?_⟩
  intro e he
  simp [rootEquations] at he
  rcases he with rfl | rfl | rfl
  · exact hre
  · exact him
  · exact hsphere

theorem rootEquations_infeasible_iff (p : Polynomial ℚ) :
    ¬ EquationSystemFeasible (rootEquations p) ↔ RatClosedDiscZeroFree p := by
  constructor
  · intro h z hz hroot
    exact h (root_gives_rootEquations_solution hz hroot)
  · intro h hfeas
    obtain ⟨x, hx, heq⟩ := hfeas
    obtain ⟨hz, hroot⟩ := rootEquations_solution_gives_root hx heq
    exact h (point x) hz hroot

theorem noRootAtDepth_complete {p : Polynomial ℚ}
    (h : RatClosedDiscZeroFree p) : ∃ depth, noRootAtDepth p depth = true := by
  apply systemInfeasible_complete (rootEquations p)
  exact (rootEquations_infeasible_iff p).2 h

end PositiveVerifier

end BelgianChocolate
