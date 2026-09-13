/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.PositiveVerifier
import Mathlib.Data.List.GetD

/-!
# A finite executable language for positive certificates

Polynomials are represented by finite lists of rational coefficients in ascending degree
order.  Thus all operations used by the checker are executable; no decision procedure for an
infinite analytic predicate is invoked.
-/

namespace BelgianChocolate

open Route1 PositiveVerifier

namespace FinitePositiveVerifier

def evalCoeffs : List ℚ → ℂ → ℂ
  | [], _ => 0
  | a :: as, z => (a : ℂ) + z * evalCoeffs as z

def compileCoeffs : List ℚ → ComplexSyntax
  | [] => cconst 0
  | a :: as => cadd (cconst a) (cmul cvar (compileCoeffs as))

theorem eval_compileCoeffs (as : List ℚ) (x : Fin 3 → ℝ) :
    evalComplexSyntax (compileCoeffs as) x = evalCoeffs as (point x) := by
  induction as with
  | nil => simp [compileCoeffs, evalCoeffs]
  | cons a as ih => simp [compileCoeffs, evalCoeffs, eval_cadd, eval_cmul, ih]

def coeffRootEquations (as : List ℚ) : List (RatPoly 3) :=
  [(compileCoeffs as).re, (compileCoeffs as).im, sphereEquation]

def coeffsNoRootAtDepth (as : List ℚ) (depth : ℕ) : Bool :=
  systemInfeasible (coeffRootEquations as) depth

def CoeffsClosedDiscZeroFree (as : List ℚ) : Prop :=
  ∀ z : ℂ, z ∈ closedUnitDisc → evalCoeffs as z ≠ 0

theorem coeffRootEquations_solution_gives_root {as : List ℚ} {x : Fin 3 → ℝ}
    (hx : RatPoly.InCube x)
    (heq : ∀ e ∈ coeffRootEquations as, e.evalR x = 0) :
    point x ∈ closedUnitDisc ∧ evalCoeffs as (point x) = 0 := by
  have hre := heq (compileCoeffs as).re (by simp [coeffRootEquations])
  have him := heq (compileCoeffs as).im (by simp [coeffRootEquations])
  have hs := heq sphereEquation (by simp [coeffRootEquations])
  refine ⟨point_mem_closedDisc_of_sphere hx hs, ?_⟩
  rw [← eval_compileCoeffs]
  simp [evalComplexSyntax, evalSyntax, hre, him]

theorem coeffRootEquations_infeasible_iff (as : List ℚ) :
    ¬ EquationSystemFeasible (coeffRootEquations as) ↔ CoeffsClosedDiscZeroFree as := by
  constructor
  · intro h z hz hzero
    obtain ⟨x, hx, hpoint, hsphere⟩ := exists_cube_sphere_lift hz
    apply h
    refine ⟨x, hx, ?_⟩
    have hcompile : evalComplexSyntax (compileCoeffs as) x = 0 := by
      rw [eval_compileCoeffs, hpoint, hzero]
    have hre : (compileCoeffs as).re.evalR x = 0 := by
      have ht := congrArg Complex.re hcompile
      simpa [evalComplexSyntax, evalSyntax] using ht
    have him : (compileCoeffs as).im.evalR x = 0 := by
      have ht := congrArg Complex.im hcompile
      simpa [evalComplexSyntax, evalSyntax] using ht
    intro e he
    simp [coeffRootEquations] at he
    rcases he with rfl | rfl | rfl
    · exact hre
    · exact him
    · exact hsphere
  · intro h hfeas
    obtain ⟨x, hx, heq⟩ := hfeas
    obtain ⟨hz, hzero⟩ := coeffRootEquations_solution_gives_root hx heq
    exact h (point x) hz hzero

theorem coeffsNoRootAtDepth_sound {as : List ℚ} {depth : ℕ}
    (h : coeffsNoRootAtDepth as depth = true) : CoeffsClosedDiscZeroFree as := by
  rw [← coeffRootEquations_infeasible_iff]
  exact systemInfeasible_sound h

theorem coeffsNoRootAtDepth_complete {as : List ℚ}
    (h : CoeffsClosedDiscZeroFree as) :
    ∃ depth, coeffsNoRootAtDepth as depth = true := by
  apply systemInfeasible_complete (coeffRootEquations as)
  exact (coeffRootEquations_infeasible_iff as).2 h

def coeffAt (as : List ℚ) (k : ℕ) : ℚ := as.getD k 0

def shiftedCoeff (as : List ℚ) (k shift : ℕ) : ℚ :=
  if shift ≤ k then coeffAt as (k - shift) else 0

def deltaZero (k : ℕ) : ℚ := if k = 0 then 1 else 0

def bezoutCoeff (q : ℚ) (u v : List ℚ) (k : ℕ) : ℚ :=
  shiftedCoeff u k 1 + shiftedCoeff v k 2 + q * coeffAt v k

def identityExtent (u v : List ℚ) : ℕ := max u.length v.length + 2

def identityCheck (q : ℚ) (u v : List ℚ) : Bool :=
  (List.range (identityExtent u v)).all fun k => decide (bezoutCoeff q u v k = deltaZero k)

def ExactBezoutIdentity (q : ℚ) (u v : List ℚ) : Prop :=
  ∀ k : ℕ, bezoutCoeff q u v k = deltaZero k

theorem identityCheck_sound {q : ℚ} {u v : List ℚ}
    (h : identityCheck q u v = true) : ExactBezoutIdentity q u v := by
  intro k
  by_cases hk : k < identityExtent u v
  · rw [identityCheck, List.all_eq_true] at h
    have hk' := h k (List.mem_range.mpr hk)
    simpa using hk'
  · have hku : u.length ≤ k - 1 := by
      rw [identityExtent] at hk
      omega
    have hkv0 : v.length ≤ k := by
      rw [identityExtent] at hk
      omega
    have hkv2 : v.length ≤ k - 2 := by
      rw [identityExtent] at hk
      omega
    have hk1 : 1 ≤ k := by
      rw [identityExtent] at hk
      omega
    have hk2 : 2 ≤ k := by
      rw [identityExtent] at hk
      omega
    have hk0 : k ≠ 0 := by omega
    have hu0 : coeffAt u (k - 1) = 0 := by
      exact List.getD_eq_default u 0 hku
    have hv0 : coeffAt v k = 0 := by
      exact List.getD_eq_default v 0 hkv0
    have hv2 : coeffAt v (k - 2) = 0 := by
      exact List.getD_eq_default v 0 hkv2
    simp [bezoutCoeff, shiftedCoeff, deltaZero, hk1, hk2, hk0, hu0, hv0, hv2]

theorem identityCheck_complete {q : ℚ} {u v : List ℚ}
    (h : ExactBezoutIdentity q u v) : identityCheck q u v = true := by
  rw [identityCheck, List.all_eq_true]
  intro k hk
  simp only [decide_eq_true_eq]
  exact h k

def FinitePositiveCertificate (q : ℚ) (u v : List ℚ) : Prop :=
  0 < q ∧ ExactBezoutIdentity q u v ∧
    CoeffsClosedDiscZeroFree u ∧ CoeffsClosedDiscZeroFree v

def certificateAt (q : ℚ) (u v : List ℚ) (du dv : ℕ) : Bool :=
  decide (0 < q) && identityCheck q u v &&
    coeffsNoRootAtDepth u du && coeffsNoRootAtDepth v dv

theorem certificateAt_sound {q : ℚ} {u v : List ℚ} {du dv : ℕ}
    (h : certificateAt q u v du dv = true) : FinitePositiveCertificate q u v := by
  simp only [certificateAt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, identityCheck_sound h.1.1.2,
    coeffsNoRootAtDepth_sound h.1.2, coeffsNoRootAtDepth_sound h.2⟩

theorem certificateAt_complete {q : ℚ} {u v : List ℚ}
    (h : FinitePositiveCertificate q u v) :
    ∃ du dv, certificateAt q u v du dv = true := by
  obtain ⟨du, hdu⟩ := coeffsNoRootAtDepth_complete h.2.2.1
  obtain ⟨dv, hdv⟩ := coeffsNoRootAtDepth_complete h.2.2.2
  refine ⟨du, dv, ?_⟩
  simp [certificateAt, h.1, identityCheck_complete h.2.1, hdu, hdv]

def candidateAtCode (code : ℕ) : Option (List ℚ × List ℚ) :=
  Encodable.decode code

/-- Fair finite search through every finite rational coefficient pair and both grid depths. -/
def positive (stage : ℕ) (q : ℚ) : Bool :=
  (List.range (stage + 1)).any fun code =>
    match candidateAtCode code with
    | none => false
    | some (u, v) =>
        (List.range (stage + 1)).any fun du =>
          (List.range (stage + 1)).any fun dv => certificateAt q u v du dv

theorem positive_sound {stage : ℕ} {q : ℚ} (h : positive stage q = true) :
    ∃ u v : List ℚ, FinitePositiveCertificate q u v := by
  rw [positive, List.any_eq_true] at h
  obtain ⟨code, hcode, hc⟩ := h
  cases hcv : candidateAtCode code with
  | none => simp [hcv] at hc
  | some pair =>
    rcases pair with ⟨u, v⟩
    simp only [hcv] at hc
    rw [List.any_eq_true] at hc
    obtain ⟨du, hdu, hc⟩ := hc
    rw [List.any_eq_true] at hc
    obtain ⟨dv, hdv, hc⟩ := hc
    exact ⟨u, v, certificateAt_sound hc⟩

theorem positive_complete {q : ℚ}
    (h : ∃ u v : List ℚ, FinitePositiveCertificate q u v) :
    ∃ stage, positive stage q = true := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨du, dv, hcert⟩ := certificateAt_complete huv
  let code := Encodable.encode (u, v)
  let stage := max code (max du dv)
  refine ⟨stage, ?_⟩
  rw [positive, List.any_eq_true]
  refine ⟨code, List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_max_left _ _)), ?_⟩
  have hdecode : candidateAtCode code = some (u, v) := Encodable.encodek _
  rw [hdecode, List.any_eq_true]
  refine ⟨du, List.mem_range.mpr (Nat.lt_succ_of_le
    ((Nat.le_max_left du dv).trans (Nat.le_max_right code (max du dv)))), ?_⟩
  rw [List.any_eq_true]
  exact ⟨dv, List.mem_range.mpr (Nat.lt_succ_of_le
    ((Nat.le_max_right du dv).trans (Nat.le_max_right code (max du dv)))), hcert⟩

end FinitePositiveVerifier

end BelgianChocolate
