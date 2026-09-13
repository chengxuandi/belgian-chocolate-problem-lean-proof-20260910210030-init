/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.FinitePositiveVerifier
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.List.GetD

/-!
# Semantic bridge from executable coefficient lists to genuine polynomials
-/

namespace BelgianChocolate

open Polynomial
open FinitePositiveVerifier

noncomputable section

def polynomialOfCoeffs : List ℚ → Polynomial ℚ
  | [] => 0
  | a :: as => C a + X * polynomialOfCoeffs as

@[simp] theorem coeff_polynomialOfCoeffs (as : List ℚ) (n : ℕ) :
    (polynomialOfCoeffs as).coeff n = coeffAt as n := by
  induction as generalizing n with
  | nil => simp [polynomialOfCoeffs, coeffAt]
  | cons a as ih =>
      cases n with
      | zero => simp [polynomialOfCoeffs, coeffAt]
      | succ n => simp [polynomialOfCoeffs, coeffAt, ih]

theorem evalRatC_add (p r : Polynomial ℚ) (z : ℂ) :
    evalRatC (p + r) z = evalRatC p z + evalRatC r z := by
  simp [evalRatC]

theorem evalRatC_mul (p r : Polynomial ℚ) (z : ℂ) :
    evalRatC (p * r) z = evalRatC p z * evalRatC r z := by
  simp [evalRatC]

theorem evalRatC_polynomialOfCoeffs (as : List ℚ) (z : ℂ) :
    evalRatC (polynomialOfCoeffs as) z = evalCoeffs as z := by
  induction as with
  | nil => simp [polynomialOfCoeffs, evalRatC, evalCoeffs]
  | cons a as ih =>
      change evalRatC (C a + X * polynomialOfCoeffs as) z = _
      rw [evalRatC_add, evalRatC_mul, ih]
      simp [evalRatC, evalCoeffs]

theorem zeroFree_polynomialOfCoeffs {as : List ℚ}
    (h : CoeffsClosedDiscZeroFree as) :
    RatClosedDiscZeroFree (polynomialOfCoeffs as) := by
  intro z hz
  rw [evalRatC_polynomialOfCoeffs]
  exact h z hz

theorem coeff_X_mul_polynomialOfCoeffs (as : List ℚ) (k : ℕ) :
    (X * polynomialOfCoeffs as).coeff k = shiftedCoeff as k 1 := by
  by_cases hk : 1 ≤ k
  · have heq : k - 1 + 1 = k := by omega
    rw [shiftedCoeff, if_pos hk, ← heq, coeff_X_mul,
      coeff_polynomialOfCoeffs]
    apply congrArg (coeffAt as)
    omega
  · have hk0 : k = 0 := by omega
    subst k
    simp [shiftedCoeff]

theorem coeff_X_sq_mul_polynomialOfCoeffs (as : List ℚ) (k : ℕ) :
    (X ^ 2 * polynomialOfCoeffs as).coeff k = shiftedCoeff as k 2 := by
  by_cases hk : 2 ≤ k
  · have heq : k - 2 + 2 = k := by omega
    rw [shiftedCoeff, if_pos hk, ← heq, coeff_X_pow_mul,
      coeff_polynomialOfCoeffs]
    apply congrArg (coeffAt as)
    omega
  · interval_cases k
    · simp [shiftedCoeff]
    · rw [show X ^ 2 * polynomialOfCoeffs as =
        X * (X * polynomialOfCoeffs as) by simp [pow_two, mul_assoc]]
      rw [show (1 : ℕ) = 0 + 1 by omega]
      rw [coeff_X_mul]
      simp [shiftedCoeff]

theorem exactPolynomialIdentity_of_exactListIdentity {q : ℚ} {u v : List ℚ}
    (h : ExactBezoutIdentity q u v) :
    X * polynomialOfCoeffs u + (X ^ 2 + C q) * polynomialOfCoeffs v = 1 := by
  ext k
  rw [coeff_add, coeff_X_mul_polynomialOfCoeffs]
  rw [add_mul, coeff_add, coeff_X_sq_mul_polynomialOfCoeffs]
  simp only [coeff_C_mul, coeff_polynomialOfCoeffs]
  rw [coeff_one]
  calc
    shiftedCoeff u k 1 + (shiftedCoeff v k 2 + q * coeffAt v k) =
        bezoutCoeff q u v k := by simp [bezoutCoeff, add_assoc]
    _ = deltaZero k := h k
    _ = (if k = 0 then 1 else 0) := rfl

theorem exactListIdentity_of_exactPolynomialIdentity {q : ℚ} {u v : List ℚ}
    (h : X * polynomialOfCoeffs u + (X ^ 2 + C q) * polynomialOfCoeffs v = 1) :
    ExactBezoutIdentity q u v := by
  intro k
  have hk := congrArg (fun p : Polynomial ℚ => p.coeff k) h
  rw [coeff_add, coeff_X_mul_polynomialOfCoeffs] at hk
  rw [add_mul, coeff_add, coeff_X_sq_mul_polynomialOfCoeffs] at hk
  simp only [coeff_C_mul, coeff_polynomialOfCoeffs, coeff_one] at hk
  simpa [bezoutCoeff, deltaZero, add_assoc] using hk

def coefficientCode (p : Polynomial ℚ) : List ℚ :=
  (List.range (p.natDegree + 1)).map p.coeff

theorem coeffAt_coefficientCode (p : Polynomial ℚ) (k : ℕ) :
    coeffAt (coefficientCode p) k = p.coeff k := by
  by_cases hk : k < p.natDegree + 1
  · rw [coeffAt, List.getD_eq_getElem?_getD]
    simp [coefficientCode, hk]
  · have hdeg : p.natDegree < k := by omega
    rw [coeffAt, List.getD_eq_getElem?_getD]
    simp [coefficientCode, hk, coeff_eq_zero_of_natDegree_lt hdeg]

theorem polynomialOfCoeffs_coefficientCode (p : Polynomial ℚ) :
    polynomialOfCoeffs (coefficientCode p) = p := by
  ext k
  rw [coeff_polynomialOfCoeffs, coeffAt_coefficientCode]

theorem ratFactors_finiteCertificate {q : ℚ} {u v : Polynomial ℚ}
    (hq : 0 < q) (h : RatClosedDiscFactors q u v) :
    FinitePositiveCertificate q (coefficientCode u) (coefficientCode v) := by
  refine ⟨hq, ?_, ?_, ?_⟩
  · apply exactListIdentity_of_exactPolynomialIdentity
    simpa [polynomialOfCoeffs_coefficientCode] using h.2.2
  · intro z hz
    rw [← evalRatC_polynomialOfCoeffs, polynomialOfCoeffs_coefficientCode]
    exact h.1 z hz
  · intro z hz
    rw [← evalRatC_polynomialOfCoeffs, polynomialOfCoeffs_coefficientCode]
    exact h.2.1 z hz

theorem positiveCertificate_finiteCertificate {q : ℚ} {v : Polynomial ℚ}
    (h : PositiveCertificate q v) :
    ∃ us vs : List ℚ, FinitePositiveCertificate q us vs := by
  let u := derivedU q v
  have hfac : RatClosedDiscFactors q u v :=
    ⟨h.2.2.2, h.2.2.1, positiveCertificate_exact_identity h⟩
  exact ⟨coefficientCode u, coefficientCode v, ratFactors_finiteCertificate h.1 hfac⟩

theorem finiteCertificate_ratFactors {q : ℚ} {u v : List ℚ}
    (h : FinitePositiveCertificate q u v) :
    RatClosedDiscFactors q (polynomialOfCoeffs u) (polynomialOfCoeffs v) := by
  exact ⟨zeroFree_polynomialOfCoeffs h.2.2.1,
    zeroFree_polynomialOfCoeffs h.2.2.2,
    exactPolynomialIdentity_of_exactListIdentity h.2.1⟩

theorem finiteCertificate_positiveCertificate {q : ℚ} {u v : List ℚ}
    (h : FinitePositiveCertificate q u v) :
    PositiveCertificate q (polynomialOfCoeffs v) := by
  exact positiveCertificate_of_ratFactors h.1 (finiteCertificate_ratFactors h)

theorem executable_positive_sound {stage : ℕ} {q : ℚ}
    (h : positive stage q = true) :
    ∃ v : Polynomial ℚ, PositiveCertificate q v := by
  obtain ⟨u, v, huv⟩ := positive_sound h
  exact ⟨polynomialOfCoeffs v, finiteCertificate_positiveCertificate huv⟩

theorem executable_positive_complete {q : ℚ}
    (h : ∃ v : Polynomial ℚ, PositiveCertificate q v) :
    ∃ stage, positive stage q = true := by
  obtain ⟨v, hv⟩ := h
  exact positive_complete (positiveCertificate_finiteCertificate hv)

end

end BelgianChocolate
