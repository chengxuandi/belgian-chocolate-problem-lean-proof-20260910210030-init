/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.PolynomialAnalyticInterface
import BCPThreshold.RCFRoute1.CompactSemialgebraic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Finite positive certificates

This file separates the mathematical certificate predicate from its finite verifier.
-/

namespace BelgianChocolate

open Set Metric Polynomial

noncomputable section

def evalRatC (p : Polynomial ℚ) (z : ℂ) : ℂ :=
  (p.map (algebraMap ℚ ℂ)).eval z

def RatClosedDiscZeroFree (p : Polynomial ℚ) : Prop :=
  ∀ z : ℂ, z ∈ closedUnitDisc → evalRatC p z ≠ 0

def derivedNumerator (q : ℚ) (v : Polynomial ℚ) : Polynomial ℚ :=
  1 - (X ^ 2 + C q) * v

def derivedU (q : ℚ) (v : Polynomial ℚ) : Polynomial ℚ :=
  (derivedNumerator q v).divX

def PositiveCertificate (q : ℚ) (v : Polynomial ℚ) : Prop :=
  0 < q ∧ v.coeff 0 = 1 / q ∧
    RatClosedDiscZeroFree v ∧ RatClosedDiscZeroFree (derivedU q v)

/-- Rational polynomial factors before packaging them as the one-polynomial certificate. -/
def RatClosedDiscFactors (q : ℚ) (u v : Polynomial ℚ) : Prop :=
  RatClosedDiscZeroFree u ∧ RatClosedDiscZeroFree v ∧
    X * u + (X ^ 2 + C q) * v = 1

theorem derivedNumerator_coeff_zero {q : ℚ} {v : Polynomial ℚ}
    (hq : q ≠ 0) (hv : v.coeff 0 = 1 / q) :
    (derivedNumerator q v).coeff 0 = 0 := by
  simp [derivedNumerator, hv, hq]

/-- The constant-term condition makes division by `X` exact. -/
theorem X_mul_derivedU {q : ℚ} {v : Polynomial ℚ}
    (hq : q ≠ 0) (hv : v.coeff 0 = 1 / q) :
    X * derivedU q v = derivedNumerator q v := by
  have h0 := derivedNumerator_coeff_zero hq hv
  have h := X_mul_divX_add (derivedNumerator q v)
  rw [h0, C_0, add_zero] at h
  exact h

/-- Every positive certificate carries the exact Bézout identity; `u` is not an
independently approximated polynomial. -/
theorem positiveCertificate_exact_identity {q : ℚ} {v : Polynomial ℚ}
    (h : PositiveCertificate q v) :
    X * derivedU q v + (X ^ 2 + C q) * v = 1 := by
  rw [X_mul_derivedU (ne_of_gt h.1) h.2.1]
  simp [derivedNumerator]

def ratToReal (p : Polynomial ℚ) : Polynomial ℝ := p.map (algebraMap ℚ ℝ)

theorem ratToReal_map_complex (p : Polynomial ℚ) :
    (ratToReal p).map (algebraMap ℝ ℂ) = p.map (algebraMap ℚ ℂ) := by
  rw [ratToReal, Polynomial.map_map]
  ext x
  simp

theorem evalC_ratToReal (p : Polynomial ℚ) (z : ℂ) :
    evalC (ratToReal p) z = evalRatC p z := by
  rw [evalC, evalRatC, ratToReal_map_complex]

theorem ratClosedDisc_to_real {p : Polynomial ℚ}
    (h : RatClosedDiscZeroFree p) :
    ∀ z : ℂ, z ∈ closedUnitDisc → evalC (ratToReal p) z ≠ 0 := by
  intro z hz
  rw [evalC_ratToReal]
  exact h z hz

theorem positiveCertificate_real_factors {q : ℚ} {v : Polynomial ℚ}
    (h : PositiveCertificate q v) :
    RealClosedDiscFactors (q : ℝ) (ratToReal (derivedU q v)) (ratToReal v) := by
  refine ⟨ratClosedDisc_to_real h.2.2.2, ratClosedDisc_to_real h.2.2.1, ?_⟩
  have hid := congrArg (fun p : Polynomial ℚ => p.map (algebraMap ℚ ℝ))
    (positiveCertificate_exact_identity h)
  simpa [ratToReal, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] using hid

theorem divX_X_mul (p : Polynomial ℚ) : (X * p).divX = p := by
  ext n
  simp [Polynomial.coeff_divX]

/-- Exact rational factors produce the manuscript's finite one-polynomial certificate.
No approximation statement is assumed here. -/
theorem positiveCertificate_of_ratFactors {q : ℚ} {u v : Polynomial ℚ}
    (hq : 0 < q) (hfac : RatClosedDiscFactors q u v) :
    PositiveCertificate q v := by
  have hconst : v.coeff 0 = 1 / q := by
    have h0 := congrArg (fun p : Polynomial ℚ => p.coeff 0) hfac.2.2
    simp at h0
    exact (eq_div_iff (ne_of_gt hq)).2 (by linarith)
  have hnum : derivedNumerator q v = X * u := by
    rw [derivedNumerator]
    rw [← hfac.2.2]
    ring
  have hu : derivedU q v = u := by
    rw [derivedU, hnum, divX_X_mul]
  exact ⟨hq, hconst, hfac.2.1, by simpa [hu] using hfac.1⟩

end

end BelgianChocolate
