/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.Definitions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.FieldSimp

/-!
# Polynomial--analytic interface for the Belgian Chocolate problem

This file fixes the concrete analytic predicates.  In particular it does not identify
polynomial and analytic feasibility at the endpoint.
-/

namespace BelgianChocolate

open Set Metric Polynomial Complex

noncomputable section

def unitDisc : Set ℂ := Metric.ball 0 1

def closedUnitDisc : Set ℂ := Metric.closedBall 0 1

def HolSymmOn (r : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 r) ∧
    ∀ z : ℂ, z ∈ Metric.ball 0 r → f (star z) = star (f z)

/-- The literal `F_(sqrt q)` formulation from the manuscript. -/
def DiscFunction (q : ℝ) (f : ℂ → ℂ) : Prop :=
  HolSymmOn 1 f ∧
  (∀ z ∈ unitDisc, f z = 0 ↔ z = 0) ∧
  deriv f 0 ≠ 0 ∧
  (∀ z ∈ unitDisc,
    f z = 1 ↔ z = Complex.I * (Real.sqrt q : ℂ) ∨
      z = -(Complex.I * (Real.sqrt q : ℂ))) ∧
  deriv f (Complex.I * (Real.sqrt q : ℂ)) ≠ 0 ∧
  deriv f (-(Complex.I * (Real.sqrt q : ℂ))) ≠ 0

def AnalyticFeasible (q : ℝ) : Prop :=
  0 < q ∧ q < 1 ∧ ∃ f : ℂ → ℂ, DiscFunction q f

/-- The exact zero-free four-factor representation. -/
structure FourFactors (q : ℝ) where
  u : ℂ → ℂ
  v : ℂ → ℂ
  uInv : ℂ → ℂ
  vInv : ℂ → ℂ
  holSymm_u : HolSymmOn 1 u
  holSymm_v : HolSymmOn 1 v
  holSymm_uInv : HolSymmOn 1 uInv
  holSymm_vInv : HolSymmOn 1 vInv
  linear : ∀ z ∈ unitDisc, z * u z + (z ^ 2 + (q : ℂ)) * v z = 1
  inverse_u : ∀ z ∈ unitDisc, u z * uInv z = 1
  inverse_v : ∀ z ∈ unitDisc, v z * vInv z = 1

/-- Polynomial factors with the strict closed-disc margin used for realization. -/
def RealClosedDiscFactors (q : ℝ) (u v : Polynomial ℝ) : Prop :=
  (∀ z : ℂ, z ∈ closedUnitDisc → evalC u z ≠ 0) ∧
  (∀ z : ℂ, z ∈ closedUnitDisc → evalC v z ≠ 0) ∧
  X * u + (X ^ 2 + C q) * v = 1

theorem deltaOfQ_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    0 < deltaOfQ q := by
  rw [deltaOfQ]
  exact div_pos (sub_pos.mpr h1) (by linarith)

theorem deltaOfQ_lt_one {q : ℝ} (h0 : 0 < q) : deltaOfQ q < 1 := by
  rw [deltaOfQ]
  rw [div_lt_one (by linarith)]
  linarith

theorem qOfDelta_deltaOfQ {q : ℝ} (hq : q ≠ -1) :
    qOfDelta (deltaOfQ q) = q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  have hnum : 1 - (1 - q) / (1 + q) = 2 * q / (1 + q) := by
    field_simp [hden]
    ring
  have hden' : 1 + (1 - q) / (1 + q) = 2 / (1 + q) := by
    field_simp [hden]
    ring
  rw [qOfDelta, deltaOfQ, hnum, hden']
  field_simp [hden]

theorem deltaOfQ_qOfDelta {δ : ℝ} (hδ : δ ≠ -1) :
    deltaOfQ (qOfDelta δ) = δ := by
  have hden : 1 + δ ≠ 0 := by
    intro h
    apply hδ
    linarith
  have hnum : 1 - (1 - δ) / (1 + δ) = 2 * δ / (1 + δ) := by
    field_simp [hden]
    ring
  have hden' : 1 + (1 - δ) / (1 + δ) = 2 / (1 + δ) := by
    field_simp [hden]
    ring
  rw [deltaOfQ, qOfDelta, hnum, hden']
  field_simp [hden]

theorem parameter_transform (q : ℝ) (h0 : 0 < q) (h1 : q < 1) :
    0 < deltaOfQ q ∧ deltaOfQ q < 1 ∧ qOfDelta (deltaOfQ q) = q := by
  exact ⟨deltaOfQ_pos h0 h1, deltaOfQ_lt_one h0,
    qOfDelta_deltaOfQ (by linarith)⟩

theorem parameter_antitone {q r : ℝ}
    (hq : 0 < q) (hqr : q < r) (hr : r < 1) :
    deltaOfQ r < deltaOfQ q := by
  rw [deltaOfQ, deltaOfQ]
  have hqden : 0 < 1 + q := by linarith
  have hrden : 0 < 1 + r := by linarith
  rw [div_lt_div_iff₀ hrden hqden]
  nlinarith

theorem qOfDelta_antitone {δ ε : ℝ}
    (hδ : 0 < δ) (hδε : δ < ε) : qOfDelta ε < qOfDelta δ := by
  rw [qOfDelta, qOfDelta]
  have hδden : 0 < 1 + δ := by linarith
  have hεden : 0 < 1 + ε := by linarith
  rw [div_lt_div_iff₀ hεden hδden]
  nlinarith

/-- This is deliberately only the forward implication.  No endpoint equivalence is stated. -/
def PolynomialToAnalyticStatement : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → PolynomialFeasible q → AnalyticFeasible q

/-- Strict-slack realization is the correct reverse interface. -/
def StrictSlackRealizationStatement : Prop :=
  ∀ r q : ℝ, 0 < r → r < q → q < 1 →
    AnalyticFeasible r → PolynomialFeasible q

end

end BelgianChocolate
