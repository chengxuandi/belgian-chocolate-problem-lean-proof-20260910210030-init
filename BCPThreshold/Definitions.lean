import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Belgian Chocolate Problem: stable definitions

This file fixes the original polynomial problem and the abstract interfaces used to isolate the
not-yet-formalized analytic core. No analytic theorem is assumed globally: future implementations
must construct the interface structures below.
-/

namespace BelgianChocolate

open Polynomial

noncomputable section

/-- Evaluation of a real polynomial at a complex point. -/
def evalC (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  (p.map (algebraMap ℝ ℂ)).eval z

/-- Strict Hurwitz stability. The explicit nonzero clause makes nonzero constants stable and
excludes the zero polynomial. -/
def HurwitzStable (p : Polynomial ℝ) : Prop :=
  p ≠ 0 ∧ ∀ z : ℂ, evalC p z = 0 → z.re < 0

/-- The first fixed quadratic in the original problem. -/
def aPoly (δ : ℝ) : Polynomial ℝ :=
  X ^ 2 - C (2 * δ) * X + 1

/-- The second fixed quadratic in the original problem. -/
def bPoly : Polynomial ℝ := X ^ 2 - 1

/-- A witness for the original simultaneous-stabilization formulation. -/
def OriginalWitness (δ : ℝ) (x y p : Polynomial ℝ) : Prop :=
  HurwitzStable x ∧ HurwitzStable y ∧ HurwitzStable p ∧
    y.natDegree ≤ x.natDegree ∧ p = aPoly δ * x + bPoly * y

/-- Original polynomial admissibility. -/
def Admissible (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ x y p : Polynomial ℝ, OriginalWitness δ x y p

/-- The decreasing change from the original parameter to the analytic parameter. -/
def qOfDelta (δ : ℝ) : ℝ := (1 - δ) / (1 + δ)

/-- The inverse parameter change. -/
def deltaOfQ (q : ℝ) : ℝ := (1 - q) / (1 + q)

/-- Original feasibility expressed in the analytic parameter. -/
def PolynomialFeasible (q : ℝ) : Prop := Admissible (deltaOfQ q)

/-- A rational interval used by the certified threshold algorithm. -/
structure RatInterval where
  left : ℚ
  right : ℚ
deriving DecidableEq, Repr

namespace RatInterval

/-- Rational width. -/
def width (I : RatInterval) : ℚ := I.right - I.left

/-- The left trisection point. -/
def leftThird (I : RatInterval) : ℚ := (2 * I.left + I.right) / 3

/-- The right trisection point. -/
def rightThird (I : RatInterval) : ℚ := (I.left + 2 * I.right) / 3

/-- Replace the left endpoint. -/
def raiseLeft (I : RatInterval) (q : ℚ) : RatInterval := ⟨q, I.right⟩

/-- Replace the right endpoint. -/
def lowerRight (I : RatInterval) (q : ℚ) : RatInterval := ⟨I.left, q⟩

end RatInterval

/-- A rational interval strictly brackets a real number. -/
def StrictlyBrackets (x : ℝ) (I : RatInterval) : Prop :=
  (I.left : ℝ) < x ∧ x < (I.right : ℝ)

/-- The invariant used by every call of the threshold subdivision routine. -/
def BracketInvariant (Q : ℝ) (I : RatInterval) : Prop :=
  0 ≤ I.left ∧ I.right ≤ (1 : ℚ) / 2 ∧ StrictlyBrackets Q I

/-- `J` is a subinterval of `I`. -/
def RatInterval.NestedIn (J I : RatInterval) : Prop :=
  I.left ≤ J.left ∧ J.right ≤ I.right

theorem RatInterval.NestedIn.refl (I : RatInterval) : I.NestedIn I := ⟨le_rfl, le_rfl⟩

theorem RatInterval.NestedIn.trans {K J I : RatInterval}
    (hKJ : K.NestedIn J) (hJI : J.NestedIn I) : K.NestedIn I :=
  ⟨hJI.1.trans hKJ.1, hKJ.2.trans hJI.2⟩

/-- The not-yet-formalized complex-analytic layer, isolated as data to be implemented later.
It deliberately contains no executable certificate machinery. -/
structure HeavyAnalysisInterface where
  analyticFeasible : ℝ → Prop
  finiteLevel : ℕ → ℝ → Prop
  analyticThreshold : ℝ
  threshold_pos : 0 < analyticThreshold
  threshold_lt_half : analyticThreshold < (1 : ℝ) / 2
  analytic_characterization : ∀ q, 0 < q → q < 1 →
    (analyticFeasible q ↔ analyticThreshold ≤ q)
  all_orders : ∀ q, 0 < q → q ≤ (9 : ℝ) / 16 →
    (analyticFeasible q ↔ ∀ N, finiteLevel N q)

/-- The future endpoint/original-polynomial formalization must implement this interface. -/
structure PolynomialInterface (core : HeavyAnalysisInterface) where
  polynomial_characterization : ∀ q, 0 < q → q < 1 →
    (PolynomialFeasible q ↔ core.analyticThreshold < q)
  endpoint_not_polynomial : ¬ PolynomialFeasible core.analyticThreshold
  delta_characterization : ∀ δ,
    (Admissible δ ↔ 0 < δ ∧ δ < deltaOfQ core.analyticThreshold)

end

end BelgianChocolate
