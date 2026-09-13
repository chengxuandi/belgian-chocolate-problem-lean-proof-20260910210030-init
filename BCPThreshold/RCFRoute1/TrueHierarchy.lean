import BCPThreshold.RCFRoute1.CompactSemialgebraic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Rat.Floor

/-!
# The actual finite hierarchy from the Belgian Chocolate manuscript

This file instantiates the compact polynomial semidecider with the exact rational
coefficient boxes and coefficient equations defining `H_N(q)`.
-/

namespace BelgianChocolate.Route1

namespace PaperBounds

def beta : ℚ := 3 / 4

def radius (r : ℚ) : ℚ := (1 + max r beta) / 2

def clearance (r : ℚ) : ℚ :=
  min (radius r - beta) (1 - radius r) / 2

def chainLength (r : ℚ) : ℕ :=
  Nat.ceil (16 * radius r / clearance r) + 1

def largeBound (r : ℚ) : ℕ :=
  3 ^ (66 * 9 ^ chainLength r)

def factorBound (r : ℚ) : ℕ :=
  Nat.ceil ((largeBound r : ℚ) *
    (1 / radius r + 1 / (radius r ^ 2 - beta ^ 2) +
      radius r + radius r ^ 2 + beta ^ 2))

/-- The manuscript radii `r_m`, indexed here by all naturals.  Only `m ≥ 1` is used. -/
def coeffRadius (m : ℕ) : ℚ := 1 - 1 / (2 : ℚ) ^ m

def localCoeffBound (m j : ℕ) : ℚ :=
  (max 1 (factorBound (coeffRadius m)) : ℚ) / coeffRadius m ^ j

/-- Minimum of the first `k+1` candidate bounds, corresponding to manuscript
indices `m = 1, ..., k+1`. -/
def coefficientBoundAux (j : ℕ) : ℕ → ℚ
  | 0 => localCoeffBound 1 j
  | k + 1 => min (coefficientBoundAux j k) (localCoeffBound (k + 2) j)

/-- The exact rational box constant `C_j` of the manuscript. -/
def coefficientBound (j : ℕ) : ℚ := coefficientBoundAux j j

theorem one_le_two_pow {m : ℕ} (hm : 1 ≤ m) : (2 : ℚ) ≤ 2 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add]
  have h : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  norm_num
  exact h

theorem coeffRadius_pos {m : ℕ} (hm : 1 ≤ m) : 0 < coeffRadius m := by
  have hp : (0 : ℚ) < 2 ^ m := pow_pos (by norm_num) _
  have htwo := one_le_two_pow hm
  rw [coeffRadius]
  have hfrac : 1 / (2 : ℚ) ^ m ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) htwo
  nlinarith

theorem localCoeffBound_pos {m j : ℕ} (hm : 1 ≤ m) :
    0 < localCoeffBound m j := by
  apply div_pos
  · exact_mod_cast (show 0 < max 1 (factorBound (coeffRadius m)) from
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  · exact pow_pos (coeffRadius_pos hm) _

theorem coefficientBoundAux_pos (j k : ℕ) :
    0 < coefficientBoundAux j k := by
  induction k with
  | zero => exact localCoeffBound_pos (by norm_num)
  | succ k ih =>
      simp only [coefficientBoundAux]
      exact lt_min ih (localCoeffBound_pos (Nat.succ_le_succ (Nat.zero_le _)))

theorem coefficientBound_pos (j : ℕ) : 0 < coefficientBound j :=
  coefficientBoundAux_pos j j

end PaperBounds

namespace TrueHierarchy

open RatPoly

noncomputable section

abbrev Family := Fin 4
abbrev Coefficients (N : ℕ) := Family → Fin (N + 1) → ℝ

def uFamily : Family := ⟨0, by norm_num⟩
def vFamily : Family := ⟨1, by norm_num⟩
def UFamily : Family := ⟨2, by norm_num⟩
def VFamily : Family := ⟨3, by norm_num⟩

def coeffAt {N : ℕ} (c : Coefficients N) (f : Family) (j : ℕ) : ℝ :=
  if h : j < N + 1 then c f ⟨j, h⟩ else 0

def shiftedCoeff {N : ℕ} (c : Coefficients N) (f : Family) (k shift : ℕ) : ℝ :=
  if shift ≤ k then coeffAt c f (k - shift) else 0

def deltaZero (k : ℕ) : ℝ := if k = 0 then 1 else 0

def convolution {N : ℕ} (c : Coefficients N) (f g : Family) (k : ℕ) : ℝ :=
  ((List.range (k + 1)).map fun i => coeffAt c f i * coeffAt c g (k - i)).sum

/-- The manuscript's system `H_N(q)`, before normalization: exactly four families of
real coefficients in their `C_j` boxes, the linear identity coefficients, and the two
inverse-product coefficient identities. -/
def Constraints (N : ℕ) (q : ℚ) (c : Coefficients N) : Prop :=
  (∀ f j, |c f j| ≤ (PaperBounds.coefficientBound j : ℝ)) ∧
  (∀ k : Fin (N + 1),
    shiftedCoeff c uFamily k 1 + shiftedCoeff c vFamily k 2 +
      (q : ℝ) * coeffAt c vFamily k = deltaZero k) ∧
  (∀ k : Fin (N + 1), convolution c uFamily UFamily k = deltaZero k) ∧
  (∀ k : Fin (N + 1), convolution c vFamily VFamily k = deltaZero k)

def H (N : ℕ) (q : ℚ) : Prop := ∃ c : Coefficients N, Constraints N q c

def variableCount (N : ℕ) : ℕ := 4 * (N + 1)

def variableIndex {N : ℕ} (f : Family) (j : Fin (N + 1)) : Fin (variableCount N) :=
  finProdFinEquiv (f, j)

def scaledVariable {N : ℕ} (f : Family) (j : Fin (N + 1)) :
    RatPoly (variableCount N) :=
  .mul (.const (PaperBounds.coefficientBound j)) (.var (variableIndex f j))

def polyCoeffAt (N : ℕ) (f : Family) (j : ℕ) : RatPoly (variableCount N) :=
  if h : j < N + 1 then scaledVariable f ⟨j, h⟩ else .const 0

def polyShiftedCoeff (N : ℕ) (f : Family) (k shift : ℕ) :
    RatPoly (variableCount N) :=
  if shift ≤ k then polyCoeffAt N f (k - shift) else .const 0

def deltaZeroQ (k : ℕ) : ℚ := if k = 0 then 1 else 0

def linearEquation (N : ℕ) (q : ℚ) (k : Fin (N + 1)) :
    RatPoly (variableCount N) :=
  .add
    (.add
      (.add (polyShiftedCoeff N uFamily k 1) (polyShiftedCoeff N vFamily k 2))
      (.mul (.const q) (polyCoeffAt N vFamily k)))
    (.neg (.const (deltaZeroQ k)))

def convolutionPoly (N : ℕ) (f g : Family) (k : Fin (N + 1)) :
    RatPoly (variableCount N) :=
  RatPoly.sumList ((List.range (k + 1)).map fun i =>
    .mul (polyCoeffAt N f i) (polyCoeffAt N g (k - i)))

def productEquation (N : ℕ) (f g : Family) (k : Fin (N + 1)) :
    RatPoly (variableCount N) :=
  .add (convolutionPoly N f g k) (.neg (.const (deltaZeroQ k)))

/-- The finite list of exactly `3(N+1)` rational polynomial equations underlying
the manuscript's `H_N(q)`. -/
def equations (N : ℕ) (q : ℚ) : List (RatPoly (variableCount N)) :=
  List.ofFn (linearEquation N q) ++
  List.ofFn (productEquation N uFamily UFamily) ++
  List.ofFn (productEquation N vFamily VFamily)

theorem equations_length (N : ℕ) (q : ℚ) :
    (equations N q).length = 3 * (N + 1) := by
  simp [equations]
  ring

def decode {N : ℕ} (y : Fin (variableCount N) → ℝ) : Coefficients N :=
  fun f j => (PaperBounds.coefficientBound j : ℝ) * y (variableIndex f j)

def encode {N : ℕ} (c : Coefficients N) : Fin (variableCount N) → ℝ :=
  fun i =>
    let fj := finProdFinEquiv.symm i
    c fj.1 fj.2 / (PaperBounds.coefficientBound fj.2 : ℝ)

@[simp] theorem decode_variable {N : ℕ} (y : Fin (variableCount N) → ℝ)
    (f : Family) (j : Fin (N + 1)) :
    decode y f j = (PaperBounds.coefficientBound j : ℝ) * y (variableIndex f j) := rfl

@[simp] theorem encode_variable {N : ℕ} (c : Coefficients N)
    (f : Family) (j : Fin (N + 1)) :
    encode c (variableIndex f j) = c f j / (PaperBounds.coefficientBound j : ℝ) := by
  simp [encode, variableIndex]

theorem decode_encode {N : ℕ} (c : Coefficients N) : decode (encode c) = c := by
  funext f j
  rw [decode_variable, encode_variable]
  exact mul_div_cancel₀ (c f j) (ne_of_gt (by exact_mod_cast PaperBounds.coefficientBound_pos j))

theorem encode_inCube_of_bounds {N : ℕ} {c : Coefficients N}
    (h : ∀ f j, |c f j| ≤ (PaperBounds.coefficientBound j : ℝ)) :
    RatPoly.InCube (encode c) := by
  intro i
  let f := (finProdFinEquiv.symm i).1
  let j := (finProdFinEquiv.symm i).2
  have hi : variableIndex f j = i := finProdFinEquiv.apply_symm_apply i
  have hC : (0 : ℝ) < PaperBounds.coefficientBound j := by
    exact_mod_cast PaperBounds.coefficientBound_pos j
  rw [← hi]
  rw [encode_variable, abs_div, abs_of_pos hC]
  exact (div_le_one hC).2 (h f j)

theorem decode_bounds_of_inCube {N : ℕ} {y : Fin (variableCount N) → ℝ}
    (hy : RatPoly.InCube y) :
    ∀ f j, |decode y f j| ≤ (PaperBounds.coefficientBound j : ℝ) := by
  intro f j
  have hC : (0 : ℝ) ≤ PaperBounds.coefficientBound j := by
    exact_mod_cast (PaperBounds.coefficientBound_pos j).le
  rw [decode_variable, abs_mul, abs_of_nonneg hC]
  exact mul_le_of_le_one_right hC (hy (variableIndex f j))

theorem eval_scaledVariable {N : ℕ} (y : Fin (variableCount N) → ℝ)
    (f : Family) (j : Fin (N + 1)) :
    (scaledVariable f j).evalR y = decode y f j := by
  rfl

theorem eval_polyCoeffAt {N : ℕ} (y : Fin (variableCount N) → ℝ)
    (f : Family) (j : ℕ) :
    (polyCoeffAt N f j).evalR y = coeffAt (decode y) f j := by
  simp only [polyCoeffAt, coeffAt]
  split
  · rfl
  · simp [RatPoly.evalR]

theorem eval_polyShiftedCoeff {N : ℕ} (y : Fin (variableCount N) → ℝ)
    (f : Family) (k shift : ℕ) :
    (polyShiftedCoeff N f k shift).evalR y = shiftedCoeff (decode y) f k shift := by
  simp only [polyShiftedCoeff, shiftedCoeff]
  split
  · exact eval_polyCoeffAt y f (k - shift)
  · simp [RatPoly.evalR]

theorem deltaZero_cast (k : ℕ) : (deltaZeroQ k : ℝ) = deltaZero k := by
  simp only [deltaZeroQ, deltaZero]
  split <;> norm_num

theorem eval_linearEquation {N : ℕ} (q : ℚ)
    (y : Fin (variableCount N) → ℝ) (k : Fin (N + 1)) :
    (linearEquation N q k).evalR y =
      shiftedCoeff (decode y) uFamily k 1 + shiftedCoeff (decode y) vFamily k 2 +
        (q : ℝ) * coeffAt (decode y) vFamily k - deltaZero k := by
  simp [linearEquation, RatPoly.evalR, eval_polyShiftedCoeff, eval_polyCoeffAt,
    deltaZero_cast, sub_eq_add_neg]

theorem eval_convolutionPoly {N : ℕ} (y : Fin (variableCount N) → ℝ)
    (f g : Family) (k : Fin (N + 1)) :
    (convolutionPoly N f g k).evalR y = convolution (decode y) f g k := by
  rw [convolutionPoly, RatPoly.evalR_sumList, convolution, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  change (polyCoeffAt N f i).evalR y * (polyCoeffAt N g (↑k - i)).evalR y = _
  rw [eval_polyCoeffAt, eval_polyCoeffAt]

theorem eval_productEquation {N : ℕ} (y : Fin (variableCount N) → ℝ)
    (f g : Family) (k : Fin (N + 1)) :
    (productEquation N f g k).evalR y =
      convolution (decode y) f g k - deltaZero k := by
  simp [productEquation, RatPoly.evalR, eval_convolutionPoly, deltaZero_cast,
    sub_eq_add_neg]

def NormalizedConstraints (N : ℕ) (q : ℚ)
    (y : Fin (variableCount N) → ℝ) : Prop :=
  RatPoly.InCube y ∧
  (∀ k : Fin (N + 1), (linearEquation N q k).evalR y = 0) ∧
  (∀ k : Fin (N + 1), (productEquation N uFamily UFamily k).evalR y = 0) ∧
  (∀ k : Fin (N + 1), (productEquation N vFamily VFamily k).evalR y = 0)

theorem constraints_decode_iff {N : ℕ} (q : ℚ)
    (y : Fin (variableCount N) → ℝ) (hy : RatPoly.InCube y) :
    Constraints N q (decode y) ↔ NormalizedConstraints N q y := by
  rw [NormalizedConstraints]
  constructor
  · rintro ⟨_, hlin, hu, hv⟩
    refine ⟨hy, ?_, ?_, ?_⟩
    · intro k
      rw [eval_linearEquation]
      linarith [hlin k]
    · intro k
      rw [eval_productEquation]
      linarith [hu k]
    · intro k
      rw [eval_productEquation]
      linarith [hv k]
  · rintro ⟨_, hlin, hu, hv⟩
    refine ⟨decode_bounds_of_inCube hy, ?_, ?_, ?_⟩
    · intro k
      have h := hlin k
      rw [eval_linearEquation] at h
      linarith
    · intro k
      have h := hu k
      rw [eval_productEquation] at h
      linarith
    · intro k
      have h := hv k
      rw [eval_productEquation] at h
      linarith

theorem equations_zero_iff {N : ℕ} (q : ℚ)
    (y : Fin (variableCount N) → ℝ) :
    (∀ p ∈ equations N q, p.evalR y = 0) ↔
      (∀ k : Fin (N + 1), (linearEquation N q k).evalR y = 0) ∧
      (∀ k : Fin (N + 1), (productEquation N uFamily UFamily k).evalR y = 0) ∧
      (∀ k : Fin (N + 1), (productEquation N vFamily VFamily k).evalR y = 0) := by
  simp only [equations, List.mem_append, List.mem_ofFn]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro k
      exact h _ (Or.inl (Or.inl ⟨k, rfl⟩))
    · intro k
      exact h _ (Or.inl (Or.inr ⟨k, rfl⟩))
    · intro k
      exact h _ (Or.inr ⟨k, rfl⟩)
  · rintro ⟨hlin, hu, hv⟩ p hp
    rcases hp with ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · exact hlin k
    · exact hu k
    · exact hv k

theorem normalized_iff_equationSystem {N : ℕ} (q : ℚ) :
    (∃ y, NormalizedConstraints N q y) ↔
      EquationSystemFeasible (equations N q) := by
  constructor <;> rintro ⟨y, hy⟩
  · exact ⟨y, hy.1, (equations_zero_iff q y).2 ⟨hy.2.1, hy.2.2.1, hy.2.2.2⟩⟩
  · refine ⟨y, hy.1, ?_⟩
    obtain ⟨hlin, hu, hv⟩ := (equations_zero_iff q y).1 hy.2
    exact ⟨hlin, hu, hv⟩

/-- Exact normalization theorem: the original bounded real coefficient system from the
manuscript is feasible iff its finite rational polynomial compiler is feasible on the unit cube. -/
theorem H_iff_equationSystem (N : ℕ) (q : ℚ) :
    H N q ↔ EquationSystemFeasible (equations N q) := by
  rw [← normalized_iff_equationSystem]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨encode c, ?_⟩
    have hy := encode_inCube_of_bounds hc.1
    rw [← constraints_decode_iff q (encode c) hy]
    simpa [decode_encode] using hc
  · rintro ⟨y, hy⟩
    refine ⟨decode y, ?_⟩
    exact (constraints_decode_iff q y hy.1).2 hy

/-- Executable negative certificate search for the actual manuscript hierarchy. -/
def negative (N : ℕ) (q : ℚ) (stage : ℕ) : Bool :=
  systemInfeasible (equations N q) stage

theorem negative_sound {N : ℕ} {q : ℚ} {stage : ℕ}
    (h : negative N q stage = true) : ¬ H N q := by
  rw [H_iff_equationSystem]
  exact systemInfeasible_sound h

theorem negative_complete {N : ℕ} {q : ℚ} (h : ¬ H N q) :
    ∃ stage, negative N q stage = true := by
  rw [H_iff_equationSystem] at h
  exact systemInfeasible_complete (equations N q) h

/-- Fair finite scan over both the hierarchy level and the box-subdivision depth.
This has exactly the `stage → rational parameter → Bool` shape consumed by the
certified threshold algorithm's negative side. -/
def hierarchyNegative (stage : ℕ) (q : ℚ) : Bool :=
  (List.range (stage + 1)).any fun N =>
    (List.range (stage + 1)).any fun depth => negative N q depth

theorem hierarchyNegative_sound {stage : ℕ} {q : ℚ}
    (h : hierarchyNegative stage q = true) : ∃ N, ¬ H N q := by
  rw [hierarchyNegative, List.any_eq_true] at h
  obtain ⟨N, _, hN⟩ := h
  rw [List.any_eq_true] at hN
  obtain ⟨depth, _, hdepth⟩ := hN
  exact ⟨N, negative_sound hdepth⟩

theorem hierarchyNegative_complete {q : ℚ} (h : ∃ N, ¬ H N q) :
    ∃ stage, hierarchyNegative stage q = true := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨depth, hdepth⟩ := negative_complete hN
  let stage := max N depth
  refine ⟨stage, ?_⟩
  rw [hierarchyNegative, List.any_eq_true]
  refine ⟨N, List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_max_left _ _)), ?_⟩
  rw [List.any_eq_true]
  exact ⟨depth, List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_max_right _ _)), hdepth⟩

end

end TrueHierarchy

end BelgianChocolate.Route1
