import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Route 1 experiment: compact polynomial infeasibility

This file is deliberately independent of `BCPThreshold`.  It develops a small executable
rational-polynomial language and the estimates needed by a grid infeasibility semidecider.
-/

namespace BelgianChocolate.Route1

/-- A deliberately small syntax for multivariate rational polynomials. -/
inductive RatPoly (n : ℕ) where
  | const : ℚ → RatPoly n
  | var : Fin n → RatPoly n
  | neg : RatPoly n → RatPoly n
  | add : RatPoly n → RatPoly n → RatPoly n
  | mul : RatPoly n → RatPoly n → RatPoly n
deriving DecidableEq, Repr

namespace RatPoly

def evalQ {n : ℕ} : RatPoly n → (Fin n → ℚ) → ℚ
  | const c, _ => c
  | var i, x => x i
  | neg p, x => -p.evalQ x
  | add p q, x => p.evalQ x + q.evalQ x
  | mul p q, x => p.evalQ x * q.evalQ x

def evalR {n : ℕ} : RatPoly n → (Fin n → ℝ) → ℝ
  | const c, _ => c
  | var i, x => x i
  | neg p, x => -p.evalR x
  | add p q, x => p.evalR x + q.evalR x
  | mul p q, x => p.evalR x * q.evalR x

/-- A computable absolute-value bound on the unit cube. -/
def absBound {n : ℕ} : RatPoly n → ℚ
  | const c => |c|
  | var _ => 1
  | neg p => p.absBound
  | add p q => p.absBound + q.absBound
  | mul p q => p.absBound * q.absBound

/-- A computable Lipschitz bound for the `ℓ1` distance on the unit cube. -/
def lipBound {n : ℕ} : RatPoly n → ℚ
  | const _ => 0
  | var _ => 1
  | neg p => p.lipBound
  | add p q => p.lipBound + q.lipBound
  | mul p q => p.lipBound * q.absBound + p.absBound * q.lipBound

def InCube {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ i, |x i| ≤ 1

def distOne {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, |x i - y i|

@[simp] theorem evalR_const {n : ℕ} (c : ℚ) (x : Fin n → ℝ) :
    (const c : RatPoly n).evalR x = c := rfl

theorem absBound_nonneg {n : ℕ} (p : RatPoly n) : 0 ≤ p.absBound := by
  induction p <;> simp [absBound, *]
  all_goals positivity

theorem lipBound_nonneg {n : ℕ} (p : RatPoly n) : 0 ≤ p.lipBound := by
  induction p with
  | const => simp [lipBound]
  | var => simp [lipBound]
  | neg p ih => simpa [lipBound] using ih
  | add p q ihp ihq => exact add_nonneg ihp ihq
  | mul p q ihp ihq =>
      exact add_nonneg (mul_nonneg ihp q.absBound_nonneg)
        (mul_nonneg p.absBound_nonneg ihq)

theorem distOne_nonneg {n : ℕ} (x y : Fin n → ℝ) : 0 ≤ distOne x y := by
  exact Finset.sum_nonneg fun i _ => abs_nonneg (x i - y i)

theorem evalR_eq_evalQ {n : ℕ} (p : RatPoly n) (x : Fin n → ℚ) :
    p.evalR (fun i => (x i : ℝ)) = (p.evalQ x : ℝ) := by
  induction p <;> simp [evalR, evalQ, *]

theorem abs_evalR_le {n : ℕ} (p : RatPoly n) {x : Fin n → ℝ}
    (hx : InCube x) : |p.evalR x| ≤ p.absBound := by
  induction p with
  | const c => norm_num [evalR, absBound]
  | var i => simpa [evalR, absBound] using hx i
  | neg p ih => simpa [evalR, absBound, abs_neg] using ih
  | add p q ihp ihq =>
      calc
        |(add p q).evalR x| ≤ |p.evalR x| + |q.evalR x| := by
          simpa [evalR] using abs_add_le (p.evalR x) (q.evalR x)
        _ ≤ (p.absBound : ℝ) + q.absBound := add_le_add ihp ihq
        _ = (add p q).absBound := by norm_num [absBound]
  | mul p q ihp ihq =>
      rw [evalR, abs_mul]
      norm_num [absBound]
      exact mul_le_mul ihp ihq (abs_nonneg _) (by exact_mod_cast p.absBound_nonneg)

private theorem coordinate_le_distOne {n : ℕ} (x y : Fin n → ℝ) (i : Fin n) :
    |x i - y i| ≤ distOne x y := by
  classical
  unfold distOne
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j - y j)) (Finset.mem_univ i)

theorem lipschitz_on_cube {n : ℕ} (p : RatPoly n) {x y : Fin n → ℝ}
    (hx : InCube x) (hy : InCube y) :
    |p.evalR x - p.evalR y| ≤ (p.lipBound : ℝ) * distOne x y := by
  induction p with
  | const c => simp [evalR, lipBound, distOne]
  | var i =>
      simpa [evalR, lipBound, one_mul] using coordinate_le_distOne x y i
  | neg p ih =>
      rw [evalR, evalR, show -p.evalR x - -p.evalR y = -(p.evalR x - p.evalR y) by ring,
        abs_neg]
      simpa [lipBound] using ih
  | add p q ihp ihq =>
      calc
        |(add p q).evalR x - (add p q).evalR y|
            ≤ |p.evalR x - p.evalR y| + |q.evalR x - q.evalR y| := by
              rw [evalR, evalR]
              rw [show p.evalR x + q.evalR x - (p.evalR y + q.evalR y) =
                (p.evalR x - p.evalR y) + (q.evalR x - q.evalR y) by ring]
              exact abs_add_le _ _
        _ ≤ (p.lipBound : ℝ) * distOne x y +
              (q.lipBound : ℝ) * distOne x y := add_le_add ihp ihq
        _ = ((add p q).lipBound : ℚ) * distOne x y := by
              norm_num [lipBound]
              ring
  | mul p q ihp ihq =>
      have hpx := p.abs_evalR_le hx
      have hqy := q.abs_evalR_le hy
      have hd := distOne_nonneg x y
      calc
        |(mul p q).evalR x - (mul p q).evalR y|
            = |p.evalR x * (q.evalR x - q.evalR y) +
                (p.evalR x - p.evalR y) * q.evalR y| := by
                  congr 1
                  simp only [evalR]
                  ring
        _ ≤ |p.evalR x| * |q.evalR x - q.evalR y| +
              |p.evalR x - p.evalR y| * |q.evalR y| := by
                simpa [abs_mul] using abs_add_le
                  (p.evalR x * (q.evalR x - q.evalR y))
                  ((p.evalR x - p.evalR y) * q.evalR y)
        _ ≤ (p.absBound : ℝ) * ((q.lipBound : ℝ) * distOne x y) +
              ((p.lipBound : ℝ) * distOne x y) * q.absBound := by
                have hBp : (0 : ℝ) ≤ p.absBound := by exact_mod_cast p.absBound_nonneg
                have hLp : (0 : ℝ) ≤ p.lipBound := by exact_mod_cast p.lipBound_nonneg
                have hLq : (0 : ℝ) ≤ q.lipBound := by exact_mod_cast q.lipBound_nonneg
                have hBq : (0 : ℝ) ≤ q.absBound := by exact_mod_cast q.absBound_nonneg
                exact add_le_add
                  (mul_le_mul hpx ihq (by positivity) hBp)
                  (mul_le_mul ihp hqy (abs_nonneg _) (mul_nonneg hLp hd))
        _ = ((mul p q).lipBound : ℚ) * distOne x y := by
              norm_num [lipBound]
              ring

end RatPoly

section Grid

/-- Rational grid points with mesh `1 / m` on the unit cube. -/
def gridPointQ {n : ℕ} (m : ℕ) (a : Fin n → Fin (2 * m + 1)) : Fin n → ℚ :=
  fun i => -1 + (a i : ℚ) / m

def gridPointR {n : ℕ} (m : ℕ) (a : Fin n → Fin (2 * m + 1)) : Fin n → ℝ :=
  fun i => (gridPointQ m a i : ℝ)

theorem gridPoint_inCube {n m : ℕ} (hm : 0 < m)
    (a : Fin n → Fin (2 * m + 1)) : RatPoly.InCube (gridPointR m a) := by
  intro i
  rw [abs_le]
  constructor
  · dsimp [gridPointR, gridPointQ]
    norm_num
    positivity
  · have hai : (a i : ℕ) ≤ 2 * m := Nat.le_of_lt_succ (a i).isLt
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp [gridPointR, gridPointQ]
    norm_num
    have haiR : ((a i : ℕ) : ℝ) ≤ 2 * m := by exact_mod_cast hai
    apply (div_le_iff₀ hmR).2
    nlinarith

/-- A (proof-only) grid index immediately below a real point. The grid itself and its verifier
remain executable; floor is used only in the coverage proof. -/
noncomputable def lowerGridIndex (m : ℕ) (x : ℝ) : ℕ :=
  ⌊(x + 1) * m⌋₊

theorem lowerGridIndex_lt {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hxlo : -1 ≤ x) (hxhi : x ≤ 1) :
    lowerGridIndex m x < 2 * m + 1 := by
  have ht0 : 0 ≤ (x + 1) * (m : ℝ) := by
    have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm.le
    have hx0 : 0 ≤ x + 1 := by linarith
    positivity
  rw [lowerGridIndex, Nat.floor_lt ht0]
  have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm.le
  norm_num
  nlinarith

noncomputable def nearbyGrid {n m : ℕ} (hm : 0 < m) (x : Fin n → ℝ)
    (hx : RatPoly.InCube x) : Fin n → Fin (2 * m + 1) :=
  fun i => ⟨lowerGridIndex m (x i),
    lowerGridIndex_lt hm (abs_le.1 (hx i)).1 (abs_le.1 (hx i)).2⟩

theorem nearbyGrid_coordinate {n m : ℕ} (hm : 0 < m) (x : Fin n → ℝ)
    (hx : RatPoly.InCube x) (i : Fin n) :
    0 ≤ x i - gridPointR m (nearbyGrid hm x hx) i ∧
      x i - gridPointR m (nearbyGrid hm x hx) i < 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxi : -1 ≤ x i := (abs_le.1 (hx i)).1
  have ht0 : 0 ≤ (x i + 1) * (m : ℝ) := mul_nonneg (by linarith) hmR.le
  have hlo := Nat.floor_le ht0
  have hhi := Nat.lt_floor_add_one ((x i + 1) * (m : ℝ))
  dsimp only [gridPointR, gridPointQ, nearbyGrid]
  norm_num
  constructor
  · change ((⌊(x i + 1) * (m : ℝ)⌋₊ : ℕ) : ℝ) / m ≤ 1 + x i
    rw [div_le_iff₀ hmR]
    nlinarith
  · dsimp [lowerGridIndex]
    rw [show (m : ℝ)⁻¹ = 1 / m by simp]
    have hdiv : x i + 1 <
        (((⌊(x i + 1) * (m : ℝ)⌋₊ : ℕ) : ℝ) + 1) / m := by
      rw [lt_div_iff₀ hmR]
      nlinarith
    have hadd :
        (((⌊(x i + 1) * (m : ℝ)⌋₊ : ℕ) : ℝ) + 1) / m =
          ((⌊(x i + 1) * (m : ℝ)⌋₊ : ℕ) : ℝ) / m + 1 / m := by ring
    rw [hadd] at hdiv
    nlinarith

theorem nearbyGrid_distOne {n m : ℕ} (hm : 0 < m) (x : Fin n → ℝ)
    (hx : RatPoly.InCube x) :
    RatPoly.distOne x (gridPointR m (nearbyGrid hm x hx)) ≤ n / (m : ℝ) := by
  classical
  unfold RatPoly.distOne
  have hcoord : ∀ i : Fin n,
      |x i - gridPointR m (nearbyGrid hm x hx) i| < 1 / (m : ℝ) := by
    intro i
    rw [abs_of_nonneg (nearbyGrid_coordinate hm x hx i).1]
    exact (nearbyGrid_coordinate hm x hx i).2
  calc
    ∑ i, |x i - gridPointR m (nearbyGrid hm x hx) i|
        ≤ ∑ _i : Fin n, (1 / (m : ℝ)) :=
          Finset.sum_le_sum (fun i _ => (hcoord i).le)
    _ = n / (m : ℝ) := by simp [div_eq_mul_inv]

end Grid

section Semidecider

open RatPoly

/-- Semantic feasibility of a polynomial equation on the compact unit cube. -/
def CubeFeasible {n : ℕ} (p : RatPoly n) : Prop :=
  ∃ x : Fin n → ℝ, InCube x ∧ p.evalR x = 0

/-- The exact rational condition checked at grid depth `m`. -/
def GridPassProp {n : ℕ} (p : RatPoly n) (m : ℕ) : Prop :=
  0 < m ∧ ∀ a : Fin n → Fin (2 * m + 1),
    p.lipBound * n / m < p.evalQ (gridPointQ m a)

instance {n : ℕ} (p : RatPoly n) (m : ℕ) : Decidable (GridPassProp p m) := by
  unfold GridPassProp
  infer_instance

/-- Executable depth-`m` verifier: only finit rational evaluation over a finite grid is used. -/
def gridInfeasible {n : ℕ} (p : RatPoly n) (m : ℕ) : Bool :=
  decide (GridPassProp p m)

theorem gridInfeasible_eq_true_iff {n : ℕ} (p : RatPoly n) (m : ℕ) :
    gridInfeasible p m = true ↔ GridPassProp p m := by
  simp [gridInfeasible]

/-- Every successful finite grid check is a sound infeasibility certificate. -/
theorem gridInfeasible_sound {n : ℕ} {p : RatPoly n} {m : ℕ}
    (hpass : gridInfeasible p m = true) : ¬ CubeFeasible p := by
  rw [gridInfeasible_eq_true_iff] at hpass
  rintro ⟨x, hx, hzero⟩
  let a := nearbyGrid hpass.1 x hx
  have haQ := hpass.2 a
  have haR : ((p.lipBound * n / m : ℚ) : ℝ) <
      p.evalR (gridPointR m a) := by
    have heval : p.evalR (gridPointR m a) =
        (p.evalQ (gridPointQ m a) : ℝ) := by
      change p.evalR (fun i => (gridPointQ m a i : ℝ)) = _
      exact p.evalR_eq_evalQ (gridPointQ m a)
    rw [heval]
    exact_mod_cast haQ
  have hdist := nearbyGrid_distOne hpass.1 x hx
  have hLip := p.lipschitz_on_cube hx (gridPoint_inCube hpass.1 a)
  have hL0 : (0 : ℝ) ≤ p.lipBound := by exact_mod_cast p.lipBound_nonneg
  have hbound : |p.evalR x - p.evalR (gridPointR m a)| ≤
      (p.lipBound : ℝ) * (n / (m : ℝ)) :=
    hLip.trans (mul_le_mul_of_nonneg_left hdist hL0)
  have hthreshold : ((p.lipBound * n / m : ℚ) : ℝ) =
      (p.lipBound : ℝ) * (n / (m : ℝ)) := by
    norm_num
    ring
  rw [hzero, zero_sub, abs_neg] at hbound
  rw [hthreshold] at haR
  have hvalpos : 0 < p.evalR (gridPointR m a) :=
    lt_of_le_of_lt (mul_nonneg hL0 (by positivity)) haR
  rw [abs_of_pos hvalpos] at hbound
  linarith

/-- The unit cube as a compact product set. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1) 1)

theorem mem_unitCube_iff {n : ℕ} {x : Fin n → ℝ} :
    x ∈ unitCube n ↔ InCube x := by
  constructor
  · intro h i
    exact (abs_le.2 (h i (Set.mem_univ i)))
  · intro h i hi
    exact abs_le.1 (h i)

theorem unitCube_nonempty (n : ℕ) : (unitCube n).Nonempty := by
  refine ⟨fun _ => 0, mem_unitCube_iff.2 ?_⟩
  intro i
  simp

theorem unitCube_compact (n : ℕ) : IsCompact (unitCube n) := by
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem RatPoly.continuous_evalR {n : ℕ} (p : RatPoly n) :
    Continuous (fun x : Fin n → ℝ => p.evalR x) := by
  induction p with
  | const c => exact continuous_const
  | var i => exact continuous_apply i
  | neg p ih =>
      change Continuous (-(fun x => p.evalR x))
      exact ih.neg
  | add p q ihp ihq =>
      change Continuous ((fun x => p.evalR x) + fun x => q.evalR x)
      exact ihp.add ihq
  | mul p q ihp ihq =>
      change Continuous ((fun x => p.evalR x) * fun x => q.evalR x)
      exact ihp.mul ihq

/-- Strict positivity on the cube gives a real positive lower margin. -/
theorem exists_positive_margin {n : ℕ} (p : RatPoly n)
    (hnonneg : ∀ x, InCube x → 0 ≤ p.evalR x)
    (hinfeasible : ¬ CubeFeasible p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, InCube x → ε ≤ p.evalR x := by
  obtain ⟨x, hx, hmin⟩ := (unitCube_compact n).exists_isMinOn
    (unitCube_nonempty n) p.continuous_evalR.continuousOn
  have hxc : InCube x := mem_unitCube_iff.1 hx
  have hxne : p.evalR x ≠ 0 := by
    intro hz
    exact hinfeasible ⟨x, hxc, hz⟩
  have hxpos : 0 < p.evalR x := lt_of_le_of_ne (hnonneg x hxc) (Ne.symm hxne)
  refine ⟨p.evalR x, hxpos, ?_⟩
  intro y hy
  exact hmin (mem_unitCube_iff.2 hy)

/-- Completeness of the dedicated compact-grid semidecider for nonnegative rational
polynomials: infeasibility is eventually certified at a finite grid depth. -/
theorem gridInfeasible_complete {n : ℕ} (p : RatPoly n)
    (hnonneg : ∀ x, InCube x → 0 ≤ p.evalR x)
    (hinfeasible : ¬ CubeFeasible p) :
    ∃ m, gridInfeasible p m = true := by
  obtain ⟨ε, hε, hmargin⟩ := exists_positive_margin p hnonneg hinfeasible
  obtain ⟨m, hm⟩ := exists_nat_gt ((p.lipBound : ℝ) * n / ε)
  have hm0 : 0 < m := by
    have hnonnegRatio : 0 ≤ (p.lipBound : ℝ) * n / ε :=
      div_nonneg (mul_nonneg (by exact_mod_cast p.lipBound_nonneg) (by positivity)) hε.le
    exact_mod_cast (lt_of_le_of_lt hnonnegRatio hm)
  refine ⟨m, (gridInfeasible_eq_true_iff p m).2 ⟨hm0, ?_⟩⟩
  intro a
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hscaled : (p.lipBound : ℝ) * n < ε * m := by
    rw [div_lt_iff₀ hε] at hm
    nlinarith
  have hratio : (p.lipBound : ℝ) * n / m < ε := by
    rw [div_lt_iff₀ hmR]
    simpa [mul_comm] using hscaled
  have hcenter := hmargin (gridPointR m a) (gridPoint_inCube hm0 a)
  have hreal : (((p.lipBound * n / m : ℚ)) : ℝ) <
      p.evalR (gridPointR m a) := by
    norm_num
    rw [show ((p.lipBound : ℝ) * (n : ℝ)) / (m : ℝ) =
      (p.lipBound : ℝ) * n / m by rfl]
    exact hratio.trans_le hcenter
  have heval : p.evalR (gridPointR m a) =
      (p.evalQ (gridPointQ m a) : ℝ) := by
    change p.evalR (fun i => (gridPointQ m a i : ℝ)) = _
    exact p.evalR_eq_evalQ (gridPointQ m a)
  rw [heval] at hreal
  exact_mod_cast hreal

/-- Syntax-tree sum; unlike an algebraic quotient, this remains directly executable. -/
def RatPoly.sumList {n : ℕ} : List (RatPoly n) → RatPoly n
  | [] => .const 0
  | p :: ps => .add p (sumList ps)

@[simp] theorem RatPoly.evalQ_sumList {n : ℕ} (ps : List (RatPoly n))
    (x : Fin n → ℚ) :
    (sumList ps).evalQ x = (ps.map fun p => p.evalQ x).sum := by
  induction ps with
  | nil => simp [sumList, evalQ]
  | cons p ps ih => simp [sumList, evalQ, ih]

@[simp] theorem RatPoly.evalR_sumList {n : ℕ} (ps : List (RatPoly n))
    (x : Fin n → ℝ) :
    (sumList ps).evalR x = (ps.map fun p => p.evalR x).sum := by
  induction ps with
  | nil => simp [sumList, evalR]
  | cons p ps ih => simp [sumList, evalR, ih]

/-- Sum of squares of a finite rational polynomial equation system. -/
def violation {n : ℕ} (equations : List (RatPoly n)) : RatPoly n :=
  RatPoly.sumList (equations.map fun p => .mul p p)

def EquationSystemFeasible {n : ℕ} (equations : List (RatPoly n)) : Prop :=
  ∃ x : Fin n → ℝ, RatPoly.InCube x ∧ ∀ p ∈ equations, p.evalR x = 0

theorem violation_nonnegative {n : ℕ} (equations : List (RatPoly n))
    (x : Fin n → ℝ) : 0 ≤ (violation equations).evalR x := by
  induction equations with
  | nil => simp [violation, RatPoly.sumList, RatPoly.evalR]
  | cons p ps ih =>
      simp only [violation, List.map_cons, RatPoly.sumList, RatPoly.evalR]
      have : 0 ≤ p.evalR x * p.evalR x := mul_self_nonneg _
      exact add_nonneg this ih

theorem violation_eq_zero_iff {n : ℕ} (equations : List (RatPoly n))
    (x : Fin n → ℝ) :
    (violation equations).evalR x = 0 ↔ ∀ p ∈ equations, p.evalR x = 0 := by
  induction equations with
  | nil => simp [violation, RatPoly.sumList, RatPoly.evalR]
  | cons p ps ih =>
      change p.evalR x * p.evalR x + (violation ps).evalR x = 0 ↔
        ∀ q ∈ p :: ps, q.evalR x = 0
      constructor
      · intro h
        have hp2 : p.evalR x ^ 2 = 0 := by
          have htail : 0 ≤ (violation ps).evalR x := violation_nonnegative ps x
          nlinarith
        have hp : p.evalR x = 0 := sq_eq_zero_iff.1 hp2
        have hps : ∀ q ∈ ps, q.evalR x = 0 := by
          have : (violation ps).evalR x = 0 := by nlinarith [sq_nonneg (p.evalR x)]
          exact (ih.mp this)
        simpa [hp] using And.intro hp hps
      · intro h
        have hp := h p (by simp)
        have hps : ∀ q ∈ ps, q.evalR x = 0 := by
          intro q hq
          exact h q (by simp [hq])
        simp [hp, ih.mpr hps]

theorem cubeFeasible_violation_iff {n : ℕ} (equations : List (RatPoly n)) :
    CubeFeasible (violation equations) ↔ EquationSystemFeasible equations := by
  constructor <;> rintro ⟨x, hx, h⟩
  · exact ⟨x, hx, (violation_eq_zero_iff equations x).1 h⟩
  · exact ⟨x, hx, (violation_eq_zero_iff equations x).2 h⟩

/-- The dedicated executable semidecider for a finite compact rational equation system. -/
def systemInfeasible {n : ℕ} (equations : List (RatPoly n)) (stage : ℕ) : Bool :=
  gridInfeasible (violation equations) stage

theorem systemInfeasible_sound {n : ℕ} {equations : List (RatPoly n)} {stage : ℕ}
    (h : systemInfeasible equations stage = true) :
    ¬ EquationSystemFeasible equations := by
  intro hfeas
  exact gridInfeasible_sound h ((cubeFeasible_violation_iff equations).2 hfeas)

theorem systemInfeasible_complete {n : ℕ} (equations : List (RatPoly n))
    (h : ¬ EquationSystemFeasible equations) :
    ∃ stage, systemInfeasible equations stage = true := by
  apply gridInfeasible_complete (violation equations)
  · exact fun x _ => violation_nonnegative equations x
  · rwa [cubeFeasible_violation_iff]

end Semidecider

end BelgianChocolate.Route1
