import BCPThreshold.RCFRoute1.TrueHierarchy
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Compact all-orders coefficient realization

Finite witnesses are embedded into one common product of compact intervals.
The decreasing closed level sets, rather than the witnesses themselves, are
made compatible.
-/

namespace BelgianChocolate.Route1.AllOrders

open Set
open TrueHierarchy

noncomputable section

abbrev InfiniteCoefficients := TrueHierarchy.Family → ℕ → ℝ

def coeffAt (c : InfiniteCoefficients) (f : TrueHierarchy.Family) (j : ℕ) : ℝ := c f j

def shiftedCoeff (c : InfiniteCoefficients) (f : TrueHierarchy.Family)
    (k shift : ℕ) : ℝ :=
  if shift ≤ k then c f (k - shift) else 0

def convolution (c : InfiniteCoefficients) (f g : TrueHierarchy.Family)
    (k : ℕ) : ℝ :=
  ((List.range (k + 1)).map fun i => c f i * c g (k - i)).sum

def CoeffBox : Set InfiniteCoefficients :=
  {c | ∀ f j, c f j ∈
    Set.Icc (-(PaperBounds.coefficientBound j : ℝ))
      (PaperBounds.coefficientBound j : ℝ)}

def PrefixConstraints (N : ℕ) (q : ℚ) (c : InfiniteCoefficients) : Prop :=
  (∀ k : Fin (N + 1),
    shiftedCoeff c uFamily k 1 + shiftedCoeff c vFamily k 2 +
      (q : ℝ) * c vFamily k = TrueHierarchy.deltaZero k) ∧
  (∀ k : Fin (N + 1),
    convolution c uFamily UFamily k = TrueHierarchy.deltaZero k) ∧
  (∀ k : Fin (N + 1),
    convolution c vFamily VFamily k = TrueHierarchy.deltaZero k)

def LevelSet (N : ℕ) (q : ℚ) : Set InfiniteCoefficients :=
  {c | c ∈ CoeffBox ∧ PrefixConstraints N q c}

def InfiniteConstraints (q : ℚ) (c : InfiniteCoefficients) : Prop :=
  c ∈ CoeffBox ∧
  (∀ k : ℕ,
    shiftedCoeff c uFamily k 1 + shiftedCoeff c vFamily k 2 +
      (q : ℝ) * c vFamily k = TrueHierarchy.deltaZero k) ∧
  (∀ k : ℕ, convolution c uFamily UFamily k = TrueHierarchy.deltaZero k) ∧
  (∀ k : ℕ, convolution c vFamily VFamily k = TrueHierarchy.deltaZero k)

def zeroExtend {N : ℕ} (c : TrueHierarchy.Coefficients N) : InfiniteCoefficients :=
  fun f j => TrueHierarchy.coeffAt c f j

@[simp] theorem zeroExtend_apply {N : ℕ} (c : TrueHierarchy.Coefficients N)
    (f : TrueHierarchy.Family) (j : ℕ) :
    zeroExtend c f j = TrueHierarchy.coeffAt c f j := rfl

theorem zeroExtend_mem_coeffBox {N : ℕ} {c : TrueHierarchy.Coefficients N}
    (hc : ∀ f j, |c f j| ≤ (PaperBounds.coefficientBound j : ℝ)) :
    zeroExtend c ∈ CoeffBox := by
  intro f j
  by_cases hj : j < N + 1
  · simpa [zeroExtend, TrueHierarchy.coeffAt, hj, abs_le] using hc f ⟨j, hj⟩
  · have hC : (0 : ℝ) ≤ (PaperBounds.coefficientBound j : ℚ) :=
      Rat.cast_nonneg.mpr (PaperBounds.coefficientBound_pos j).le
    simp [zeroExtend, TrueHierarchy.coeffAt, hj, hC]

theorem zeroExtend_shiftedCoeff {N : ℕ} (c : TrueHierarchy.Coefficients N)
    (f : TrueHierarchy.Family) (k shift : ℕ) :
    shiftedCoeff (zeroExtend c) f k shift =
      TrueHierarchy.shiftedCoeff c f k shift := by
  simp [shiftedCoeff, TrueHierarchy.shiftedCoeff, zeroExtend]

theorem zeroExtend_convolution {N : ℕ} (c : TrueHierarchy.Coefficients N)
    (f g : TrueHierarchy.Family) (k : ℕ) :
    convolution (zeroExtend c) f g k = TrueHierarchy.convolution c f g k := by
  simp [convolution, TrueHierarchy.convolution, zeroExtend]

theorem levelSet_nonempty {N : ℕ} {q : ℚ} (hN : TrueHierarchy.H N q) :
    (LevelSet N q).Nonempty := by
  obtain ⟨c, hc⟩ := hN
  refine ⟨zeroExtend c, zeroExtend_mem_coeffBox hc.1, ?_⟩
  constructor
  · intro k
    simpa [zeroExtend_shiftedCoeff, zeroExtend] using hc.2.1 k
  constructor
  · intro k
    simpa [zeroExtend_convolution] using hc.2.2.1 k
  · intro k
    simpa [zeroExtend_convolution] using hc.2.2.2 k

theorem coeffBox_isCompact : IsCompact CoeffBox := by
  unfold CoeffBox
  exact isCompact_pi_infinite (fun _ =>
    isCompact_pi_infinite (fun _ => isCompact_Icc))

theorem coeffBox_isClosed : IsClosed CoeffBox := coeffBox_isCompact.isClosed

theorem continuous_shiftedCoeff (f : TrueHierarchy.Family) (k shift : ℕ) :
    Continuous (fun c : InfiniteCoefficients => shiftedCoeff c f k shift) := by
  simp only [shiftedCoeff]
  split
  · exact continuous_apply_apply f (k - shift)
  · exact continuous_const

theorem continuous_convolution (f g : TrueHierarchy.Family) (k : ℕ) :
    Continuous (fun c : InfiniteCoefficients => convolution c f g k) := by
  simp only [convolution]
  apply continuous_list_sum
  intro x hx
  exact (continuous_apply_apply f x).mul (continuous_apply_apply g (k - x))

theorem prefixConstraints_isClosed (N : ℕ) (q : ℚ) :
    IsClosed {c : InfiniteCoefficients | PrefixConstraints N q c} := by
  let lin : InfiniteCoefficients → Fin (N + 1) → ℝ := fun c k =>
    shiftedCoeff c uFamily k 1 + shiftedCoeff c vFamily k 2 +
      (q : ℝ) * c vFamily k
  let uu : InfiniteCoefficients → Fin (N + 1) → ℝ := fun c k =>
    convolution c uFamily UFamily k
  let vv : InfiniteCoefficients → Fin (N + 1) → ℝ := fun c k =>
    convolution c vFamily VFamily k
  have hlin : ∀ k, Continuous (fun c => lin c k) := by
    intro k
    exact ((continuous_shiftedCoeff uFamily k 1).add
      (continuous_shiftedCoeff vFamily k 2)).add
      (continuous_const.mul (continuous_apply_apply vFamily (k : ℕ)))
  have huu : ∀ k, Continuous (fun c => uu c k) := by
    intro k
    exact continuous_convolution uFamily UFamily k
  have hvv : ∀ k, Continuous (fun c => vv c k) := by
    intro k
    exact continuous_convolution vFamily VFamily k
  have hlinClosed : IsClosed {c | ∀ k, lin c k = TrueHierarchy.deltaZero k} := by
    rw [show {c | ∀ k, lin c k = TrueHierarchy.deltaZero k} =
        ⋂ k, {c | lin c k = TrueHierarchy.deltaZero k} by ext; simp]
    exact isClosed_iInter (fun k => isClosed_eq (hlin k) continuous_const)
  have huuClosed : IsClosed {c | ∀ k, uu c k = TrueHierarchy.deltaZero k} := by
    rw [show {c | ∀ k, uu c k = TrueHierarchy.deltaZero k} =
        ⋂ k, {c | uu c k = TrueHierarchy.deltaZero k} by ext; simp]
    exact isClosed_iInter (fun k => isClosed_eq (huu k) continuous_const)
  have hvvClosed : IsClosed {c | ∀ k, vv c k = TrueHierarchy.deltaZero k} := by
    rw [show {c | ∀ k, vv c k = TrueHierarchy.deltaZero k} =
        ⋂ k, {c | vv c k = TrueHierarchy.deltaZero k} by ext; simp]
    exact isClosed_iInter (fun k => isClosed_eq (hvv k) continuous_const)
  change IsClosed ({c | (∀ k, lin c k = TrueHierarchy.deltaZero k) ∧
    (∀ k, uu c k = TrueHierarchy.deltaZero k) ∧
    (∀ k, vv c k = TrueHierarchy.deltaZero k)})
  exact hlinClosed.inter (huuClosed.inter hvvClosed)

theorem levelSet_isClosed (N : ℕ) (q : ℚ) : IsClosed (LevelSet N q) := by
  exact coeffBox_isClosed.inter (prefixConstraints_isClosed N q)

theorem levelSet_succ_subset (N : ℕ) (q : ℚ) :
    LevelSet (N + 1) q ⊆ LevelSet N q := by
  intro c hc
  refine ⟨hc.1, ?_⟩
  rcases hc.2 with ⟨hlin, huu, hvv⟩
  constructor
  · intro k
    exact hlin ⟨k, Nat.lt.step k.isLt⟩
  constructor
  · intro k
    exact huu ⟨k, Nat.lt.step k.isLt⟩
  · intro k
    exact hvv ⟨k, Nat.lt.step k.isLt⟩

theorem levelSet_zero_isCompact (q : ℚ) : IsCompact (LevelSet 0 q) :=
  coeffBox_isCompact.inter_right (prefixConstraints_isClosed 0 q)

theorem exists_mem_all_levelSets {q : ℚ} (hH : ∀ N, TrueHierarchy.H N q) :
    (⋂ N, LevelSet N q).Nonempty := by
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun N => LevelSet N q) (fun N => levelSet_succ_subset N q)
    (fun N => levelSet_nonempty (hH N)) (levelSet_zero_isCompact q)
    (fun N => levelSet_isClosed N q)

theorem infiniteConstraints_of_mem_all_levelSets {q : ℚ} {c : InfiniteCoefficients}
    (hc : c ∈ ⋂ N, LevelSet N q) : InfiniteConstraints q c := by
  have hlevel : ∀ N, c ∈ LevelSet N q := by simpa only [mem_iInter] using hc
  refine ⟨(hlevel 0).1, ?_, ?_, ?_⟩
  · intro k
    exact (hlevel k).2.1 ⟨k, Nat.lt_succ_self k⟩
  · intro k
    exact (hlevel k).2.2.1 ⟨k, Nat.lt_succ_self k⟩
  · intro k
    exact (hlevel k).2.2.2 ⟨k, Nat.lt_succ_self k⟩

theorem infiniteCoefficients_of_all_levels {q : ℚ}
    (hH : ∀ N, TrueHierarchy.H N q) :
    ∃ c : InfiniteCoefficients, InfiniteConstraints q c := by
  obtain ⟨c, hc⟩ := exists_mem_all_levelSets hH
  exact ⟨c, infiniteConstraints_of_mem_all_levelSets hc⟩

end

end BelgianChocolate.Route1.AllOrders
