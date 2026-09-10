import BCPThreshold.CertificateInterface
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified threshold algorithm

This file proves the complete algorithmic layer conditionally on a concrete
`CertificateInterface`. It formalizes the two trisection points, fair finite-stage search
termination, preservation of strict rational brackets, geometric contraction, iteration, and an
explicit arbitrary-precision bound. It uses no complex analysis.
-/

namespace BelgianChocolate

open RatInterval CertificateInterface

section Elementary

variable {Q : ℝ} (C : CertificateInterface Q)

@[simp] theorem width_raiseLeft (I : RatInterval) (q : ℚ) :
    (I.raiseLeft q).width = I.right - q := rfl

@[simp] theorem width_lowerRight (I : RatInterval) (q : ℚ) :
    (I.lowerRight q).width = q - I.left := rfl

theorem leftThird_lt_rightThird (I : RatInterval) (h : I.left < I.right) :
    I.leftThird < I.rightThird := by
  dsimp [RatInterval.leftThird, RatInterval.rightThird]
  linarith

theorem left_lt_leftThird (I : RatInterval) (h : I.left < I.right) :
    I.left < I.leftThird := by
  dsimp [RatInterval.leftThird]
  linarith

theorem rightThird_lt_right (I : RatInterval) (h : I.left < I.right) :
    I.rightThird < I.right := by
  dsimp [RatInterval.rightThird]
  linarith

theorem trisection_cast_left (I : RatInterval) :
    ((I.leftThird : ℚ) : ℝ) = (2 * (I.left : ℝ) + (I.right : ℝ)) / 3 := by
  norm_num [RatInterval.leftThird]

theorem trisection_cast_right (I : RatInterval) :
    ((I.rightThird : ℚ) : ℝ) = ((I.left : ℝ) + 2 * (I.right : ℝ)) / 3 := by
  norm_num [RatInterval.rightThird]

theorem invariant_order {I : RatInterval} (hI : BracketInvariant Q I) : I.left < I.right := by
  exact_mod_cast hI.2.2.1.trans hI.2.2.2

theorem trisection_in_range {I : RatInterval} (hI : BracketInvariant Q I) :
    0 < I.leftThird ∧ I.leftThird < (1 : ℚ) / 2 ∧
      0 < I.rightThird ∧ I.rightThird < (1 : ℚ) / 2 := by
  have hLR : I.left < I.right := invariant_order hI
  have hL0 : 0 ≤ I.left := hI.1
  have hRhalf : I.right ≤ (1 : ℚ) / 2 := hI.2.1
  constructor
  · dsimp [RatInterval.leftThird]
    linarith
  constructor
  · dsimp [RatInterval.leftThird]
    linarith
  constructor
  · dsimp [RatInterval.rightThird]
    linarith
  · dsimp [RatInterval.rightThird]
    linarith

theorem updateAt_some_iff_stageHits {I : RatInterval} {s : ℕ} :
    (C.updateAt I s).isSome = C.stageHits I s := by
  by_cases h₁ : C.negative s I.leftThird = true
  · simp [CertificateInterface.updateAt, CertificateInterface.stageHits, h₁]
  by_cases h₂ : C.negative s I.rightThird = true
  · simp [CertificateInterface.updateAt, CertificateInterface.stageHits, h₁, h₂]
  by_cases h₃ : C.positive s I.leftThird = true
  · simp [CertificateInterface.updateAt, CertificateInterface.stageHits, h₁, h₂, h₃]
  by_cases h₄ : C.positive s I.rightThird = true
  · simp [CertificateInterface.updateAt, CertificateInterface.stageHits, h₁, h₂, h₃, h₄]
  · simp [CertificateInterface.updateAt, CertificateInterface.stageHits, h₁, h₂, h₃, h₄]

end Elementary

section Termination

variable {Q : ℝ} (C : CertificateInterface Q)

/-- The parallel finite-stage search always has a successful stage on a valid strict bracket.
If one trisection point equals the threshold, the other one lies strictly on one side. -/
theorem parallel_search_terminates {I : RatInterval} (hI : BracketInvariant Q I) :
    ∃ s, C.stageHits I s = true := by
  have hRange := trisection_in_range hI
  have hOrder : I.leftThird < I.rightThird :=
    leftThird_lt_rightThird I (invariant_order hI)
  have hCastOrder : (I.leftThird : ℝ) < (I.rightThird : ℝ) := by exact_mod_cast hOrder
  rcases lt_trichotomy (I.leftThird : ℝ) Q with ha | ha | ha
  · obtain ⟨s, hs⟩ := C.negative_complete hRange.1 hRange.2.1 ha
    refine ⟨s, ?_⟩
    simp [CertificateInterface.stageHits, hs]
  · have hb : Q < (I.rightThird : ℝ) := by linarith
    obtain ⟨s, hs⟩ := C.positive_complete hRange.2.2.1 hRange.2.2.2 hb
    refine ⟨s, ?_⟩
    simp [CertificateInterface.stageHits, hs]
  · rcases lt_trichotomy (I.rightThird : ℝ) Q with hb | hb | hb
    · obtain ⟨s, hs⟩ := C.negative_complete hRange.2.2.1 hRange.2.2.2 hb
      refine ⟨s, ?_⟩
      simp [CertificateInterface.stageHits, hs]
    · have : (I.leftThird : ℝ) < Q := by linarith
      obtain ⟨s, hs⟩ := C.negative_complete hRange.1 hRange.2.1 this
      refine ⟨s, ?_⟩
      simp [CertificateInterface.stageHits, hs]
    · obtain ⟨s, hs⟩ := C.positive_complete hRange.2.2.1 hRange.2.2.2 hb
      refine ⟨s, ?_⟩
      simp [CertificateInterface.stageHits, hs]

/-- Least finite stage at which one of the four parallel searches succeeds. This is a
mathematical packaging of the terminating unbounded finite-stage loop. -/
noncomputable def firstHit (I : RatInterval) (hI : BracketInvariant Q I) : ℕ :=
  Nat.find (parallel_search_terminates C hI)

theorem firstHit_spec (I : RatInterval) (hI : BracketInvariant Q I) :
    C.stageHits I (firstHit C I hI) = true :=
  Nat.find_spec (parallel_search_terminates C hI)

theorem updateAt_firstHit_some (I : RatInterval) (hI : BracketInvariant Q I) :
    ∃ J, C.updateAt I (firstHit C I hI) = some J := by
  generalize ho : C.updateAt I (firstHit C I hI) = o
  have hb : o.isSome = true := by
    rw [← ho, updateAt_some_iff_stageHits C]
    exact firstHit_spec C I hI
  cases o with
  | none => simp at hb
  | some J => exact ⟨J, rfl⟩

/-- A hit at stage `s` is discovered by the executable finite scan through stage `s`. -/
theorem scanThrough_some_of_updateAt_some {I J : RatInterval} {s : ℕ}
    (h : C.updateAt I s = some J) : ∃ K, C.scanThrough I s = some K := by
  cases s with
  | zero => exact ⟨J, h⟩
  | succ s =>
      cases hs : C.scanThrough I s with
      | none => exact ⟨J, by simpa [CertificateInterface.scanThrough, hs] using h⟩
      | some K => exact ⟨K, by simp [CertificateInterface.scanThrough, hs]⟩

/-- Operational totality: for a valid bracket, a finite fuel value suffices for the explicit
stage-by-stage scan. -/
theorem finite_parallel_scan_terminates {I : RatInterval} (hI : BracketInvariant Q I) :
    ∃ fuel J, C.scanThrough I fuel = some J := by
  obtain ⟨J, hJ⟩ := updateAt_firstHit_some C I hI
  obtain ⟨K, hK⟩ := scanThrough_some_of_updateAt_some C hJ
  exact ⟨firstHit C I hI, K, hK⟩

end Termination

section Soundness

variable {Q : ℝ} (C : CertificateInterface Q)

private theorem update_leftThird_correct {I : RatInterval} {s : ℕ} (hI : BracketInvariant Q I)
    (h : C.negative s I.leftThird = true) :
    BracketInvariant Q (I.raiseLeft I.leftThird) ∧
      (I.raiseLeft I.leftThird).width ≤ (2 / 3 : ℚ) * I.width := by
  have hLR := invariant_order hI
  have htri := trisection_in_range hI
  have hqQ : (I.leftThird : ℝ) < Q := C.negative_sound h
  constructor
  · exact ⟨le_of_lt htri.1, hI.2.1, hqQ, hI.2.2.2⟩
  · dsimp [RatInterval.width, RatInterval.raiseLeft, RatInterval.leftThird]
    linarith

private theorem update_rightThird_negative_correct {I : RatInterval} {s : ℕ}
    (hI : BracketInvariant Q I) (h : C.negative s I.rightThird = true) :
    BracketInvariant Q (I.raiseLeft I.rightThird) ∧
      (I.raiseLeft I.rightThird).width ≤ (2 / 3 : ℚ) * I.width := by
  have hLR := invariant_order hI
  have htri := trisection_in_range hI
  have hqQ : (I.rightThird : ℝ) < Q := C.negative_sound h
  constructor
  · exact ⟨le_of_lt htri.2.2.1, hI.2.1, hqQ, hI.2.2.2⟩
  · dsimp [RatInterval.width, RatInterval.raiseLeft, RatInterval.rightThird]
    linarith

private theorem update_leftThird_positive_correct {I : RatInterval} {s : ℕ}
    (hI : BracketInvariant Q I) (h : C.positive s I.leftThird = true) :
    BracketInvariant Q (I.lowerRight I.leftThird) ∧
      (I.lowerRight I.leftThird).width ≤ (2 / 3 : ℚ) * I.width := by
  have hLR := invariant_order hI
  have htri := trisection_in_range hI
  have hQq : Q < (I.leftThird : ℝ) := C.positive_sound h
  constructor
  · exact ⟨hI.1, le_of_lt htri.2.1, hI.2.2.1, hQq⟩
  · dsimp [RatInterval.width, RatInterval.lowerRight, RatInterval.leftThird]
    linarith

private theorem update_rightThird_positive_correct {I : RatInterval} {s : ℕ}
    (hI : BracketInvariant Q I) (h : C.positive s I.rightThird = true) :
    BracketInvariant Q (I.lowerRight I.rightThird) ∧
      (I.lowerRight I.rightThird).width ≤ (2 / 3 : ℚ) * I.width := by
  have hLR := invariant_order hI
  have htri := trisection_in_range hI
  have hQq : Q < (I.rightThird : ℝ) := C.positive_sound h
  constructor
  · exact ⟨hI.1, le_of_lt htri.2.2.2, hI.2.2.1, hQq⟩
  · dsimp [RatInterval.width, RatInterval.lowerRight, RatInterval.rightThird]
    linarith

/-- Every finite successful return is sound, preserves the full interval invariant, and contracts
width by at least the required factor. -/
theorem updateAt_sound {I J : RatInterval} {s : ℕ} (hI : BracketInvariant Q I)
    (hstep : C.updateAt I s = some J) :
    BracketInvariant Q J ∧ J.width ≤ (2 / 3 : ℚ) * I.width := by
  simp only [CertificateInterface.updateAt] at hstep
  split at hstep
  next h =>
    simp only [Option.some.injEq] at hstep
    subst J
    exact update_leftThird_correct C hI h
  next hn =>
    split at hstep
    next h =>
      simp only [Option.some.injEq] at hstep
      subst J
      exact update_rightThird_negative_correct C hI h
    next hn2 =>
      split at hstep
      next h =>
        simp only [Option.some.injEq] at hstep
        subst J
        exact update_leftThird_positive_correct C hI h
      next hn3 =>
        split at hstep
        next h =>
          simp only [Option.some.injEq] at hstep
          subst J
          exact update_rightThird_positive_correct C hI h
        next hn4 => simp at hstep

/-- Every returned interval is contained in its input interval. -/
theorem updateAt_nested {I J : RatInterval} {s : ℕ} (hI : BracketInvariant Q I)
    (hstep : C.updateAt I s = some J) : J.NestedIn I := by
  have horder := invariant_order hI
  have hLL := le_of_lt (left_lt_leftThird I horder)
  have hRR := le_of_lt (rightThird_lt_right I horder)
  have hLR : I.left ≤ I.rightThird := by
    dsimp [RatInterval.rightThird]
    linarith
  have hRL : I.leftThird ≤ I.right := by
    dsimp [RatInterval.leftThird]
    linarith
  simp only [CertificateInterface.updateAt] at hstep
  split at hstep
  next h =>
    simp only [Option.some.injEq] at hstep
    subst J
    exact ⟨hLL, le_rfl⟩
  next hn =>
    split at hstep
    next h =>
      simp only [Option.some.injEq] at hstep
      subst J
      exact ⟨hLR, le_rfl⟩
    next hn₂ =>
      split at hstep
      next h =>
        simp only [Option.some.injEq] at hstep
        subst J
        exact ⟨le_rfl, hRL⟩
      next hn₃ =>
        split at hstep
        next h =>
          simp only [Option.some.injEq] at hstep
          subst J
          exact ⟨le_rfl, hRR⟩
        next hn₄ => simp at hstep

end Soundness

section Iteration

/-- Threshold bounds plus the concrete certificate-search implementation. -/
structure ThresholdData where
  Q : ℝ
  Q_pos : 0 < Q
  Q_lt_half : Q < (1 : ℝ) / 2
  certificates : CertificateInterface Q

namespace ThresholdData

/-- Initial strict certified bracket. -/
def initial (_D : ThresholdData) : RatInterval := ⟨0, 1 / 2⟩

theorem initial_invariant (D : ThresholdData) : BracketInvariant D.Q D.initial := by
  refine ⟨by norm_num [initial], by norm_num [initial], ?_, ?_⟩
  · simpa [initial] using D.Q_pos
  · have h := D.Q_lt_half
    norm_num [initial, div_eq_mul_inv] at h ⊢
    exact h

/-- One total certified subdivision, extracted from the proved terminating staged search. -/
noncomputable def next (D : ThresholdData) (I : RatInterval)
    (hI : BracketInvariant D.Q I) : RatInterval :=
  Classical.choose (updateAt_firstHit_some D.certificates I hI)

theorem next_eq_some (D : ThresholdData) (I : RatInterval)
    (hI : BracketInvariant D.Q I) :
    D.certificates.updateAt I (firstHit D.certificates I hI) = some (D.next I hI) := by
  exact Classical.choose_spec (updateAt_firstHit_some D.certificates I hI)

theorem next_correct (D : ThresholdData) (I : RatInterval)
    (hI : BracketInvariant D.Q I) :
    BracketInvariant D.Q (D.next I hI) ∧
      (D.next I hI).width ≤ (2 / 3 : ℚ) * I.width := by
  exact updateAt_sound D.certificates hI (D.next_eq_some I hI)

theorem next_nested (D : ThresholdData) (I : RatInterval)
    (hI : BracketInvariant D.Q I) : (D.next I hI).NestedIn I := by
  exact updateAt_nested D.certificates hI (D.next_eq_some I hI)

/-- An interval bundled with the invariant required by the next certified step. -/
abbrev CertifiedInterval (D : ThresholdData) := {I : RatInterval // BracketInvariant D.Q I}

/-- Initial certified state. -/
def initialState (D : ThresholdData) : D.CertifiedInterval :=
  ⟨D.initial, D.initial_invariant⟩

/-- One total transition on certified states. -/
noncomputable def nextState (D : ThresholdData) (S : D.CertifiedInterval) :
    D.CertifiedInterval :=
  ⟨D.next S.1 S.2, (D.next_correct S.1 S.2).1⟩

/-- The certified state sequence. Structural recursion is now independent of proof terms. -/
noncomputable def states (D : ThresholdData) : ℕ → D.CertifiedInterval
  | 0 => D.initialState
  | n + 1 => D.nextState (D.states n)

/-- The rational intervals underlying the certified states. -/
noncomputable def intervals (D : ThresholdData) (n : ℕ) : RatInterval :=
  (D.states n).1

@[simp] theorem intervals_zero (D : ThresholdData) : D.intervals 0 = D.initial := rfl

@[simp] theorem intervals_succ (D : ThresholdData) (n : ℕ) :
    D.intervals (n + 1) =
      D.next (D.intervals n) (D.states n).2 := rfl

theorem intervals_invariant (D : ThresholdData) :
    ∀ n, BracketInvariant D.Q (D.intervals n) := fun n => (D.states n).2

/-- Successive certified intervals are nested. -/
theorem intervals_nested (D : ThresholdData) (n : ℕ) :
    (D.intervals (n + 1)).NestedIn (D.intervals n) := by
  rw [D.intervals_succ n]
  exact D.next_nested (D.intervals n) (D.states n).2

/-- The whole sequence is nested, not merely adjacent pairs. -/
theorem intervals_nested_of_le (D : ThresholdData) {m n : ℕ} (h : m ≤ n) :
    (D.intervals n).NestedIn (D.intervals m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simpa using RatInterval.NestedIn.refl (D.intervals m)
  | succ k ih =>
      have hstep := D.intervals_nested (m + k)
      exact RatInterval.NestedIn.trans (by simpa [Nat.add_assoc] using hstep) ih

theorem intervals_width_succ (D : ThresholdData) (n : ℕ) :
    (D.intervals (n + 1)).width ≤
      (2 / 3 : ℚ) * (D.intervals n).width := by
  rw [D.intervals_succ n]
  exact (D.next_correct (D.intervals n) (D.states n).2).2

theorem intervals_width_bound (D : ThresholdData) (n : ℕ) :
    (D.intervals n).width ≤ (1 / 2 : ℚ) * (2 / 3 : ℚ) ^ n := by
  induction n with
  | zero =>
      change (1 / 2 : ℚ) - 0 ≤ (1 / 2 : ℚ) * (2 / 3 : ℚ) ^ 0
      norm_num
  | succ n ih =>
      calc
        (D.intervals (n + 1)).width ≤
            (2 / 3 : ℚ) * (D.intervals n).width := D.intervals_width_succ n
        _ ≤ (2 / 3 : ℚ) * ((1 / 2 : ℚ) * (2 / 3 : ℚ) ^ n) := by
          gcongr
        _ = (1 / 2 : ℚ) * (2 / 3 : ℚ) ^ (n + 1) := by ring

/-- Three contractions per requested bit are more than enough. -/
def precisionIndex (m : ℕ) : ℕ := 3 * (m + 1)

private theorem cubic_ratio_lt_half : (2 / 3 : ℚ) ^ 3 < 1 / 2 := by norm_num

theorem precision_geometric_bound (m : ℕ) :
    (1 / 2 : ℚ) * (2 / 3 : ℚ) ^ precisionIndex m < (1 / 2 : ℚ) ^ m := by
  induction m with
  | zero => norm_num [precisionIndex]
  | succ m ih =>
      have hindex : precisionIndex (m + 1) = precisionIndex m + 3 := by
        simp [precisionIndex]
        omega
      rw [hindex, pow_add]
      calc
        (1 / 2 : ℚ) * ((2 / 3 : ℚ) ^ precisionIndex m * (2 / 3 : ℚ) ^ 3)
            = ((1 / 2 : ℚ) * (2 / 3 : ℚ) ^ precisionIndex m) *
                (2 / 3 : ℚ) ^ 3 := by ring
        _ < (1 / 2 : ℚ) ^ m * (2 / 3 : ℚ) ^ 3 := by
          exact mul_lt_mul_of_pos_right ih (by positivity)
        _ < (1 / 2 : ℚ) ^ m * (1 / 2 : ℚ) := by
          exact mul_lt_mul_of_pos_left cubic_ratio_lt_half (by positivity)
        _ = (1 / 2 : ℚ) ^ (m + 1) := by rw [pow_succ]

/-- The interval returned for a requested binary precision. -/
noncomputable def precisionInterval (D : ThresholdData) (m : ℕ) : RatInterval :=
  D.intervals (precisionIndex m)

/-- Complete arbitrary-precision guarantee: the returned rational endpoints strictly bracket the
threshold and have width strictly below `2⁻ᵐ`. -/
theorem precisionInterval_correct (D : ThresholdData) (m : ℕ) :
    StrictlyBrackets D.Q (D.precisionInterval m) ∧
      (D.precisionInterval m).width < 1 / 2 ^ m := by
  constructor
  · exact (D.intervals_invariant (precisionIndex m)).2.2
  · exact (D.intervals_width_bound (precisionIndex m)).trans_lt
      (by simpa [one_div, inv_pow] using precision_geometric_bound m)

theorem certified_interval_exists (D : ThresholdData) (m : ℕ) :
    ∃ L R : ℚ, (L : ℝ) < D.Q ∧ D.Q < (R : ℝ) ∧ R - L < 1 / 2 ^ m := by
  refine ⟨(D.precisionInterval m).left, (D.precisionInterval m).right, ?_⟩
  rcases D.precisionInterval_correct m with ⟨⟨hL, hR⟩, hw⟩
  exact ⟨hL, hR, by simpa [RatInterval.width] using hw⟩

end ThresholdData

end Iteration

end BelgianChocolate
