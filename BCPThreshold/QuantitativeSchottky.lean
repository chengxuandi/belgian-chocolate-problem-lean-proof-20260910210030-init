import BCPThreshold.RCFRoute1.TrueHierarchy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Checked arithmetic for the quantitative Schottky bridge

This file does NOT assert Jenkins's omitted-value theorem. That classical
analytic theorem has not yet been formalized in this project. The lemmas here
prove the exact arithmetic needed after its half-disc specialization.
-/

namespace BelgianChocolate.Schottky

/-- A rational-polynomial upper bound for one half-disc propagation step. -/
theorem jenkins_half_bound_arithmetic {A : ℝ} (hA : 1 ≤ A) :
    (16 * A + 8) ^ 3 / 16 + 1 ≤ 3 ^ 7 * A ^ 3 := by
  have h0 : 0 ≤ A := by linarith
  have h1 : 1 ≤ A ^ 3 := one_le_pow₀ hA
  have hc : (16 * A + 8) ^ 3 ≤ (24 * A) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  nlinarith

def envelope (k : ℕ) : ℝ := 3 ^ (8 * 4 ^ k)

theorem envelope_one_le (k : ℕ) : 1 ≤ envelope k :=
  one_le_pow₀ (by norm_num)

theorem envelope_step (k : ℕ) :
    (3 : ℝ) ^ 7 * envelope k ^ 3 ≤ envelope (k + 1) := by
  unfold envelope
  rw [← pow_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  have h : 1 ≤ (4 : ℕ) ^ k := Nat.one_le_pow k 4 (by omega)
  rw [pow_succ]
  omega

/-- This is an arithmetic induction, not a substitute for analytic propagation. -/
theorem chain_bound (x : ℕ → ℝ) (h0 : x 0 ≤ 1)
    (hs : ∀ k, x (k + 1) ≤ (3 : ℝ) ^ 7 * (max 1 (x k)) ^ 3) :
    ∀ k, x k ≤ envelope k := by
  intro k
  induction k with
  | zero => exact h0.trans (envelope_one_le 0)
  | succ k ih =>
    apply (hs k).trans
    apply le_trans _ (envelope_step k)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (max_le (envelope_one_le k) ih) _

theorem envelope_le_paper_exponent (k : ℕ) :
    envelope k ≤ (3 : ℝ) ^ (66 * 9 ^ k) := by
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  have h : (4 : ℕ) ^ k ≤ 9 ^ k := Nat.pow_le_pow_left (by omega) k
  omega

theorem envelope_le_largeBound (r : ℚ) :
    envelope (Route1.PaperBounds.chainLength r) ≤
      (Route1.PaperBounds.largeBound r : ℝ) := by
  simpa [Route1.PaperBounds.largeBound] using
    envelope_le_paper_exponent (Route1.PaperBounds.chainLength r)

end BelgianChocolate.Schottky
