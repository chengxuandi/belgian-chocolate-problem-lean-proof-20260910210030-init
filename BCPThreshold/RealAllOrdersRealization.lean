import BCPThreshold.HierarchyClosedness
import BCPThreshold.InfiniteFourFactors
import BCPThreshold.FourFactorsHierarchy

/-!
# Real-parameter all-orders realization

The executable hierarchy is rational-valued, but endpoint attainment needs the
same compact inverse-limit argument at the real number `analyticQ`.  This file
states the literal real-parameter analogue without changing the rational API.
-/

namespace BelgianChocolate.Route1.RealAllOrders

open Set Metric Complex
open TrueHierarchy

noncomputable section

abbrev InfiniteCoefficients := AllOrders.InfiniteCoefficients

def PrefixConstraints (N : ℕ) (q : ℝ) (c : InfiniteCoefficients) : Prop :=
  (∀ k : Fin (N + 1),
    AllOrders.shiftedCoeff c uFamily k 1 + AllOrders.shiftedCoeff c vFamily k 2 +
      q * c vFamily k = deltaZero k) ∧
  (∀ k : Fin (N + 1),
    AllOrders.convolution c uFamily UFamily k = deltaZero k) ∧
  (∀ k : Fin (N + 1),
    AllOrders.convolution c vFamily VFamily k = deltaZero k)

def LevelSet (N : ℕ) (q : ℝ) : Set InfiniteCoefficients :=
  {c | c ∈ AllOrders.CoeffBox ∧ PrefixConstraints N q c}

def InfiniteConstraints (q : ℝ) (c : InfiniteCoefficients) : Prop :=
  c ∈ AllOrders.CoeffBox ∧
  (∀ k : ℕ,
    AllOrders.shiftedCoeff c uFamily k 1 + AllOrders.shiftedCoeff c vFamily k 2 +
      q * c vFamily k = deltaZero k) ∧
  (∀ k : ℕ, AllOrders.convolution c uFamily UFamily k = deltaZero k) ∧
  (∀ k : ℕ, AllOrders.convolution c vFamily VFamily k = deltaZero k)

theorem levelSet_nonempty {N : ℕ} {q : ℝ} (hN : RealHierarchy.H N q) :
    (LevelSet N q).Nonempty := by
  obtain ⟨c, hcbox, hceq⟩ := hN
  refine ⟨AllOrders.zeroExtend c, AllOrders.zeroExtend_mem_coeffBox hcbox, ?_⟩
  rcases hceq with ⟨hlin, huu, hvv⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simpa [AllOrders.zeroExtend_shiftedCoeff, AllOrders.zeroExtend] using hlin k
  · intro k
    simpa [AllOrders.zeroExtend_convolution] using huu k
  · intro k
    simpa [AllOrders.zeroExtend_convolution] using hvv k

theorem prefixConstraints_isClosed (N : ℕ) (q : ℝ) :
    IsClosed {c : InfiniteCoefficients | PrefixConstraints N q c} := by
  let lin : InfiniteCoefficients → Fin (N + 1) → ℝ := fun c k =>
    AllOrders.shiftedCoeff c uFamily k 1 + AllOrders.shiftedCoeff c vFamily k 2 +
      q * c vFamily k
  let uu : InfiniteCoefficients → Fin (N + 1) → ℝ := fun c k =>
    AllOrders.convolution c uFamily UFamily k
  let vv : InfiniteCoefficients → Fin (N + 1) → ℝ := fun c k =>
    AllOrders.convolution c vFamily VFamily k
  have hlin : ∀ k, Continuous (fun c => lin c k) := by
    intro k
    exact ((AllOrders.continuous_shiftedCoeff uFamily k 1).add
      (AllOrders.continuous_shiftedCoeff vFamily k 2)).add
      (continuous_const.mul (continuous_apply_apply vFamily (k : ℕ)))
  have huu : ∀ k, Continuous (fun c => uu c k) := fun k =>
    AllOrders.continuous_convolution uFamily UFamily k
  have hvv : ∀ k, Continuous (fun c => vv c k) := fun k =>
    AllOrders.continuous_convolution vFamily VFamily k
  have hlinClosed : IsClosed {c | ∀ k, lin c k = deltaZero k} := by
    rw [show {c | ∀ k, lin c k = deltaZero k} =
        ⋂ k, {c | lin c k = deltaZero k} by ext; simp]
    exact isClosed_iInter (fun k => isClosed_eq (hlin k) continuous_const)
  have huuClosed : IsClosed {c | ∀ k, uu c k = deltaZero k} := by
    rw [show {c | ∀ k, uu c k = deltaZero k} =
        ⋂ k, {c | uu c k = deltaZero k} by ext; simp]
    exact isClosed_iInter (fun k => isClosed_eq (huu k) continuous_const)
  have hvvClosed : IsClosed {c | ∀ k, vv c k = deltaZero k} := by
    rw [show {c | ∀ k, vv c k = deltaZero k} =
        ⋂ k, {c | vv c k = deltaZero k} by ext; simp]
    exact isClosed_iInter (fun k => isClosed_eq (hvv k) continuous_const)
  change IsClosed ({c | (∀ k, lin c k = deltaZero k) ∧
    (∀ k, uu c k = deltaZero k) ∧ (∀ k, vv c k = deltaZero k)})
  exact hlinClosed.inter (huuClosed.inter hvvClosed)

theorem levelSet_isClosed (N : ℕ) (q : ℝ) : IsClosed (LevelSet N q) :=
  AllOrders.coeffBox_isClosed.inter (prefixConstraints_isClosed N q)

theorem levelSet_succ_subset (N : ℕ) (q : ℝ) :
    LevelSet (N + 1) q ⊆ LevelSet N q := by
  intro c hc
  refine ⟨hc.1, ?_⟩
  rcases hc.2 with ⟨hlin, huu, hvv⟩
  exact ⟨fun k => hlin ⟨k, Nat.lt.step k.isLt⟩,
    fun k => huu ⟨k, Nat.lt.step k.isLt⟩,
    fun k => hvv ⟨k, Nat.lt.step k.isLt⟩⟩

theorem levelSet_zero_isCompact (q : ℝ) : IsCompact (LevelSet 0 q) :=
  AllOrders.coeffBox_isCompact.inter_right (prefixConstraints_isClosed 0 q)

theorem exists_mem_all_levelSets {q : ℝ} (hH : ∀ N, RealHierarchy.H N q) :
    (⋂ N, LevelSet N q).Nonempty := by
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun N => LevelSet N q) (fun N => levelSet_succ_subset N q)
    (fun N => levelSet_nonempty (hH N)) (levelSet_zero_isCompact q)
    (fun N => levelSet_isClosed N q)

theorem infiniteConstraints_of_mem_all_levelSets {q : ℝ} {c : InfiniteCoefficients}
    (hc : c ∈ ⋂ N, LevelSet N q) : InfiniteConstraints q c := by
  have hlevel : ∀ N, c ∈ LevelSet N q := by simpa only [mem_iInter] using hc
  exact ⟨(hlevel 0).1,
    fun k => (hlevel k).2.1 ⟨k, Nat.lt_succ_self k⟩,
    fun k => (hlevel k).2.2.1 ⟨k, Nat.lt_succ_self k⟩,
    fun k => (hlevel k).2.2.2 ⟨k, Nat.lt_succ_self k⟩⟩

theorem infiniteCoefficients_of_all_levels {q : ℝ}
    (hH : ∀ N, RealHierarchy.H N q) :
    ∃ c : InfiniteCoefficients, InfiniteConstraints q c := by
  obtain ⟨c, hc⟩ := exists_mem_all_levelSets hH
  exact ⟨c, infiniteConstraints_of_mem_all_levelSets hc⟩

theorem series_convolution_eq_one {q : ℝ} {c : InfiniteCoefficients}
    (hc : InfiniteConstraints q c) (f g : Family)
    (hconv : ∀ n, AllOrders.convolution c f g n = deltaZero n)
    {z : ℂ} (hz : ‖z‖ < 1) :
    AllOrders.seriesFun c f z * AllOrders.seriesFun c g z = 1 := by
  rw [AllOrders.seriesFun_mul hc.1 f g hz]
  calc
    (∑' n : ℕ, (AllOrders.convolution c f g n : ℂ) * z ^ n) =
        ∑' n : ℕ, (deltaZero n : ℂ) * z ^ n := by
          apply tsum_congr
          intro n
          rw [hconv n]
    _ = 1 := AllOrders.tsum_deltaZero z

theorem seriesFun_linear_identity {q : ℝ} {c : InfiniteCoefficients}
    (hc : InfiniteConstraints q c) {z : ℂ} (hz : ‖z‖ < 1) :
    z * AllOrders.seriesFun c uFamily z +
      (z ^ 2 + (q : ℂ)) * AllOrders.seriesFun c vFamily z = 1 := by
  let d : ℕ → ℂ := fun n =>
    (AllOrders.shiftedCoeff c uFamily n 1 : ℂ) +
      (AllOrders.shiftedCoeff c vFamily n 2 : ℂ) +
      (q : ℂ) * (c vFamily n : ℂ)
  have hd : ∀ n, d n = (deltaZero n : ℂ) := by
    intro n
    simpa [d] using congrArg (fun x : ℝ => (x : ℂ)) (hc.2.1 n)
  have hu := AllOrders.seriesFun_summable hc.1 uFamily hz
  have hv := AllOrders.seriesFun_summable hc.1 vFamily hz
  have hsuShift := AllOrders.shifted_seriesFun_summable hc.1 uFamily 1 hz
  have hsvShift := AllOrders.shifted_seriesFun_summable hc.1 vFamily 2 hz
  have hqv : Summable (fun n => ((q : ℂ) * (c vFamily n : ℂ)) * z ^ n) := by
    refine (hv.mul_left (q : ℂ)).congr ?_
    intro n
    simp [AllOrders.complexCoeff]
    ring
  calc
    z * AllOrders.seriesFun c uFamily z +
        (z ^ 2 + (q : ℂ)) * AllOrders.seriesFun c vFamily z =
      z * AllOrders.seriesFun c uFamily z + z ^ 2 * AllOrders.seriesFun c vFamily z +
        (q : ℂ) * AllOrders.seriesFun c vFamily z := by ring
    _ = (∑' n, (AllOrders.shiftedCoeff c uFamily n 1 : ℂ) * z ^ n) +
        (∑' n, (AllOrders.shiftedCoeff c vFamily n 2 : ℂ) * z ^ n) +
        ∑' n, ((q : ℂ) * (c vFamily n : ℂ)) * z ^ n := by
      rw [AllOrders.shifted_seriesFun hc.1 uFamily 1 hz,
        AllOrders.shifted_seriesFun hc.1 vFamily 2 hz]
      simp only [pow_one]
      congr 1
      rw [AllOrders.seriesFun, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp [AllOrders.complexCoeff]
      ring
    _ = ∑' n, d n * z ^ n := by
      rw [← hsuShift.tsum_add hsvShift, ← (hsuShift.add hsvShift).tsum_add hqv]
      apply tsum_congr
      intro n
      simp [d]
      ring
    _ = ∑' n, (deltaZero n : ℂ) * z ^ n := by
      apply tsum_congr
      intro n
      rw [hd n]
    _ = 1 := AllOrders.tsum_deltaZero z

noncomputable def infiniteCoefficientsToFourFactors {q : ℝ} {c : InfiniteCoefficients}
    (hc : InfiniteConstraints q c) : FourFactors q where
  u := AllOrders.seriesFun c uFamily
  v := AllOrders.seriesFun c vFamily
  uInv := AllOrders.seriesFun c UFamily
  vInv := AllOrders.seriesFun c VFamily
  holSymm_u := AllOrders.seriesFun_holSymm hc.1 uFamily
  holSymm_v := AllOrders.seriesFun_holSymm hc.1 vFamily
  holSymm_uInv := AllOrders.seriesFun_holSymm hc.1 UFamily
  holSymm_vInv := AllOrders.seriesFun_holSymm hc.1 VFamily
  linear := fun z hz => seriesFun_linear_identity hc
    (by simpa [unitDisc, mem_ball, dist_zero_right] using hz)
  inverse_u := fun z hz => series_convolution_eq_one hc uFamily UFamily hc.2.2.1
    (by simpa [unitDisc, mem_ball, dist_zero_right] using hz)
  inverse_v := fun z hz => series_convolution_eq_one hc vFamily VFamily hc.2.2.2
    (by simpa [unitDisc, mem_ball, dist_zero_right] using hz)

theorem allOrders_realization {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hH : ∀ N, RealHierarchy.H N q) : AnalyticFeasible q := by
  obtain ⟨c, hc⟩ := infiniteCoefficients_of_all_levels hH
  refine ⟨hq0, hq1, factorMap (infiniteCoefficientsToFourFactors hc), ?_⟩
  exact fourFactors_to_discFunction hq0 hq1 (infiniteCoefficientsToFourFactors hc)

theorem factorCoefficients_constraints {q : ℝ}
    (hq0 : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (F : FourFactors q) (N : ℕ) :
    RealHierarchy.CoefficientBox N (factorCoefficients F N) ∧
      RealHierarchy.Equations N q (factorCoefficients F N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a j
    exact (abs_re_le_norm (Schottky.taylorCoefficient F a j)).trans
      (Schottky.coefficientBound hq0 hqb F a j)
  · intro k
    have hc := congrArg Complex.re (fourFactors_linear_coefficient F (k : ℕ))
    rw [factorCoefficients_shiftedCoeff F uFamily k 1,
      factorCoefficients_shiftedCoeff F vFamily k 2,
      factorCoefficients_coeffAt F vFamily k.isLt]
    by_cases h1 : 1 ≤ (k : ℕ) <;> by_cases h2 : 2 ≤ (k : ℕ) <;>
      simp [h1, h2, Complex.add_re, Complex.mul_re] at hc ⊢
    all_goals exact hc
  · intro k
    have hc := fourFactors_product_coefficient F uFamily UFamily
      (fun z hz => F.inverse_u z hz) (k : ℕ)
    rw [← factorCoefficients_convolution_cast F uFamily UFamily k] at hc
    exact_mod_cast hc
  · intro k
    have hc := fourFactors_product_coefficient F vFamily VFamily
      (fun z hz => F.inverse_v z hz) (k : ℕ)
    rw [← factorCoefficients_convolution_cast F vFamily VFamily k] at hc
    exact_mod_cast hc

theorem analyticFeasible_all_levels {q : ℝ}
    (hq0 : 0 < q) (hqb : q ≤ (3 / 4 : ℝ) ^ 2)
    (hA : AnalyticFeasible q) : ∀ N, RealHierarchy.H N q := by
  obtain ⟨_, hq1, f, hf⟩ := hA
  intro N
  exact ⟨factorCoefficients (discFunctionToFourFactors hq0 hq1 hf) N,
    factorCoefficients_constraints hq0 hqb (discFunctionToFourFactors hq0 hq1 hf) N⟩

end

end BelgianChocolate.Route1.RealAllOrders
