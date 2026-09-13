import BCPThreshold.PowerSeriesIdentities

/-!
# From all-order coefficients to four analytic factors
-/

namespace BelgianChocolate.Route1.AllOrders

open Set Metric Complex
open TrueHierarchy

noncomputable section

theorem seriesFun_holSymm {c : InfiniteCoefficients} (hc : c ∈ CoeffBox)
    (f : TrueHierarchy.Family) : HolSymmOn 1 (seriesFun c f) := by
  constructor
  · exact seriesFun_differentiableOn hc f
  · intro z hz
    exact seriesFun_star c f z

/-- Construct the four analytic factors from one compatible infinite array. -/
noncomputable def infiniteCoefficientsToFourFactors {q : ℚ} {c : InfiniteCoefficients}
    (hc : InfiniteConstraints q c) : FourFactors (q : ℝ) := by
  let F : FourFactors (q : ℝ) := {
    u := seriesFun c uFamily
    v := seriesFun c vFamily
    uInv := seriesFun c UFamily
    vInv := seriesFun c VFamily
    holSymm_u := seriesFun_holSymm hc.1 uFamily
    holSymm_v := seriesFun_holSymm hc.1 vFamily
    holSymm_uInv := seriesFun_holSymm hc.1 UFamily
    holSymm_vInv := seriesFun_holSymm hc.1 VFamily
    linear := fun z hz => seriesFun_linear_identity hc
      (by simpa [unitDisc, mem_ball, dist_zero_right] using hz)
    inverse_u := fun z hz => series_convolution_eq_one hc uFamily UFamily hc.2.2.1
      (by simpa [unitDisc, mem_ball, dist_zero_right] using hz)
    inverse_v := fun z hz => series_convolution_eq_one hc vFamily VFamily hc.2.2.2
      (by simpa [unitDisc, mem_ball, dist_zero_right] using hz)
  }
  exact F

end

end BelgianChocolate.Route1.AllOrders
