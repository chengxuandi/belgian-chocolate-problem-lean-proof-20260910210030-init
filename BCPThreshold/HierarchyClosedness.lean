import BCPThreshold.AllOrdersRealization
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Closedness in the real parameter

This is the literal real-parameter version of the existing finite equations.
The rational hierarchy and its executable compiler are unchanged. Their exact
agreement with this version is `H_rat_iff`.
-/

namespace BelgianChocolate.Route1.RealHierarchy

open Set TrueHierarchy

noncomputable section

def CoefficientBox (N : ℕ) : Set (Coefficients N) :=
  {c | ∀ f j, |c f j| ≤ (PaperBounds.coefficientBound j : ℝ)}

def Equations (N : ℕ) (q : ℝ) (c : Coefficients N) : Prop :=
  (∀ k : Fin (N + 1),
    shiftedCoeff c uFamily k 1 + shiftedCoeff c vFamily k 2 +
      q * coeffAt c vFamily k = deltaZero k) ∧
  (∀ k : Fin (N + 1), convolution c uFamily UFamily k = deltaZero k) ∧
  (∀ k : Fin (N + 1), convolution c vFamily VFamily k = deltaZero k)

def H (N : ℕ) (q : ℝ) : Prop :=
  ∃ c : Coefficients N, c ∈ CoefficientBox N ∧ Equations N q c

theorem H_rat_iff (N : ℕ) (q : ℚ) : H N (q : ℝ) ↔ TrueHierarchy.H N q := Iff.rfl

theorem coefficientBox_isCompact (N : ℕ) : IsCompact (CoefficientBox N) := by
  have heq : CoefficientBox N =
      {c : Coefficients N | ∀ (f : Family) (j : Fin (N + 1)),
        c f j ∈ Icc (-(PaperBounds.coefficientBound j : ℝ))
          (PaperBounds.coefficientBound j : ℝ)} := by
    ext c
    simp [CoefficientBox, abs_le]
  rw [heq]
  exact isCompact_pi_infinite (fun _ =>
    isCompact_pi_infinite (fun _ => isCompact_Icc))

theorem continuous_coeffAt (N : ℕ) (f : Family) (k : ℕ) :
    Continuous (fun c : Coefficients N => coeffAt c f k) := by
  unfold coeffAt
  split
  · exact continuous_apply_apply f _
  · exact continuous_const

theorem continuous_shiftedCoeff (N : ℕ) (f : Family) (k shift : ℕ) :
    Continuous (fun c : Coefficients N => shiftedCoeff c f k shift) := by
  unfold shiftedCoeff
  split
  · exact continuous_coeffAt N f _
  · exact continuous_const

theorem continuous_convolution (N : ℕ) (f g : Family) (k : ℕ) :
    Continuous (fun c : Coefficients N => convolution c f g k) := by
  unfold convolution
  apply continuous_list_sum
  intro i _
  exact (continuous_coeffAt N f i).mul (continuous_coeffAt N g (k - i))

theorem equations_jointly_closed (N : ℕ) :
    IsClosed {p : ℝ × Coefficients N | Equations N p.1 p.2} := by
  have hlin (k : Fin (N + 1)) : Continuous (fun p : ℝ × Coefficients N =>
      shiftedCoeff p.2 uFamily k 1 + shiftedCoeff p.2 vFamily k 2 +
        p.1 * coeffAt p.2 vFamily k) :=
    (((continuous_shiftedCoeff N uFamily k 1).comp continuous_snd).add
      ((continuous_shiftedCoeff N vFamily k 2).comp continuous_snd)).add
      (continuous_fst.mul ((continuous_coeffAt N vFamily k).comp continuous_snd))
  have hprod (f g : Family) (k : Fin (N + 1)) :
      Continuous (fun p : ℝ × Coefficients N => convolution p.2 f g k) :=
    (continuous_convolution N f g k).comp continuous_snd
  have heq : {p : ℝ × Coefficients N | Equations N p.1 p.2} =
      (⋂ k : Fin (N + 1), {p |
        shiftedCoeff p.2 uFamily k 1 + shiftedCoeff p.2 vFamily k 2 +
          p.1 * coeffAt p.2 vFamily k = deltaZero k}) ∩
      ((⋂ k : Fin (N + 1), {p | convolution p.2 uFamily UFamily k = deltaZero k}) ∩
       (⋂ k : Fin (N + 1), {p | convolution p.2 vFamily VFamily k = deltaZero k})) := by
    ext p
    simp [Equations]
  rw [heq]
  exact (isClosed_iInter (fun k => isClosed_eq (hlin k) continuous_const)).inter
    ((isClosed_iInter (fun k => isClosed_eq (hprod uFamily UFamily k) continuous_const)).inter
      (isClosed_iInter (fun k => isClosed_eq (hprod vFamily VFamily k) continuous_const)))

/-- The witness coordinate is compact. The parameter coordinate need not be. -/
theorem H_parameter_closed (N : ℕ) : IsClosed {q : ℝ | H N q} := by
  let W := ↥(CoefficientBox N)
  letI : CompactSpace W := isCompact_iff_compactSpace.mp (coefficientBox_isCompact N)
  let S : Set (ℝ × W) := {p | Equations N p.1 p.2.val}
  have hS : IsClosed S :=
    (equations_jointly_closed N).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have himage : Prod.fst '' S = {q : ℝ | H N q} := by
    ext q
    constructor
    · rintro ⟨⟨r, c⟩, hc, rfl⟩
      exact ⟨c.val, c.property, hc⟩
    · rintro ⟨c, hc, he⟩
      exact ⟨(q, ⟨c, hc⟩), he, rfl⟩
  rw [← himage]
  exact isClosedMap_fst_of_compactSpace S hS

theorem H_parameter_limit {N : ℕ} {q : ℕ → ℝ} {a : ℝ}
    (hq : Filter.Tendsto q Filter.atTop (nhds a)) (hH : ∀ n, H N (q n)) :
    H N a :=
  (H_parameter_closed N).mem_of_tendsto hq (Filter.Eventually.of_forall hH)

end

end BelgianChocolate.Route1.RealHierarchy
