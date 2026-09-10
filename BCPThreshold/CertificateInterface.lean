import BCPThreshold.Definitions

/-!
# Finite certificate interface

The booleans in `CertificateInterface` stand for the already specified finite real-algebraic
checks and the finite positive-certificate enumeration. Soundness and completeness are fields of
an implementation record, not global axioms. The certified algorithm is proved for every record
implementing this interface.
-/

namespace BelgianChocolate

/-- Operational finite certificate searches, relative to a threshold `Q`.

`negative s q` means that a finite obstruction has been found by stage `s`.
`positive s q` means that a finite positive certificate has been found by stage `s`.
Completeness is required only on the rational range queried by the algorithm. -/
structure CertificateInterface (Q : ℝ) where
  negative : ℕ → ℚ → Bool
  positive : ℕ → ℚ → Bool
  negative_sound : ∀ {s q}, negative s q = true → (q : ℝ) < Q
  positive_sound : ∀ {s q}, positive s q = true → Q < (q : ℝ)
  negative_complete : ∀ {q : ℚ}, 0 < q → q < (1 : ℚ) / 2 → (q : ℝ) < Q →
    ∃ s, negative s q = true
  positive_complete : ∀ {q : ℚ}, 0 < q → q < (1 : ℚ) / 2 → Q < (q : ℝ) →
    ∃ s, positive s q = true

namespace CertificateInterface

/-- At least one of the four tests at a fixed finite stage has succeeded. -/
def stageHits {Q : ℝ} (C : CertificateInterface Q) (I : RatInterval) (s : ℕ) : Bool :=
  C.negative s I.leftThird || C.negative s I.rightThird ||
    C.positive s I.leftThird || C.positive s I.rightThird

/-- The four-way update, in the frozen priority order: negative left, negative right,
positive left, positive right. -/
def updateAt {Q : ℝ} (C : CertificateInterface Q) (I : RatInterval) (s : ℕ) :
    Option RatInterval :=
  if C.negative s I.leftThird then
    some (I.raiseLeft I.leftThird)
  else if C.negative s I.rightThird then
    some (I.raiseLeft I.rightThird)
  else if C.positive s I.leftThird then
    some (I.lowerRight I.leftThird)
  else if C.positive s I.rightThird then
    some (I.lowerRight I.rightThird)
  else none

/-- Executable finite prefix of the fair stage-by-stage search. It returns the first update found
among stages `0, …, fuel`; increasing `fuel` is the operational unbounded loop. -/
def scanThrough {Q : ℝ} (C : CertificateInterface Q) (I : RatInterval) :
    ℕ → Option RatInterval
  | 0 => C.updateAt I 0
  | fuel + 1 =>
      match C.scanThrough I fuel with
      | some J => some J
      | none => C.updateAt I (fuel + 1)

end CertificateInterface

end BelgianChocolate
