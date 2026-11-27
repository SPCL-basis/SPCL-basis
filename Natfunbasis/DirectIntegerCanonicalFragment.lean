import Natfunbasis.CanonicalNormalizer
import Natfunbasis.DirectIntegerRapidSeparation

/-!
# The directly separated fragment of the canonical raw normalizer

The strategic-prime argument separates exactly those canonical raw
polynomials whose variables lie in the original/filler subfamily.  This file
states that fragment at the actual canonicity boundary and packages the exact
additional closure premise that would turn it into a full fixed-family
certificate.
-/

namespace Natfunbasis

namespace NormalForm

open MvPolynomial

noncomputable section

open DirectIntegerRapidSeparation

/-- A polynomial uses only the original coordinate and the canonical
stage-zero filler coordinates, up to renaming. -/
def UsesOnlyCanonicalRapidCoordinates
    (P : MvPolynomial Nat Nat) : Prop :=
  ∃ Q : MvPolynomial Nat Nat,
    MvPolynomial.rename canonicalRapidIndex Q = P

/-- Semantic equality is reflected syntactically whenever both canonical raw
polynomials belong to the directly separated rapid-coordinate fragment. -/
theorem canonicalRaw_eq_of_semEq_of_rapidCoordinates
    {e d : UnaryExpr} (hsem : UnaryExpr.SemEq e d)
    (he : UsesOnlyCanonicalRapidCoordinates (canonicalRaw e))
    (hd : UsesOnlyCanonicalRapidCoordinates (canonicalRaw d)) :
    canonicalRaw e = canonicalRaw d := by
  obtain ⟨P, hP⟩ := he
  obtain ⟨Q, hQ⟩ := hd
  have heval :
      AlgebraicIndependence.natAeval (K := Int)
          Wilkie.canonicalGeneratorSequence.integerCoordinates
          (MvPolynomial.rename canonicalRapidIndex P) =
        AlgebraicIndependence.natAeval (K := Int)
          Wilkie.canonicalGeneratorSequence.integerCoordinates
          (MvPolynomial.rename canonicalRapidIndex Q) := by
    funext n
    calc
      (AlgebraicIndependence.natAeval (K := Int)
          Wilkie.canonicalGeneratorSequence.integerCoordinates
          (MvPolynomial.rename canonicalRapidIndex P)) n =
          (UnaryExpr.eval e n : Int) := by
        rw [hP]
        exact canonicalRaw_represents e n
      _ = (UnaryExpr.eval d n : Int) := congrArg Int.ofNat (hsem n)
      _ = (AlgebraicIndependence.natAeval (K := Int)
          Wilkie.canonicalGeneratorSequence.integerCoordinates
          (MvPolynomial.rename canonicalRapidIndex Q)) n := by
        rw [hQ]
        exact (canonicalRaw_represents d n).symm
  have hPQ : P = Q :=
    canonicalRapidRename_natAeval_injective heval
  rw [← hP, ← hQ, hPQ]

/-- The one genuinely additional premise needed to make the rapid-coordinate
argument certify the existing canonical raw normalizer: every output would
have to use only original/filler coordinates. -/
def canonicalCertificateOfRapidClosure
    (hclosure : ∀ e : UnaryExpr,
      UsesOnlyCanonicalRapidCoordinates (canonicalRaw e)) :
    FixedFamilyCertificate where
  toFixedFamilyPrecertificate := canonicalPrecertificate
  canonical := by
    intro e d hsem
    exact canonicalRaw_eq_of_semEq_of_rapidCoordinates hsem
      (hclosure e) (hclosure d)

/-- Pairwise form of the remaining obstruction: after the direct discrete
argument, a semantic pair is canonical as soon as its two raw outputs can be
reified over the filler subfamily. -/
theorem canonicalRaw_eq_of_semEq_iff_rapid_reification_suffices
    {e d : UnaryExpr}
    (he : UsesOnlyCanonicalRapidCoordinates (canonicalRaw e))
    (hd : UsesOnlyCanonicalRapidCoordinates (canonicalRaw d)) :
    UnaryExpr.SemEq e d → canonicalRaw e = canonicalRaw d :=
  fun hsem ↦ canonicalRaw_eq_of_semEq_of_rapidCoordinates hsem he hd

end

end NormalForm

end Natfunbasis
