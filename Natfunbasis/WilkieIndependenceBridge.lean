import Natfunbasis.NormalFormConstruction
import Natfunbasis.WilkieIntegerEvaluation

/-!
# From real-function independence to the positive-integer grid

Wilkie's Theorem 4.4 concerns real functions on the positive real orthant,
whereas natural functions in this project are equal when they agree at every
positive integer.  Those facts cannot be identified by analyticity alone.

This module isolates two bridge statements.  The first is the exact restricted
statement used in the cited proof: equality of two original expressions on
the integer grid makes their two raw normal-form polynomials equal as real
functions.  The second is a stronger, global polynomial-identity transfer; it
implies algebraic independence of the entire integer-valued coordinate family.

In the cited route, the restricted transfer is the contribution obtained via
Macintyre and the real independence premise is Wilkie Theorem 4.4. Neither is
postulated here; all theorems retain both as visible hypotheses. The stronger
global bridge is recorded only as an optional sufficient hypothesis and is not
attributed to the source without an additional proof.
-/

namespace Natfunbasis.Wilkie

noncomputable section

/-- Integer-valued functions on the strictly positive natural numbers. -/
abbrev IntegerGridFunction := PosNat → Int

/-- Real-valued functions on the strictly positive real numbers. -/
abbrev PositiveRealFunction := PositiveReal → Real

/-- The source-scoped integer-to-real bridge: it concerns precisely the raw
normal forms of original expressions, not arbitrary expanded-language
polynomials in the auxiliary coordinates. -/
def OriginalTermRealIdentityBridge
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (realCoordinates : Nat → PositiveRealFunction) : Prop :=
  ∀ {e d : UnaryExpr}, UnaryExpr.SemEq e d →
    AlgebraicIndependence.natAeval (K := Real) realCoordinates (raw e) =
      AlgebraicIndependence.natAeval (K := Real) realCoordinates (raw d)

/-- The restricted source bridge plus real algebraic independence makes the
raw normalizer canonical on original expressions. -/
theorem raw_eq_of_real_independence
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (realCoordinates : Nat → PositiveRealFunction)
    (hbridge : OriginalTermRealIdentityBridge raw realCoordinates)
    (hreal : AlgebraicIndependent Real realCoordinates)
    {e d : UnaryExpr} (h : UnaryExpr.SemEq e d) : raw e = raw d := by
  apply AlgebraicIndependence.natAeval_injective realCoordinates hreal
  exact hbridge h

/-- Assemble the exact downstream certificate from an expression-level
precertificate, the restricted source bridge, and real-function algebraic
independence. -/
noncomputable def _root_.Natfunbasis.NormalForm.FixedFamilyPrecertificate.ofRealIndependence
    (C : NormalForm.FixedFamilyPrecertificate)
    (realCoordinates : Nat → PositiveRealFunction)
    (hbridge : OriginalTermRealIdentityBridge C.raw realCoordinates)
    (hreal : AlgebraicIndependent Real realCoordinates) :
    NormalForm.FixedFamilyCertificate where
  toFixedFamilyPrecertificate := C
  canonical := raw_eq_of_real_independence C.raw realCoordinates hbridge hreal

/-- A stronger polynomial-identity transfer between the whole integer-grid
coordinate family and a real coordinate family.

This is useful as a sufficient abstraction, but is stronger than the
original-term bridge used by Wilkie's Theorem 1.9. -/
def IntegerGridIdentityBridge
    (integerCoordinates : Nat → IntegerGridFunction)
    (realCoordinates : Nat → PositiveRealFunction) : Prop :=
  ∀ p q : MvPolynomial Nat Int,
    MvPolynomial.aeval integerCoordinates p =
        MvPolynomial.aeval integerCoordinates q →
      MvPolynomial.aeval realCoordinates
          (MvPolynomial.map (Int.castRingHom Real) p) =
        MvPolynomial.aeval realCoordinates
          (MvPolynomial.map (Int.castRingHom Real) q)

/-- The Macintyre-style grid bridge and Wilkie-style real algebraic
independence imply algebraic independence of the integer coordinate
functions. -/
theorem integer_algebraicIndependent_of_real
    (integerCoordinates : Nat → IntegerGridFunction)
    (realCoordinates : Nat → PositiveRealFunction)
    (hbridge : IntegerGridIdentityBridge integerCoordinates realCoordinates)
    (hreal : AlgebraicIndependent Real realCoordinates) :
    AlgebraicIndependent Int integerCoordinates := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro p q hpq
  apply MvPolynomial.map_injective (Int.castRingHom Real) Int.cast_injective
  apply (algebraicIndependent_iff_injective_aeval.mp hreal)
  exact hbridge p q hpq

/-- Equality form of the preceding theorem, convenient when constructing a
`NormalForm.FixedFamilyCertificate`. -/
theorem integer_aeval_injective_of_real
    (integerCoordinates : Nat → IntegerGridFunction)
    (realCoordinates : Nat → PositiveRealFunction)
    (hbridge : IntegerGridIdentityBridge integerCoordinates realCoordinates)
    (hreal : AlgebraicIndependent Real realCoordinates) :
    Function.Injective
      (MvPolynomial.aeval integerCoordinates :
        MvPolynomial Nat Int → (PosNat → Int)) :=
  algebraicIndependent_iff_injective_aeval.mp
    (integer_algebraicIndependent_of_real integerCoordinates realCoordinates
      hbridge hreal)

end

end Natfunbasis.Wilkie
