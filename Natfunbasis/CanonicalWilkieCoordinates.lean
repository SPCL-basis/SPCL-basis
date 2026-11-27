import Natfunbasis.WilkieGeneratorExistence
import Natfunbasis.WilkieIndependenceBridge

/-!
# The concrete Wilkie coordinate families

This module specializes the generic real/integer comparison and independence
handoff to the generator system constructed in `WilkieGeneratorExistence`.
Coordinate zero is the original variable; coordinate `k + 1` is the `k`th
canonical auxiliary function.

The coordinatewise compatibility theorem below is unconditional.  The two
deep source inputs remain explicit in the final handoff theorem: real
algebraic independence (Wilkie Theorem 4.4) and an integer-to-real identity
bridge of the required scope.
-/

namespace Natfunbasis.Wilkie

noncomputable section

/-- The discrete coordinate family of the concrete generator sequence. -/
def canonicalIntegerCoordinates : Nat → IntegerGridFunction :=
  canonicalGeneratorSequence.integerCoordinates

/-- The real coordinate family of the concrete generator realization:
`Y, tau_1, tau_2, ...`. -/
def canonicalRealCoordinates : Nat → PositiveRealFunction
  | 0 => fun y ↦ y.1
  | k + 1 => fun y ↦
      canonicalGeneratorSequence.canonicalRealization.tau k y

@[simp]
theorem canonicalIntegerCoordinates_zero (n : PosNat) :
    canonicalIntegerCoordinates 0 n = (n.1 : Int) :=
  rfl

@[simp]
theorem canonicalIntegerCoordinates_succ (k : Nat) (n : PosNat) :
    canonicalIntegerCoordinates (k + 1) n =
      canonicalGeneratorSequence.integerTau k n :=
  rfl

@[simp]
theorem canonicalRealCoordinates_zero (y : PositiveReal) :
    canonicalRealCoordinates 0 y = y.1 :=
  rfl

@[simp]
theorem canonicalRealCoordinates_succ (k : Nat) (y : PositiveReal) :
    canonicalRealCoordinates (k + 1) y =
      canonicalGeneratorSequence.canonicalRealization.tau k y :=
  rfl

/-- Every concrete real coordinate is positive on the positive real line. -/
theorem canonicalRealCoordinates_pos (i : Nat) (y : PositiveReal) :
    0 < canonicalRealCoordinates i y := by
  cases i with
  | zero => exact y.2
  | succ k =>
      exact canonicalGeneratorSequence.canonicalRealization.tau_pos k y

/-- Every concrete integer coordinate is positive. -/
theorem canonicalIntegerCoordinates_pos (i : Nat) (n : PosNat) :
    0 < canonicalIntegerCoordinates i n :=
  canonicalGeneratorSequence.integerCoordinates_pos i n

/-- At every positive integer input, each real coordinate is exactly the real
cast of the corresponding recursively constructed integer coordinate. -/
theorem canonicalCoordinates_integer_compat (i : Nat) (n : PosNat) :
    canonicalRealCoordinates i (integerRealInput n) =
      (canonicalIntegerCoordinates i n : Real) := by
  cases i with
  | zero => rfl
  | succ k =>
      exact
        canonicalGeneratorSequence.canonicalRealization.tau_integer_compat k n

/-- Evaluation of every natural-coefficient polynomial commutes with the
coordinatewise integer-to-real comparison. -/
theorem canonical_natAeval_integer_compat
    (p : MvPolynomial Nat Nat) (n : PosNat) :
    ((AlgebraicIndependence.natAeval (K := Int)
        canonicalIntegerCoordinates p n : Int) : Real) =
      AlgebraicIndependence.natAeval (K := Real)
        canonicalRealCoordinates p (integerRealInput n) := by
  induction p using MvPolynomial.induction_on with
  | C value =>
      simp
  | add p q hp hq =>
      simp [hp, hq]
  | @mul_X p i hp =>
      simp [hp, canonicalCoordinates_integer_compat]

/-- Concrete specialization of the stronger whole-grid independence
handoff.  This theorem proves the implication; it does not supply either of
the two displayed deep hypotheses. -/
theorem canonicalInteger_algebraicIndependent_of_real
    (hbridge : IntegerGridIdentityBridge canonicalIntegerCoordinates
      canonicalRealCoordinates)
    (hreal : AlgebraicIndependent Real canonicalRealCoordinates) :
    AlgebraicIndependent Int canonicalIntegerCoordinates :=
  integer_algebraicIndependent_of_real canonicalIntegerCoordinates
    canonicalRealCoordinates hbridge hreal

/-- Concrete specialization of the source-scoped original-term handoff. -/
theorem canonical_raw_eq_of_real_independence
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (hbridge : OriginalTermRealIdentityBridge raw canonicalRealCoordinates)
    (hreal : AlgebraicIndependent Real canonicalRealCoordinates)
    {e d : UnaryExpr} (h : UnaryExpr.SemEq e d) : raw e = raw d :=
  raw_eq_of_real_independence raw canonicalRealCoordinates hbridge hreal h

end

end Natfunbasis.Wilkie
