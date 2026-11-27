import Natfunbasis.CanonicalWilkieCoordinates

/-!
# Exact targets for the Wilkie--Macintyre source inputs

This module states, but does not assume, the two non-elementary source inputs
still needed by the fixed-family normalizer.  It also proves the elementary
reductions around them.

Wilkie's Theorem 4.4 is literally a simultaneous induction about differential
fields of partially defined real-analytic functions.  Its clause `(I)_i`
adjoins both the auxiliary functions `tau_j` and selected functions
`log u_j` to a differential field `F_0`; clause `(II)_i` classifies solutions
of `X' = Y' X` in the resulting field.  The theorem is therefore strictly
stronger than the conclusion named below.  The conclusion actually used in
the proof of Wilkie's Theorem 1.9 is algebraic independence, over `Real`, of
the original coordinate functions together with all auxiliary functions.

In the source proof, Theorem 4.4 is applied after substituting a positive
real-analytic curve whose coordinate functions are differentially
independent.  The elementary `algebraicIndependent_of_reparametrized` lemma
below records the final descent from that curve to the original function
family.  No analyticity or differential-independence assertion is hidden in
that lemma.

At the end of Section 2 Wilkie cites Macintyre for the fact that equality of
`L*` terms on the positive integers implies equality of their interpretations
on the positive real orthant.  `OriginalTermIntegerToReal` below is exactly
the original-language, one-variable specialization needed here.  The theorem
`originalTermRealIdentityBridge_of_representation` separates that source
input from the independent obligation that a raw normal form represents the
same expression over the positive reals.

No declaration in this file supplies either deep proposition as a theorem,
axiom, instance, or opaque value.
-/

namespace Natfunbasis.Wilkie

noncomputable section

/-! ## Positive-real semantics of original expressions -/

namespace RealExpression

/-- Interpret an original natural expression over the reals, using
`Real.rpow` for binary exponentiation. -/
@[simp]
def eval {Var : Type*} (assignment : Var → Real) : Expr Var → Real
  | .one => 1
  | .var x => assignment x
  | .add s t => eval assignment s + eval assignment t
  | .mul s t => eval assignment s * eval assignment t
  | .pow s t => Real.rpow (eval assignment s) (eval assignment t)

/-- Original expressions remain positive at every strictly positive real
assignment. -/
theorem eval_pos {Var : Type*} (assignment : Var → Real)
    (hassignment : ∀ x, 0 < assignment x) (e : Expr Var) :
    0 < eval assignment e := by
  induction e with
  | one => simp
  | var x => exact hassignment x
  | add s t hs ht => exact add_pos hs ht
  | mul s t hs ht => exact mul_pos hs ht
  | pow s t hs ht => exact Real.rpow_pos_of_pos hs _

/-- Real evaluation after casting a natural assignment agrees with natural
evaluation. -/
theorem eval_natCast {Var : Type*} (assignment : Var → Nat)
    (e : Expr Var) :
    eval (fun x ↦ (assignment x : Real)) e =
      (Expr.eval assignment e : Real) := by
  induction e with
  | one => norm_num
  | var x => rfl
  | add s t hs ht => simp [hs, ht]
  | mul s t hs ht => simp [hs, ht]
  | pow s t hs ht => simp [hs, ht, Real.rpow_natCast]

end RealExpression

namespace UnaryExpr

/-- Positive-real interpretation of a unary original-language expression. -/
def evalReal (e : UnaryExpr) (y : PositiveReal) : Real :=
  RealExpression.eval (fun _ ↦ y.1) e

/-- Every unary real interpretation is positive. -/
theorem evalReal_pos (e : UnaryExpr) (y : PositiveReal) :
    0 < evalReal e y :=
  RealExpression.eval_pos (fun _ ↦ y.1) (fun _ ↦ y.2) e

/-- Real semantics agrees with natural semantics at positive-integer inputs. -/
theorem evalReal_integer (e : UnaryExpr) (n : PosNat) :
    evalReal e (integerRealInput n) = (UnaryExpr.eval e n : Real) := by
  simpa only [evalReal, integerRealInput, UnaryExpr.eval] using
    (RealExpression.eval_natCast (fun _ : Unit ↦ n.1) e)

end UnaryExpr

/-! ## The precise Macintyre handoff needed by this project -/

/-- **Macintyre integer-to-real transfer (the exact specialization used here).**

For any two unary terms `e,d` built only from `1`, the variable, addition,
multiplication, and binary exponentiation, if

`eval e n = eval d n` for every positive integer `n`,

then

`evalReal e y = evalReal d y` for every positive real `y`.

Natural exponentiation is used on the integer side and `Real.rpow` on the
positive-real side.  This is the one-variable, original-language consequence
of Macintyre's *The laws of exponentiation* cited by Wilkie at the end of
Section 2.  It contains no raw normalizer and no auxiliary coordinates. -/
def OriginalTermIntegerToReal : Prop :=
  ∀ {e d : UnaryExpr}, UnaryExpr.SemEq e d →
    UnaryExpr.evalReal e = UnaryExpr.evalReal d

/-- The preceding definition with all semantic abbreviations and function
extensionality made explicit.  This theorem is included so that the exact
external dependency can be inspected directly with `#print`. -/
theorem originalTermIntegerToReal_iff_explicit :
    OriginalTermIntegerToReal ↔
      ∀ e d : UnaryExpr,
        (∀ n : PosNat, UnaryExpr.eval e n = UnaryExpr.eval d n) →
          ∀ y : PositiveReal,
            UnaryExpr.evalReal e y = UnaryExpr.evalReal d y := by
  constructor
  · intro h e d hInteger y
    exact congrFun (h hInteger) y
  · intro h e d hInteger
    funext y
    exact h e d hInteger y

/-- A raw normal form represents each original expression when evaluated at a
specified family of positive-real coordinate functions. -/
def RawRepresentsOverPositiveReals
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (realCoordinates : Nat → PositiveRealFunction) : Prop :=
  ∀ e : UnaryExpr,
    AlgebraicIndependence.natAeval (K := Real) realCoordinates (raw e) =
      UnaryExpr.evalReal e

/-- For the canonical coordinate families, positive-real representation
automatically specializes to the integer representation required by
`FixedFamilyPrecertificate`. -/
theorem canonical_integer_representation_of_real
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (hrep : RawRepresentsOverPositiveReals raw canonicalRealCoordinates)
    (e : UnaryExpr) (n : PosNat) :
    (AlgebraicIndependence.natAeval (K := Int)
        canonicalIntegerCoordinates (raw e)) n =
      (UnaryExpr.eval e n : Int) := by
  apply Int.cast_injective (α := Real)
  calc
    ((AlgebraicIndependence.natAeval (K := Int)
        canonicalIntegerCoordinates (raw e) n : Int) : Real) =
        AlgebraicIndependence.natAeval (K := Real)
          canonicalRealCoordinates (raw e) (integerRealInput n) :=
      canonical_natAeval_integer_compat (raw e) n
    _ = UnaryExpr.evalReal e (integerRealInput n) :=
      congrFun (hrep e) (integerRealInput n)
    _ = (UnaryExpr.eval e n : Real) := UnaryExpr.evalReal_integer e n

/-- The Macintyre transfer and positive-real representation of the raw forms
imply the restricted bridge used by `raw_eq_of_real_independence`. -/
theorem originalTermRealIdentityBridge_of_representation
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (realCoordinates : Nat → PositiveRealFunction)
    (htransfer : OriginalTermIntegerToReal)
    (hrep : RawRepresentsOverPositiveReals raw realCoordinates) :
    OriginalTermRealIdentityBridge raw realCoordinates := by
  intro e d hsem
  rw [hrep e, hrep d]
  exact htransfer hsem

/-! ## Reparameterization and the exact Wilkie independence target -/

/-- Precomposition by a map of domains, as an algebra homomorphism between
rings of real-valued functions. -/
def precomposeAlgHom {Domain Parameter : Type*}
    (curve : Parameter → Domain) :
    (Domain → Real) →ₐ[Real] (Parameter → Real) :=
  AlgHom.pi fun parameter ↦
    Pi.evalAlgHom Real (fun _ : Domain ↦ Real) (curve parameter)

@[simp]
theorem precomposeAlgHom_apply {Domain Parameter : Type*}
    (curve : Parameter → Domain) (f : Domain → Real) (parameter : Parameter) :
    precomposeAlgHom curve f parameter = f (curve parameter) :=
  rfl

/-- Algebraic independence after substitution along one curve already implies
algebraic independence of the original family of functions.  Injectivity of
the curve is not required: a polynomial relation before substitution would
remain a relation afterward. -/
theorem algebraicIndependent_of_reparametrized
    {Index Domain Parameter : Type*}
    (coordinates : Index → Domain → Real)
    (curve : Parameter → Domain)
    (hcurve : AlgebraicIndependent Real
      (fun i parameter ↦ coordinates i (curve parameter))) :
    AlgebraicIndependent Real coordinates := by
  apply AlgebraicIndependent.of_comp (precomposeAlgHom curve)
  change AlgebraicIndependent Real
    (fun i parameter ↦ coordinates i (curve parameter))
  exact hcurve

/-- The concrete coordinate family pulled back along a positive-real curve. -/
def canonicalRealCoordinatesAlong
    (curve : PositiveReal → PositiveReal) :
    Nat → PositiveRealFunction :=
  fun i parameter ↦ canonicalRealCoordinates i (curve parameter)

/-- **Wilkie independence theorem (the exact corollary used here).**

The positive-real function family

`y, tau 0 y, tau 1 y, tau 2 y, ...`

constructed by `canonicalGeneratorSequence` is algebraically independent
over `Real`.  Equivalently, evaluation at this family is injective on
`MvPolynomial Nat Real`: no nonzero real-coefficient polynomial in finitely
many of these functions is identically zero on the positive real axis.

This is the project-needed corollary of Wilkie's Theorem 4.4 used in his proof
of Theorem 1.9.  It is deliberately not presented as a restatement of the
stronger differential-field clauses `(I)_i` and `(II)_i` of Theorem 4.4. -/
def CanonicalWilkieIndependence : Prop :=
  AlgebraicIndependent Real canonicalRealCoordinates

/-- Exact injective-polynomial-evaluation form of
`CanonicalWilkieIndependence`. -/
theorem canonicalWilkieIndependence_iff_aeval_injective :
    CanonicalWilkieIndependence ↔
      Function.Injective
        (MvPolynomial.aeval canonicalRealCoordinates :
          MvPolynomial Nat Real → (PositiveReal → Real)) := by
  exact algebraicIndependent_iff_injective_aeval

/-- Fully pointwise form: every real polynomial relation which vanishes for
all positive real inputs is the zero formal polynomial. -/
theorem canonicalWilkieIndependence_iff_no_polynomial_relation :
    CanonicalWilkieIndependence ↔
      ∀ p : MvPolynomial Nat Real,
        (∀ y : PositiveReal,
          MvPolynomial.aeval canonicalRealCoordinates p y = 0) →
        p = 0 := by
  rw [canonicalWilkieIndependence_iff_aeval_injective]
  constructor
  · intro hinjective p hp
    apply hinjective
    funext y
    simpa using hp y
  · intro h p q hpq
    apply sub_eq_zero.mp
    apply h (p - q)
    intro y
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun hpq y)

/-- The curve-level conclusion established in Wilkie's proof is sufficient
for the concrete project target. -/
theorem canonicalWilkieIndependence_of_curve
    (curve : PositiveReal → PositiveReal)
    (hcurve : AlgebraicIndependent Real
      (canonicalRealCoordinatesAlong curve)) :
    CanonicalWilkieIndependence := by
  exact algebraicIndependent_of_reparametrized
    canonicalRealCoordinates curve hcurve

/-- Once the raw real representation, the Macintyre transfer, and the exact
Wilkie independence target are supplied, semantically equal original
expressions have literally equal raw normal-form polynomials.  This theorem is
only a checked reduction: its three named premises remain visible. -/
theorem canonical_raw_eq_of_macintyre_and_wilkie
    (raw : UnaryExpr → MvPolynomial Nat Nat)
    (hrep : RawRepresentsOverPositiveReals raw canonicalRealCoordinates)
    (htransfer : OriginalTermIntegerToReal)
    (hindependent : CanonicalWilkieIndependence)
    {e d : UnaryExpr} (hsem : UnaryExpr.SemEq e d) :
    raw e = raw d := by
  apply canonical_raw_eq_of_real_independence raw
    (originalTermRealIdentityBridge_of_representation raw
      canonicalRealCoordinates htransfer hrep)
    hindependent hsem

end

end Natfunbasis.Wilkie
