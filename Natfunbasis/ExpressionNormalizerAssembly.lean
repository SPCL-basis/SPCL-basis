import Natfunbasis.NormalFormConstruction
import Natfunbasis.NormalizerCore
import Natfunbasis.WilkieTheorem44Target

/-!
# Recursive expression-normalizer assembly

This module isolates the expression-recursive part of the one-variable AJK
normalizer.  The coordinate family is the concrete, single Wilkie family
constructed in `WilkieGeneratorExistence`; no fresh variable is introduced
for a power subexpression.

The only input still required by the recursion is the genuinely
nonconstant-power branch.  `NonconstantPowerStep` states that obligation at
the polynomial level: it must preserve evaluation at the fixed positive-real
coordinates, and it must send a nonzero, non-one base raised to a
nonconstant coefficient-one monomial to another nonconstant coefficient-one
monomial.  Integer correctness is derived from canonical real/integer
compatibility.  Constant exponents are handled here, without using the
interface.

The resulting recursive `raw` construction proves all semiring constructor
equations, nonzeroness, pointwise representation, and the syntactic-tower
monomial clause, and packages them as a `FixedFamilyPrecertificate`.  Thus
completing the remaining AJK factorization/reification step amounts precisely
to constructing one `NonconstantPowerStep` value.
-/

namespace Natfunbasis

open MvPolynomial

namespace NormalForm

namespace ExpressionNormalizerAssembly

noncomputable section

/-- The common family used by every recursively normalized expression. -/
def coordinates : Nat → PosNat → Int :=
  Wilkie.canonicalGeneratorSequence.integerCoordinates

/-- Evaluate a natural-coefficient polynomial at the common integer
coordinate family. -/
def evaluate (p : MvPolynomial Nat Nat) (n : PosNat) : Int :=
  (AlgebraicIndependence.natAeval (K := Int) coordinates p) n

/-- Evaluate a natural-coefficient polynomial at the common positive-real
coordinate family. -/
def evaluateReal (p : MvPolynomial Nat Nat) (y : Wilkie.PositiveReal) : Real :=
  (AlgebraicIndependence.natAeval (K := Real)
    Wilkie.canonicalRealCoordinates p) y

@[simp]
theorem evaluate_zero (n : PosNat) : evaluate 0 n = 0 := by
  simp [evaluate]

@[simp]
theorem evaluate_one (n : PosNat) : evaluate 1 n = 1 := by
  simp [evaluate]

@[simp]
theorem evaluate_X (i : Nat) (n : PosNat) :
    evaluate (X i) n = coordinates i n := by
  simp [evaluate]

@[simp]
theorem evaluate_add (p q : MvPolynomial Nat Nat) (n : PosNat) :
    evaluate (p + q) n = evaluate p n + evaluate q n := by
  simp [evaluate]

@[simp]
theorem evaluate_mul (p q : MvPolynomial Nat Nat) (n : PosNat) :
    evaluate (p * q) n = evaluate p n * evaluate q n := by
  simp [evaluate]

@[simp]
theorem evaluate_pow (p : MvPolynomial Nat Nat) (k : Nat) (n : PosNat) :
    evaluate (p ^ k) n = evaluate p n ^ k := by
  simp [evaluate]

@[simp]
theorem evaluateReal_zero (y : Wilkie.PositiveReal) : evaluateReal 0 y = 0 := by
  simp [evaluateReal]

@[simp]
theorem evaluateReal_one (y : Wilkie.PositiveReal) : evaluateReal 1 y = 1 := by
  simp [evaluateReal]

@[simp]
theorem evaluateReal_X (i : Nat) (y : Wilkie.PositiveReal) :
    evaluateReal (X i) y = Wilkie.canonicalRealCoordinates i y := by
  simp [evaluateReal]

@[simp]
theorem evaluateReal_add (p q : MvPolynomial Nat Nat)
    (y : Wilkie.PositiveReal) :
    evaluateReal (p + q) y = evaluateReal p y + evaluateReal q y := by
  simp [evaluateReal]

@[simp]
theorem evaluateReal_mul (p q : MvPolynomial Nat Nat)
    (y : Wilkie.PositiveReal) :
    evaluateReal (p * q) y = evaluateReal p y * evaluateReal q y := by
  simp [evaluateReal]

@[simp]
theorem evaluateReal_pow (p : MvPolynomial Nat Nat) (k : Nat)
    (y : Wilkie.PositiveReal) :
    evaluateReal (p ^ k) y = evaluateReal p y ^ k := by
  simp [evaluateReal]

/-- A coefficient-one monomial with nonzero exponent vector is not a
constant polynomial. -/
theorem monomial_one_not_constant {m : Nat →₀ Nat} (hm : m ≠ 0) :
    ¬ NormalizerCore.IsConstant (monomial m (1 : Nat)) := by
  intro hconstant
  have hzero : monomial m (1 : Nat) = 0 := by
    rw [NormalizerCore.IsConstant,
      MvPolynomial.constantCoeff_monomial, if_neg hm] at hconstant
    simpa using hconstant
  exact one_ne_zero (MvPolynomial.monomial_eq_zero.mp hzero)

/-- The exact unresolved branch of the recursive construction.  It is
restricted to a normalized exponent which is genuinely nonconstant.

The first law is the required pointwise power identity at the one fixed real
coordinate family.  Integer correctness is then a theorem, via the canonical
integer/real compatibility result.  The second law is the only shape law
needed for towers: a non-one normalized base raised to a nonconstant
coefficient-one monomial is again a nonconstant coefficient-one monomial. -/
structure NonconstantPowerStep where
  normalize : ∀ (base exponent : MvPolynomial Nat Nat),
    ¬ NormalizerCore.IsConstant exponent → MvPolynomial Nat Nat
  evalReal_normalize : ∀ (base exponent : MvPolynomial Nat Nat)
      (h : ¬ NormalizerCore.IsConstant exponent) (y : Wilkie.PositiveReal),
    evaluateReal (normalize base exponent h) y =
      Real.rpow (evaluateReal base y) (evaluateReal exponent y)
  normalize_monomial : ∀ (base : MvPolynomial Nat Nat) (m : Nat →₀ Nat)
      (hbaseZero : base ≠ 0) (hbaseOne : base ≠ 1) (hm : m ≠ 0),
      ∃ out : Nat →₀ Nat, out ≠ 0 ∧
        normalize base (monomial m 1) (monomial_one_not_constant hm) =
          monomial out 1

namespace NonconstantPowerStep

variable (P : NonconstantPowerStep)

/-- Assemble the already-formalized constant power case with the one
unresolved genuinely nonconstant case. -/
noncomputable def normalizePower (P : NonconstantPowerStep)
    (base exponent : MvPolynomial Nat Nat) : MvPolynomial Nat Nat := by
  classical
  exact if h : NormalizerCore.IsConstant exponent then
    base ^ constantCoeff exponent
  else
    P.normalize base exponent h

/-- Recursively normalize an expression.  Only a genuinely nonconstant
normalized exponent is delegated to `P`; a constant exponent is ordinary
polynomial exponentiation. -/
noncomputable def raw (P : NonconstantPowerStep) :
    UnaryExpr → MvPolynomial Nat Nat
  | .one => 1
  | .var _ => X 0
  | .add e d => raw P e + raw P d
  | .mul e d => raw P e * raw P d
  | .pow base exponent =>
      P.normalizePower (raw P base) (raw P exponent)

@[simp]
theorem raw_one : P.raw .one = 1 :=
  rfl

@[simp]
theorem raw_var : P.raw (.var ()) = X 0 :=
  rfl

@[simp]
theorem raw_add (e d : UnaryExpr) :
    P.raw (.add e d) = P.raw e + P.raw d :=
  rfl

@[simp]
theorem raw_mul (e d : UnaryExpr) :
    P.raw (.mul e d) = P.raw e * P.raw d :=
  rfl

theorem raw_pow_of_constant (base exponent : UnaryExpr)
    (h : NormalizerCore.IsConstant (P.raw exponent)) :
    P.raw (.pow base exponent) =
      P.raw base ^ constantCoeff (P.raw exponent) := by
  simp [raw, normalizePower, h]

theorem raw_pow_of_nonconstant (base exponent : UnaryExpr)
    (h : ¬ NormalizerCore.IsConstant (P.raw exponent)) :
    P.raw (.pow base exponent) =
      P.normalize (P.raw base) (P.raw exponent) h := by
  simp [raw, normalizePower, h]

/-- Positive-real correctness of the same recursively assembled normalizer.
This is kept alongside integer correctness because it is the representation
premise used by the Macintyre/Wilkie canonicity handoff. -/
theorem raw_represents_real (e : UnaryExpr) (y : Wilkie.PositiveReal) :
    evaluateReal (P.raw e) y = Wilkie.UnaryExpr.evalReal e y := by
  induction e with
  | one => simp [Wilkie.UnaryExpr.evalReal]
  | var x =>
      cases x
      simp [Wilkie.UnaryExpr.evalReal, evaluateReal,
        Wilkie.canonicalRealCoordinates]
  | add e d he hd =>
      simp [Wilkie.UnaryExpr.evalReal, he, hd]
  | mul e d he hd =>
      simp [Wilkie.UnaryExpr.evalReal, he, hd]
  | pow base exponent hbase hexponent =>
      by_cases hconstant : NormalizerCore.IsConstant (P.raw exponent)
      · rw [P.raw_pow_of_constant base exponent hconstant]
        have hexponentValue :
            Wilkie.UnaryExpr.evalReal exponent y =
              ((constantCoeff (P.raw exponent) : Nat) : Real) := by
          rw [← hexponent]
          rw [hconstant]
          simp [evaluateReal]
        simp only [evaluateReal_pow, hbase, Wilkie.UnaryExpr.evalReal,
          Wilkie.RealExpression.eval]
        change Wilkie.RealExpression.eval (fun _ : Unit ↦ y.1) exponent =
          ((constantCoeff (P.raw exponent) : Nat) : Real) at hexponentValue
        rw [hexponentValue]
        exact (Real.rpow_natCast _ _).symm
      · rw [P.raw_pow_of_nonconstant base exponent hconstant,
          P.evalReal_normalize, hbase, hexponent]
        rfl

/-- Function-level positive-real representation in the exact form consumed
by `originalTermRealIdentityBridge_of_representation`. -/
theorem raw_represents_over_positive_reals :
    Wilkie.RawRepresentsOverPositiveReals P.raw
      Wilkie.canonicalRealCoordinates := by
  intro e
  funext y
  exact P.raw_represents_real e y

/-- Pointwise correctness at the concrete integer Wilkie coordinates follows
from positive-real correctness and compatibility of the two canonical
coordinate families. -/
theorem raw_represents (e : UnaryExpr) (n : PosNat) :
    evaluate (P.raw e) n = (UnaryExpr.eval e n : Int) := by
  simpa [evaluate, coordinates, Wilkie.canonicalIntegerCoordinates] using
    Wilkie.canonical_integer_representation_of_real P.raw
      P.raw_represents_over_positive_reals e n

/-- Every assembled raw polynomial is nonzero.  This follows from its
positive natural value at any positive integer input, rather than being an
extra requirement on the unresolved power step. -/
theorem raw_nonzero (e : UnaryExpr) : P.raw e ≠ 0 := by
  intro hzero
  let n : PosNat := ⟨1, by decide⟩
  have heval : (UnaryExpr.eval e n : Int) = 0 := by
    rw [← P.raw_represents e n, hzero]
    simp [evaluate]
  have hpositive : 0 < (UnaryExpr.eval e n : Int) := by
    exact_mod_cast UnaryExpr.eval_pos e n
  omega

/-- Equality of assembled raw polynomials is already sound for unary
semantics; algebraic independence is needed only for the converse. -/
theorem semEq_of_raw_eq {e d : UnaryExpr} (h : P.raw e = P.raw d) :
    UnaryExpr.SemEq e d := by
  intro n
  apply Int.ofNat_injective
  calc
    (UnaryExpr.eval e n : Int) = evaluate (P.raw e) n :=
      (P.raw_represents e n).symm
    _ = evaluate (P.raw d) n := congrArg (fun p ↦ evaluate p n) h
    _ = (UnaryExpr.eval d n : Int) := P.raw_represents d n

/-- A semantically non-one expression cannot have raw polynomial `1`.
This direction uses only pointwise representation, not independence. -/
theorem raw_ne_one_of_not_semEq_one {e : UnaryExpr}
    (he : ¬ UnaryExpr.SemEq e .one) : P.raw e ≠ 1 := by
  intro hraw
  apply he
  apply P.semEq_of_raw_eq
  simpa using hraw

/-- The assembled normal form of a syntactic tower is a coefficient-one
nonconstant monomial. -/
theorem raw_tower {e : UnaryExpr} (he : SyntacticTower e) :
    ∃ m : Monomial, m ≠ 0 ∧ P.raw e = monomial m 1 := by
  induction he with
  | input =>
      refine ⟨Finsupp.single 0 1, ?_, ?_⟩
      · exact Finsupp.single_ne_zero.mpr one_ne_zero
      · rfl
  | @pow base exponent hbase hexponent ih =>
      obtain ⟨m, hm, hexponentRaw⟩ := ih
      have hbaseRaw : P.raw base ≠ 1 :=
        P.raw_ne_one_of_not_semEq_one hbase
      have hnonconstant :
          ¬ NormalizerCore.IsConstant (P.raw exponent) := by
        rw [hexponentRaw]
        exact monomial_one_not_constant hm
      rw [P.raw_pow_of_nonconstant base exponent hnonconstant]
      obtain ⟨out, hout, hnormalize⟩ :=
        P.normalize_monomial (P.raw base) m (P.raw_nonzero base) hbaseRaw hm
      refine ⟨out, hout, ?_⟩
      simpa only [hexponentRaw] using hnormalize

/-- The recursively assembled data is an actual fixed-family precertificate.
Constructing a `NonconstantPowerStep` is now the sole normalizer-specific
obligation; canonicity and algebraic independence are not fields here. -/
noncomputable def toPrecertificate : FixedFamilyPrecertificate where
  coordinates := coordinates
  raw := P.raw
  raw_nonzero := P.raw_nonzero
  raw_one := P.raw_one
  raw_add := P.raw_add
  raw_mul := P.raw_mul
  raw_tower := P.raw_tower
  represents := P.raw_represents

/-- Once the two explicitly named source inputs are supplied, positive-real
representation makes the assembled precertificate canonical. -/
noncomputable def toCertificate
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence) :
    FixedFamilyCertificate where
  toFixedFamilyPrecertificate := P.toPrecertificate
  canonical := by
    intro e d hsem
    exact Wilkie.canonical_raw_eq_of_macintyre_and_wilkie P.raw
      P.raw_represents_over_positive_reals htransfer hindependent hsem

end NonconstantPowerStep

end

end ExpressionNormalizerAssembly

end NormalForm

end Natfunbasis
