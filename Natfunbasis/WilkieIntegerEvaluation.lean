import Natfunbasis.WilkieGenerators

/-!
# Integer evaluation of a Wilkie generator sequence

The W1--W2 data in `WilkieGenerators` is triangular: the pair at stage `k`
mentions the original variable and only the first `k` auxiliary variables.
This module uses that triangularity to construct, without any existence or
independence assumption, the corresponding auxiliary functions on positive
natural inputs.

At a stage, the integer-valued base and exponent polynomials are evaluated at
the already constructed coordinates.  Positivity on the real orthant implies
that the integer base is positive; the coefficient-one monomial exponent is
positive as well.  The new auxiliary value is therefore their ordinary
integer natural power.  Finally `integerCoordinates` packages the input at
coordinate zero and the auxiliary functions at successor coordinates, in the
exact type expected by `NormalForm.FixedFamilyCertificate.coordinates`.

The discrete construction uses no `GeneratorRealization`, algebraic-
independence hypothesis, or derivability property. A separate final section
then proves that any supplied real W3 realization agrees with this canonical
integer recursion at every positive integer input.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

namespace StagePolynomial

/-- Evaluation of a stage polynomial in its coefficient ring `Int`. -/
def evalInt {k : Nat} (p : StagePolynomial k)
    (assignment : StageVar k → Int) : Int :=
  MvPolynomial.eval assignment p

/-- Casting an integer evaluation to `Real` agrees with evaluating the same
integer-coefficient polynomial over `Real`. -/
theorem cast_evalInt {k : Nat} (p : StagePolynomial k)
    (assignment : StageVar k → Int) :
    ((p.evalInt assignment : Int) : Real) =
      p.evalReal (fun i ↦ (assignment i : Real)) := by
  simpa [evalInt, evalReal] using
    (MvPolynomial.hom_eval₂ p (RingHom.id Int) (Int.castRingHom Real) assignment)

/-- A polynomial positive on the positive real orthant remains positive when
evaluated at positive integers. -/
theorem evalInt_pos_of_positiveOnOrthant {k : Nat} {p : StagePolynomial k}
    (hp : PositiveOnOrthant p) (assignment : StageVar k → Int)
    (hassignment : ∀ i, 0 < assignment i) :
    0 < p.evalInt assignment := by
  have hrealAssignment : ∀ i, 0 < (assignment i : Real) := by
    intro i
    exact_mod_cast hassignment i
  have hreal := hp (fun i ↦ (assignment i : Real)) hrealAssignment
  have hcast : (0 : Real) < (p.evalInt assignment : Real) := by
    rw [p.cast_evalInt assignment]
    exact hreal
  exact_mod_cast hcast

end StagePolynomial

namespace Base

/-- Every encoded W1 base evaluates positively at a positive integer stage
assignment. -/
theorem evalInt_pos {k : Nat} (b : Base k)
    (assignment : StageVar k → Int) (hassignment : ∀ i, 0 < assignment i) :
    0 < b.polynomial.evalInt assignment :=
  StagePolynomial.evalInt_pos_of_positiveOnOrthant b.positiveOnOrthant
    assignment hassignment

end Base

namespace NonconstantMonomial

/-- Every W1 coefficient-one monomial exponent evaluates positively at a
positive integer stage assignment. -/
theorem evalInt_pos {k : Nat} (m : NonconstantMonomial k)
    (assignment : StageVar k → Int) (hassignment : ∀ i, 0 < assignment i) :
    0 < m.polynomial.evalInt assignment := by
  apply StagePolynomial.evalInt_pos_of_positiveOnOrthant
      (assignment := assignment) _ hassignment
  intro realAssignment hrealAssignment
  exact m.evalReal_pos realAssignment hrealAssignment

end NonconstantMonomial

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The discrete auxiliary functions determined by a triangular generator
sequence.  At stage `k`, recursive calls are made only at indices `j < k`, as
witnessed by `j : Fin k`.

The integer exponent is converted to `Nat` for ordinary ring exponentiation.
Its positivity, proved below, ensures that this conversion loses no data. -/
def integerTau (k : Nat) (n : PosNat) : Int :=
  let baseAssignment : StageVar (S.pair k).baseStage → Int :=
    Fin.cases (n.1 : Int) (fun j ↦ integerTau j.1 n)
  let exponentAssignment : StageVar (S.pair k).exponentStage → Int :=
    Fin.cases (n.1 : Int) (fun j ↦ integerTau j.1 n)
  let base := (S.pair k).base.polynomial.evalInt baseAssignment
  let exponent := (S.pair k).exponent.polynomial.evalInt exponentAssignment
  base ^ exponent.toNat
termination_by k
decreasing_by
  · exact j.2.trans_le (S.pair k).baseStage_le
  · exact j.2.trans_le (S.pair k).exponentStage_le

/-- The stage assignment consisting of the original positive integer followed
by the earlier recursively constructed auxiliary values. -/
def integerAssignment (k : Nat) (n : PosNat) : StageVar k → Int :=
  Fin.cases (n.1 : Int) (fun j ↦ S.integerTau j.1 n)

@[simp]
theorem integerAssignment_original (k : Nat) (n : PosNat) :
    S.integerAssignment k n 0 = (n.1 : Int) :=
  rfl

@[simp]
theorem integerAssignment_auxiliary {k : Nat} (n : PosNat) (j : Fin k) :
    S.integerAssignment k n j.succ = S.integerTau j.1 n :=
  rfl

/-- The base value at a discrete recursive stage. -/
def integerBase (k : Nat) (n : PosNat) : Int :=
  (S.pair k).base.polynomial.evalInt
    (S.integerAssignment (S.pair k).baseStage n)

/-- The exponent value at a discrete recursive stage, before conversion to a
natural exponent. -/
def integerExponent (k : Nat) (n : PosNat) : Int :=
  (S.pair k).exponent.polynomial.evalInt
    (S.integerAssignment (S.pair k).exponentStage n)

/-- The defining discrete W3 recursion equation. -/
theorem integerTau_eq (k : Nat) (n : PosNat) :
    S.integerTau k n =
      S.integerBase k n ^ (S.integerExponent k n).toNat := by
  rw [integerTau]
  rfl

/-- All recursively constructed auxiliary values are positive. -/
theorem integerTau_pos (k : Nat) (n : PosNat) :
    0 < S.integerTau k n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [S.integerTau_eq]
      apply pow_pos
      apply (S.pair k).base.evalInt_pos
      intro i
      refine Fin.cases ?_ ?_ i
      · change (0 : Int) < (n.1 : Int)
        exact_mod_cast n.2
      · intro j
        exact ih j.1 (j.2.trans_le (S.pair k).baseStage_le)

/-- Every coordinate available at a stage is a positive integer. -/
theorem integerAssignment_pos (k : Nat) (n : PosNat) (i : StageVar k) :
    0 < S.integerAssignment k n i := by
  refine Fin.cases ?_ ?_ i
  · change (0 : Int) < (n.1 : Int)
    exact_mod_cast n.2
  · intro j
    exact S.integerTau_pos j.1 n

/-- The recursively evaluated base is positive. -/
theorem integerBase_pos (k : Nat) (n : PosNat) :
    0 < S.integerBase k n := by
  apply (S.pair k).base.evalInt_pos
  exact S.integerAssignment_pos (S.pair k).baseStage n

/-- The recursively evaluated exponent is a positive integer. -/
theorem integerExponent_pos (k : Nat) (n : PosNat) :
    0 < S.integerExponent k n := by
  apply (S.pair k).exponent.evalInt_pos
  exact S.integerAssignment_pos (S.pair k).exponentStage n

/-- Converting the positive integer exponent to the natural exponent used by
`integerTau` is exact. -/
theorem integerExponent_toNat_cast (k : Nat) (n : PosNat) :
    ((S.integerExponent k n).toNat : Int) = S.integerExponent k n :=
  Int.toNat_of_nonneg (le_of_lt (S.integerExponent_pos k n))

/-- In particular the natural exponent in the recursion is nonzero. -/
theorem integerExponent_toNat_pos (k : Nat) (n : PosNat) :
    0 < (S.integerExponent k n).toNat := by
  have h : (0 : Int) < ((S.integerExponent k n).toNat : Int) := by
    rw [S.integerExponent_toNat_cast]
    exact S.integerExponent_pos k n
  exact_mod_cast h

/-- The common integer-valued coordinate family: coordinate zero is the
original input and coordinate `k+1` is the `k`th recursively evaluated
auxiliary function. -/
def integerCoordinates : Nat → PosNat → Int
  | 0, n => n.1
  | k + 1, n => S.integerTau k n

@[simp]
theorem integerCoordinates_zero (n : PosNat) :
    S.integerCoordinates 0 n = (n.1 : Int) :=
  rfl

@[simp]
theorem integerCoordinates_succ (k : Nat) (n : PosNat) :
    S.integerCoordinates (k + 1) n = S.integerTau k n :=
  rfl

/-- The assignment at stage `k` is precisely the restriction of the common
coordinate family to indices below `k+1`.  This makes explicit that the
recursion uses no future auxiliary coordinate. -/
theorem integerAssignment_eq_coordinates (k : Nat) (n : PosNat)
    (i : StageVar k) :
    S.integerAssignment k n i = S.integerCoordinates i.1 n := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Every member of the common coordinate family is positive on positive
natural inputs. -/
theorem integerCoordinates_pos (i : Nat) (n : PosNat) :
    0 < S.integerCoordinates i n := by
  cases i with
  | zero =>
      change (0 : Int) < (n.1 : Int)
      exact_mod_cast n.2
  | succ k =>
      exact S.integerTau_pos k n

end GeneratorSequence

/-! ## Compatibility with the real W3 recursion -/

/-- A positive natural input regarded as a positive real input. -/
def integerRealInput (n : PosNat) : PositiveReal :=
  ⟨(n.1 : Real), by exact_mod_cast n.2⟩

@[simp]
theorem integerRealInput_val (n : PosNat) :
    (integerRealInput n).1 = (n.1 : Real) :=
  rfl

namespace GeneratorRealization

variable {D : PolynomialDerivability} {S : GeneratorSequence D}
variable (R : GeneratorRealization S)

/-- The real W3 recursion agrees, at every positive integer input, with the
discrete integer recursion.  The strong induction is legitimate because the
stage-`k` polynomials can mention only auxiliary coordinates indexed below
`k`.
-/
theorem tau_integer_compat (k : Nat) (n : PosNat) :
    R.tau k (integerRealInput n) = (S.integerTau k n : Real) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hassignment (stage : Nat) (hstage : stage ≤ k) :
          recursiveAssignment R.tau stage (integerRealInput n) =
            fun i ↦ (S.integerAssignment stage n i : Real) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          exact ih j.1 (j.2.trans_le hstage)
      have hbase :
          (S.pair k).base.polynomial.evalReal
              (recursiveAssignment R.tau (S.pair k).baseStage
                (integerRealInput n)) =
            (S.integerBase k n : Real) := by
        rw [hassignment (S.pair k).baseStage (S.pair k).baseStage_le]
        exact (StagePolynomial.cast_evalInt
          (S.pair k).base.polynomial
          (S.integerAssignment (S.pair k).baseStage n)).symm
      have hexponent :
          (S.pair k).exponent.polynomial.evalReal
              (recursiveAssignment R.tau (S.pair k).exponentStage
                (integerRealInput n)) =
            (S.integerExponent k n : Real) := by
        rw [hassignment (S.pair k).exponentStage
          (S.pair k).exponentStage_le]
        exact (StagePolynomial.cast_evalInt
          (S.pair k).exponent.polynomial
          (S.integerAssignment (S.pair k).exponentStage n)).symm
      have hexponentCast :
          (S.integerExponent k n : Real) =
            ((S.integerExponent k n).toNat : Real) := by
        exact_mod_cast (S.integerExponent_toNat_cast k n).symm
      rw [R.w3, hbase, hexponent]
      calc
        Real.rpow (S.integerBase k n : Real)
              (S.integerExponent k n : Real) =
            Real.rpow (S.integerBase k n : Real)
              ((S.integerExponent k n).toNat : Real) :=
          congrArg (Real.rpow (S.integerBase k n : Real)) hexponentCast
        _ = (S.integerBase k n : Real) ^
              (S.integerExponent k n).toNat :=
          Real.rpow_natCast _ _
        _ = ((S.integerBase k n ^
              (S.integerExponent k n).toNat : Int) : Real) := by
          exact_mod_cast rfl
        _ = (S.integerTau k n : Real) := by
          exact_mod_cast (S.integerTau_eq k n).symm

/-- At an integer input, the real recursive stage assignment is the real cast
of the discrete integer stage assignment. -/
theorem recursiveAssignment_integer_compat (k : Nat) (n : PosNat) :
    recursiveAssignment R.tau k (integerRealInput n) =
      fun i ↦ (S.integerAssignment k n i : Real) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact R.tau_integer_compat j.1 n

/-- At an integer input, evaluation of the real W3 base is the real cast of
the recursively evaluated integer base. -/
theorem base_integer_compat (k : Nat) (n : PosNat) :
    (S.pair k).base.polynomial.evalReal
        (recursiveAssignment R.tau (S.pair k).baseStage
          (integerRealInput n)) =
      (S.integerBase k n : Real) := by
  rw [R.recursiveAssignment_integer_compat]
  exact (StagePolynomial.cast_evalInt
    (S.pair k).base.polynomial
    (S.integerAssignment (S.pair k).baseStage n)).symm

/-- At an integer input, evaluation of the real W3 exponent is the real cast
of the recursively evaluated integer exponent. -/
theorem exponent_integer_compat (k : Nat) (n : PosNat) :
    (S.pair k).exponent.polynomial.evalReal
        (recursiveAssignment R.tau (S.pair k).exponentStage
          (integerRealInput n)) =
      (S.integerExponent k n : Real) := by
  rw [R.recursiveAssignment_integer_compat]
  exact (StagePolynomial.cast_evalInt
    (S.pair k).exponent.polynomial
    (S.integerAssignment (S.pair k).exponentStage n)).symm

end GeneratorRealization

end

end Natfunbasis.Wilkie
