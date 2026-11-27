import Natfunbasis.Expressions

/-!
# The one-variable Wilkie generator conditions

This file transcribes the paired generator conditions (W1.1)--(W3.2) used in
Alsulami--Jackson--Kinyon, Section 2, in the one-original-variable case, and
constructs the real W3 recursion for any W1--W2 sequence.  The companion
module `WilkieGeneratorExistence` constructs an actual sequence.  Neither
module proves Wilkie's algebraic independence theorem.

Indices in the paper are one-based.  Here `pair k` represents
`(p_(k+1), q_(k+1))`.  A polynomial at stage `k` has variables

* `0`, representing the original variable `Y`; and
* `j.succ`, representing the earlier auxiliary variable `X_(j+1)`, for
  `j : Fin k`.

Consequently, future auxiliary variables cannot occur in `pair k` by type.
The two members of a pair are enumerated together: both coverage clauses
return one common index.  This is essential in the power-normalization
argument and is stronger than two unrelated surjectivity assertions.

AJK states W2.1 with two positive arities.  Wilkie's original condition also
allows arity zero; the formulation below allows every `Nat`.  Dummy variables
turn either presentation into the other, but that transport is not asserted
here.

The relation in `PolynomialDerivability` is an explicit parameter.  In the
source it is HSI-star derivability between the corresponding expanded
polynomial-operation terms.  Bundling it here does **not** construct that
proof system: any later theorem using a `GeneratorSystem D` still visibly
depends on the supplied `D` and system value.  For the narrower semantic
normal-form application, `equalityDerivability` below gives a concrete
relation: exact coefficient-level coverage is a harmless strengthening of
W2, without importing the separate HSI-star proof theory.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

/-! ## Polynomial presentations and their semantics -/

/-- One original variable followed by `k` earlier auxiliary variables. -/
abbrev StageVar (k : Nat) := Fin (k + 1)

/-- Integer-coefficient polynomials in the variables available at stage `k`. -/
abbrev StagePolynomial (k : Nat) := MvPolynomial (StageVar k) Int

/-- A common variable type in which presentations from different stages can
be compared. -/
inductive GlobalVar where
  | original : GlobalVar
  | auxiliary : Nat → GlobalVar
  deriving DecidableEq, Repr, Encodable

/-- An integer-coefficient polynomial in the original variable and all
auxiliary variables. -/
abbrev GlobalPolynomial := MvPolynomial GlobalVar Int

/-- Embed a stage variable into the common variable type. -/
def stageVarEmbedding (k : Nat) : StageVar k → GlobalVar :=
  Fin.cases .original (fun j ↦ .auxiliary j.1)

@[simp]
theorem stageVarEmbedding_zero (k : Nat) :
    stageVarEmbedding k 0 = .original :=
  rfl

@[simp]
theorem stageVarEmbedding_succ {k : Nat} (j : Fin k) :
    stageVarEmbedding k j.succ = .auxiliary j.1 :=
  rfl

/-- A stage polynomial regarded as a polynomial in the common variable type. -/
def StagePolynomial.toGlobal {k : Nat} (p : StagePolynomial k) :
    GlobalPolynomial :=
  MvPolynomial.rename (stageVarEmbedding k) p

/-- Evaluation of an integer-coefficient stage polynomial over the reals. -/
def StagePolynomial.evalReal {k : Nat} (p : StagePolynomial k)
    (assignment : StageVar k → Real) : Real :=
  MvPolynomial.eval₂ (Int.castRingHom Real) assignment p

/-- Positive on the entire strictly positive real orthant.  This is AJK's
notion `P_k` of a *positive* polynomial; it permits negative coefficients. -/
def PositiveOnOrthant {k : Nat} (p : StagePolynomial k) : Prop :=
  ∀ assignment : StageVar k → Real,
    (∀ i, 0 < assignment i) → 0 < p.evalReal assignment

/-- The irreducible bases allowed in W1.1: positive on the positive orthant,
irreducible over `Int`, and neither `1` nor a single variable.  Constant prime
bases (for example `2`) are intentionally allowed. -/
structure IsAdmissibleIrreducible {k : Nat} (p : StagePolynomial k) : Prop where
  positive : PositiveOnOrthant p
  irreducible : Irreducible p
  ne_one : p ≠ 1
  ne_variable : ∀ i : StageVar k, p ≠ X i

/-- A coefficient-one monomial other than `1`.  Storing its exponent vector
makes both the coefficient-one and nonconstant requirements structural. -/
structure NonconstantMonomial (k : Nat) where
  exponents : StageVar k →₀ Nat
  nonzero : exponents ≠ 0

namespace NonconstantMonomial

/-- The integer polynomial represented by a coefficient-one monomial. -/
def polynomial {k : Nat} (m : NonconstantMonomial k) : StagePolynomial k :=
  MvPolynomial.monomial m.exponents 1

/-- The common-variable presentation of a monomial. -/
def toGlobal {k : Nat} (m : NonconstantMonomial k) : GlobalPolynomial :=
  m.polynomial.toGlobal

/-- A coefficient-one monomial is positive at every positive real
assignment. -/
theorem evalReal_pos {k : Nat} (m : NonconstantMonomial k)
    (assignment : StageVar k → Real) (hassignment : ∀ i, 0 < assignment i) :
    0 < m.polynomial.evalReal assignment := by
  rw [polynomial, StagePolynomial.evalReal, MvPolynomial.eval₂_monomial]
  simp only [map_one, one_mul]
  apply Finset.prod_pos
  intro i hi
  exact pow_pos (hassignment i) _

end NonconstantMonomial

/-- A W1.1 base at stage `k`.  It is either the sole original variable, or an
admissible irreducible polynomial involving only `Y,X_1,...,X_k`.  Auxiliary
variables themselves are excluded by `IsAdmissibleIrreducible.ne_variable`. -/
inductive Base (k : Nat) where
  | original : Base k
  | irreducible (p : StagePolynomial k) (admissible : IsAdmissibleIrreducible p) :
      Base k

namespace Base

/-- The stage-polynomial presentation of a base. -/
def polynomial {k : Nat} : Base k → StagePolynomial k
  | .original => X 0
  | .irreducible p _ => p

/-- The common-variable presentation of a base. -/
def toGlobal {k : Nat} (b : Base k) : GlobalPolynomial :=
  b.polynomial.toGlobal

/-- Every encoded base is positive after a positive real assignment. -/
theorem positiveOnOrthant {k : Nat} (b : Base k) :
    PositiveOnOrthant b.polynomial := by
  cases b with
  | original =>
      intro assignment hassignment
      simpa [polynomial, StagePolynomial.evalReal] using hassignment (0 : StageVar k)
  | irreducible p hp =>
      exact hp.positive

end Base

/-- The global presentation of the original variable `Y`. -/
def originalPolynomial : GlobalPolynomial := X .original

@[simp]
theorem Base.original_toGlobal (k : Nat) :
    (Base.original : Base k).toGlobal = originalPolynomial := by
  simp [Base.toGlobal, Base.polynomial, StagePolynomial.toGlobal,
    originalPolynomial]

/-- Assign strictly positive natural values to all common variables. -/
abbrev PositiveNatAssignment := GlobalVar → PosNat

/-- Evaluate a common integer polynomial at a positive-natural assignment,
with the result kept in `Int` because admissible bases may have negative
coefficients. -/
def GlobalPolynomial.evalNat (p : GlobalPolynomial)
    (assignment : PositiveNatAssignment) : Int :=
  MvPolynomial.eval (fun i ↦ ((assignment i).1 : Int)) p

/-- Semantic equality on all positive-natural assignments.  W1.3 uses this
notion, rather than mere inequality of the names chosen for two generators. -/
def PolynomialSemEq (p q : GlobalPolynomial) : Prop :=
  ∀ assignment : PositiveNatAssignment, p.evalNat assignment = q.evalNat assignment

namespace PolynomialSemEq

theorem refl (p : GlobalPolynomial) : PolynomialSemEq p p :=
  fun _ ↦ rfl

theorem symm {p q : GlobalPolynomial} (h : PolynomialSemEq p q) :
    PolynomialSemEq q p :=
  fun assignment ↦ (h assignment).symm

theorem trans {p q r : GlobalPolynomial} (hpq : PolynomialSemEq p q)
    (hqr : PolynomialSemEq q r) : PolynomialSemEq p r :=
  fun assignment ↦ (hpq assignment).trans (hqr assignment)

/-- Positive-natural evaluation detects an integer polynomial.  This is a
pure polynomial identity theorem, not Wilkie's much deeper independence
result: `MvPolynomial.funext_set` applies because the positive integers form
an infinite subset of `Int` in every coordinate. -/
theorem eq {p q : GlobalPolynomial} (h : PolynomialSemEq p q) : p = q := by
  let positiveInts : Set Int := {z | 0 < z}
  have hpositiveInts : positiveInts.Infinite := by
    let successorCast : Nat → Int := fun n ↦ (n + 1 : Nat)
    have hinjective : Function.Injective successorCast := by
      intro m n hmn
      exact Nat.succ.inj (Int.ofNat_injective hmn)
    apply (Set.infinite_range_of_injective hinjective).mono
    rintro z ⟨n, rfl⟩
    simp [positiveInts, successorCast]
  apply MvPolynomial.funext_set (fun _ ↦ positiveInts) (fun _ ↦ hpositiveInts)
  intro assignment hassignment
  have hpos : ∀ i, 0 < assignment i := by
    intro i
    exact hassignment i (Set.mem_univ i)
  let natAssignment : PositiveNatAssignment := fun i ↦
    ⟨(assignment i).toNat, by
      have hcast : (0 : Int) < ((assignment i).toNat : Int) := by
        rw [Int.toNat_of_nonneg (le_of_lt (hpos i))]
        exact hpos i
      exact_mod_cast hcast⟩
  have heq := h natAssignment
  simpa only [GlobalPolynomial.evalNat, natAssignment,
    Int.toNat_of_nonneg (le_of_lt (hpos _))] using heq

end PolynomialSemEq

/-! ## W1 and W2: one fixed paired enumeration -/

/-- The fragment of HSI-star derivability needed to state W2.  `derives p q`
means that the expanded polynomial-operation presentations associated with
`p` and `q` are equationally interderivable.  Soundness is recorded because it
is exactly what connects W2 to the semantic no-duplicates condition W1.3.

This is interface data, not a postulated global instance. -/
structure PolynomialDerivability where
  derives : GlobalPolynomial → GlobalPolynomial → Prop
  refl : ∀ p, derives p p
  symm : ∀ {p q}, derives p q → derives q p
  trans : ∀ {p q r}, derives p q → derives q r → derives p r
  sound : ∀ {p q}, derives p q → PolynomialSemEq p q

/-- Literal polynomial equality as a concrete derivability relation.  A
`GeneratorSequence equalityDerivability` asks for exact joint coverage.  This
is stronger than the HSI-star-derivability formulation of W2 and is sufficient
for the semantic normal-form arguments, but it does not claim to formalize
HSI-star itself. -/
def equalityDerivability : PolynomialDerivability where
  derives := Eq
  refl := fun _ ↦ rfl
  symm := Eq.symm
  trans := Eq.trans
  sound := by
    intro p q hpq
    subst q
    exact PolynomialSemEq.refl p

@[simp]
theorem equalityDerivability_derives_iff {p q : GlobalPolynomial} :
    equalityDerivability.derives p q ↔ p = q :=
  Iff.rfl

/-- One paired entry `(p_(k+1),q_(k+1))` in position `k`.

The source permits the base and exponent presentations to use independently
bounded numbers `k'` and `k''` of auxiliary variables.  Keeping those stages
as data avoids artificial dummy-variable transports.  The two inequalities
are exactly the W1 requirement that no future auxiliary variable occurs. -/
structure GeneratorEntry (k : Nat) where
  baseStage : Nat
  baseStage_le : baseStage ≤ k
  base : Base baseStage
  exponentStage : Nat
  exponentStage_le : exponentStage ≤ k
  exponent : NonconstantMonomial exponentStage

/-- Conditions W1.1--W2.2 for a single coherent, paired enumeration.

* W1.1 and W1.2 are enforced by the type of `pair`.
* `w1_noRepeatedPair` is W1.3, stated semantically on positive naturals.
* `w2_irreducible` is joint coverage of every admissible
  irreducible-base/monomial-exponent pair.
* `w2_original` is joint coverage of every
  original-variable/monomial-exponent pair.
-/
structure GeneratorSequence (D : PolynomialDerivability) where
  pair : (k : Nat) → GeneratorEntry k
  w1_noRepeatedPair : ∀ {i j : Nat}, i ≠ j →
    ¬ (PolynomialSemEq (pair i).base.toGlobal (pair j).base.toGlobal ∧
       PolynomialSemEq (pair i).exponent.toGlobal (pair j).exponent.toGlobal)
  w2_irreducible : ∀ (baseStage exponentStage : Nat)
    (p : StagePolynomial baseStage), IsAdmissibleIrreducible p →
    ∀ m : NonconstantMonomial exponentStage,
      ∃ index : Nat,
        D.derives (pair index).base.toGlobal p.toGlobal ∧
        D.derives (pair index).exponent.toGlobal m.toGlobal
  w2_original : ∀ (exponentStage : Nat) (m : NonconstantMonomial exponentStage),
    ∃ index : Nat,
      D.derives (pair index).base.toGlobal originalPolynomial ∧
      D.derives (pair index).exponent.toGlobal m.toGlobal

namespace GeneratorSequence

/-- W1.3 makes an index jointly realizing a prescribed base and exponent
unique.  This lemma is also a guard against accidentally treating W2 as two
unrelated enumerations. -/
theorem index_unique_of_joint_derivation {D : PolynomialDerivability}
    (S : GeneratorSequence D) {i j : Nat} {p q : GlobalPolynomial}
    (hip : D.derives (S.pair i).base.toGlobal p)
    (hiq : D.derives (S.pair i).exponent.toGlobal q)
    (hjp : D.derives (S.pair j).base.toGlobal p)
    (hjq : D.derives (S.pair j).exponent.toGlobal q) :
    i = j := by
  by_contra hij
  apply S.w1_noRepeatedPair hij
  constructor
  · exact PolynomialSemEq.trans (D.sound hip) (PolynomialSemEq.symm (D.sound hjp))
  · exact PolynomialSemEq.trans (D.sound hiq) (PolynomialSemEq.symm (D.sound hjq))

/-- The joint W2.1 witness is unique. -/
theorem existsUnique_irreducible {D : PolynomialDerivability}
    (S : GeneratorSequence D) (baseStage exponentStage : Nat)
    (p : StagePolynomial baseStage) (hp : IsAdmissibleIrreducible p)
    (m : NonconstantMonomial exponentStage) :
    ∃! index : Nat,
      D.derives (S.pair index).base.toGlobal p.toGlobal ∧
      D.derives (S.pair index).exponent.toGlobal m.toGlobal := by
  obtain ⟨index, hbase, hexponent⟩ :=
    S.w2_irreducible baseStage exponentStage p hp m
  refine ⟨index, ⟨hbase, hexponent⟩, ?_⟩
  intro other hother
  exact S.index_unique_of_joint_derivation hother.1 hother.2 hbase hexponent

/-- The joint W2.2 witness is unique. -/
theorem existsUnique_original {D : PolynomialDerivability}
    (S : GeneratorSequence D) (exponentStage : Nat)
    (m : NonconstantMonomial exponentStage) :
    ∃! index : Nat,
      D.derives (S.pair index).base.toGlobal originalPolynomial ∧
      D.derives (S.pair index).exponent.toGlobal m.toGlobal := by
  obtain ⟨index, hbase, hexponent⟩ := S.w2_original exponentStage m
  refine ⟨index, ⟨hbase, hexponent⟩, ?_⟩
  intro other hother
  exact S.index_unique_of_joint_derivation hother.1 hother.2 hbase hexponent

end GeneratorSequence

/-! ## W3: recursive substitution of the earlier generators -/

/-- A strictly positive real input for the sole original variable. -/
abbrev PositiveReal := {x : Real // 0 < x}

/-- The assignment used at stage `k`: `Y` receives `y`, while `X_(j+1)`
receives the already constructed `tau_(j+1)(y)`. -/
def recursiveAssignment (tau : Nat → PositiveReal → Real) (k : Nat)
    (y : PositiveReal) : StageVar k → Real :=
  Fin.cases y.1 (fun j ↦ tau j.1 y)

@[simp]
theorem recursiveAssignment_original (tau : Nat → PositiveReal → Real)
    (k : Nat) (y : PositiveReal) :
    recursiveAssignment tau k y 0 = y.1 :=
  rfl

@[simp]
theorem recursiveAssignment_auxiliary (tau : Nat → PositiveReal → Real)
    {k : Nat} (y : PositiveReal) (j : Fin k) :
    recursiveAssignment tau k y j.succ = tau j.1 y :=
  rfl

/-- A semantic realization of W3.1--W3.2.  One equation covers both clauses:
at stage zero no auxiliary value is available (W3.1), and at stage `k+1`
only `tau 0,...,tau k` can be substituted (W3.2).  Real exponentiation is
used because this is the realization relevant to Wilkie's independence
theorem on the positive real orthant. -/
structure GeneratorRealization {D : PolynomialDerivability}
    (S : GeneratorSequence D) where
  tau : Nat → PositiveReal → Real
  w3 : ∀ (k : Nat) (y : PositiveReal),
    tau k y = Real.rpow
      ((S.pair k).base.polynomial.evalReal
        (recursiveAssignment tau (S.pair k).baseStage y))
      ((S.pair k).exponent.polynomial.evalReal
        (recursiveAssignment tau (S.pair k).exponentStage y))

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The canonical real auxiliary functions recursively determined by a
triangular generator sequence.  Termination uses the two W1 bounds stored in
the entry at `k`: every auxiliary coordinate read by either polynomial has
index strictly below `k`. -/
def realTau (k : Nat) (y : PositiveReal) : Real :=
  let baseAssignment : StageVar (S.pair k).baseStage → Real :=
    Fin.cases y.1 (fun j ↦ realTau j.1 y)
  let exponentAssignment : StageVar (S.pair k).exponentStage → Real :=
    Fin.cases y.1 (fun j ↦ realTau j.1 y)
  Real.rpow
    ((S.pair k).base.polynomial.evalReal baseAssignment)
    ((S.pair k).exponent.polynomial.evalReal exponentAssignment)
termination_by k
decreasing_by
  · exact j.2.trans_le (S.pair k).baseStage_le
  · exact j.2.trans_le (S.pair k).exponentStage_le

/-- The defining equation for the canonical real recursion. -/
theorem realTau_eq (k : Nat) (y : PositiveReal) :
    S.realTau k y = Real.rpow
      ((S.pair k).base.polynomial.evalReal
        (recursiveAssignment S.realTau (S.pair k).baseStage y))
      ((S.pair k).exponent.polynomial.evalReal
        (recursiveAssignment S.realTau (S.pair k).exponentStage y)) := by
  rw [realTau]
  rfl

/-- Every triangular sequence has a canonical W3 realization; realization
existence is therefore not an additional mathematical hypothesis. -/
def canonicalRealization : GeneratorRealization S where
  tau := S.realTau
  w3 := S.realTau_eq

end GeneratorSequence

namespace GeneratorRealization

/-- Every recursively realized auxiliary function is positive. -/
theorem tau_pos {D : PolynomialDerivability} {S : GeneratorSequence D}
    (R : GeneratorRealization S) (k : Nat) (y : PositiveReal) :
    0 < R.tau k y := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [R.w3]
      apply Real.rpow_pos_of_pos
      apply (S.pair k).base.positiveOnOrthant
      intro i
      refine Fin.cases y.2 ?_ i
      intro j
      exact ih j.1 (j.2.trans_le (S.pair k).baseStage_le)

end GeneratorRealization

/-- The complete one-variable W1--W3 package.  The companion existence module
constructs an inhabitant; proving its `tau` family algebraically independent
is a separate mathematical obligation. -/
structure GeneratorSystem (D : PolynomialDerivability) where
  sequence : GeneratorSequence D
  realization : GeneratorRealization sequence

end

end Natfunbasis.Wilkie
