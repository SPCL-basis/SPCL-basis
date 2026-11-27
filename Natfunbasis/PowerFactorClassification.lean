import Natfunbasis.NormalizerCore
import Natfunbasis.WilkieGenerators

/-!
# Classification of the irreducible factors in the power branch

This file supplies the finite-stage classification immediately following the
factorization step in AJK Lemma 2.6.  A positive irreducible integer
polynomial in the variables available at stage `k` is exactly one of:

* the original variable `Y`;
* an earlier auxiliary variable `X_j`; or
* a nonvariable admissible irreducible of W1.1.

The auxiliary-variable case is deliberately retained.  It is not covered by
W2; in the normalizer it is handled by the flattening identity
`(a^b)^c = a^(bc)`.  The other two cases are connected below to the joint W2
coverage theorem.

No generator-existence or algebraic-independence assumption is used here.
-/

namespace Natfunbasis

open MvPolynomial

namespace Wilkie

noncomputable section

/-! ## The finite-stage trichotomy -/

/-- The three mutually exhaustive kinds of signed positive irreducible
factors occurring in a finite-stage base polynomial. -/
inductive PositiveIrreducibleFactor {k : Nat} (q : StagePolynomial k) : Prop
  | original (hq : q = X 0)
  | auxiliary (j : Fin k) (hq : q = X j.succ)
  | admissible (hq : IsAdmissibleIrreducible q)

/-- Irreducibility excludes the unit polynomial `1`. -/
theorem ne_one_of_irreducible {k : Nat} {q : StagePolynomial k}
    (hq : Irreducible q) : q ≠ 1 := by
  intro hOne
  apply hq.not_isUnit
  rw [hOne]
  exact isUnit_one

/-- The positivity predicate used by the factorization module is definitionally
the W1 positivity predicate when the variable type is a finite stage. -/
theorem positiveOnOrthant_of_positiveOnRealOrthant {k : Nat}
    {q : StagePolynomial k}
    (hq : NormalizerCore.PositiveOnRealOrthant q) :
    PositiveOnOrthant q := by
  intro assignment hassignment
  exact hq assignment hassignment

/-- A positive irreducible factor is either the original variable, an earlier
auxiliary variable, or an admissible nonvariable W1.1 base. -/
theorem classify_positive_irreducible {k : Nat} {q : StagePolynomial k}
    (hirreducible : Irreducible q)
    (hpositive : NormalizerCore.PositiveOnRealOrthant q) :
    PositiveIrreducibleFactor q := by
  classical
  by_cases hvariable : ∃ i : StageVar k, q = X i
  · obtain ⟨i, hi⟩ := hvariable
    cases i using Fin.cases with
    | zero => exact PositiveIrreducibleFactor.original hi
    | succ j => exact PositiveIrreducibleFactor.auxiliary j hi
  · apply PositiveIrreducibleFactor.admissible
    refine
      { positive := positiveOnOrthant_of_positiveOnRealOrthant hpositive
        irreducible := hirreducible
        ne_one := ne_one_of_irreducible hirreducible
        ne_variable := ?_ }
    intro i hi
    exact hvariable ⟨i, hi⟩

/-- Forgetting the W1 packaging recovers irreducibility of every classified
factor.  In the two variable cases this uses primality of multivariate
indeterminates over `Int`. -/
theorem PositiveIrreducibleFactor.irreducible {k : Nat}
    {q : StagePolynomial k} (hq : PositiveIrreducibleFactor q) :
    Irreducible q := by
  cases hq with
  | original h =>
      rw [h]
      exact MvPolynomial.X_prime.irreducible
  | auxiliary j h =>
      rw [h]
      exact MvPolynomial.X_prime.irreducible
  | admissible h => exact h.irreducible

/-- Every classified factor is positive throughout the positive real
orthant. -/
theorem PositiveIrreducibleFactor.positive {k : Nat}
    {q : StagePolynomial k} (hq : PositiveIrreducibleFactor q) :
    PositiveOnOrthant q := by
  cases hq with
  | original h =>
      rw [h]
      intro assignment hassignment
      simpa [StagePolynomial.evalReal] using hassignment (0 : StageVar k)
  | auxiliary j h =>
      rw [h]
      intro assignment hassignment
      simpa [StagePolynomial.evalReal] using hassignment j.succ
  | admissible h => exact h.positive

/-! ## Classification of the complete signed factorization -/

/-- A finite-stage natural polynomial different from `0` and `1` has an exact
nonempty factorization in which every factor carries the preceding
original/auxiliary/admissible classification. -/
theorem exists_classified_positive_irreducible_factorization {k : Nat}
    (p : MvPolynomial (StageVar k) Nat) (hpZero : p ≠ 0) (hpOne : p ≠ 1) :
    ∃ factors : Multiset (StagePolynomial k),
      factors ≠ 0 ∧
      factors.prod = MvPolynomial.map (Nat.castRingHom Int) p ∧
      ∀ q ∈ factors, PositiveIrreducibleFactor q := by
  classical
  obtain ⟨rawFactors, sign, hnonempty, -, hproduct, hfactor⟩ :=
    NormalizerCore.exists_exact_positive_irreducible_factorization
      p hpZero hpOne
  let factors : Multiset (StagePolynomial k) :=
    rawFactors.map fun q ↦ C (sign q) * q
  refine ⟨factors, ?_, ?_, ?_⟩
  · simpa [factors] using hnonempty
  · simpa [factors] using hproduct
  · intro q hq
    obtain ⟨raw, hraw, rfl⟩ := Multiset.mem_map.mp (by simpa [factors] using hq)
    exact classify_positive_irreducible (hfactor raw hraw).1 (hfactor raw hraw).2

/-! ## The two W2-eligible cases -/

/-- Apart from an auxiliary-variable factor (which must be flattened), every
classified factor is jointly covered with any prescribed nonconstant
monomial exponent by W2. -/
theorem PositiveIrreducibleFactor.auxiliary_or_existsUnique_w2
    {D : PolynomialDerivability} (S : GeneratorSequence D)
    {k exponentStage : Nat} {q : StagePolynomial k}
    (hq : PositiveIrreducibleFactor q)
    (m : NonconstantMonomial exponentStage) :
    (∃ j : Fin k, q = X j.succ) ∨
      ∃! index : Nat,
        D.derives (S.pair index).base.toGlobal q.toGlobal ∧
        D.derives (S.pair index).exponent.toGlobal m.toGlobal := by
  cases hq with
  | original hq =>
      right
      rw [hq]
      simpa [StagePolynomial.toGlobal, originalPolynomial] using
        S.existsUnique_original exponentStage m
  | auxiliary j hq =>
      exact Or.inl ⟨j, hq⟩
  | admissible hq =>
      right
      exact S.existsUnique_irreducible k exponentStage q hq m

/-- A nonvariable classified factor is always W2-covered.  This form is
convenient after the normalizer has discharged the auxiliary-variable cases. -/
theorem PositiveIrreducibleFactor.existsUnique_w2_of_ne_variable
    {D : PolynomialDerivability} (S : GeneratorSequence D)
    {k exponentStage : Nat} {q : StagePolynomial k}
    (hq : PositiveIrreducibleFactor q)
    (hne : ∀ i : StageVar k, q ≠ X i)
    (m : NonconstantMonomial exponentStage) :
    ∃! index : Nat,
      D.derives (S.pair index).base.toGlobal q.toGlobal ∧
      D.derives (S.pair index).exponent.toGlobal m.toGlobal := by
  rcases hq.auxiliary_or_existsUnique_w2 S m with haux | hw2
  · obtain ⟨j, hj⟩ := haux
    exact (hne j.succ hj).elim
  · exact hw2

end

end Wilkie

end Natfunbasis
