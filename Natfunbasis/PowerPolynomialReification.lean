import Natfunbasis.MonomialSums
import Natfunbasis.PowerBranchEvaluation
import Natfunbasis.WilkieIntegerEvaluation
import Mathlib.Data.Finsupp.Multiset

/-!
# Reification of arbitrary power-branch polynomials

This module converts an arbitrary natural-coefficient exponent polynomial
into its constant part and a finite list of coefficient-one nonconstant
monomials.  Multiplicity in the list is exactly the original coefficient.
It also converts the classified factor multiset from the UFD step into the
list format used by the finite W2/W3 grid identity.

The final theorem combines those two reifications with
`exists_powerBranch_grid_identity`.  It is a semantic theorem for arbitrary
nonzero, nonunit base polynomials and arbitrary exponent polynomials.  It
does not yet reify the construction as an expression-level HSI-star
derivation.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

/-! ## Constant plus nonconstant-monomial decomposition -/

/-- Natural-coefficient polynomials in the variables available at stage `k`. -/
abbrev StageNatPolynomial (k : Nat) := MvPolynomial (StageVar k) Nat

namespace StageNatPolynomial

/-- The multiset of exponent vectors of a natural polynomial, with each
vector repeated according to its coefficient and the zero vector removed. -/
def nonconstantExponentMultiset {k : Nat}
    (p : StageNatPolynomial k) : Multiset (StageVar k →₀ Nat) :=
  (Finsupp.toMultiset
    (AddMonoidAlgebra.coeff p)).filter
      fun exponents ↦ exponents ≠ 0

/-- A chosen list presentation of `nonconstantExponentMultiset`. -/
def nonconstantExponents {k : Nat}
    (p : StageNatPolynomial k) : List (StageVar k →₀ Nat) :=
  p.nonconstantExponentMultiset.toList

@[simp]
theorem coe_nonconstantExponents {k : Nat}
    (p : StageNatPolynomial k) :
    (p.nonconstantExponents : Multiset (StageVar k →₀ Nat)) =
      p.nonconstantExponentMultiset := by
  exact Multiset.coe_toList _

/-- Every exponent vector retained in the decomposition is nonconstant. -/
theorem ne_zero_of_mem_nonconstantExponents {k : Nat}
    {p : StageNatPolynomial k} {exponents : StageVar k →₀ Nat}
    (h : exponents ∈ p.nonconstantExponents) : exponents ≠ 0 := by
  have hmultiset : exponents ∈ p.nonconstantExponentMultiset := by
    rw [← p.coe_nonconstantExponents]
    exact h
  exact (Multiset.mem_filter.mp hmultiset).2

/-- Bundle the exponent-vector list as the nonconstant monomials used by W2. -/
def nonconstantMonomials {k : Nat}
    (p : StageNatPolynomial k) : List (NonconstantMonomial k) :=
  p.nonconstantExponents.attach.map fun exponents ↦
    { exponents := exponents.1
      nonzero := ne_zero_of_mem_nonconstantExponents exponents.2 }

/-- Forgetting the bundled nonzeroness proofs recovers the original exponent
list exactly. -/
@[simp]
theorem map_exponents_nonconstantMonomials {k : Nat}
    (p : StageNatPolynomial k) :
    p.nonconstantMonomials.map NonconstantMonomial.exponents =
      p.nonconstantExponents := by
  simp [nonconstantMonomials]

/-- The coefficient of a nonzero exponent vector is its multiplicity in the
chosen nonconstant list. -/
theorem count_nonconstantExponents {k : Nat}
    (p : StageNatPolynomial k) (exponents : StageVar k →₀ Nat)
    (h : exponents ≠ 0) :
    Multiset.count exponents
        (p.nonconstantExponents : Multiset (StageVar k →₀ Nat)) =
      coeff exponents p := by
  rw [p.coe_nonconstantExponents]
  simp [nonconstantExponentMultiset, h, Finsupp.count_toMultiset,
    MvPolynomial.coeff]

/-- Exact polynomial reification: the zero exponent vector contributes the
constant coefficient, and every other coefficient is represented by list
multiplicity of a coefficient-one monomial. -/
theorem eq_C_constantCoeff_add_monomialSum {k : Nat}
    (p : StageNatPolynomial k) :
    p = C (constantCoeff p) +
      NormalPolynomial.monomialSum p.nonconstantExponents := by
  classical
  ext exponents
  by_cases hzero : exponents = 0
  · subst exponents
    rw [coeff_add, coeff_zero_C,
      NormalPolynomial.coeff_monomialSum]
    have hcount : Multiset.count 0
        (p.nonconstantExponents : Multiset (StageVar k →₀ Nat)) = 0 := by
      rw [p.coe_nonconstantExponents, nonconstantExponentMultiset,
        Multiset.count_filter_of_neg]
      exact not_ne_iff.mpr rfl
    rw [hcount, add_zero]
    rfl
  · rw [coeff_add, coeff_C_of_ne_zero hzero,
      zero_add, NormalPolynomial.coeff_monomialSum]
    exact (p.count_nonconstantExponents exponents hzero).symm

/-- For a nonzero polynomial, either the constant coefficient is nonzero or
the nonconstant monomial list is nonempty. -/
theorem constantCoeff_ne_zero_or_nonconstantExponents_ne_nil {k : Nat}
    {p : StageNatPolynomial k} (hp : p ≠ 0) :
    constantCoeff p ≠ 0 ∨ p.nonconstantExponents ≠ [] := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hp
  rw [p.eq_C_constantCoeff_add_monomialSum, h.1, h.2]
  simp [NormalPolynomial.monomialSum]

/-- The bundled W2 monomial list is empty exactly when the underlying
exponent-vector list is empty. -/
theorem nonconstantMonomials_eq_nil_iff {k : Nat}
    (p : StageNatPolynomial k) :
    p.nonconstantMonomials = [] ↔ p.nonconstantExponents = [] := by
  constructor
  · intro h
    rw [← p.map_exponents_nonconstantMonomials, h]
    rfl
  · intro h
    have hmap :
        p.nonconstantMonomials.map NonconstantMonomial.exponents = [] := by
      rw [p.map_exponents_nonconstantMonomials, h]
    simpa only [List.map_eq_nil_iff] using hmap

/-- Nonzeroness is visible directly in the W2-ready decomposition. -/
theorem constantCoeff_ne_zero_or_nonconstantMonomials_ne_nil {k : Nat}
    {p : StageNatPolynomial k} (hp : p ≠ 0) :
    constantCoeff p ≠ 0 ∨ p.nonconstantMonomials ≠ [] := by
  rcases constantCoeff_ne_zero_or_nonconstantExponents_ne_nil hp with
    hconstant | hmonomials
  · exact Or.inl hconstant
  · exact Or.inr (mt (p.nonconstantMonomials_eq_nil_iff.mp) hmonomials)

/-! ## Exact evaluation identities -/

/-- Evaluate a natural-coefficient stage polynomial over `Int`. -/
def evalInt {k : Nat} (p : StageNatPolynomial k)
    (assignment : StageVar k → Int) : Int :=
  MvPolynomial.eval₂ (Nat.castRingHom Int) assignment p

/-- Evaluate a natural-coefficient stage polynomial over `Real`. -/
def evalReal {k : Nat} (p : StageNatPolynomial k)
    (assignment : StageVar k → Real) : Real :=
  MvPolynomial.eval₂ (Nat.castRingHom Real) assignment p

/-- Evaluation commutes with the explicit list sum defining
`NormalPolynomial.monomialSum`. -/
theorem eval₂_monomialSum {k : Nat} {S : Type*} [CommSemiring S]
    (coefficientMap : Nat →+* S) (assignment : StageVar k → S)
    (exponents : List (StageVar k →₀ Nat)) :
    MvPolynomial.eval₂ coefficientMap assignment
        (NormalPolynomial.monomialSum exponents) =
      (exponents.map fun powers ↦
        MvPolynomial.eval₂ coefficientMap assignment
          (monomial powers 1)).sum := by
  induction exponents with
  | nil => simp [NormalPolynomial.monomialSum]
  | cons powers exponents ih =>
      change MvPolynomial.eval₂ coefficientMap assignment
          (monomial powers 1 + NormalPolynomial.monomialSum exponents) = _
      rw [MvPolynomial.eval₂_add, ih]
      rfl

/-- Integer evaluation is the constant coefficient plus the evaluations of
the reified nonconstant coefficient-one monomials. -/
theorem evalInt_eq_constant_add_monomials {k : Nat}
    (p : StageNatPolynomial k) (assignment : StageVar k → Int) :
    p.evalInt assignment = ((constantCoeff p : Nat) : Int) +
      (p.nonconstantMonomials.map fun m ↦
        StagePolynomial.evalInt m.polynomial assignment).sum := by
  calc
    p.evalInt assignment =
        evalInt (C (constantCoeff p) +
          NormalPolynomial.monomialSum p.nonconstantExponents) assignment :=
      congrArg (fun polynomial : StageNatPolynomial k ↦
        evalInt polynomial assignment)
        p.eq_C_constantCoeff_add_monomialSum
    _ = ((constantCoeff p : Nat) : Int) +
        (p.nonconstantExponents.map fun exponents ↦
          MvPolynomial.eval₂ (Nat.castRingHom Int) assignment
            (monomial exponents 1)).sum := by
      rw [evalInt, MvPolynomial.eval₂_add, MvPolynomial.eval₂_C,
        eval₂_monomialSum]
      simp
    _ = ((constantCoeff p : Nat) : Int) +
        (p.nonconstantMonomials.map fun m ↦
          StagePolynomial.evalInt m.polynomial assignment).sum := by
      rw [← p.map_exponents_nonconstantMonomials, List.map_map]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro m hm
      symm
      simpa [NonconstantMonomial.polynomial, StagePolynomial.evalInt] using
        (MvPolynomial.eval_monomial
          (f := assignment) (s := m.exponents) (a := (1 : Int)))

/-- Real evaluation is the constant coefficient plus the evaluations of the
reified nonconstant coefficient-one monomials. -/
theorem evalReal_eq_constant_add_monomials {k : Nat}
    (p : StageNatPolynomial k) (assignment : StageVar k → Real) :
    p.evalReal assignment = ((constantCoeff p : Nat) : Real) +
      (p.nonconstantMonomials.map fun m ↦
        StagePolynomial.evalReal m.polynomial assignment).sum := by
  calc
    p.evalReal assignment =
        evalReal (C (constantCoeff p) +
          NormalPolynomial.monomialSum p.nonconstantExponents) assignment :=
      congrArg (fun polynomial : StageNatPolynomial k ↦
        evalReal polynomial assignment)
        p.eq_C_constantCoeff_add_monomialSum
    _ = ((constantCoeff p : Nat) : Real) +
        (p.nonconstantExponents.map fun exponents ↦
          MvPolynomial.eval₂ (Nat.castRingHom Real) assignment
            (monomial exponents 1)).sum := by
      rw [evalReal, MvPolynomial.eval₂_add, MvPolynomial.eval₂_C,
        eval₂_monomialSum]
      simp
    _ = ((constantCoeff p : Nat) : Real) +
        (p.nonconstantMonomials.map fun m ↦
          StagePolynomial.evalReal m.polynomial assignment).sum := by
      rw [← p.map_exponents_nonconstantMonomials, List.map_map]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro m hm
      simp [NonconstantMonomial.polynomial, StagePolynomial.evalReal,
        MvPolynomial.eval₂_monomial]

end StageNatPolynomial

/-! ## From the factor multiset to a classified list -/

/-- The exact positive irreducible factorization, converted to a nonempty
list of classified factors without changing its product. -/
theorem exists_classified_positive_irreducible_factor_list {k : Nat}
    (p : StageNatPolynomial k) (hpZero : p ≠ 0) (hpOne : p ≠ 1) :
    ∃ factors : List (ClassifiedFactor k),
      factors ≠ [] ∧
      (factors.map fun q ↦ q.1).prod =
        MvPolynomial.map (Nat.castRingHom Int) p := by
  classical
  obtain ⟨rawFactors, hnonempty, hproduct, hclassified⟩ :=
    exists_classified_positive_irreducible_factorization p hpZero hpOne
  let rawList : List (StagePolynomial k) := rawFactors.toList
  let factors : List (ClassifiedFactor k) :=
    rawList.attach.map fun q ↦
      ⟨q.1, hclassified q.1 (by
        apply Multiset.mem_toList.mp
        simpa [rawList] using q.2)⟩
  have hvalues : (factors.map fun q ↦ q.1) = rawList := by
    simp [factors, rawList]
  have hrawList : rawList ≠ [] := by
    intro hzero
    apply hnonempty
    apply Multiset.toList_eq_nil.mp
    simpa [rawList] using hzero
  refine ⟨factors, ?_, ?_⟩
  · intro hzero
    apply hrawList
    rw [← hvalues, hzero]
    rfl
  · rw [hvalues]
    exact (Multiset.prod_toList rawFactors).trans hproduct

/-- The polynomial product equality of a classified factor list remains an
exact equality after real evaluation. -/
theorem evalReal_factorList_eq {k : Nat} {p : StageNatPolynomial k}
    {factors : List (ClassifiedFactor k)}
    (hproduct : (factors.map fun q ↦ q.1).prod =
      MvPolynomial.map (Nat.castRingHom Int) p)
    (assignment : StageVar k → Real) :
    (factors.map fun q ↦ q.1.evalReal assignment).prod =
      p.evalReal assignment := by
  have hcast :
      (Int.castRingHom Real).comp (Nat.castRingHom Int) =
        Nat.castRingHom Real := by
    ext n
    simp
  calc
    (factors.map fun q ↦ q.1.evalReal assignment).prod =
        MvPolynomial.eval₂ (Int.castRingHom Real) assignment
          (factors.map fun q ↦ q.1).prod := by
      clear hproduct
      induction factors with
      | nil => simp [StagePolynomial.evalReal]
      | cons q factors ih =>
          change
            MvPolynomial.eval₂ (Int.castRingHom Real) assignment q.1 *
                (factors.map fun next ↦
                  MvPolynomial.eval₂ (Int.castRingHom Real) assignment
                    next.1).prod =
              MvPolynomial.eval₂ (Int.castRingHom Real) assignment
                (q.1 * (factors.map fun next ↦ next.1).prod)
          change
            (factors.map fun next ↦
                MvPolynomial.eval₂ (Int.castRingHom Real) assignment
                  next.1).prod =
              MvPolynomial.eval₂ (Int.castRingHom Real) assignment
                (factors.map fun next ↦ next.1).prod at ih
          rw [MvPolynomial.eval₂_mul, ih]
    _ = MvPolynomial.eval₂ (Int.castRingHom Real) assignment
          (MvPolynomial.map (Nat.castRingHom Int) p) := by
      rw [hproduct]
    _ = MvPolynomial.eval₂ (Nat.castRingHom Real) assignment p := by
      rw [MvPolynomial.eval₂_map, hcast]
    _ = p.evalReal assignment := rfl

/-! ## Arbitrary-polynomial semantic power branch -/

/-- The complete semantic power-branch identity for an arbitrary nonzero,
nonunit natural-coefficient base polynomial and an arbitrary nonzero
natural-coefficient exponent polynomial.

The constant exponent coefficient becomes an ordinary natural power.  Every
remaining coefficient is represented by multiplicity in
`exponent.nonconstantMonomials`, and every factor/monomial grid cell is one
fixed W3 generator coordinate. -/
theorem exists_arbitraryPolynomial_powerBranch_identity
    {D : PolynomialDerivability} (S : GeneratorSequence D)
    {baseStage exponentStage : Nat}
    (base : StageNatPolynomial baseStage)
    (exponent : StageNatPolynomial exponentStage)
    (hbaseZero : base ≠ 0) (hbaseOne : base ≠ 1)
    (hexponentZero : exponent ≠ 0) :
    ∃ (factors : List (ClassifiedFactor baseStage))
      (index : ClassifiedFactor baseStage →
        NonconstantMonomial exponentStage → Nat),
      factors ≠ [] ∧
      (factors.map fun q ↦ q.1).prod =
        MvPolynomial.map (Nat.castRingHom Int) base ∧
      (constantCoeff exponent ≠ 0 ∨
        exponent.nonconstantMonomials ≠ []) ∧
      (∀ q m (R : GeneratorRealization S) (y : PositiveReal),
        Real.rpow
            (q.1.evalReal (recursiveAssignment R.tau baseStage y))
            (m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
          R.tau (index q m) y) ∧
      ∀ (R : GeneratorRealization S) (y : PositiveReal),
        Real.rpow
            (base.evalReal (recursiveAssignment R.tau baseStage y))
            (exponent.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
          (base.evalReal
              (recursiveAssignment R.tau baseStage y)) ^
              constantCoeff exponent *
            (factors.map fun q ↦
              (exponent.nonconstantMonomials.map fun m ↦
                R.tau (index q m) y).prod).prod := by
  obtain ⟨factors, hfactorsNonempty, hfactorProduct⟩ :=
    exists_classified_positive_irreducible_factor_list
      base hbaseZero hbaseOne
  obtain ⟨index, hcell, hgrid⟩ :=
    exists_powerBranch_grid_identity S factors
      exponent.nonconstantMonomials
  refine ⟨factors, index, hfactorsNonempty, hfactorProduct,
    StageNatPolynomial.constantCoeff_ne_zero_or_nonconstantMonomials_ne_nil
      hexponentZero, hcell, ?_⟩
  intro R y
  have hbasePositive :
      0 < base.evalReal (recursiveAssignment R.tau baseStage y) := by
    apply NormalizerCore.evalNatReal_positive base hbaseZero
    exact R.recursiveAssignment_pos baseStage y
  have hbaseFactors :
      (factors.map fun q ↦
        q.1.evalReal (recursiveAssignment R.tau baseStage y)).prod =
        base.evalReal (recursiveAssignment R.tau baseStage y) :=
    evalReal_factorList_eq hfactorProduct _
  have hexponentEvaluation :=
    exponent.evalReal_eq_constant_add_monomials
      (recursiveAssignment R.tau exponentStage y)
  calc
    Real.rpow
        (base.evalReal (recursiveAssignment R.tau baseStage y))
        (exponent.evalReal
          (recursiveAssignment R.tau exponentStage y)) =
        Real.rpow
          (base.evalReal (recursiveAssignment R.tau baseStage y))
          (((constantCoeff exponent : Nat) : Real) +
            (exponent.nonconstantMonomials.map fun m ↦
              m.polynomial.evalReal
                (recursiveAssignment R.tau exponentStage y)).sum) := by
      rw [hexponentEvaluation]
    _ = Real.rpow
          (base.evalReal (recursiveAssignment R.tau baseStage y))
          ((constantCoeff exponent : Nat) : Real) *
        Real.rpow
          (base.evalReal (recursiveAssignment R.tau baseStage y))
          (exponent.nonconstantMonomials.map fun m ↦
            m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)).sum :=
      Real.rpow_add hbasePositive _ _
    _ = (base.evalReal
            (recursiveAssignment R.tau baseStage y)) ^
            constantCoeff exponent *
        Real.rpow
          (base.evalReal (recursiveAssignment R.tau baseStage y))
          (exponent.nonconstantMonomials.map fun m ↦
            m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)).sum := by
      congr 1
      exact Real.rpow_natCast _ _
    _ = (base.evalReal
            (recursiveAssignment R.tau baseStage y)) ^
            constantCoeff exponent *
        Real.rpow
          ((factors.map fun q ↦
            q.1.evalReal
              (recursiveAssignment R.tau baseStage y)).prod)
          (exponent.nonconstantMonomials.map fun m ↦
            m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)).sum := by
      rw [hbaseFactors]
    _ = (base.evalReal
            (recursiveAssignment R.tau baseStage y)) ^
            constantCoeff exponent *
        (factors.map fun q ↦
          (exponent.nonconstantMonomials.map fun m ↦
            R.tau (index q m) y).prod).prod := by
      rw [hgrid R y]

end


end Natfunbasis.Wilkie
