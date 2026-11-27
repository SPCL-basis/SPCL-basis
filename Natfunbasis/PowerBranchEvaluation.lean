import Natfunbasis.PowerFactorClassification

/-!
# Semantic assembly of the nonconstant power branch

This module continues the unconditional part of the AJK Lemma 2.6
normalizer.  It transports coefficient-one monomials to a common finite
stage, multiplies them, and uses W2 together with W3 to flatten an
auxiliary-variable factor.

The principal result of this file is a semantic identity: for every
classified positive irreducible factor `q` and every nonconstant monomial
`m`, one fixed generator index represents `q ^ m` in every real W3
realization.  If `q` is an auxiliary variable `X_j`, its defining W3 power is
flattened first and W2 is applied to the product of its inner exponent with
`m`.

This is still a bounded layer of the full normalizer.  It does not select a
finite monomial expansion of an arbitrary exponent polynomial or turn an
integer factorization back into an expression-level HSI derivation.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

/-! ## Transport and multiplication of finite-stage monomials -/

/-- The order-preserving inclusion of the variables at an earlier stage into
the variables at a later stage. -/
def stageInclusion {k l : Nat} (h : k ≤ l) : StageVar k → StageVar l :=
  fun i ↦ ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ h)⟩

theorem stageInclusion_injective {k l : Nat} (h : k ≤ l) :
    Function.Injective (stageInclusion h) := by
  intro i j hij
  have hval : i.1 = j.1 :=
    congrArg (fun x : StageVar l ↦ x.1) hij
  exact Fin.ext hval

@[simp]
theorem stageInclusion_zero {k l : Nat} (h : k ≤ l) :
    stageInclusion h (0 : StageVar k) = 0 :=
  rfl

@[simp]
theorem stageInclusion_succ {k l : Nat} (h : k ≤ l) (j : Fin k) :
    stageInclusion h j.succ = (Fin.castLE h j).succ :=
  rfl

/-- Stage inclusion does not change the corresponding global variable. -/
theorem stageVarEmbedding_stageInclusion {k l : Nat} (h : k ≤ l)
    (i : StageVar k) :
    stageVarEmbedding l (stageInclusion h i) = stageVarEmbedding k i := by
  cases i using Fin.cases <;> rfl

namespace NonconstantMonomial

/-- Regard a coefficient-one nonconstant monomial as a monomial at a later
finite stage. -/
def lift {k l : Nat} (m : NonconstantMonomial k) (h : k ≤ l) :
    NonconstantMonomial l where
  exponents := m.exponents.mapDomain (stageInclusion h)
  nonzero := by
    intro hzero
    apply m.nonzero
    apply Finsupp.mapDomain_injective (stageInclusion_injective h)
    simpa using hzero

/-- Lifting a monomial to a later finite stage does not change its global
polynomial. -/
theorem lift_toGlobal {k l : Nat} (m : NonconstantMonomial k) (h : k ≤ l) :
    (m.lift h).toGlobal = m.toGlobal := by
  simp only [toGlobal, polynomial, StagePolynomial.toGlobal,
    MvPolynomial.rename_monomial, lift]
  apply congrArg (fun exponents : GlobalVar →₀ Nat ↦
    MvPolynomial.monomial exponents (1 : Int))
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro i hi
  exact stageVarEmbedding_stageInclusion h i

/-- Multiply monomials initially presented at two possibly different stages,
after transporting both to their common maximum stage. -/
def product {k l : Nat} (left : NonconstantMonomial k)
    (right : NonconstantMonomial l) : NonconstantMonomial (max k l) where
  exponents :=
    (left.lift (Nat.le_max_left k l)).exponents +
      (right.lift (Nat.le_max_right k l)).exponents
  nonzero := by
    intro hzero
    have hleft :
        (left.lift (Nat.le_max_left k l)).exponents = 0 := by
      apply Finsupp.ext
      intro i
      have hat := congrArg (fun e : StageVar (max k l) →₀ Nat ↦ e i) hzero
      simp only [Finsupp.add_apply] at hat
      exact (Nat.add_eq_zero_iff.mp hat).1
    exact (left.lift (Nat.le_max_left k l)).nonzero hleft

/-- The global polynomial of the product monomial is the product of the two
global monomial polynomials. -/
theorem product_toGlobal {k l : Nat} (left : NonconstantMonomial k)
    (right : NonconstantMonomial l) :
    (left.product right).toGlobal = left.toGlobal * right.toGlobal := by
  rw [← left.lift_toGlobal (Nat.le_max_left k l),
    ← right.lift_toGlobal (Nat.le_max_right k l)]
  simp [toGlobal, polynomial, StagePolynomial.toGlobal, product,
    MvPolynomial.rename_monomial, Finsupp.mapDomain_add,
    MvPolynomial.monomial_mul]

end NonconstantMonomial

/-! ## Comparing finite-stage and global real evaluation -/

/-- The common real coordinate assignment induced by a W3 realization. -/
def realCoordinates {D : PolynomialDerivability} {S : GeneratorSequence D}
    (R : GeneratorRealization S) (y : PositiveReal) : GlobalVar → Real
  | .original => y.1
  | .auxiliary j => R.tau j y

/-- Evaluation after embedding a stage polynomial into the global variable
type agrees with evaluation at the corresponding recursive stage assignment. -/
theorem evalReal_toGlobal {D : PolynomialDerivability}
    {S : GeneratorSequence D} (R : GeneratorRealization S)
    (y : PositiveReal) {k : Nat} (p : StagePolynomial k) :
    MvPolynomial.eval₂ (Int.castRingHom Real) (realCoordinates R y) p.toGlobal =
      p.evalReal (recursiveAssignment R.tau k y) := by
  rw [StagePolynomial.toGlobal, MvPolynomial.eval₂_rename]
  apply congrArg (fun assignment : StageVar k → Real ↦
    MvPolynomial.eval₂ (Int.castRingHom Real) assignment p)
  funext i
  cases i using Fin.cases <;> rfl

/-- Equality of global presentations can be evaluated across unrelated
finite presentation stages. -/
theorem evalReal_eq_of_toGlobal_eq {D : PolynomialDerivability}
    {S : GeneratorSequence D} (R : GeneratorRealization S)
    (y : PositiveReal) {k l : Nat} {p : StagePolynomial k}
    {q : StagePolynomial l} (h : p.toGlobal = q.toGlobal) :
    p.evalReal (recursiveAssignment R.tau k y) =
      q.evalReal (recursiveAssignment R.tau l y) := by
  rw [← evalReal_toGlobal R y p, ← evalReal_toGlobal R y q, h]

/-- Real evaluation of the common-stage product monomial is the product of
the two original stage evaluations. -/
theorem NonconstantMonomial.evalReal_product
    {D : PolynomialDerivability} {S : GeneratorSequence D}
    (R : GeneratorRealization S) (y : PositiveReal)
    {k l : Nat} (left : NonconstantMonomial k)
    (right : NonconstantMonomial l) :
    (left.product right).polynomial.evalReal
        (recursiveAssignment R.tau (max k l) y) =
      left.polynomial.evalReal (recursiveAssignment R.tau k y) *
        right.polynomial.evalReal (recursiveAssignment R.tau l y) := by
  calc
    (left.product right).polynomial.evalReal
        (recursiveAssignment R.tau (max k l) y) =
        MvPolynomial.eval₂ (Int.castRingHom Real) (realCoordinates R y)
          (left.product right).toGlobal :=
      (evalReal_toGlobal R y (left.product right).polynomial).symm
    _ = left.polynomial.evalReal (recursiveAssignment R.tau k y) *
          right.polynomial.evalReal (recursiveAssignment R.tau l y) := by
      rw [NonconstantMonomial.product_toGlobal,
        MvPolynomial.eval₂_mul]
      change
        MvPolynomial.eval₂ (Int.castRingHom Real) (realCoordinates R y)
            left.polynomial.toGlobal *
          MvPolynomial.eval₂ (Int.castRingHom Real) (realCoordinates R y)
            right.polynomial.toGlobal = _
      rw [
        evalReal_toGlobal R y left.polynomial,
        evalReal_toGlobal R y right.polynomial]

/-! ## W2 witnesses and auxiliary-variable flattening -/

/-- W2 jointly covers every encoded W1 base with every nonconstant monomial
exponent. -/
theorem Base.existsUnique_w2 {D : PolynomialDerivability}
    (S : GeneratorSequence D) {baseStage exponentStage : Nat}
    (base : Base baseStage) (m : NonconstantMonomial exponentStage) :
    ∃! index : Nat,
      D.derives (S.pair index).base.toGlobal base.toGlobal ∧
      D.derives (S.pair index).exponent.toGlobal m.toGlobal := by
  cases base with
  | original =>
      simpa using S.existsUnique_original exponentStage m
  | irreducible p hp =>
      exact S.existsUnique_irreducible baseStage exponentStage p hp m

/-- Derivability in W2 yields literal equality of the global polynomial
presentations.  This uses only soundness and polynomial detection on the
positive integer grid, not Wilkie algebraic independence. -/
theorem global_eq_of_derives {D : PolynomialDerivability}
    {p q : GlobalPolynomial} (h : D.derives p q) : p = q :=
  PolynomialSemEq.eq (D.sound h)

/-- One fixed generator represents `q ^ m` in every W3 realization.  The
auxiliary-variable case recursively exposes the W3 definition of that
variable, multiplies its inner exponent by `m`, and invokes W2 on the
resulting base/exponent pair. -/
theorem PositiveIrreducibleFactor.exists_flattened_generator
    {D : PolynomialDerivability} (S : GeneratorSequence D)
    {factorStage exponentStage : Nat} {q : StagePolynomial factorStage}
    (hq : PositiveIrreducibleFactor q)
    (m : NonconstantMonomial exponentStage) :
    ∃ index : Nat, ∀ (R : GeneratorRealization S) (y : PositiveReal),
      Real.rpow
          (q.evalReal (recursiveAssignment R.tau factorStage y))
          (m.polynomial.evalReal
            (recursiveAssignment R.tau exponentStage y)) =
        R.tau index y := by
  cases hq with
  | original hq =>
      obtain ⟨index, hindex, -⟩ := S.existsUnique_original exponentStage m
      refine ⟨index, ?_⟩
      intro R y
      have hbaseGlobal :
          (S.pair index).base.toGlobal = q.toGlobal := by
        rw [hq]
        simpa [StagePolynomial.toGlobal, originalPolynomial] using
          global_eq_of_derives hindex.1
      have hexponentGlobal :
          (S.pair index).exponent.toGlobal = m.toGlobal :=
        global_eq_of_derives hindex.2
      calc
        Real.rpow
            (q.evalReal (recursiveAssignment R.tau factorStage y))
            (m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
            Real.rpow
              ((S.pair index).base.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair index).baseStage y))
              ((S.pair index).exponent.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair index).exponentStage y)) := by
                  congr 1
                  · exact (evalReal_eq_of_toGlobal_eq R y hbaseGlobal).symm
                  · exact (evalReal_eq_of_toGlobal_eq R y hexponentGlobal).symm
        _ = R.tau index y := (R.w3 index y).symm
  | admissible hadmissible =>
      obtain ⟨index, hindex, -⟩ :=
        S.existsUnique_irreducible factorStage exponentStage q hadmissible m
      refine ⟨index, ?_⟩
      intro R y
      have hbaseGlobal :
          (S.pair index).base.toGlobal = q.toGlobal :=
        global_eq_of_derives hindex.1
      have hexponentGlobal :
          (S.pair index).exponent.toGlobal = m.toGlobal :=
        global_eq_of_derives hindex.2
      calc
        Real.rpow
            (q.evalReal (recursiveAssignment R.tau factorStage y))
            (m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
            Real.rpow
              ((S.pair index).base.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair index).baseStage y))
              ((S.pair index).exponent.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair index).exponentStage y)) := by
                  congr 1
                  · exact (evalReal_eq_of_toGlobal_eq R y hbaseGlobal).symm
                  · exact (evalReal_eq_of_toGlobal_eq R y hexponentGlobal).symm
        _ = R.tau index y := (R.w3 index y).symm
  | auxiliary j hq =>
      let combined := (S.pair j.1).exponent.product m
      obtain ⟨index, hindex, -⟩ :=
        (S.pair j.1).base.existsUnique_w2 S combined
      refine ⟨index, ?_⟩
      intro R y
      have hbaseGlobal :
          (S.pair index).base.toGlobal = (S.pair j.1).base.toGlobal :=
        global_eq_of_derives hindex.1
      have hexponentGlobal :
          (S.pair index).exponent.toGlobal = combined.toGlobal :=
        global_eq_of_derives hindex.2
      have hbasePositive :
          0 < (S.pair j.1).base.polynomial.evalReal
            (recursiveAssignment R.tau (S.pair j.1).baseStage y) := by
        apply (S.pair j.1).base.positiveOnOrthant
        intro i
        refine Fin.cases y.2 ?_ i
        intro earlier
        exact R.tau_pos earlier.1 y
      have hfactorEval :
          q.evalReal (recursiveAssignment R.tau factorStage y) =
            R.tau j.1 y := by
        rw [hq]
        simp [StagePolynomial.evalReal]
      have hcombinedEval :
          combined.polynomial.evalReal
              (recursiveAssignment R.tau
                (max (S.pair j.1).exponentStage exponentStage) y) =
            (S.pair j.1).exponent.polynomial.evalReal
                (recursiveAssignment R.tau
                  (S.pair j.1).exponentStage y) *
              m.polynomial.evalReal
                (recursiveAssignment R.tau exponentStage y) := by
        exact (S.pair j.1).exponent.evalReal_product R y m
      calc
        Real.rpow
            (q.evalReal (recursiveAssignment R.tau factorStage y))
            (m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
            Real.rpow (R.tau j.1 y)
              (m.polynomial.evalReal
                (recursiveAssignment R.tau exponentStage y)) := by
                  rw [hfactorEval]
        _ = Real.rpow
              (Real.rpow
                ((S.pair j.1).base.polynomial.evalReal
                  (recursiveAssignment R.tau (S.pair j.1).baseStage y))
                ((S.pair j.1).exponent.polynomial.evalReal
                  (recursiveAssignment R.tau
                    (S.pair j.1).exponentStage y)))
              (m.polynomial.evalReal
                (recursiveAssignment R.tau exponentStage y)) := by
                  rw [R.w3]
        _ = Real.rpow
              ((S.pair j.1).base.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair j.1).baseStage y))
              ((S.pair j.1).exponent.polynomial.evalReal
                  (recursiveAssignment R.tau
                    (S.pair j.1).exponentStage y) *
                m.polynomial.evalReal
                  (recursiveAssignment R.tau exponentStage y)) := by
                    exact (Real.rpow_mul hbasePositive.le _ _).symm
        _ = Real.rpow
              ((S.pair j.1).base.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair j.1).baseStage y))
              (combined.polynomial.evalReal
                (recursiveAssignment R.tau
                  (max (S.pair j.1).exponentStage exponentStage) y)) := by
                    rw [hcombinedEval]
        _ = Real.rpow
              ((S.pair index).base.polynomial.evalReal
                (recursiveAssignment R.tau (S.pair index).baseStage y))
              ((S.pair index).exponent.polynomial.evalReal
                (recursiveAssignment R.tau
                  (S.pair index).exponentStage y)) := by
                    congr 1
                    · exact (evalReal_eq_of_toGlobal_eq R y hbaseGlobal).symm
                    · exact
                        (evalReal_eq_of_toGlobal_eq R y hexponentGlobal).symm
        _ = R.tau index y := (R.w3 index y).symm

/-! ## Assembly of the finite factor-by-monomial grid -/

/-- A classified factor bundled with its finite-stage polynomial. -/
abbrev ClassifiedFactor (k : Nat) :=
  {q : StagePolynomial k // PositiveIrreducibleFactor q}

/-- Every coordinate in a recursive W3 stage assignment is positive. -/
theorem GeneratorRealization.recursiveAssignment_pos
    {D : PolynomialDerivability} {S : GeneratorSequence D}
    (R : GeneratorRealization S) (k : Nat) (y : PositiveReal)
    (i : StageVar k) : 0 < recursiveAssignment R.tau k y i := by
  refine Fin.cases y.2 ?_ i
  intro j
  exact R.tau_pos j.1 y

/-- A classified factor has positive value at every recursive W3
assignment. -/
theorem ClassifiedFactor.evalReal_pos
    {D : PolynomialDerivability} {S : GeneratorSequence D}
    (R : GeneratorRealization S) {k : Nat} (q : ClassifiedFactor k)
    (y : PositiveReal) :
    0 < q.1.evalReal (recursiveAssignment R.tau k y) :=
  q.2.positive _ (R.recursiveAssignment_pos k y)

/-- A positive real base raised to a finite sum is the product of its powers
by the individual summands. -/
theorem rpow_list_sum {x : Real} (hx : 0 < x) (values : List Real) :
    Real.rpow x values.sum =
      (values.map fun exponent ↦ Real.rpow x exponent).prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.map_cons, List.prod_cons]
      calc
        Real.rpow x (value + values.sum) =
            Real.rpow x value * Real.rpow x values.sum :=
          Real.rpow_add hx value values.sum
        _ = Real.rpow x value *
            (values.map fun exponent ↦ Real.rpow x exponent).prod := by
          rw [ih]

/-- The semantic power-branch grid identity.  One generator index is chosen
for every classified factor / nonconstant monomial pair, independently of
the W3 realization and input.  Raising the product of the factors to the sum
of the monomials is then exactly the product of those generator coordinates.

This is the evaluation identity used after the base factorization and
exponent monomial expansion in the AJK Lemma 2.6 power case. -/
theorem exists_powerBranch_grid_identity
    {D : PolynomialDerivability} (S : GeneratorSequence D)
    {factorStage exponentStage : Nat}
    (factors : List (ClassifiedFactor factorStage))
    (monomials : List (NonconstantMonomial exponentStage)) :
    ∃ index : ClassifiedFactor factorStage →
        NonconstantMonomial exponentStage → Nat,
      (∀ q m (R : GeneratorRealization S) (y : PositiveReal),
        Real.rpow
            (q.1.evalReal (recursiveAssignment R.tau factorStage y))
            (m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
          R.tau (index q m) y) ∧
      ∀ (R : GeneratorRealization S) (y : PositiveReal),
        Real.rpow
            ((factors.map fun q ↦
              q.1.evalReal
                (recursiveAssignment R.tau factorStage y)).prod)
            ((monomials.map fun m ↦
              m.polynomial.evalReal
                (recursiveAssignment R.tau exponentStage y)).sum) =
          (factors.map fun q ↦
            (monomials.map fun m ↦ R.tau (index q m) y).prod).prod := by
  have hwitness : ∀ (q : ClassifiedFactor factorStage)
      (m : NonconstantMonomial exponentStage),
      ∃ index : Nat, ∀ (R : GeneratorRealization S) (y : PositiveReal),
        Real.rpow
            (q.1.evalReal (recursiveAssignment R.tau factorStage y))
            (m.polynomial.evalReal
              (recursiveAssignment R.tau exponentStage y)) =
          R.tau index y := by
    intro q m
    exact q.2.exists_flattened_generator S m
  choose index hindex using hwitness
  refine ⟨index, hindex, ?_⟩
  intro R y
  induction factors with
  | nil => simp
  | cons q factors ih =>
      have hqPositive := q.evalReal_pos R y
      have hfactorsPositive :
          0 < (factors.map fun next ↦
            next.1.evalReal
              (recursiveAssignment R.tau factorStage y)).prod := by
        apply List.prod_pos
        intro value hvalue
        obtain ⟨next, -, rfl⟩ := List.mem_map.mp hvalue
        exact next.evalReal_pos R y
      simp only [List.map_cons, List.prod_cons]
      calc
        Real.rpow
            (q.1.evalReal (recursiveAssignment R.tau factorStage y) *
              (factors.map fun next ↦
                next.1.evalReal
                  (recursiveAssignment R.tau factorStage y)).prod)
            ((monomials.map fun m ↦
              m.polynomial.evalReal
                (recursiveAssignment R.tau exponentStage y)).sum) =
            Real.rpow
                (q.1.evalReal (recursiveAssignment R.tau factorStage y))
                ((monomials.map fun m ↦
                  m.polynomial.evalReal
                    (recursiveAssignment R.tau exponentStage y)).sum) *
              Real.rpow
                ((factors.map fun next ↦
                  next.1.evalReal
                    (recursiveAssignment R.tau factorStage y)).prod)
                ((monomials.map fun m ↦
                  m.polynomial.evalReal
                    (recursiveAssignment R.tau exponentStage y)).sum) :=
          Real.mul_rpow hqPositive.le hfactorsPositive.le
        _ = (monomials.map fun m ↦ R.tau (index q m) y).prod *
              (factors.map fun next ↦
                (monomials.map fun m ↦
                  R.tau (index next m) y).prod).prod := by
          rw [rpow_list_sum hqPositive]
          rw [List.map_map]
          have hpowerFunction :
              ((fun exponent : Real ↦
                  Real.rpow
                    (q.1.evalReal
                      (recursiveAssignment R.tau factorStage y)) exponent) ∘
                (fun m : NonconstantMonomial exponentStage ↦
                  m.polynomial.evalReal
                    (recursiveAssignment R.tau exponentStage y))) =
                (fun m ↦ R.tau (index q m) y) := by
            funext m
            exact hindex q m R y
          rw [hpowerFunction, ih]

end

end Natfunbasis.Wilkie
