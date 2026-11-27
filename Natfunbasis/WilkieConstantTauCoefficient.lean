import Natfunbasis.WilkieTauPrimitivePolynomialRelation
import Natfunbasis.WilkieFiniteStageInduction

/-!
# Coefficient extraction for a constant current W1 base

For a constant current base, the current tau primitive is the exponent
monomial multiplied by the scalar logarithm of a natural prime.  This file
computes the coefficient of that exponent monomial in every reified
primitive ingredient.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial
open scoped BigOperators

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

theorem beforeTauExponentVector_ne_single_logIndex
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hjConstant : ¬ S.IsConstantBase j)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    S.beforeTauExponentVector n i hin ≠
      Finsupp.single (S.beforeTauLogIndex hjn hjConstant) 1 := by
  intro heq
  have hvalue := congrArg
    (fun v : S.beforeTauGenerators n →₀ Nat ↦
      v (S.beforeTauLogIndex hjn hjConstant)) heq
  have hzero := S.beforeTauExponentVector_apply_log_eq_zero
    hjn hin hjConstant htau hlog
  simpa [hzero] using hvalue

theorem beforeTauExponentVector_ne_single_logX
    {i n : Nat} (hin : i ≤ n)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q))) :
    S.beforeTauExponentVector n i hin ≠
      Finsupp.single (S.beforeTauLogXIndex n) 1 := by
  intro heq
  have hvalue := congrArg
    (fun v : S.beforeTauGenerators n →₀ Nat ↦
      v (S.beforeTauLogXIndex n)) heq
  have hzero := S.beforeTauExponentVector_apply_logX_eq_zero hin htau
  simpa [beforeTauLogXIndex, hzero] using hvalue

theorem beforeTauTaggedExponentVector_ne_exponentVector
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hiConstant : ¬ S.IsConstantBase i)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    S.beforeTauTaggedExponentVector hin hiConstant ≠
      S.beforeTauExponentVector n j hjn := by
  intro heq
  have hvalue := congrArg
    (fun v : S.beforeTauGenerators n →₀ Nat ↦
      v (S.beforeTauLogIndex hin hiConstant)) heq
  have hii := S.beforeTauExponentVector_apply_log_eq_zero
    hin hin hiConstant htau hlog
  have hji := S.beforeTauExponentVector_apply_log_eq_zero
    hin hjn hiConstant htau hlog
  simp [beforeTauTaggedExponentVector, hii, hji] at hvalue

/-- A pure logarithm polynomial has zero coefficient at every nonconstant
exponent monomial. -/
theorem coeff_beforeTauLogPolynomial_at_exponent
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    coeff (S.beforeTauExponentVector n i hin)
      (S.beforeTauLogPolynomial n j hjn) = 0 := by
  classical
  by_cases hjConstant : S.IsConstantBase j
  · rw [beforeTauLogPolynomial, dif_pos hjConstant]
    exact MvPolynomial.coeff_C_of_ne_zero
      (S.beforeTauExponentVector_ne_zero n i hin) _
  · rw [beforeTauLogPolynomial, dif_neg hjConstant]
    rw [MvPolynomial.coeff_X, if_neg]
    exact (S.beforeTauExponentVector_ne_single_logIndex
      hin hjn hjConstant htau hlog).symm

/-- A constant-base tau term with a matching exponent vector contributes
exactly its prime logarithm. -/
theorem coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_constant_of_eq
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hjConstant : S.IsConstantBase j)
    (heq : S.beforeTauExponentVector n j hjn =
      S.beforeTauExponentVector n i hin) :
    coeff (S.beforeTauExponentVector n i hin)
        (S.beforeTauTauPrimitivePolynomial n j hjn) =
      Real.log (S.constantBasePrime hjConstant : Real) := by
  classical
  rw [beforeTauTauPrimitivePolynomial,
    beforeTauLogPolynomial, dif_pos hjConstant,
    S.beforeTauExponentPolynomial_eq_monomial, mul_comm,
    MvPolynomial.C_mul_monomial, MvPolynomial.coeff_monomial]
  simp [heq]

/-- A constant-base tau term with a different exponent vector has zero
coefficient at the selected exponent. -/
theorem coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_constant_of_ne
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hjConstant : S.IsConstantBase j)
    (hne : S.beforeTauExponentVector n j hjn ≠
      S.beforeTauExponentVector n i hin) :
    coeff (S.beforeTauExponentVector n i hin)
        (S.beforeTauTauPrimitivePolynomial n j hjn) = 0 := by
  classical
  rw [beforeTauTauPrimitivePolynomial,
    beforeTauLogPolynomial, dif_pos hjConstant,
    S.beforeTauExponentPolynomial_eq_monomial, mul_comm,
    MvPolynomial.C_mul_monomial, MvPolynomial.coeff_monomial,
    if_neg hne]

/-- A nonconstant-base tau term has a logarithm-variable factor and hence
has zero coefficient at every pure coordinate exponent monomial. -/
theorem coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_not_constant
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hjConstant : ¬ S.IsConstantBase j)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    coeff (S.beforeTauExponentVector n i hin)
      (S.beforeTauTauPrimitivePolynomial n j hjn) = 0 := by
  classical
  rw [beforeTauTauPrimitivePolynomial,
    beforeTauLogPolynomial, dif_neg hjConstant,
    S.beforeTauExponentPolynomial_eq_monomial]
  change coeff (S.beforeTauExponentVector n i hin)
    (monomial (S.beforeTauExponentVector n j hjn) 1 *
      monomial
        (Finsupp.single (S.beforeTauLogIndex hjn hjConstant) 1) 1) = 0
  rw [MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial, if_neg]
  exact S.beforeTauTaggedExponentVector_ne_exponentVector
    hjn hin hjConstant htau hlog

/-- The scalar contribution of an earlier tau term to a selected pure
coordinate exponent.  It is nonzero only for a constant base with exactly
the selected exponent vector. -/
noncomputable def constantTauCoefficientAtExponent
    {i n : Nat} (hin : i ≤ n)
    (coeffs : S.PrimitiveCoefficients n (n + 1)) (j : Fin n) : Real := by
  classical
  exact if hjConstant : S.IsConstantBase j.1 then
      if S.beforeTauExponentVector n j.1 (Nat.le_of_lt j.2) =
          S.beforeTauExponentVector n i hin then
        (coeffs.tauCoeff j : Real) *
          Real.log (S.constantBasePrime hjConstant : Real)
      else 0
    else 0

/-- Coefficient of a complete flattened primitive at a pure exponent
monomial. -/
theorem coeff_beforeTauPrimitiveCoefficientsPolynomial_at_exponent
    {i n : Nat} (hin : i ≤ n)
    (coeffs : S.PrimitiveCoefficients n (n + 1))
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    coeff (S.beforeTauExponentVector n i hin)
        (S.beforeTauPrimitiveCoefficientsPolynomial n coeffs) =
      ∑ j : Fin n,
        S.constantTauCoefficientAtExponent hin coeffs j := by
  classical
  rw [beforeTauPrimitiveCoefficientsPolynomial]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum]
  rw [MvPolynomial.coeff_C_of_ne_zero
    (S.beforeTauExponentVector_ne_zero n i hin)]
  have hlogX : coeff (S.beforeTauExponentVector n i hin)
      (X (S.beforeTauLogXIndex n) :
        MvPolynomial (S.beforeTauGenerators n) Real) = 0 := by
    rw [MvPolynomial.coeff_X, if_neg]
    exact (S.beforeTauExponentVector_ne_single_logX hin htau).symm
  rw [hlogX, mul_zero, zero_add]
  have htauSum :
      (∑ x : Fin n,
          (coeffs.tauCoeff x : Real) *
            coeff (S.beforeTauExponentVector n i hin)
              (S.beforeTauTauPrimitivePolynomial n x.1
                (Nat.le_of_lt x.2))) =
        ∑ x : Fin n,
          S.constantTauCoefficientAtExponent hin coeffs x := by
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hjConstant : S.IsConstantBase j.1
    · by_cases heq : S.beforeTauExponentVector n j.1
          (Nat.le_of_lt j.2) = S.beforeTauExponentVector n i hin
      · rw [S.coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_constant_of_eq
          hin (Nat.le_of_lt j.2) hjConstant heq]
        simp [constantTauCoefficientAtExponent, hjConstant, heq]
      · rw [S.coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_constant_of_ne
          hin (Nat.le_of_lt j.2) hjConstant heq]
        simp [constantTauCoefficientAtExponent, hjConstant, heq]
    · rw [S.coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_not_constant
        hin (Nat.le_of_lt j.2) hjConstant htau hlog]
      simp [constantTauCoefficientAtExponent, hjConstant]
  rw [htauSum]
  have hfreshLogSum :
      (∑ x : Fin (n + 1),
          (coeffs.freshLogCoeff x : Real) *
            coeff (S.beforeTauExponentVector n i hin)
              (S.beforeTauLogPolynomial n x.1
                (Nat.lt_succ_iff.mp x.2))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    rw [S.coeff_beforeTauLogPolynomial_at_exponent
      hin (Nat.lt_succ_iff.mp j.2) htau hlog, mul_zero]
  rw [hfreshLogSum, add_zero]
  simp

/-- The structured primitive relation is impossible when the current W1
base is constant.  The coefficient of the current exponent yields an
integer relation among logarithms of distinct natural primes; W1.3 supplies
the required distinctness. -/
theorem tauPrimitiveRelationExclusion_of_constant {n : Nat}
    (hconstant : S.IsConstantBase n)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (hbefore : AlgebraicIndepOn Real id (S.beforeTauGenerators n)) :
    S.TauPrimitiveRelationExclusion n := by
  classical
  intro m hm L hL c hrelation
  obtain ⟨coeffs, _hcoeffs, hpoly⟩ :=
    S.beforeTau_polynomial_relation_of_primitive_relation
      hbefore m L hL c hrelation
  let target := S.beforeTauExponentVector n n le_rfl
  have htarget_ne : target ≠ 0 :=
    S.beforeTauExponentVector_ne_zero n n le_rfl
  have hcoeff := congrArg
    (MvPolynomial.coeff target) hpoly
  have hleft :
      coeff target
          (C (m : Real) *
            S.beforeTauTauPrimitivePolynomial n n le_rfl) =
        (m : Real) *
          Real.log (S.constantBasePrime hconstant : Real) := by
    rw [MvPolynomial.coeff_C_mul]
    apply congrArg ((m : Real) * ·)
    exact S.coeff_beforeTauTauPrimitivePolynomial_at_exponent_of_constant_of_eq
      le_rfl le_rfl hconstant rfl
  have hright :
      coeff target
          (C c + S.beforeTauPrimitiveCoefficientsPolynomial n coeffs) =
        ∑ j : Fin n,
          S.constantTauCoefficientAtExponent le_rfl coeffs j := by
    rw [MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_of_ne_zero htarget_ne, zero_add]
    exact S.coeff_beforeTauPrimitiveCoefficientsPolynomial_at_exponent
      le_rfl coeffs htau hlog
  rw [hleft, hright] at hcoeff
  let Matches : Fin n → Prop := fun j ↦
    S.IsConstantBase j.1 ∧
      S.beforeTauExponentVector n j.1 (Nat.le_of_lt j.2) = target
  let I := {j : Fin n // Matches j}
  have hcontribution_of_match (j : I) :
      S.constantTauCoefficientAtExponent le_rfl coeffs j.1 =
        (coeffs.tauCoeff j.1 : Real) *
          Real.log
            (S.constantBasePrime
              (show S.IsConstantBase j.1.1 from j.2.1) : Real) := by
    have hjConstant : S.IsConstantBase j.1.1 := j.2.1
    have hjExponent : S.beforeTauExponentVector n j.1.1
        (Nat.le_of_lt j.1.2) = target := j.2.2
    dsimp [target] at hjExponent
    simp [constantTauCoefficientAtExponent, hjConstant, hjExponent]
  have hcontribution_of_not_match (j : {j : Fin n // ¬ Matches j}) :
      S.constantTauCoefficientAtExponent le_rfl coeffs j.1 = 0 := by
    rcases not_and_or.mp j.2 with hjConstant | hjExponent
    · simp [constantTauCoefficientAtExponent, hjConstant]
    · by_cases hjc : S.IsConstantBase j.1.1
      · dsimp [target] at hjExponent
        simp [constantTauCoefficientAtExponent, hjc, hjExponent]
      · simp [constantTauCoefficientAtExponent, hjc]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    Matches (S.constantTauCoefficientAtExponent le_rfl coeffs)
  have hnotMatchSum :
      (∑ j : {j : Fin n // ¬ Matches j},
        S.constantTauCoefficientAtExponent le_rfl coeffs j.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    exact hcontribution_of_not_match j
  have hmatchingSum :
      (∑ j : Fin n,
          S.constantTauCoefficientAtExponent le_rfl coeffs j) =
        ∑ j : I,
          (coeffs.tauCoeff j.1 : Real) *
            Real.log
              (S.constantBasePrime
                (show S.IsConstantBase j.1.1 from j.2.1) : Real) := by
    rw [← hsplit, hnotMatchSum, add_zero]
    apply Finset.sum_congr rfl
    intro j _hj
    exact hcontribution_of_match j
  rw [hmatchingSum] at hcoeff
  let k : Option I → Nat
    | none => n
    | some j => j.1.1
  have hkConstant : ∀ u : Option I, S.IsConstantBase (k u) := by
    intro u
    cases u with
    | none => exact hconstant
    | some j => exact j.2.1
  let z : Option I → Int
    | none => -m
    | some j => coeffs.tauCoeff j.1
  have hkInjective : Function.Injective
      (fun u : Option I ↦ S.baseGlobal (k u)) := by
    intro u v huv
    cases u with
    | none =>
        cases v with
        | none => rfl
        | some j =>
            exfalso
            simp only [k] at huv
            have hjExponent :
                S.beforeTauExponentVector n j.1.1
                    (Nat.le_of_lt j.1.2) = target := j.2.2
            have hexponent : S.exponentGlobal j.1.1 =
                S.exponentGlobal n :=
              S.exponentGlobal_eq_of_beforeTauExponentVector_eq
                (Nat.le_of_lt j.1.2) le_rfl htau hjExponent
            apply S.w1_noRepeatedPair (Nat.ne_of_lt j.1.2)
            constructor
            · change PolynomialSemEq
                (S.baseGlobal j.1.1) (S.baseGlobal n)
              rw [huv]
              exact PolynomialSemEq.refl _
            · change PolynomialSemEq
                (S.exponentGlobal j.1.1) (S.exponentGlobal n)
              rw [hexponent]
              exact PolynomialSemEq.refl _
    | some i =>
        cases v with
        | none =>
            exfalso
            simp only [k] at huv
            have hiExponent :
                S.beforeTauExponentVector n i.1.1
                    (Nat.le_of_lt i.1.2) = target := i.2.2
            have hexponent : S.exponentGlobal i.1.1 =
                S.exponentGlobal n :=
              S.exponentGlobal_eq_of_beforeTauExponentVector_eq
                (Nat.le_of_lt i.1.2) le_rfl htau hiExponent
            apply S.w1_noRepeatedPair (Nat.ne_of_lt i.1.2)
            constructor
            · change PolynomialSemEq
                (S.baseGlobal i.1.1) (S.baseGlobal n)
              rw [huv]
              exact PolynomialSemEq.refl _
            · change PolynomialSemEq
                (S.exponentGlobal i.1.1) (S.exponentGlobal n)
              rw [hexponent]
              exact PolynomialSemEq.refl _
        | some j =>
            simp only [k] at huv
            apply congrArg some
            apply Subtype.ext
            apply Fin.ext
            by_contra hij
            have hvector :
                S.beforeTauExponentVector n i.1.1
                    (Nat.le_of_lt i.1.2) =
                  S.beforeTauExponentVector n j.1.1
                    (Nat.le_of_lt j.1.2) := i.2.2.trans j.2.2.symm
            have hexponent : S.exponentGlobal i.1.1 =
                S.exponentGlobal j.1.1 :=
              S.exponentGlobal_eq_of_beforeTauExponentVector_eq
                (Nat.le_of_lt i.1.2) (Nat.le_of_lt j.1.2)
                htau hvector
            apply S.w1_noRepeatedPair hij
            constructor
            · change PolynomialSemEq
                (S.baseGlobal i.1.1) (S.baseGlobal j.1.1)
              rw [huv]
              exact PolynomialSemEq.refl _
            · change PolynomialSemEq
                (S.exponentGlobal i.1.1) (S.exponentGlobal j.1.1)
              rw [hexponent]
              exact PolynomialSemEq.refl _
  have hlogCombination :
      ∑ u : Option I, (z u : Real) *
        Real.log (S.constantBasePrime (hkConstant u) : Real) = 0 := by
    rw [Fintype.sum_option]
    simp only [k, z, Int.cast_neg]
    change (-(m : Real)) *
        Real.log (S.constantBasePrime hconstant : Real) +
      (∑ j : I, (coeffs.tauCoeff j.1 : Real) *
        Real.log
          (S.constantBasePrime
            (show S.IsConstantBase j.1.1 from j.2.1) : Real)) = 0
    linarith
  have hz := S.int_constantBase_log_combination_eq_zero
    k hkConstant hkInjective z hlogCombination
  have hzm := hz none
  change -m = 0 at hzm
  exact hm (neg_eq_zero.mp hzm)

end GeneratorSequence

end

end Natfunbasis.Wilkie
