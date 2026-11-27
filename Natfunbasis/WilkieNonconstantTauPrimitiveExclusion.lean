import Natfunbasis.WilkieTauPrimitivePolynomialRelation
import Natfunbasis.WilkieFiniteStageInduction

/-!
# Excluding the tau-primitive relation for a nonconstant current base

For a nonconstant current W1 base, `tauPrimitive n` reifies as a monomial
tagged by both its exponent vector and its base-logarithm variable.  No
constant, logarithm-only term, or earlier constant-base tau primitive can
have this tagged exponent.  If an earlier nonconstant-base tau primitive had
the same tag, the base and exponent presentations would both agree with the
current pair, contradicting W1.3.

This file proves only the nonconstant-current-base branch.  Constant current
bases require the separate independence argument for logarithms of primes.
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

/-- A nonconstant-base tau primitive is literally its tagged coefficient-one
monomial in the pre-`tau` polynomial coordinates. -/
theorem beforeTauTauPrimitivePolynomial_eq_taggedMonomial
    {j n : Nat} (hjn : j ≤ n) (hconstant : ¬ S.IsConstantBase j) :
    S.beforeTauTauPrimitivePolynomial n j hjn =
      monomial (S.beforeTauTaggedExponentVector hjn hconstant) 1 := by
  rw [beforeTauTauPrimitivePolynomial,
    S.beforeTauExponentPolynomial_eq_monomial,
    beforeTauLogPolynomial, dif_neg hconstant]
  simp [MvPolynomial.X, beforeTauTaggedExponentVector,
    MvPolynomial.monomial_mul]

/-- A constant-base tau primitive has only the exponent tag; its base
logarithm is absorbed into the real coefficient. -/
theorem beforeTauTauPrimitivePolynomial_eq_constantMonomial
    {j n : Nat} (hjn : j ≤ n) (hconstant : S.IsConstantBase j) :
    S.beforeTauTauPrimitivePolynomial n j hjn =
      monomial (S.beforeTauExponentVector n j hjn)
        (Real.log (S.constantBasePrime hconstant : Real)) := by
  rw [beforeTauTauPrimitivePolynomial,
    S.beforeTauExponentPolynomial_eq_monomial,
    beforeTauLogPolynomial, dif_pos hconstant]
  rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/-- The current tagged exponent vector is nonzero. -/
theorem beforeTauTaggedExponentVector_ne_zero_current {n : Nat}
    (hconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    S.beforeTauTaggedExponentVector le_rfl hconstant ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun v : S.beforeTauGenerators n →₀ Nat ↦
      v (S.beforeTauLogIndex le_rfl hconstant)) hzero
  have hexponent := S.beforeTauExponentVector_apply_log_eq_zero
    le_rfl le_rfl hconstant hpriorTau hlog
  simp [beforeTauTaggedExponentVector, hexponent] at hvalue

/-- No one-variable logarithm monomial can have the current tagged exponent:
if its variable is the current logarithm, the nonzero exponent vector remains;
otherwise evaluation at the current logarithm separates them. -/
theorem single_ne_beforeTauTaggedExponentVector_current {n : Nat}
    (x : S.beforeTauGenerators n)
    (hconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    Finsupp.single x 1 ≠
      S.beforeTauTaggedExponentVector le_rfl hconstant := by
  intro heq
  let currentLog : S.beforeTauGenerators n :=
    S.beforeTauLogIndex le_rfl hconstant
  have hexponent := S.beforeTauExponentVector_apply_log_eq_zero
    le_rfl le_rfl hconstant hpriorTau hlog
  by_cases hx : x = currentLog
  · apply S.beforeTauExponentVector_ne_zero n n le_rfl
    apply add_right_cancel (b := Finsupp.single currentLog 1)
    calc
      S.beforeTauExponentVector n n le_rfl +
          Finsupp.single currentLog 1 =
          S.beforeTauTaggedExponentVector le_rfl hconstant := rfl
      _ = Finsupp.single x 1 := heq.symm
      _ = 0 + Finsupp.single currentLog 1 := by simp [hx]
  · have hvalue := congrArg
      (fun v : S.beforeTauGenerators n →₀ Nat ↦ v currentLog) heq
    simp [currentLog, beforeTauTaggedExponentVector, hexponent, hx] at hvalue

/-- Every untagged exponent vector, including those arising from
constant-base tau primitives, differs from the current tagged vector. -/
theorem beforeTauExponentVector_ne_taggedCurrent {j n : Nat}
    (hjn : j ≤ n) (hconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    S.beforeTauExponentVector n j hjn ≠
      S.beforeTauTaggedExponentVector le_rfl hconstant := by
  intro heq
  have hvalue := congrArg
    (fun v : S.beforeTauGenerators n →₀ Nat ↦
      v (S.beforeTauLogIndex le_rfl hconstant)) heq
  have hjzero := S.beforeTauExponentVector_apply_log_eq_zero
    le_rfl hjn hconstant hpriorTau hlog
  have hnzero := S.beforeTauExponentVector_apply_log_eq_zero
    le_rfl le_rfl hconstant hpriorTau hlog
  simp [beforeTauTaggedExponentVector, hjzero, hnzero] at hvalue

/-- W1.3 prevents an earlier nonconstant tau primitive from carrying the
current tagged exponent vector. -/
theorem prior_beforeTauTaggedExponentVector_ne_current
    {j n : Nat} (hjn : j < n)
    (hjconstant : ¬ S.IsConstantBase j)
    (hnconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (hcoord : AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r))) :
    S.beforeTauTaggedExponentVector hjn.le hjconstant ≠
      S.beforeTauTaggedExponentVector le_rfl hnconstant := by
  intro heq
  obtain ⟨hbase, hexponent⟩ :=
    S.baseGlobal_eq_and_exponentGlobal_eq_of_taggedExponentVector_eq
      hjn.le le_rfl hjconstant hnconstant hpriorTau hlog hcoord heq
  apply S.w1_noRepeatedPair (Nat.ne_of_lt hjn)
  constructor
  · change (S.pair j).base.toGlobal = (S.pair n).base.toGlobal at hbase
    rw [hbase]
    exact PolynomialSemEq.refl _
  · change (S.pair j).exponent.toGlobal =
      (S.pair n).exponent.toGlobal at hexponent
    rw [hexponent]
    exact PolynomialSemEq.refl _

/-! ## Coefficients at the current tagged monomial -/

/-- A base-logarithm polynomial has zero coefficient at the current tagged
monomial, whether that base is constant or nonconstant. -/
theorem coeff_beforeTauLogPolynomial_taggedCurrent_eq_zero
    {j n : Nat} (hjn : j ≤ n)
    (hnconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    coeff (S.beforeTauTaggedExponentVector le_rfl hnconstant)
        (S.beforeTauLogPolynomial n j hjn) = 0 := by
  classical
  by_cases hjconstant : S.IsConstantBase j
  · rw [beforeTauLogPolynomial, dif_pos hjconstant]
    exact MvPolynomial.coeff_C_of_ne_zero
      (S.beforeTauTaggedExponentVector_ne_zero_current
        hnconstant hpriorTau hlog) _
  · rw [beforeTauLogPolynomial, dif_neg hjconstant,
      MvPolynomial.coeff_X,
      if_neg (S.single_ne_beforeTauTaggedExponentVector_current
        (S.beforeTauLogIndex hjn hjconstant)
        hnconstant hpriorTau hlog)]

/-- The distinguished `log x` variable is also a log-only monomial and hence
has zero coefficient at the current tagged monomial. -/
theorem coeff_beforeTauLogX_taggedCurrent_eq_zero
    {n : Nat} (hnconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) :
    coeff (S.beforeTauTaggedExponentVector le_rfl hnconstant)
        (X (S.beforeTauLogXIndex n) :
          MvPolynomial (S.beforeTauGenerators n) Real) = 0 := by
  classical
  rw [MvPolynomial.coeff_X,
    if_neg (S.single_ne_beforeTauTaggedExponentVector_current
      (S.beforeTauLogXIndex n) hnconstant hpriorTau hlog)]

/-- Every earlier tau primitive has zero coefficient at the current tagged
monomial.  Constant earlier bases are untagged; a matching nonconstant tag is
excluded by W1.3. -/
theorem coeff_prior_beforeTauTauPrimitivePolynomial_taggedCurrent_eq_zero
    {j n : Nat} (hjn : j < n)
    (hnconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (hcoord : AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r))) :
    coeff (S.beforeTauTaggedExponentVector le_rfl hnconstant)
        (S.beforeTauTauPrimitivePolynomial n j hjn.le) = 0 := by
  classical
  by_cases hjconstant : S.IsConstantBase j
  · rw [S.beforeTauTauPrimitivePolynomial_eq_constantMonomial
      hjn.le hjconstant, MvPolynomial.coeff_monomial,
      if_neg (S.beforeTauExponentVector_ne_taggedCurrent
        hjn.le hnconstant hpriorTau hlog)]
  · rw [S.beforeTauTauPrimitivePolynomial_eq_taggedMonomial
      hjn.le hjconstant, MvPolynomial.coeff_monomial,
      if_neg (S.prior_beforeTauTaggedExponentVector_ne_current
        hjn hjconstant hnconstant hpriorTau hlog hcoord)]

/-- Pre-`tau` algebraic independence restricts to algebraic independence of
the labeled finite analytic coordinates.  Prior tau transcendence supplies
the required injectivity of their indexing map. -/
theorem algebraicIndependent_analyticAssignment_of_beforeTau
    {n : Nat}
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hbefore : AlgebraicIndepOn Real id (S.beforeTauGenerators n)) :
    AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r)) := by
  let f : StageVar n → S.beforeTauGenerators n :=
    S.beforeTauCoordinateIndex n
  have hf : Function.Injective f :=
    S.beforeTauCoordinateIndex_injective hpriorTau
  have hcomp := hbefore.comp f hf
  simpa [f, Function.comp_def,
    S.finiteFractionCoordinates_eq_analyticAssignment] using hcomp

/-! ## The nonconstant-current-base exclusion theorem -/

/-- The structured tau-primitive relation is impossible when the current W1
base is nonconstant.  This is the complete nonconstant branch of
`TauPrimitiveRelationExclusion`. -/
theorem tauPrimitiveRelationExclusion_of_not_constant {n : Nat}
    (hnconstant : ¬ S.IsConstantBase n)
    (hpriorTau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (hbefore : AlgebraicIndepOn Real id (S.beforeTauGenerators n)) :
    S.TauPrimitiveRelationExclusion n := by
  classical
  have hcoord : AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r)) :=
    S.algebraicIndependent_analyticAssignment_of_beforeTau
      hpriorTau hbefore
  intro m hm L hL c hrelation
  obtain ⟨coeffs, _hcoeffs, hpoly⟩ :=
    S.beforeTau_polynomial_relation_of_primitive_relation
      hbefore m L hL c hrelation
  let target : S.beforeTauGenerators n →₀ Nat :=
    S.beforeTauTaggedExponentVector le_rfl hnconstant
  have htarget : target ≠ 0 :=
    S.beforeTauTaggedExponentVector_ne_zero_current
      hnconstant hpriorTau hlog
  have hlogXzero :
      coeff target
          (X (S.beforeTauLogXIndex n) :
            MvPolynomial (S.beforeTauGenerators n) Real) = 0 :=
    S.coeff_beforeTauLogX_taggedCurrent_eq_zero
      hnconstant hpriorTau hlog
  have hfreshLogZero : ∀ j : Fin (n + 1),
      coeff target
          (S.beforeTauLogPolynomial n j.1
            (Nat.lt_succ_iff.mp j.2)) = 0 := by
    intro j
    exact S.coeff_beforeTauLogPolynomial_taggedCurrent_eq_zero
      (Nat.lt_succ_iff.mp j.2) hnconstant hpriorTau hlog
  have hcoeff := congrArg (MvPolynomial.coeff target) hpoly
  dsimp [target] at hcoeff htarget hlogXzero hfreshLogZero
  rw [S.beforeTauTauPrimitivePolynomial_eq_taggedMonomial
    le_rfl hnconstant] at hcoeff
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
    if_pos rfl, mul_one] at hcoeff
  simp only [beforeTauPrimitiveCoefficientsPolynomial,
    MvPolynomial.coeff_add, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul] at hcoeff
  rw [MvPolynomial.coeff_C_of_ne_zero htarget,
    MvPolynomial.coeff_C_of_ne_zero htarget,
    hlogXzero, mul_zero] at hcoeff
  simp only [hfreshLogZero, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add] at hcoeff
  have hmReal : (m : Real) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hsumNe :
      (∑ j : Fin n,
        (coeffs.tauCoeff j : Real) *
          coeff (S.beforeTauTaggedExponentVector le_rfl hnconstant)
            (S.beforeTauTauPrimitivePolynomial n j.1
              (Nat.le_of_lt j.2))) ≠ 0 := by
    rw [← hcoeff]
    exact hmReal
  obtain ⟨j, _hjmem, hjterm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  have hjcoeff :
      coeff (S.beforeTauTaggedExponentVector le_rfl hnconstant)
          (S.beforeTauTauPrimitivePolynomial n j.1
            (Nat.le_of_lt j.2)) ≠ 0 := by
    intro hjzero
    apply hjterm
    rw [hjzero, mul_zero]
  have hjconstant : ¬ S.IsConstantBase j.1 := by
    intro hconstant
    apply hjcoeff
    rw [S.beforeTauTauPrimitivePolynomial_eq_constantMonomial
      (Nat.le_of_lt j.2) hconstant,
      MvPolynomial.coeff_monomial,
      if_neg (S.beforeTauExponentVector_ne_taggedCurrent
        (Nat.le_of_lt j.2) hnconstant hpriorTau hlog)]
  have htag :
      S.beforeTauTaggedExponentVector (Nat.le_of_lt j.2) hjconstant =
        S.beforeTauTaggedExponentVector le_rfl hnconstant := by
    by_contra hne
    apply hjcoeff
    rw [S.beforeTauTauPrimitivePolynomial_eq_taggedMonomial
      (Nat.le_of_lt j.2) hjconstant,
      MvPolynomial.coeff_monomial, if_neg hne]
  exact S.prior_beforeTauTaggedExponentVector_ne_current
    j.2 hjconstant hnconstant hpriorTau hlog hcoord htag

end GeneratorSequence

end

end Natfunbasis.Wilkie
