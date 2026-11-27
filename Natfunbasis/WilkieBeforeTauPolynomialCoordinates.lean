import Natfunbasis.WilkieBaseLogSeparation
import Natfunbasis.WilkiePrimitiveCoefficientRepresentation

/-!
# Polynomial coordinates before a Wilkie power adjunction

This file embeds the labeled finite coordinate polynomials into the real
polynomial ring on the actual algebraically-independent pre-`tau` generator
set.  It also records exactly which logarithms are variables there: every
nonconstant base logarithm is either `logX` or a fresh logarithm already
inserted in the tower; a constant base logarithm is a real scalar.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial Set

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-! ## Generator-set membership -/

theorem stageGenerators_subset_beforeTauGenerators (n : Nat) :
    S.stageGenerators n ⊆ S.beforeTauGenerators n := by
  classical
  by_cases hfresh : S.IsFreshBase n
  · rw [S.beforeTauGenerators_eq_of_fresh hfresh]
    exact Set.subset_insert _ _
  · rw [S.beforeTauGenerators_eq_of_not_fresh hfresh]

theorem finiteFractionCoordinate_mem_beforeTauGenerators (n : Nat)
    (i : StageVar n) :
    S.finiteFractionCoordinates n i ∈ S.beforeTauGenerators n :=
  S.stageGenerators_subset_beforeTauGenerators n
    (S.finiteFractionCoordinate_mem_stageGenerators n i)

theorem logX_mem_stageGenerators (n : Nat) :
    OneVariableBaseField.logX ∈ S.stageGenerators n := by
  apply S.stageGenerators_mono (Nat.zero_le n)
  simp [stageGenerators]

theorem logX_mem_beforeTauGenerators (n : Nat) :
    OneVariableBaseField.logX ∈ S.beforeTauGenerators n :=
  S.stageGenerators_subset_beforeTauGenerators n
    (S.logX_mem_stageGenerators n)

/-- Every fresh logarithm with index at most `n` is an actual generator of
the pre-`tau_n` set. -/
theorem freshLog_mem_beforeTauGenerators {j n : Nat} (hj : j ≤ n)
    (hfresh : S.IsFreshBase j) :
    ι (S.logBaseAnalytic j) ∈ S.beforeTauGenerators n := by
  rcases hj.eq_or_lt with rfl | hjlt
  · rw [S.beforeTauGenerators_eq_of_fresh hfresh]
    exact Set.mem_insert _ _
  · apply S.stageGenerators_subset_beforeTauGenerators n
    apply S.stageGenerators_mono (Nat.succ_le_iff.mpr hjlt)
    rw [S.stageGenerators_succ,
      S.beforeTauGenerators_eq_of_fresh hfresh]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

/-- A nonconstant base logarithm is represented by a logarithm variable in
the pre-`tau` generator set.  Original and repeated bases are rewritten to
the already present representative. -/
theorem logBase_mem_beforeTauGenerators_of_not_constant {j n : Nat}
    (hj : j ≤ n) (hconstant : ¬ S.IsConstantBase j) :
    ι (S.logBaseAnalytic j) ∈ S.beforeTauGenerators n := by
  rcases S.constant_original_fresh_or_repeated j with
      hconst | horiginal | hfresh | hrepeated
  · exact False.elim (hconstant hconst)
  · rw [S.logBase_eq_logX_of_isOriginalBase horiginal]
    exact S.logX_mem_beforeTauGenerators n
  · exact S.freshLog_mem_beforeTauGenerators hj hfresh
  · obtain ⟨r, ⟨hrj, hrfresh, hbase⟩, -⟩ := hrepeated
    rw [← S.logBaseAnalytic_eq_of_baseGlobal_eq hbase]
    exact S.freshLog_mem_beforeTauGenerators (hrj.le.trans hj) hrfresh

/-- A constant W1 base logarithm is an embedded real scalar. -/
theorem exists_logBaseFraction_eq_real_of_constant {j : Nat}
    (hconstant : S.IsConstantBase j) :
    ∃ c : Real,
      ι (S.logBaseAnalytic j) = algebraMap Real K c := by
  obtain ⟨z, hz⟩ := hconstant
  refine ⟨Real.log (z : Real), ?_⟩
  have hlogA : S.logBaseAnalytic j =
      algebraMap Real A (Real.log (z : Real)) := by
    apply Subtype.ext
    funext y
    rw [S.logBaseAnalytic_apply, S.baseAnalytic_eq_const hz]
    rfl
  rw [hlogA]
  exact IsScalarTower.algebraMap_apply Real A K _

/-! ## Separation of logarithm variables from algebraic coordinates -/

private theorem transcendental_ne_of_mem
    (F : DifferentialIntermediateField Real K) {z w : K}
    (hz : Transcendental F z) (hw : w ∈ F) : z ≠ w := by
  intro hzw
  apply hz
  let wF : F := ⟨w, hw⟩
  have halg : IsAlgebraic F (algebraMap F K wF) :=
    isAlgebraic_algebraMap wF
  simpa [wF, hzw] using halg

/-- `log x` is different from every algebraic coordinate available at stage
`n`, assuming the earlier power adjunctions are transcendental. -/
theorem logX_ne_finiteFractionCoordinate {n : Nat}
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (i : StageVar n) :
    OneVariableBaseField.logX ≠ S.finiteFractionCoordinates n i := by
  cases i using Fin.cases with
  | zero =>
      intro heq
      have hindices : (1 : Fin 2) = 0 :=
        OneVariableBaseField.x_logX_algebraicIndependent.injective heq
      have hvals : (1 : Nat) = 0 := congrArg Fin.val hindices
      omega
  | succ q =>
      have hne : ι (S.realTauAnalyticFunction q.1) ≠
          OneVariableBaseField.logX :=
        transcendental_ne_of_mem (S.finiteStageBeforeTau q.1)
          (htau q.1 q.2)
          (S.finiteStageField_le_beforeTau q.1
            (S.logX_mem_finiteStageField q.1))
      simpa using hne.symm

/-- A fresh logarithm is different from every algebraic coordinate at a
later stage.  The proof separates coordinates before and after the logarithm
was adjoined, using the corresponding transcendence direction. -/
theorem freshLog_ne_finiteFractionCoordinate {r n : Nat} (hrn : r ≤ n)
    (hrfresh : S.IsFreshBase r)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : Transcendental (S.finiteStageField r)
      (ι (S.logBaseAnalytic r)))
    (i : StageVar n) :
    ι (S.logBaseAnalytic r) ≠ S.finiteFractionCoordinates n i := by
  cases i using Fin.cases with
  | zero =>
      exact transcendental_ne_of_mem (S.finiteStageField r) hlog
        (S.x_mem_finiteStageField r)
  | succ q =>
      by_cases hqr : q.1 < r
      · exact transcendental_ne_of_mem (S.finiteStageField r) hlog
          (S.tau_mem_finiteStageField hqr)
      · have hrq : r ≤ q.1 := Nat.le_of_not_gt hqr
        have hlogmem : ι (S.logBaseAnalytic r) ∈
            S.finiteStageBeforeTau q.1 := by
          rcases hrq.eq_or_lt with rfl | hrq
          · exact S.current_log_mem_finiteStageBeforeTau hrfresh
          · exact S.finiteStageField_le_beforeTau q.1
              (S.freshLog_mem_finiteStageField hrq hrfresh)
        exact (transcendental_ne_of_mem (S.finiteStageBeforeTau q.1)
          (htau q.1 q.2) hlogmem).symm

/-- Every nonconstant W1 base logarithm is separated from the labeled
algebraic coordinates. -/
theorem logBase_ne_finiteFractionCoordinate_of_not_constant
    {j n : Nat} (hjn : j ≤ n) (hconstant : ¬ S.IsConstantBase j)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (i : StageVar n) :
    ι (S.logBaseAnalytic j) ≠ S.finiteFractionCoordinates n i := by
  rcases S.constant_original_fresh_or_repeated j with
      hconst | horiginal | hfresh | hrepeated
  · exact False.elim (hconstant hconst)
  · rw [S.logBase_eq_logX_of_isOriginalBase horiginal]
    exact S.logX_ne_finiteFractionCoordinate htau i
  · exact S.freshLog_ne_finiteFractionCoordinate hjn hfresh htau
      (hlog j hjn hfresh) i
  · obtain ⟨r, ⟨hrj, hrfresh, hbase⟩, -⟩ := hrepeated
    rw [← S.logBaseAnalytic_eq_of_baseGlobal_eq hbase]
    exact S.freshLog_ne_finiteFractionCoordinate (hrj.le.trans hjn)
      hrfresh htau (hlog r (hrj.le.trans hjn) hrfresh) i

/-- The actual pre-`tau` variable corresponding to a nonconstant base
logarithm. -/
def beforeTauLogIndex {j n : Nat} (hjn : j ≤ n)
    (hconstant : ¬ S.IsConstantBase j) : S.beforeTauGenerators n :=
  ⟨ι (S.logBaseAnalytic j),
    S.logBase_mem_beforeTauGenerators_of_not_constant hjn hconstant⟩

@[simp]
theorem coe_beforeTauLogIndex {j n : Nat} (hjn : j ≤ n)
    (hconstant : ¬ S.IsConstantBase j) :
    ((S.beforeTauLogIndex hjn hconstant : S.beforeTauGenerators n) : K) =
      ι (S.logBaseAnalytic j) :=
  rfl

theorem beforeTauLogIndex_ne_coordinate {j n : Nat} (hjn : j ≤ n)
    (hconstant : ¬ S.IsConstantBase j)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (i : StageVar n) :
    S.beforeTauLogIndex hjn hconstant ≠
      (⟨S.finiteFractionCoordinates n i,
        S.finiteFractionCoordinate_mem_beforeTauGenerators n i⟩ :
          S.beforeTauGenerators n) := by
  intro heq
  have hval := congrArg Subtype.val heq
  exact S.logBase_ne_finiteFractionCoordinate_of_not_constant
    hjn hconstant htau hlog i hval

/-! ## Real polynomials in the pre-`tau` generator set -/

/-- A finite coordinate, regarded as an index in the actual pre-`tau`
generator set. -/
def beforeTauCoordinateIndex (n : Nat) (i : StageVar n) :
    S.beforeTauGenerators n :=
  ⟨S.finiteFractionCoordinates n i,
    S.finiteFractionCoordinate_mem_beforeTauGenerators n i⟩

@[simp]
theorem coe_beforeTauCoordinateIndex (n : Nat) (i : StageVar n) :
    ((S.beforeTauCoordinateIndex n i : S.beforeTauGenerators n) : K) =
      S.finiteFractionCoordinates n i :=
  rfl

/-- Map an integer stage polynomial to the real polynomial ring on the
pre-`tau` generator set. -/
def beforeTauStagePolynomial (n : Nat) (p : StagePolynomial n) :
    MvPolynomial (S.beforeTauGenerators n) Real :=
  rename (S.beforeTauCoordinateIndex n)
    (map (Int.castRingHom Real) p)

/-- Evaluation of the transported real polynomial is the original analytic
stage-polynomial evaluation. -/
theorem aeval_beforeTauStagePolynomial (n : Nat)
    (p : StagePolynomial n) :
    MvPolynomial.aeval
        ((↑) : S.beforeTauGenerators n → K)
        (S.beforeTauStagePolynomial n p) =
      S.stagePolynomialEval n p := by
  rw [beforeTauStagePolynomial, MvPolynomial.aeval_rename]
  change MvPolynomial.eval₂ (algebraMap Real K)
      (((↑) : S.beforeTauGenerators n → K) ∘
        S.beforeTauCoordinateIndex n)
      (map (Int.castRingHom Real) p) = S.stagePolynomialEval n p
  rw [MvPolynomial.eval₂_map]
  rw [show (algebraMap Real K).comp (Int.castRingHom Real) =
      Int.castRingHom K by
    ext z
    simp]
  change MvPolynomial.eval₂ (Int.castRingHom K)
      (((↑) : S.beforeTauGenerators n → K) ∘
        S.beforeTauCoordinateIndex n) p =
    MvPolynomial.eval₂ (Int.castRingHom K)
      (fun i ↦ ι (S.analyticAssignment n i)) p
  apply congrArg (fun assignment : StageVar n → K ↦
    MvPolynomial.eval₂ (Int.castRingHom K) assignment p)
  funext i
  exact S.finiteFractionCoordinates_eq_analyticAssignment n i

/-- The exponent presentation at index `j`, transported to the full stage
`n`. -/
def exponentPolynomialAtStage (n j : Nat) (hj : j ≤ n) :
    StagePolynomial n :=
  liftStagePolynomial (S.pair j).exponent.polynomial
    ((S.pair j).exponentStage_le.trans hj)

/-- The exponent monomial itself, transported to the common current stage. -/
def exponentMonomialAtStage (n j : Nat) (hj : j ≤ n) :
    NonconstantMonomial n :=
  (S.pair j).exponent.lift
    ((S.pair j).exponentStage_le.trans hj)

theorem exponentPolynomialAtStage_eq_monomialPolynomial
    (n j : Nat) (hj : j ≤ n) :
    S.exponentPolynomialAtStage n j hj =
      (S.exponentMonomialAtStage n j hj).polynomial := by
  simp [exponentPolynomialAtStage, exponentMonomialAtStage,
    liftStagePolynomial, NonconstantMonomial.polynomial,
    NonconstantMonomial.lift, MvPolynomial.rename_monomial]

theorem stagePolynomialEval_exponentPolynomialAtStage
    (n j : Nat) (hj : j ≤ n) :
    S.stagePolynomialEval n (S.exponentPolynomialAtStage n j hj) =
      ι (S.exponentAnalytic j) := by
  rw [exponentPolynomialAtStage, stagePolynomialEval_lift,
    stagePolynomialEval_eq_map_evalAnalytic]
  rfl

/-- The real pre-`tau` polynomial representing the substituted exponent at
index `j`. -/
def beforeTauExponentPolynomial (n j : Nat) (hj : j ≤ n) :
    MvPolynomial (S.beforeTauGenerators n) Real :=
  S.beforeTauStagePolynomial n (S.exponentPolynomialAtStage n j hj)

/-- The exponent vector of the transported exponent polynomial in the actual
pre-`tau` generator variables. -/
def beforeTauExponentVector (n j : Nat) (hj : j ≤ n) :
    S.beforeTauGenerators n →₀ Nat :=
  (S.exponentMonomialAtStage n j hj).exponents.mapDomain
    (S.beforeTauCoordinateIndex n)

theorem beforeTauExponentVector_ne_zero
    (n j : Nat) (hj : j ≤ n) :
    S.beforeTauExponentVector n j hj ≠ 0 := by
  intro hzero
  apply (S.exponentMonomialAtStage n j hj).nonzero
  exact (Finsupp.mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits
    (S.beforeTauCoordinateIndex n)
    (S.exponentMonomialAtStage n j hj).exponents).mp hzero

theorem beforeTauCoordinateIndex_injective {n : Nat}
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q))) :
    Function.Injective (S.beforeTauCoordinateIndex n) := by
  intro i j hij
  apply S.finiteFractionCoordinates_injective_of_tauTranscendence htau
  exact congrArg Subtype.val hij

/-- Equality of transported exponent vectors reflects to equality of the
original common-variable exponent polynomials. -/
theorem exponentGlobal_eq_of_beforeTauExponentVector_eq
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (heq : S.beforeTauExponentVector n i hin =
      S.beforeTauExponentVector n j hjn) :
    S.exponentGlobal i = S.exponentGlobal j := by
  have hexponents :
      (S.exponentMonomialAtStage n i hin).exponents =
        (S.exponentMonomialAtStage n j hjn).exponents :=
    (Finsupp.mapDomain_injective
      (S.beforeTauCoordinateIndex_injective htau)) heq
  calc
    S.exponentGlobal i =
        (S.exponentMonomialAtStage n i hin).toGlobal :=
      ((S.pair i).exponent.lift_toGlobal
        ((S.pair i).exponentStage_le.trans hin)).symm
    _ = (S.exponentMonomialAtStage n j hjn).toGlobal := by
      simp only [NonconstantMonomial.toGlobal,
        NonconstantMonomial.polynomial]
      rw [hexponents]
    _ = S.exponentGlobal j :=
      (S.pair j).exponent.lift_toGlobal
        ((S.pair j).exponentStage_le.trans hjn)

/-- A transported exponent monomial contains no logarithm variable. -/
theorem beforeTauExponentVector_apply_log_eq_zero
    {r j n : Nat} (hrn : r ≤ n) (hjn : j ≤ n)
    (hconstant : ¬ S.IsConstantBase r)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ s ≤ n, S.IsFreshBase s →
      Transcendental (S.finiteStageField s)
        (ι (S.logBaseAnalytic s))) :
    S.beforeTauExponentVector n j hjn
        (S.beforeTauLogIndex hrn hconstant) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨i, hi⟩
  exact S.beforeTauLogIndex_ne_coordinate hrn hconstant htau hlog i
    (by simpa [beforeTauCoordinateIndex] using hi.symm)

/-- A transported exponent monomial also contains no `log x` variable. -/
theorem beforeTauExponentVector_apply_logX_eq_zero
    {j n : Nat} (hjn : j ≤ n)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q))) :
    S.beforeTauExponentVector n j hjn
        (⟨OneVariableBaseField.logX,
          S.logX_mem_beforeTauGenerators n⟩ :
            S.beforeTauGenerators n) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨i, hi⟩
  apply S.logX_ne_finiteFractionCoordinate htau i
  exact congrArg Subtype.val hi.symm

/-- The monomial exponent vector for
`exponent_j * log(base_j)` when the base is nonconstant. -/
def beforeTauTaggedExponentVector {j n : Nat} (hjn : j ≤ n)
    (hconstant : ¬ S.IsConstantBase j) :
    S.beforeTauGenerators n →₀ Nat :=
  S.beforeTauExponentVector n j hjn +
    Finsupp.single (S.beforeTauLogIndex hjn hconstant) 1

/-- Equality of two tagged exponent/logarithm monomials separates into
equality of their logarithm variables and equality of their exponent
vectors. -/
theorem eq_logIndex_and_exponentVector_of_taggedExponentVector_eq
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hiConstant : ¬ S.IsConstantBase i)
    (hjConstant : ¬ S.IsConstantBase j)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (heq : S.beforeTauTaggedExponentVector hin hiConstant =
      S.beforeTauTaggedExponentVector hjn hjConstant) :
    S.beforeTauLogIndex hin hiConstant =
        S.beforeTauLogIndex hjn hjConstant ∧
      S.beforeTauExponentVector n i hin =
        S.beforeTauExponentVector n j hjn := by
  have hindex : S.beforeTauLogIndex hin hiConstant =
      S.beforeTauLogIndex hjn hjConstant := by
    by_contra hne
    have hvalue := congrArg
      (fun v : S.beforeTauGenerators n →₀ Nat ↦
        v (S.beforeTauLogIndex hin hiConstant)) heq
    have hii := S.beforeTauExponentVector_apply_log_eq_zero
      hin hin hiConstant htau hlog
    have hji := S.beforeTauExponentVector_apply_log_eq_zero
      hin hjn hiConstant htau hlog
    simp [beforeTauTaggedExponentVector, hii, hji, hne] at hvalue
  refine ⟨hindex, ?_⟩
  change S.beforeTauExponentVector n i hin +
      Finsupp.single (S.beforeTauLogIndex hin hiConstant) 1 =
    S.beforeTauExponentVector n j hjn +
      Finsupp.single (S.beforeTauLogIndex hjn hjConstant) 1 at heq
  rw [hindex] at heq
  exact add_right_cancel heq

/-- A match of tagged monomials gives the two literal W1 data equalities
needed for the no-repeated-pair axiom. -/
theorem baseGlobal_eq_and_exponentGlobal_eq_of_taggedExponentVector_eq
    {i j n : Nat} (hin : i ≤ n) (hjn : j ≤ n)
    (hiConstant : ¬ S.IsConstantBase i)
    (hjConstant : ¬ S.IsConstantBase j)
    (htau : ∀ q < n,
      Transcendental (S.finiteStageBeforeTau q)
        (ι (S.realTauAnalyticFunction q)))
    (hlog : ∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r)))
    (hcoord : AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r)))
    (heq : S.beforeTauTaggedExponentVector hin hiConstant =
      S.beforeTauTaggedExponentVector hjn hjConstant) :
    S.baseGlobal i = S.baseGlobal j ∧
      S.exponentGlobal i = S.exponentGlobal j := by
  obtain ⟨hindex, hexponents⟩ :=
    S.eq_logIndex_and_exponentVector_of_taggedExponentVector_eq
      hin hjn hiConstant hjConstant htau hlog heq
  have hlogeq : ι (S.logBaseAnalytic i) =
      ι (S.logBaseAnalytic j) :=
    congrArg Subtype.val hindex
  exact ⟨S.baseGlobal_eq_of_logBaseFraction_eq hin hjn hcoord hlogeq,
    S.exponentGlobal_eq_of_beforeTauExponentVector_eq hin hjn htau
      hexponents⟩

/-- Transport preserves the literal coefficient-one monomial shape. -/
theorem beforeTauExponentPolynomial_eq_monomial
    (n j : Nat) (hj : j ≤ n) :
    S.beforeTauExponentPolynomial n j hj =
      MvPolynomial.monomial (S.beforeTauExponentVector n j hj) 1 := by
  rw [beforeTauExponentPolynomial,
    S.exponentPolynomialAtStage_eq_monomialPolynomial]
  simp [beforeTauStagePolynomial, beforeTauExponentVector,
    NonconstantMonomial.polynomial, MvPolynomial.rename_monomial]

theorem aeval_beforeTauExponentPolynomial
    (n j : Nat) (hj : j ≤ n) :
    MvPolynomial.aeval
        ((↑) : S.beforeTauGenerators n → K)
        (S.beforeTauExponentPolynomial n j hj) =
      ι (S.exponentAnalytic j) := by
  rw [beforeTauExponentPolynomial, aeval_beforeTauStagePolynomial,
    stagePolynomialEval_exponentPolynomialAtStage]

end GeneratorSequence

end

end Natfunbasis.Wilkie
