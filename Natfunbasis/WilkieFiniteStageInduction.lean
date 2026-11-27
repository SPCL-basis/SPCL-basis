import Natfunbasis.WilkieStageZeroClassification
import Natfunbasis.WilkieFreshBaseExclusion
import Natfunbasis.WilkieStageClassificationSteps
import Natfunbasis.WilkieStageAlgebraicIndependence
import Natfunbasis.WilkieMonomialPrimitives

/-!
# Assembly of Wilkie's finite-stage induction

This file wires together the two simultaneous induction invariants:
algebraic independence of the finite generator set and classification of
logarithmic derivatives.  It records the exact remaining local inputs.

There are two entry points.  The first accepts transcendence of each power
generator directly.  The second accepts only exclusion of the structured
primitive relation forced by algebraicity; Proposition 3.2(i) and the
logarithmic-derivative classification then supply power-generator
transcendence during the induction.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The stage-specific rigidity premise required only at a fresh logarithmic
adjunction. -/
def FreshStageIntegralSlopeRigidity : Prop :=
  ∀ n, S.IsFreshBase n →
    Proposition31II.IntegralSlopeRigidity
      (⟨ι (S.baseAnalytic n), S.baseAnalytic_mem_finiteStageField n⟩ :
        S.finiteStageField n)

/-- The direct unresolved input asserting transcendence of every power
generator over the field immediately before it is adjoined. -/
def TauTranscendenceInput : Prop :=
  ∀ n, Transcendental (S.finiteStageBeforeTau n)
    (ι (S.realTauAnalyticFunction n))

/-- The exact structured relation whose exclusion suffices for power-generator
transcendence.  This is the remaining coefficient-comparison/W1.3 input after
Proposition 3.2(i) and the preceding-stage classification have been applied. -/
def TauPrimitiveRelationExclusion (n : Nat) : Prop :=
  ∀ (m : Int), m ≠ 0 → ∀ (L : K), S.BeforeTauPrimitive n L →
    ∀ c : Real,
      (m : K) * (S.tauPrimitive n : K) ≠ algebraMap Real K c + L

/-- A complete local handoff at stage `n`.  In addition to the two induction
invariants at `n`, it contains everything derived at the logarithmic half-step
and both invariants after adjoining the power generator. -/
structure FiniteStageInductionResult (n : Nat) : Prop where
  stageAlgebraicIndependent :
    AlgebraicIndepOn Real id (S.stageGenerators n)
  stageLogDerivClassification : S.StageLogDerivClassification n
  freshLogTranscendental :
    S.IsFreshBase n →
      Transcendental (S.finiteStageField n)
        (ι (S.logBaseAnalytic n))
  beforeTauAlgebraicIndependent :
    AlgebraicIndepOn Real id (S.beforeTauGenerators n)
  beforeTauLogDerivClassification :
    S.BeforeTauLogDerivClassification n
  tauTranscendental :
    Transcendental (S.finiteStageBeforeTau n)
      (ι (S.realTauAnalyticFunction n))
  successorStageAlgebraicIndependent :
    AlgebraicIndepOn Real id (S.stageGenerators (n + 1))
  successorStageLogDerivClassification :
    S.StageLogDerivClassification (n + 1)

/-- Excluding the primitive relation forced by algebraicity turns the local
pre-`tau` classification into transcendence of `tau_n`. -/
theorem tau_transcendental_of_primitiveRelationExclusion {n : Nat}
    (hbefore : S.BeforeTauLogDerivClassification n)
    (hexclude : S.TauPrimitiveRelationExclusion n) :
    Transcendental (S.finiteStageBeforeTau n)
      (ι (S.realTauAnalyticFunction n)) := by
  intro halgebraic
  obtain ⟨m, hm, L, hL, c, hrelation⟩ :=
    S.tau_algebraic_implies_primitive_relation hbefore halgebraic
  exact hexclude m hm L hL c hrelation

/-- One simultaneous local induction step.  The hypotheses are precisely the
two invariants at stage `n`, all earlier power transcendences needed for the
fresh-base exclusion, fresh-stage rigidity, and the current power
transcendence. -/
theorem finiteStageInductionStep {n : Nat}
    (hpriorTau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j)
        (ι (S.realTauAnalyticFunction j)))
    (hrigid : S.IsFreshBase n →
      Proposition31II.IntegralSlopeRigidity
        (⟨ι (S.baseAnalytic n),
          S.baseAnalytic_mem_finiteStageField n⟩ :
            S.finiteStageField n))
    (htau : Transcendental (S.finiteStageBeforeTau n)
      (ι (S.realTauAnalyticFunction n)))
    (hstageAI : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hstageII : S.StageLogDerivClassification n) :
    S.FiniteStageInductionResult n := by
  have hlog : S.IsFreshBase n →
      Transcendental (S.finiteStageField n)
        (ι (S.logBaseAnalytic n)) := by
    intro hfresh
    exact S.freshLog_transcendental_of_stage_induction
      hfresh hpriorTau hstageAI hstageII
  have hbeforeAI :
      AlgebraicIndepOn Real id (S.beforeTauGenerators n) :=
    S.algebraicIndepOn_beforeTauGenerators hstageAI hlog
  have hbeforeII : S.BeforeTauLogDerivClassification n := by
    by_cases hfresh : S.IsFreshBase n
    · exact S.beforeTauLogDerivClassification_of_fresh
        hfresh (hlog hfresh) (hrigid hfresh) hstageII
    · exact S.beforeTauLogDerivClassification_of_not_fresh hfresh hstageII
  have hsuccAI :
      AlgebraicIndepOn Real id (S.stageGenerators (n + 1)) :=
    S.algebraicIndepOn_stageGenerators_succ hstageAI hlog htau
  have hsuccII : S.StageLogDerivClassification (n + 1) :=
    S.stageLogDerivClassification_succ htau hbeforeII
  exact
    { stageAlgebraicIndependent := hstageAI
      stageLogDerivClassification := hstageII
      freshLogTranscendental := hlog
      beforeTauAlgebraicIndependent := hbeforeAI
      beforeTauLogDerivClassification := hbeforeII
      tauTranscendental := htau
      successorStageAlgebraicIndependent := hsuccAI
      successorStageLogDerivClassification := hsuccII }

/-- The complete simultaneous finite-stage induction from directly supplied
power-generator transcendence. -/
theorem finiteStageInduction_of_tauTranscendence
    (hrigid : S.FreshStageIntegralSlopeRigidity)
    (htau : S.TauTranscendenceInput) :
    ∀ n, S.FiniteStageInductionResult n := by
  have hcore : ∀ n,
      AlgebraicIndepOn Real id (S.stageGenerators n) ∧
        S.StageLogDerivClassification n := by
    intro n
    induction n with
    | zero =>
        exact ⟨S.algebraicIndepOn_stageGenerators_zero,
          S.stageLogDerivClassification_zero⟩
    | succ n ih =>
        have hstep := S.finiteStageInductionStep
          (fun j _hj ↦ htau j) (hrigid n) (htau n) ih.1 ih.2
        exact ⟨hstep.successorStageAlgebraicIndependent,
          hstep.successorStageLogDerivClassification⟩
  intro n
  exact S.finiteStageInductionStep
    (fun j _hj ↦ htau j) (hrigid n) (htau n)
    (hcore n).1 (hcore n).2

/-- The strongest assembled form: local exclusion of the sole structured
primitive relation yields, simultaneously at every stage, fresh-logarithm
transcendence, both pre-`tau` invariants, power-generator transcendence, and
both successor-stage invariants. -/
theorem finiteStageInduction_of_tauPrimitiveRelationExclusion
    (hrigid : S.FreshStageIntegralSlopeRigidity)
    (hexclude : ∀ n, S.TauPrimitiveRelationExclusion n) :
    ∀ n, S.FiniteStageInductionResult n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hstage :
          AlgebraicIndepOn Real id (S.stageGenerators n) ∧
            S.StageLogDerivClassification n := by
        cases n with
        | zero =>
            exact ⟨S.algebraicIndepOn_stageGenerators_zero,
              S.stageLogDerivClassification_zero⟩
        | succ k =>
            have hk := ih k (Nat.lt_succ_self k)
            exact ⟨hk.successorStageAlgebraicIndependent,
              hk.successorStageLogDerivClassification⟩
      have hpriorTau : ∀ j < n,
          Transcendental (S.finiteStageBeforeTau j)
            (ι (S.realTauAnalyticFunction j)) := by
        intro j hj
        exact (ih j hj).tauTranscendental
      have hlog : S.IsFreshBase n →
          Transcendental (S.finiteStageField n)
            (ι (S.logBaseAnalytic n)) := by
        intro hfresh
        exact S.freshLog_transcendental_of_stage_induction
          hfresh hpriorTau hstage.1 hstage.2
      have hbeforeAI :
          AlgebraicIndepOn Real id (S.beforeTauGenerators n) :=
        S.algebraicIndepOn_beforeTauGenerators hstage.1 hlog
      have hbeforeII : S.BeforeTauLogDerivClassification n := by
        by_cases hfresh : S.IsFreshBase n
        · exact S.beforeTauLogDerivClassification_of_fresh
            hfresh (hlog hfresh) (hrigid n hfresh) hstage.2
        · exact S.beforeTauLogDerivClassification_of_not_fresh
            hfresh hstage.2
      have htau : Transcendental (S.finiteStageBeforeTau n)
          (ι (S.realTauAnalyticFunction n)) :=
        S.tau_transcendental_of_primitiveRelationExclusion
          hbeforeII (hexclude n)
      exact S.finiteStageInductionStep hpriorTau (hrigid n) htau
        hstage.1 hstage.2

end GeneratorSequence

end

end Natfunbasis.Wilkie
