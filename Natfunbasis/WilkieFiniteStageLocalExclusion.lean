import Natfunbasis.WilkieFiniteStageInduction

/-!
# Finite-stage induction from a stage-local coefficient exclusion

The coefficient proof excluding the primitive relation uses the already
established transcendence of earlier power generators and fresh logarithms.
This file gives the correctly dependent strong-induction interface, avoiding
an artificially unconditional exclusion premise.
-/

namespace Natfunbasis.Wilkie

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- At stage `n`, prior power transcendence, all fresh-log transcendences up
to `n`, and the two current algebraic-independence invariants suffice to
exclude the sole primitive relation forced by algebraicity of `tau_n`. -/
def LocalTauPrimitiveRelationExclusionInput : Prop :=
  ∀ n,
    (∀ j < n,
      Transcendental (S.finiteStageBeforeTau j)
        (ι (S.realTauAnalyticFunction j))) →
    (∀ r ≤ n, S.IsFreshBase r →
      Transcendental (S.finiteStageField r)
        (ι (S.logBaseAnalytic r))) →
    AlgebraicIndepOn Real id (S.stageGenerators n) →
    AlgebraicIndepOn Real id (S.beforeTauGenerators n) →
    S.TauPrimitiveRelationExclusion n

/-- Wilkie's complete simultaneous finite-stage induction from the genuine
stage-local coefficient-exclusion theorem. -/
theorem finiteStageInduction_of_localTauPrimitiveRelationExclusion
    (hrigid : S.FreshStageIntegralSlopeRigidity)
    (hexclude : S.LocalTauPrimitiveRelationExclusionInput) :
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
      have hcurrentLog : S.IsFreshBase n →
          Transcendental (S.finiteStageField n)
            (ι (S.logBaseAnalytic n)) := by
        intro hfresh
        exact S.freshLog_transcendental_of_stage_induction
          hfresh hpriorTau hstage.1 hstage.2
      have hlogs : ∀ r ≤ n, S.IsFreshBase r →
          Transcendental (S.finiteStageField r)
            (ι (S.logBaseAnalytic r)) := by
        intro r hrn hrfresh
        rcases hrn.eq_or_lt with rfl | hrn
        · exact hcurrentLog hrfresh
        · exact (ih r hrn).freshLogTranscendental hrfresh
      have hbeforeAI :
          AlgebraicIndepOn Real id (S.beforeTauGenerators n) :=
        S.algebraicIndepOn_beforeTauGenerators hstage.1 hcurrentLog
      have hbeforeII : S.BeforeTauLogDerivClassification n := by
        by_cases hfresh : S.IsFreshBase n
        · exact S.beforeTauLogDerivClassification_of_fresh
            hfresh (hcurrentLog hfresh) (hrigid n hfresh) hstage.2
        · exact S.beforeTauLogDerivClassification_of_not_fresh
            hfresh hstage.2
      have htau : Transcendental (S.finiteStageBeforeTau n)
          (ι (S.realTauAnalyticFunction n)) :=
        S.tau_transcendental_of_primitiveRelationExclusion hbeforeII
          (hexclude n hpriorTau hlogs hstage.1 hbeforeAI)
      exact S.finiteStageInductionStep hpriorTau (hrigid n) htau
        hstage.1 hstage.2

end GeneratorSequence

end

end Natfunbasis.Wilkie
