import Natfunbasis.WilkieConstantTauCoefficient
import Natfunbasis.WilkieNonconstantTauPrimitiveExclusion
import Natfunbasis.WilkieFiniteStageLocalExclusion
import Natfunbasis.WilkieInfiniteIndependence

/-!
# Closing the tau coefficient-comparison half of Wilkie's induction

The constant-base branch uses independence of logarithms of natural primes;
the nonconstant branch uses the tagged-monomial coefficient and W1.3.  Their
combination supplies the exact local exclusion input, so the only remaining
premise of the finite-stage induction is fresh-stage integral-slope rigidity.
-/

namespace Natfunbasis.Wilkie

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The two coefficient arguments together give the genuine stage-local
primitive-relation exclusion input. -/
theorem localTauPrimitiveRelationExclusion :
    S.LocalTauPrimitiveRelationExclusionInput := by
  intro n hpriorTau hlog _hstage hbefore
  by_cases hconstant : S.IsConstantBase n
  · exact S.tauPrimitiveRelationExclusion_of_constant
      hconstant hpriorTau hlog hbefore
  · exact S.tauPrimitiveRelationExclusion_of_not_constant
      hconstant hpriorTau hlog hbefore

/-- All finite-stage transcendence, algebraic-independence, and
logarithmic-derivative classification statements now follow from the sole
fresh-stage integral-slope rigidity premise. -/
theorem finiteStageInduction_of_freshStageIntegralSlopeRigidity
    (hrigid : S.FreshStageIntegralSlopeRigidity) :
    ∀ n, S.FiniteStageInductionResult n :=
  S.finiteStageInduction_of_localTauPrimitiveRelationExclusion
    hrigid S.localTauPrimitiveRelationExclusion

end GeneratorSequence

/-- For the canonical generator sequence, fresh-stage integral-slope
rigidity alone now implies the exact Wilkie independence proposition used by
the normalizer. -/
theorem canonicalWilkieIndependence_of_freshStageIntegralSlopeRigidity
    (hrigid : canonicalGeneratorSequence.FreshStageIntegralSlopeRigidity) :
    CanonicalWilkieIndependence := by
  let R := canonicalGeneratorSequence
    |>.finiteStageInduction_of_freshStageIntegralSlopeRigidity hrigid
  have htau : ∀ n,
      Transcendental
        (canonicalGeneratorSequence.finiteStageBeforeTau n)
        (ι (canonicalGeneratorSequence.realTauAnalyticFunction n)) :=
    fun n ↦ (R n).tauTranscendental
  apply canonicalWilkieIndependence_of_stage
  · exact canonicalGeneratorSequence
      |>.analyticFractionCoordinates_injective_of_tauTranscendence htau
  · exact fun n ↦ (R n).stageAlgebraicIndependent

end

end Natfunbasis.Wilkie
