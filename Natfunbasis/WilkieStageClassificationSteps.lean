import Natfunbasis.WilkieClassificationExtensions

/-!
# The two concrete steps in Wilkie's logarithmic-derivative induction

This file specializes the generic adjunction lemmas to the recursively
constructed finite-stage fields.  A fresh logarithm is handled by the valid
integral-slope form of Proposition 3.1(ii), and the subsequent power
generator is handled by Proposition 3.1(i).
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

private theorem baseAnalytic_ne_zero (n : Nat) :
    ι (S.baseAnalytic n) ≠ 0 := by
  have hbaseA : S.baseAnalytic n ≠ 0 := by
    intro hzero
    have hpos := S.baseAnalytic_pos n ⟨1, zero_lt_one⟩
    rw [hzero] at hpos
    simp at hpos
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hbaseA)

/-- In the nonfresh case the pre-`tau` field is the old stage, so clause
`(II)` passes to it without an adjunction. -/
theorem beforeTauLogDerivClassification_of_not_fresh {n : Nat}
    (hfresh : ¬ S.IsFreshBase n)
    (hstage : S.StageLogDerivClassification n) :
    S.BeforeTauLogDerivClassification n := by
  rw [BeforeTauLogDerivClassification, finiteStageBeforeTau,
    DifferentialStage.beforeTau, dif_neg hfresh]
  intro X Y hX0 heq
  apply (S.beforeTauMonomial_iff_of_not_fresh hfresh).2
  exact hstage X Y hX0 heq

/-- The fresh-logarithm half-step in the concrete finite-stage tower.

The explicit `IntegralSlopeRigidity` hypothesis is the additional
stage-specific input needed by the mathematically valid form of Wilkie
Proposition 3.1(ii). -/
theorem beforeTauLogDerivClassification_of_fresh {n : Nat}
    (hfresh : S.IsFreshBase n)
    (hlog : Transcendental (S.finiteStageField n)
      (ι (S.logBaseAnalytic n)))
    (hrigid : Proposition31II.IntegralSlopeRigidity
      (⟨ι (S.baseAnalytic n),
        S.baseAnalytic_mem_finiteStageField n⟩ :
          S.finiteStageField n))
    (hstage : S.StageLogDerivClassification n) :
    S.BeforeTauLogDerivClassification n := by
  let beta : S.finiteStageField n :=
    ⟨ι (S.baseAnalytic n), S.baseAnalytic_mem_finiteStageField n⟩
  let z : K := ι (S.logBaseAnalytic n)
  have hbeta : beta ≠ 0 := by
    intro hzero
    apply S.baseAnalytic_ne_zero n
    exact congrArg Subtype.val hzero
  have hzd : z′ =
      algebraMap (S.finiteStageField n) K (beta′ / beta) := by
    change PositiveAnalyticFractionField.derivation
        (ι (S.logBaseAnalytic n)) =
      PositiveAnalyticFractionField.derivation
          (ι (S.baseAnalytic n)) /
        ι (S.baseAnalytic n)
    exact PositiveAnalyticFractionField.derivation_logBaseAnalytic S n
  have hgenerator : ∀ x ∈ ({z} : Set K),
      x′ ∈ IntermediateField.adjoin (S.finiteStageField n) {z} := by
    intro x hx
    have hxz : x = z := by simpa using hx
    subst x
    rw [hzd]
    exact IntermediateField.algebraMap_mem _ (beta′ / beta)
  have hclassification :=
    logDerivClassification_adjoin_logarithm
      (S.finiteStageField n)
      (S.StageMonomial n) (S.BeforeTauMonomial n)
      beta hbeta hrigid z hlog hzd hgenerator hstage
      (fun m {u} hu ↦ by
        have hcoe : (((beta ^ m : S.finiteStageField n) : K)) =
            ι (S.baseAnalytic n) ^ m := by
          rfl
        rw [hcoe]
        exact S.beforeTauMonomial_mul_base_zpow hfresh hu m)
  have hfield : S.finiteStageBeforeTau n =
      (S.finiteStageField n).adjoinOver {z} hgenerator := by
    unfold finiteStageBeforeTau
    rw [DifferentialStage.beforeTau, dif_pos hfresh]
    rfl
  rw [BeforeTauLogDerivClassification, hfield]
  exact hclassification

/-- The exponential/power half-step in the concrete finite-stage tower.
This is the exact use of Wilkie Proposition 3.1(i) in the induction. -/
theorem stageLogDerivClassification_succ {n : Nat}
    (htau : Transcendental (S.finiteStageBeforeTau n)
      (ι (S.realTauAnalyticFunction n)))
    (hbefore : S.BeforeTauLogDerivClassification n) :
    S.StageLogDerivClassification (n + 1) := by
  let z : K := ι (S.realTauAnalyticFunction n)
  have hzd : z′ =
      algebraMap (S.finiteStageBeforeTau n) K
          ((S.tauPrimitive n)′) * z := by
    exact S.deriv_tau_eq_tauPrimitive_deriv_mul n
  have hgenerator : ∀ x ∈ ({z} : Set K),
      x′ ∈ IntermediateField.adjoin (S.finiteStageBeforeTau n) {z} := by
    intro x hx
    have hxz : x = z := by simpa using hx
    subst x
    rw [hzd]
    exact mul_mem
      (IntermediateField.algebraMap_mem _ ((S.tauPrimitive n)′))
      (IntermediateField.subset_adjoin _ _ (by simp))
  have hclassification :=
    logDerivClassification_adjoin_exponential
      (S.finiteStageBeforeTau n)
      (S.BeforeTauMonomial n) (S.StageMonomial (n + 1))
      (S.tauPrimitive n) z htau hzd hgenerator hbefore
      (fun m {u} hu ↦ S.stageMonomial_succ_mul_tau_zpow hu m)
  have hfield : S.finiteStageField (n + 1) =
      (S.finiteStageBeforeTau n).adjoinOver {z} hgenerator := by
    unfold finiteStageField finiteStageBeforeTau
    rw [differentialStage]
    rfl
  rw [StageLogDerivClassification, hfield]
  exact hclassification

end GeneratorSequence

end

end Natfunbasis.Wilkie
