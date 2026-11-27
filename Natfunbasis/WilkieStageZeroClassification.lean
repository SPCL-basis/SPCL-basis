import Natfunbasis.WilkieBaseFieldClassification
import Natfunbasis.WilkieBaseLogRigidity
import Natfunbasis.WilkieStageClassification

/-!
# The stage-zero logarithmic-derivative invariant

This file combines the rational residue calculation over `Real(x)` with the
classification in `F0 = Real(x, log x)`.  It supplies the concrete base case
`(II)₀` for every generator sequence.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "K" => PositiveAnalyticFractionField

namespace BaseFieldClassification

/-- The two independently packaged differential copies of `Real(x)` have
the same carrier. -/
theorem realXField_eq_analyticXField :
    realXField = BaseLogRigidity.analyticXField := by
  apply DifferentialIntermediateField.ext
  intro y
  rfl

/-- The residue theorem supplies the explicit rigidity premise used by the
base-field classification. -/
theorem realX_integralSlopeRigidity : RealXIntegralSlopeRigidity := by
  intro a u v ha hu0 hu
  let lift (y : realXField) : BaseLogRigidity.analyticXField :=
    ⟨(y : K), by
      simpa [realXField, BaseLogRigidity.analyticXField] using y.2⟩
  have haLift : (lift a)′ = 0 := by
    apply Subtype.ext
    exact congrArg Subtype.val ha
  have huLift0 : lift u ≠ 0 := by
    intro hzero
    apply hu0
    apply Subtype.ext
    exact congrArg Subtype.val hzero
  have coeMul (p q : BaseLogRigidity.analyticXField) :
      (((p * q : BaseLogRigidity.analyticXField) : K)) =
        (p : K) * (q : K) := rfl
  have coeAdd (p q : BaseLogRigidity.analyticXField) :
      (((p + q : BaseLogRigidity.analyticXField) : K)) =
        (p : K) + (q : K) := rfl
  rw [deriv_xGen] at hu
  have huLift :
      (lift u)′ =
        (lift a *
          (BaseLogRigidity.analyticXCoordinate′ /
            BaseLogRigidity.analyticXCoordinate) + (lift v)′) * lift u := by
    rw [BaseLogRigidity.deriv_analyticXCoordinate]
    apply Subtype.ext
    have h := congrArg Subtype.val hu
    simp only [DifferentialIntermediateField.coe_deriv, coeMul, coeAdd,
      one_div] at h ⊢
    dsimp only [lift]
    change ((u : K))′ =
      ((a : K) * OneVariableBaseField.x⁻¹ + ((v : K))′) * (u : K)
    change ((u : K))′ =
      ((a : K) * OneVariableBaseField.x⁻¹ + ((v : K))′) * (u : K) at h
    exact h
  obtain ⟨m, hm⟩ :=
    BaseLogRigidity.analyticX_integralSlopeRigidity
      (lift a) (lift u) (lift v) haLift huLift0 huLift
  refine ⟨m, ?_⟩
  apply Subtype.ext
  simpa [lift] using congrArg Subtype.val hm

end BaseFieldClassification

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Wilkie's logarithmic-derivative classification at the initial field
`F0 = Real(x, log x)`. -/
theorem stageLogDerivClassification_zero :
    S.StageLogDerivClassification 0 := by
  change ∀ (X Y : OneVariableBaseField.F0), (X : K) ≠ 0 →
    ((X : K))′ = ((Y : K))′ * (X : K) → S.StageMonomial 0 (X : K)
  intro X Y hX0 heq
  have hX0' : X ≠ 0 := by
    intro hzero
    apply hX0
    exact congrArg Subtype.val hzero
  have heq' : X′ = Y′ * X := by
    apply Subtype.ext
    exact heq
  obtain ⟨m, c, d, hc0, hX, _hY⟩ :=
    BaseFieldClassification.F0_solution_classification_of_integralSlopeRigidity
      BaseFieldClassification.realX_integralSlopeRigidity X Y hX0' heq'
  exact ⟨c, hc0, m, hX⟩

end GeneratorSequence

end

end Natfunbasis.Wilkie
