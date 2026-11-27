import Natfunbasis.WilkieProposition31II
import Natfunbasis.WilkieOneVariableBaseField

/-!
# Logarithmic-derivative classification in the base field `Real(x)`

For the ordinary translation derivation `x′ = 1`, a nonzero rational
function cannot have the derivative of another rational function as its
logarithmic derivative unless both functions are constant.  This file proves
that seed classification first in exact rational coordinates, then transports
it to a concrete transcendental simple extension and finally to the analytic
coordinate used by Wilkie's one-variable induction.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.BaseRationalClassification

noncomputable section

/-! ## A generic zero-derivation coefficient field -/

variable {K L : Type*} [Field K] [CharZero K] [Field L]
  [Differential K] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L] [Differential.ContainConstants K L]

/-- Coordinate classification over a coefficient field on which the
derivation is zero.  The nonzero translation speed excludes the affine slope
left by the general primitive-adjunction calculation. -/
theorem rationalFunction_constant_of_zeroDerivation_translation
    (hzero : ∀ a : K, a′ = 0)
    (c : K) (hc : c ≠ 0)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L c)
    {p q r s : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q) * s ^ 2 =
        (Differential.implicitDeriv (C c) r * s -
          r * Differential.implicitDeriv (C c) s) * p * q) :
    ∃ u v : K, u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q = RatFunc.C u ∧
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s = RatFunc.C v := by
  have hprimitive : ∃ y : K[X],
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        algebraMap K[X] (RatFunc K) y ∧
      Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q =
        Differential.implicitDeriv (C c) y * p * q := by
    by_cases hr0 : r = 0
    · have hAsq :
          (Differential.implicitDeriv (C c) p * q -
              p * Differential.implicitDeriv (C c) q) * s ^ 2 = 0 := by
        simpa [hr0] using heq
      have hA :
          Differential.implicitDeriv (C c) p * q -
              p * Differential.implicitDeriv (C c) q = 0 :=
        (mul_eq_zero.mp hAsq).resolve_right (pow_ne_zero 2 hs0)
      refine ⟨0, ?_, ?_⟩
      · simp [hr0]
      · simpa using hA
    · have hsunit : IsUnit s :=
        Proposition31II.denominator_isUnit_of_translation_logEquation
          c z hz hzd hp0 hq0 hr0 hs0 hpq hrs heq
      exact Proposition31II.exists_polynomial_primitive_of_translation_logEquation
        c hsunit heq
  obtain ⟨y, hYpoly, hcross⟩ := hprimitive
  obtain ⟨a, u, v, _hazero, hu0, hX, hy, hu⟩ :=
    Proposition31II.rationalFunction_affine_of_polynomial_logEquation
      c z hz hzd hp0 hq0 hpq hcross
  have hac : a * c = 0 := by
    have hu' := hu
    rw [hzero u, hzero v] at hu'
    simp only [add_zero] at hu'
    exact (mul_eq_zero.mp hu'.symm).resolve_right hu0
  have ha : a = 0 := (mul_eq_zero.mp hac).resolve_right hc
  have hyconst : y = C v := by
    simpa [ha] using hy
  have hyrat := congrArg (algebraMap K[X] (RatFunc K)) hyconst
  refine ⟨u, v, hu0, hX, ?_⟩
  rw [hYpoly]
  simpa [RatFunc.algebraMap_C] using hyrat

/-- Element-level transport of the zero-derivation classification to a
concrete transcendental simple extension. -/
theorem simpleExtension_constant_of_zeroDerivation_translation
    (hzero : ∀ a : K, a′ = 0)
    (c : K) (hc : c ≠ 0)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L c)
    (U V : RatFunc K) (hU0 : U ≠ 0)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (Proposition31.evalAtTranscendental z hz V)′ *
        Proposition31.evalAtTranscendental z hz U) :
    ∃ u v : K, u ≠ 0 ∧
      Proposition31.evalAtTranscendental z hz U = algebraMap K L u ∧
      Proposition31.evalAtTranscendental z hz V = algebraMap K L v := by
  have hzdPolynomial : z′ = Polynomial.aeval z (C c) := by
    simpa using hzd
  have hcleared := Proposition31.clearedEquation_of_evalAtTranscendental
    z hz (C c) hzdPolynomial U V heq
  obtain ⟨u, v, hu0, hU, hV⟩ :=
    rationalFunction_constant_of_zeroDerivation_translation
      hzero c hc z hz hzd
      (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
      U.isCoprime_num_denom V.isCoprime_num_denom hcleared
  refine ⟨u, v, hu0, ?_, ?_⟩
  · have h := congrArg (Proposition31.evalAtTranscendental z hz) hU
    simpa [RatFunc.num_div_denom] using h
  · have h := congrArg (Proposition31.evalAtTranscendental z hz) hV
    simpa [RatFunc.num_div_denom] using h

/-- Subtype-valued form for the actual simple intermediate field `K(z)`. -/
theorem simpleAdjoin_constant_of_zeroDerivation_translation
    (hzero : ∀ a : K, a′ = 0)
    (c : K) (hc : c ≠ 0)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L c)
    (X Y : IntermediateField.adjoin K {z})
    (hX0 : (X : L) ≠ 0)
    (heq : ((X : L))′ = ((Y : L))′ * (X : L)) :
    ∃ u v : K, u ≠ 0 ∧
      (X : L) = algebraMap K L u ∧
      (Y : L) = algebraMap K L v := by
  let e := RatFunc.algEquivOfTranscendental z hz
  let U : RatFunc K := e.symm X
  let V : RatFunc K := e.symm Y
  have hU : Proposition31.evalAtTranscendental z hz U = (X : L) := by
    simp [Proposition31.evalAtTranscendental, U, e]
  have hV : Proposition31.evalAtTranscendental z hz V = (Y : L) := by
    simp [Proposition31.evalAtTranscendental, V, e]
  have hU0 : U ≠ 0 := by
    intro hzeroU
    apply hX0
    rw [← hU, hzeroU, map_zero]
  obtain ⟨u, v, hu0, hXu, hYv⟩ :=
    simpleExtension_constant_of_zeroDerivation_translation
      hzero c hc z hz hzd U V hU0 (by simpa [hU, hV] using heq)
  exact ⟨u, v, hu0, hU.symm.trans hXu, hV.symm.trans hYv⟩

/-! ## The real coefficient field and the analytic coordinate -/

/-- The canonical zero differential structure on the real coefficient
field. -/
instance realZeroDifferential : Differential Real where
  deriv := 0

@[simp]
theorem deriv_real_eq_zero (a : Real) : a′ = 0 :=
  rfl

/-- Embedded real constants differentiate to zero in the analytic fraction
field, so its inclusion is a differential algebra for the zero derivation. -/
instance realDifferentialAlgebraAnalyticFraction :
    DifferentialAlgebra Real PositiveAnalyticFractionField where
  deriv_algebraMap a := by
    rw [deriv_real_eq_zero, map_zero]
    change PositiveAnalyticFractionField.derivation
      (algebraMap Real PositiveAnalyticFractionField a) = 0
    exact PositiveAnalyticFractionField.derivation_algebraMap_real a

/-- Exact rational-coordinate seed classification for `Real(T)` with
`T′ = 1`. -/
theorem realRationalFunction_classification_of_clearedEquation
    (U V : RatFunc Real) (hU0 : U ≠ 0)
    (hcleared :
      (Differential.implicitDeriv (C 1) U.num * U.denom -
          U.num * Differential.implicitDeriv (C 1) U.denom) * V.denom ^ 2 =
        (Differential.implicitDeriv (C 1) V.num * V.denom -
          V.num * Differential.implicitDeriv (C 1) V.denom) *
            U.num * U.denom) :
    ∃ u v : Real, u ≠ 0 ∧ U = RatFunc.C u ∧ V = RatFunc.C v := by
  obtain ⟨u, v, hu0, hU, hV⟩ :=
    rationalFunction_constant_of_zeroDerivation_translation
      deriv_real_eq_zero 1 one_ne_zero
      OneVariableBaseField.x OneVariableBaseField.x_transcendental
      (by simp)
      (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
      U.isCoprime_num_denom V.isCoprime_num_denom hcleared
  refine ⟨u, v, hu0, ?_, ?_⟩
  · rw [← RatFunc.num_div_denom U]
    exact hU
  · rw [← RatFunc.num_div_denom V]
    exact hV

/-- Evaluation-level seed classification for any no-new-real-constants
primitive extension with `z′ = 1`. -/
theorem realSimpleExtension_classification
    {E : Type*} [Field E] [Differential E] [Algebra Real E]
    [DifferentialAlgebra Real E] [Differential.ContainConstants Real E]
    (z : E) (hz : Transcendental Real z) (hzd : z′ = 1)
    (U V : RatFunc Real) (hU0 : U ≠ 0)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (Proposition31.evalAtTranscendental z hz V)′ *
        Proposition31.evalAtTranscendental z hz U) :
    ∃ u v : Real, u ≠ 0 ∧
      Proposition31.evalAtTranscendental z hz U = algebraMap Real E u ∧
      Proposition31.evalAtTranscendental z hz V = algebraMap Real E v := by
  exact simpleExtension_constant_of_zeroDerivation_translation
    deriv_real_eq_zero 1 one_ne_zero z hz (by simpa using hzd)
    U V hU0 heq

/-- Simple-adjoin seed classification for any such real primitive
extension. -/
theorem realSimpleAdjoin_classification
    {E : Type*} [Field E] [Differential E] [Algebra Real E]
    [DifferentialAlgebra Real E] [Differential.ContainConstants Real E]
    (z : E) (hz : Transcendental Real z) (hzd : z′ = 1)
    (X Y : IntermediateField.adjoin Real {z})
    (hX0 : (X : E) ≠ 0)
    (heq : ((X : E))′ = ((Y : E))′ * (X : E)) :
    ∃ u v : Real, u ≠ 0 ∧
      (X : E) = algebraMap Real E u ∧
      (Y : E) = algebraMap Real E v := by
  exact simpleAdjoin_constant_of_zeroDerivation_translation
    deriv_real_eq_zero 1 one_ne_zero z hz (by simpa using hzd)
    X Y hX0 heq

/-- Concrete analytic `Real(x)` seed used by the finite-stage induction. -/
theorem analyticX_simpleAdjoin_classification
    (X Y : IntermediateField.adjoin Real {OneVariableBaseField.x})
    (hX0 : (X : PositiveAnalyticFractionField) ≠ 0)
    (heq : ((X : PositiveAnalyticFractionField))′ =
      ((Y : PositiveAnalyticFractionField))′ *
        (X : PositiveAnalyticFractionField)) :
    ∃ u v : Real, u ≠ 0 ∧
      (X : PositiveAnalyticFractionField) =
        algebraMap Real PositiveAnalyticFractionField u ∧
      (Y : PositiveAnalyticFractionField) =
        algebraMap Real PositiveAnalyticFractionField v := by
  exact realSimpleAdjoin_classification
    OneVariableBaseField.x OneVariableBaseField.x_transcendental
    OneVariableBaseField.deriv_x X Y hX0 heq

end

end Natfunbasis.Wilkie.BaseRationalClassification
