import Natfunbasis.WilkieDifferentialIntermediateField
import Natfunbasis.WilkieAnalyticPowerDifferential
import Natfunbasis.WilkieGeneratorDifferentialEquations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# The initial one-variable differential field in Wilkie's construction

This file constructs, inside the fraction field of positive-axis analytic
functions, the two elements represented by `x` and `log x` and the
differential intermediate field

`F₀ = ℝ(x, log x)`.

Everything in this file is unconditional.  In particular, closure under the
ambient derivation is proved from the exact identities

`x' = 1` and `(log x)' = x⁻¹`.

We also prove that the analytic element `x` is transcendental over `ℝ`.
The stronger algebraic independence of `x` and `log x`, which is the base
case used in Wilkie's Theorem 4.4, requires an additional differential-
algebra or asymptotic argument and is not asserted here.
-/

namespace Natfunbasis.Wilkie

open Set
open Polynomial
open scoped Differential

noncomputable section

namespace OneVariableBaseField

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

/-! ## The coordinate and its logarithm -/

/-- The coordinate function, embedded in the analytic fraction field. -/
def x : K :=
  ι inputAnalyticFunction

/-- The coordinate function is strictly positive on the positive axis. -/
theorem inputAnalyticFunction_pos (y : PositiveReal) :
    0 < inputAnalyticFunction.1 y :=
  y.2

/-- The positive-axis analytic function `log x`. -/
def logInputAnalyticFunction : A :=
  PositiveAnalyticFunction.log inputAnalyticFunction
    inputAnalyticFunction_pos

@[simp]
theorem logInputAnalyticFunction_apply (y : PositiveReal) :
    logInputAnalyticFunction.1 y = Real.log y.1 :=
  rfl

/-- The analytic function `log x`, embedded in the fraction field. -/
def logX : K :=
  ι logInputAnalyticFunction

/-! ## Exact differential equations -/

/-- The bundled analytic derivative of the coordinate function is one. -/
@[simp]
theorem derivative_inputAnalyticFunction :
    PositiveAnalyticFunction.derivative inputAnalyticFunction = 1 := by
  apply Subtype.ext
  funext y
  rw [PositiveAnalyticFunction.derivative_eq_deriv_of_extension
    inputAnalyticFunction id analyticOnNhd_id (fun _ ↦ rfl) y]
  exact deriv_id y.1

/-- In the ambient differential field, `x' = 1`. -/
@[simp]
theorem deriv_x : x′ = 1 := by
  change PositiveAnalyticFractionField.derivation
    (ι inputAnalyticFunction) = 1
  rw [PositiveAnalyticFractionField.derivation_algebraMap]
  simp [PositiveAnalyticFunction.derivation_apply]

/-- The field element represented by the coordinate function is nonzero. -/
theorem x_ne_zero : x ≠ 0 := by
  intro hx
  have h := congrArg (fun z : K ↦ z′) hx
  rw [deriv_x, map_zero] at h
  exact one_ne_zero h

/-- In the ambient differential field, `(log x)' = x⁻¹`. -/
@[simp]
theorem deriv_logX : logX′ = x⁻¹ := by
  change PositiveAnalyticFractionField.derivation
    (ι (PositiveAnalyticFunction.log inputAnalyticFunction
      inputAnalyticFunction_pos)) = x⁻¹
  rw [PositiveAnalyticFractionField.derivation_log]
  change x′ / x = x⁻¹
  rw [deriv_x]
  simp

/-! ## The derivative-closed field `ℝ(x, log x)` -/

/-- The two generators of the initial field. -/
def generators : Set K :=
  {x, logX}

private theorem deriv_generator_mem
    (z : K) (hz : z ∈ generators) :
    z′ ∈ IntermediateField.adjoin Real generators := by
  rcases hz with (rfl | hz)
  · rw [deriv_x]
    exact one_mem _
  · have hzlog : z = logX := by simpa [generators] using hz
    subst z
    rw [deriv_logX]
    exact inv_mem (IntermediateField.subset_adjoin Real generators
      (by simp [generators]))

/-- Wilkie's initial field `F₀ = ℝ(x, log x)`, equipped with the
restriction of the analytic fraction-field derivation. -/
def F0 : DifferentialIntermediateField Real K :=
  DifferentialIntermediateField.adjoinOfConstants generators
    PositiveAnalyticFractionField.derivation_algebraMap_real
    deriv_generator_mem

@[simp]
theorem mem_F0_iff (z : K) :
    z ∈ F0 ↔ z ∈ IntermediateField.adjoin Real generators :=
  Iff.rfl

@[simp]
theorem x_mem_F0 : x ∈ F0 := by
  change x ∈ IntermediateField.adjoin Real generators
  exact IntermediateField.subset_adjoin Real generators (by simp [generators])

@[simp]
theorem logX_mem_F0 : logX ∈ F0 := by
  change logX ∈ IntermediateField.adjoin Real generators
  exact IntermediateField.subset_adjoin Real generators (by simp [generators])

theorem inv_x_mem_F0 : x⁻¹ ∈ F0 :=
  inv_mem x_mem_F0

theorem deriv_x_mem_F0 : x′ ∈ F0 :=
  F0.deriv_mem x_mem_F0

theorem deriv_logX_mem_F0 : logX′ ∈ F0 :=
  F0.deriv_mem logX_mem_F0

/-- Every derivative of an element of `F₀` remains in `F₀`. -/
theorem deriv_mem_F0 {z : K} (hz : z ∈ F0) : z′ ∈ F0 :=
  F0.deriv_mem hz

/-- `F₀` is the smallest differential intermediate field containing
`x` and `log x`. -/
theorem F0_le_iff {F : DifferentialIntermediateField Real K} :
    F0 ≤ F ↔ x ∈ F ∧ logX ∈ F := by
  change IntermediateField.adjoin Real generators ≤
      F.toIntermediateField ↔ _
  rw [IntermediateField.adjoin_le_iff]
  constructor
  · intro h
    exact ⟨h (by simp [generators]), h (by simp [generators])⟩
  · rintro ⟨hx, hlog⟩ z hz
    simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hlog

/-- The constant field of `F₀` is exactly the embedded real field. -/
theorem F0_containConstants : Differential.ContainConstants Real F0 :=
  inferInstance

/-! ## Transcendence of the coordinate -/

/-- Polynomial evaluation at the bundled coordinate function is pointwise
ordinary real polynomial evaluation. -/
theorem aeval_inputAnalyticFunction_apply (p : Real[X])
    (y : PositiveReal) :
    (Polynomial.aeval inputAnalyticFunction p : A).1 y = p.eval y.1 := by
  change StagePolynomial.analyticEvaluation y
    (Polynomial.aeval inputAnalyticFunction p) = p.eval y.1
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  have hcoeff :
      (StagePolynomial.analyticEvaluation y).comp (algebraMap Real A) =
        RingHom.id Real := by
    ext c
    rfl
  rw [hcoeff, Polynomial.eval₂_id]
  rfl

/-- The coordinate function is transcendental over `ℝ` in the analytic
function ring. -/
theorem inputAnalyticFunction_transcendental :
    Transcendental Real inputAnalyticFunction := by
  rw [transcendental_iff_injective]
  intro p q hpq
  apply Polynomial.eq_of_infinite_eval_eq p q
  refine (Set.Ioi_infinite (0 : Real)).mono ?_
  intro r hr
  let y : PositiveReal := ⟨r, hr⟩
  have hpoint := congrArg (fun f : A ↦ f.1 y) hpq
  simpa [aeval_inputAnalyticFunction_apply, y] using hpoint

/-- The embedded coordinate remains transcendental in the analytic fraction
field. -/
theorem x_transcendental : Transcendental Real x := by
  rw [transcendental_iff_injective]
  intro p q hpq
  apply (transcendental_iff_injective.mp
    inputAnalyticFunction_transcendental)
  apply IsFractionRing.injective A K
  have hmap (r : Real[X]) :
      ι (Polynomial.aeval inputAnalyticFunction r) =
        Polynomial.aeval x r := by
    simpa [x] using
      (Polynomial.map_aeval_eq_aeval_map
        (R := Real) (S := A) (T := Real) (U := K)
        (p := r) (a := inputAnalyticFunction)
        (φ := RingHom.id Real) (ψ := ι)
        (by
          ext c
          simp [IsScalarTower.algebraMap_apply Real A K]))
  rw [hmap, hmap]
  exact hpq

/-- The singleton coordinate family is algebraically independent. -/
theorem x_algebraicIndependent :
    AlgebraicIndependent Real ![x] :=
  algebraicIndependent_iff_transcendental.mpr x_transcendental

end OneVariableBaseField

end

end Natfunbasis.Wilkie
