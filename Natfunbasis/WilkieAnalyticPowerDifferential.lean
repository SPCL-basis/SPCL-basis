import Natfunbasis.WilkieFractionConstants
import Natfunbasis.WilkieGeneratorAnalyticity

/-!
# Logarithms and powers in the analytic differential field

This file packages the two analytic operations which occur at every step of
Wilkie's differential-field induction.  If `f` is positive on the positive
axis, then `log f` is again a positive-axis analytic function.  If `g` is
positive-axis analytic as well, then so is `f ^ g`.  Their ordinary
derivatives satisfy the exact cross-multiplied identities used in the source
proof; after embedding in the fraction field these become the familiar
logarithmic-derivative formulas.

These are analytic/calculus lemmas only.  No algebraic-independence claim is
made here.
-/

namespace Natfunbasis.Wilkie

open Set

noncomputable section

namespace PositiveAnalyticFunction

/-- The pointwise logarithm of an everywhere-positive analytic function. -/
def log (f : PositiveAnalyticFunction) (hf : ∀ y, 0 < f.1 y) :
    PositiveAnalyticFunction := by
  refine ⟨fun y ↦ Real.log (f.1 y), ?_⟩
  let F := extension f
  have hFpos : ∀ x ∈ positiveAxis, 0 < F x := by
    intro x hx
    let y : PositiveReal := ⟨x, hx⟩
    change 0 < extension f y.1
    rw [← extension_restrict f y]
    exact hf y
  refine ⟨fun x ↦ Real.log (F x), ?_, ?_⟩
  · intro x hx
    exact (analyticAt_log (hFpos x hx)).comp (extension_analytic f x hx)
  · intro y
    exact congrArg Real.log (extension_restrict f y)

@[simp]
theorem log_apply (f : PositiveAnalyticFunction) (hf : ∀ y, 0 < f.1 y)
    (y : PositiveReal) :
    (log f hf).1 y = Real.log (f.1 y) :=
  rfl

/-- The pointwise real power of a positive analytic base by an analytic
exponent, bundled as a positive-axis analytic function. -/
def rpow (f g : PositiveAnalyticFunction) (hf : ∀ y, 0 < f.1 y) :
    PositiveAnalyticFunction :=
  ⟨fun y ↦ Real.rpow (f.1 y) (g.1 y),
    IsPositiveAnalytic.rpow f.2 g.2 hf⟩

@[simp]
theorem rpow_apply (f g : PositiveAnalyticFunction)
    (hf : ∀ y, 0 < f.1 y) (y : PositiveReal) :
    (rpow f g hf).1 y = Real.rpow (f.1 y) (g.1 y) :=
  rfl

/-- Cross-multiplied derivative identity for a logarithm.  The formulation
lives in the analytic integral domain and therefore does not use division. -/
theorem mul_derivative_log (f : PositiveAnalyticFunction)
    (hf : ∀ y, 0 < f.1 y) :
    f * derivative (log f hf) = derivative f := by
  apply Subtype.ext
  funext y
  let F := extension f
  have hyF : 0 < F y.1 := by
    change 0 < extension f y.1
    rw [← extension_restrict f y]
    exact hf y
  have hlogAnalytic :
      AnalyticOnNhd Real (fun x ↦ Real.log (F x)) positiveAxis := by
    intro x hx
    have hxF : 0 < F x := by
      let z : PositiveReal := ⟨x, hx⟩
      change 0 < extension f z.1
      rw [← extension_restrict f z]
      exact hf z
    exact (analyticAt_log hxF).comp (extension_analytic f x hx)
  change f.1 y * (derivative (log f hf)).1 y = (derivative f).1 y
  rw [derivative_eq_deriv_of_extension (log f hf)
      (fun x ↦ Real.log (F x)) hlogAnalytic]
  · have hFdiff := (extension_analytic f y.1 y.2).differentiableAt
    have hderivLog :
        deriv (fun x ↦ Real.log (F x)) y.1 =
          (F y.1)⁻¹ * deriv F y.1 :=
      ((Real.hasDerivAt_log hyF.ne').comp y.1 hFdiff.hasDerivAt).deriv
    rw [hderivLog, derivative_apply, extension_restrict f y]
    field_simp
    simp [F]
  · intro z
    simp only [log_apply]
    rw [extension_restrict f z]

/-- Denominator-free differential equation for a positive real power. -/
theorem mul_derivative_rpow (f g : PositiveAnalyticFunction)
    (hf : ∀ y, 0 < f.1 y) :
    f * derivative (rpow f g hf) =
      rpow f g hf *
        (derivative f * g + f * log f hf * derivative g) := by
  apply Subtype.ext
  funext y
  let F := extension f
  let G := extension g
  have hFpos : ∀ x ∈ positiveAxis, 0 < F x := by
    intro x hx
    let z : PositiveReal := ⟨x, hx⟩
    change 0 < extension f z.1
    rw [← extension_restrict f z]
    exact hf z
  have hpowerAnalytic :
      AnalyticOnNhd Real (positiveRpowExtension F G) positiveAxis := by
    have hlogF :
        AnalyticOnNhd Real (fun x ↦ Real.log (F x)) positiveAxis := by
      intro x hx
      exact (analyticAt_log (hFpos x hx)).comp
        (extension_analytic f x hx)
    exact (hlogF.mul (extension_analytic g)).rexp
  change f.1 y * (derivative (rpow f g hf)).1 y =
    (rpow f g hf).1 y *
      ((derivative f).1 y * g.1 y +
        f.1 y * (log f hf).1 y * (derivative g).1 y)
  rw [derivative_eq_deriv_of_extension (rpow f g hf)
      (positiveRpowExtension F G) hpowerAnalytic]
  · have hFdiff := (extension_analytic f y.1 y.2).differentiableAt
    have hGdiff := (extension_analytic g y.1 y.2).differentiableAt
    rw [rpow_apply, derivative_apply, derivative_apply, log_apply,
      extension_restrict f y, extension_restrict g y]
    simpa [F, G, positiveRpowExtension,
      Real.rpow_def_of_pos (hFpos y.1 y.2)] using
      (mul_deriv_positiveRpowExtension hFdiff hGdiff
        (hFpos y.1 y.2).ne')
  · intro z
    simp only [rpow_apply, positiveRpowExtension]
    rw [extension_restrict f z, extension_restrict g z]
    simpa [F, G] using
      (Real.rpow_def_of_pos (hFpos z.1 z.2) (G z.1))

end PositiveAnalyticFunction

namespace PositiveAnalyticFractionField

local notation "ι" =>
  (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField)

/-- In the analytic fraction field, the derivative of `log f` is `f'/f`. -/
theorem derivation_log (f : PositiveAnalyticFunction)
    (hf : ∀ y, 0 < f.1 y) :
    derivation (ι (PositiveAnalyticFunction.log f hf)) =
      derivation (ι f) / ι f := by
  rw [derivation_algebraMap, derivation_algebraMap]
  have hfne : ι f ≠ 0 := by
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    let y : PositiveReal := ⟨1, zero_lt_one⟩
    have hpoint := congrArg (fun h : PositiveAnalyticFunction ↦ h.1 y) hzero
    exact (ne_of_gt (hf y)) (by simpa [y] using hpoint)
  apply (eq_div_iff hfne).2
  rw [← map_mul]
  apply congrArg ι
  simpa [PositiveAnalyticFunction.derivation_apply, mul_comm] using
    PositiveAnalyticFunction.mul_derivative_log f hf

/-- The logarithmic differential equation for a positive real power, now in
the field form used by Wilkie's induction. -/
theorem derivation_rpow (f g : PositiveAnalyticFunction)
    (hf : ∀ y, 0 < f.1 y) :
    derivation (ι (PositiveAnalyticFunction.rpow f g hf)) =
      ι (PositiveAnalyticFunction.rpow f g hf) *
        (derivation (ι g) * ι (PositiveAnalyticFunction.log f hf) +
          ι g * derivation (ι f) / ι f) := by
  have hfne : ι f ≠ 0 := by
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    let y : PositiveReal := ⟨1, zero_lt_one⟩
    have hpoint := congrArg (fun h : PositiveAnalyticFunction ↦ h.1 y) hzero
    exact (ne_of_gt (hf y)) (by simpa [y] using hpoint)
  have hcross := congrArg ι
    (PositiveAnalyticFunction.mul_derivative_rpow f g hf)
  simp only [map_mul, map_add] at hcross
  simp only [derivation_algebraMap,
    PositiveAnalyticFunction.derivation_apply]
  field_simp [hfne]
  linear_combination hcross

end PositiveAnalyticFractionField

end

end Natfunbasis.Wilkie
