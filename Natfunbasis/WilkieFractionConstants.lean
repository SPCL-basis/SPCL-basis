import Natfunbasis.WilkieFractionDifferential
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Constants of the analytic fraction field

This file is separate from the construction of the fraction-field
derivation.  Its main analytic input is elementary: if analytic functions
`f,g` satisfy `f'g - fg' = 0` and `g` is not identically zero, then `f` is a
real constant multiple of `g`.  We prove this first on a ball avoiding a zero
of `g`, and then use the analytic identity theorem on the connected positive
axis.
-/

namespace Natfunbasis.Wilkie

open Set Filter

noncomputable section

namespace PositiveAnalyticFunction

/-- A nonzero positive-axis analytic function is nonzero at some positive
argument. -/
theorem exists_apply_ne_zero_of_ne_zero {f : PositiveAnalyticFunction}
    (hf : f ≠ 0) : ∃ y : PositiveReal, f.1 y ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  apply Subtype.ext
  funext y
  exact h y

/-- The elementary analytic constant-ratio lemma needed to identify the
constants of the fraction field. -/
theorem exists_eq_smul_of_derivative_mul_sub_mul_derivative_eq_zero
    (f g : PositiveAnalyticFunction) (hg : g ≠ 0)
    (hcross : derivative f * g - f * derivative g = 0) :
    ∃ c : Real, f = c • g := by
  obtain ⟨y, hy⟩ := exists_apply_ne_zero_of_ne_zero hg
  have hyG : extension g y.1 ≠ 0 := by
    rw [← extension_restrict g y]
    exact hy
  have hGevent : ∀ᶠ x in nhds y.1, extension g x ≠ 0 :=
    ((extension_analytic g y.1 y.2).continuousAt.eventually_ne hyG)
  have hneighborhood :
      positiveAxis ∩ {x | extension g x ≠ 0} ∈ nhds y.1 :=
    inter_mem (positiveAxis_isOpen.mem_nhds y.2) hGevent
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hneighborhood
  have hquotientDifferentiable :
      DifferentiableOn Real (extension f / extension g) (Metric.ball y.1 r) := by
    apply DifferentiableOn.div
    · intro x hx
      exact (extension_analytic f x (hrsub hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (extension_analytic g x (hrsub hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hrsub hx).2
  have hquotientDerivative :
      Set.EqOn (deriv (extension f / extension g)) 0 (Metric.ball y.1 r) := by
    intro x hx
    have hxpos : x ∈ positiveAxis := (hrsub hx).1
    have hxg : extension g x ≠ 0 := (hrsub hx).2
    let z : PositiveReal := ⟨x, hxpos⟩
    have hpoint := congrFun (congrArg Subtype.val hcross) z
    change (derivative f).1 z * g.1 z -
      f.1 z * (derivative g).1 z = 0 at hpoint
    rw [derivative_apply, derivative_apply,
      extension_restrict f z, extension_restrict g z] at hpoint
    rw [deriv_div
      ((extension_analytic f x hxpos).differentiableAt)
      ((extension_analytic g x hxpos).differentiableAt) hxg]
    have hnumerator : deriv (extension f) x * extension g x -
        extension f x * deriv (extension g) x = 0 := by
      simpa [z] using hpoint
    rw [hnumerator]
    simp
  obtain ⟨c, hc⟩ :=
    Metric.isOpen_ball.exists_is_const_of_deriv_eq_zero
      Metric.isPreconnected_ball hquotientDifferentiable hquotientDerivative
  have hlocal :
      (fun x ↦ extension f x - c * extension g x) =ᶠ[nhds y.1] 0 := by
    filter_upwards [Metric.ball_mem_nhds y.1 hr] with x hx
    have hxg : extension g x ≠ 0 := (hrsub hx).2
    have hcx := hc x hx
    change extension f x / extension g x = c at hcx
    change extension f x - c * extension g x = 0
    exact sub_eq_zero.mpr ((div_eq_iff hxg).mp hcx)
  have hanalytic :
      AnalyticOnNhd Real
        (fun x ↦ extension f x - c * extension g x) positiveAxis := by
    exact (extension_analytic f).sub
      (show AnalyticOnNhd Real
          (fun x ↦ c * extension g x) positiveAxis from
        analyticOnNhd_const.mul (extension_analytic g))
  have hglobal :
      Set.EqOn (fun x ↦ extension f x - c * extension g x) 0 positiveAxis :=
    hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      positiveAxis_isPreconnected y.2 hlocal
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext z
  change f.1 z = c * g.1 z
  rw [extension_restrict f z, extension_restrict g z]
  exact sub_eq_zero.mp (hglobal z.2)

/-- Real constant functions have zero analytic derivative. -/
@[simp]
theorem derivative_algebraMap (c : Real) :
    derivative (algebraMap Real PositiveAnalyticFunction c) = 0 := by
  apply Subtype.ext
  funext y
  rw [derivative_eq_deriv_of_extension
    (algebraMap Real PositiveAnalyticFunction c) (fun _ ↦ c)
    analyticOnNhd_const (by simp) y]
  exact deriv_const y.1 c

end PositiveAnalyticFunction

namespace PositiveAnalyticFractionField

/-- The canonical derivation vanishes on embedded real constants. -/
@[simp]
theorem derivation_algebraMap_real (c : Real) :
    derivation (algebraMap Real PositiveAnalyticFractionField c) = 0 := by
  rw [IsScalarTower.algebraMap_apply Real PositiveAnalyticFunction
    PositiveAnalyticFractionField, derivation_algebraMap]
  simp [PositiveAnalyticFunction.derivation_apply]

/-- Every element of the analytic fraction field with zero derivative is an
embedded real constant. -/
theorem mem_range_algebraMap_real_of_derivation_eq_zero
    {x : PositiveAnalyticFractionField} (hx : derivation x = 0) :
    x ∈ (algebraMap Real PositiveAnalyticFractionField).range := by
  obtain ⟨f, g, hg, hfg⟩ :=
    IsFractionRing.div_surjective PositiveAnalyticFunction x
  have hgmap :
      algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hg
  have hquotient :
      (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
          (PositiveAnalyticFunction.derivation f) *
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g -
        algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField f *
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
            (PositiveAnalyticFunction.derivation g)) /
        (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g) ^ 2 = 0 := by
    rw [← derivation_div_algebraMap]
    rw [hfg]
    exact hx
  have hnumerator :
      algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
          (PositiveAnalyticFunction.derivation f) *
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g -
        algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField f *
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
            (PositiveAnalyticFunction.derivation g) = 0 := by
    exact (div_eq_zero_iff.mp hquotient).resolve_right (pow_ne_zero 2 hgmap)
  have hcross :
      PositiveAnalyticFunction.derivative f * g -
        f * PositiveAnalyticFunction.derivative g = 0 := by
    apply IsFractionRing.injective PositiveAnalyticFunction
      PositiveAnalyticFractionField
    simpa [PositiveAnalyticFunction.derivation_apply] using hnumerator
  obtain ⟨c, hc⟩ :=
    PositiveAnalyticFunction.exists_eq_smul_of_derivative_mul_sub_mul_derivative_eq_zero
      f g (nonZeroDivisors.ne_zero hg) hcross
  rw [← hfg]
  refine ⟨c, ?_⟩
  rw [hc, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply Real PositiveAnalyticFunction
      PositiveAnalyticFractionField]
  field_simp

/-- Exact identification of the constants of the analytic fraction field. -/
theorem derivation_eq_zero_iff_mem_range_algebraMap_real
    (x : PositiveAnalyticFractionField) :
    derivation x = 0 ↔
      x ∈ (algebraMap Real PositiveAnalyticFractionField).range := by
  constructor
  · exact mem_range_algebraMap_real_of_derivation_eq_zero
  · rintro ⟨c, rfl⟩
    exact derivation_algebraMap_real c

/-- The constant field of the analytic fraction field is exactly `Real`. -/
instance : Differential.ContainConstants Real PositiveAnalyticFractionField where
  mem_range_of_deriv_eq_zero {_x} hx :=
    mem_range_algebraMap_real_of_derivation_eq_zero hx

end PositiveAnalyticFractionField

end


end Natfunbasis.Wilkie
