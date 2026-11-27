import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.FieldTheory.Differential.Basic
import Natfunbasis.WilkieGenerators

/-!
# Analytic-function infrastructure for Wilkie's differential-field argument

Wilkie works with fields of partially defined real-analytic functions on the
positive real axis.  This file develops only unconditional infrastructure
which is already supported by mathlib:

* the identity theorem makes analytic functions on the connected positive
  axis an integral domain;
* equality on that open axis is preserved by differentiation; and
* the ring of real-valued functions on `PositiveReal` admitting an analytic
  extension is an explicit integral domain.

This does not prove Wilkie's Theorem 4.4.  In particular, it does not yet
construct the differential field of fractions used as `F_0`, prove that its
constant field is exactly `Real`, or formalize the Singer-style differential
algebra propositions used in Wilkie's induction.
-/

namespace Natfunbasis.Wilkie

open Set Filter

noncomputable section

/-- The positive real axis, viewed as an open subset of `Real`. -/
def positiveAxis : Set Real := Set.Ioi 0

theorem positiveAxis_isOpen : IsOpen positiveAxis :=
  isOpen_Ioi

theorem positiveAxis_isPreconnected : IsPreconnected positiveAxis :=
  isPreconnected_Ioi

/-- The derivative is well-defined modulo equality on the positive real
axis.  Openness is the essential point: equality on the axis is equality on a
neighborhood of each of its points. -/
theorem deriv_eqOn_positiveAxis_of_eqOn {f g : Real → Real}
    (hfg : Set.EqOn f g positiveAxis) :
    Set.EqOn (deriv f) (deriv g) positiveAxis := by
  intro x hx
  have hlocal : f =ᶠ[nhds x] g :=
    eventually_of_mem (positiveAxis_isOpen.mem_nhds hx) hfg
  exact Filter.EventuallyEq.deriv_eq hlocal

/-- Differentiation preserves analyticity on the positive axis. -/
theorem analyticOnNhd_positiveAxis_deriv {f : Real → Real}
    (hf : AnalyticOnNhd Real f positiveAxis) :
    AnalyticOnNhd Real (deriv f) positiveAxis :=
  hf.deriv

/-- The identity theorem supplies the no-zero-divisors fact needed before
passing from analytic functions to a fraction field. -/
theorem eqOn_zero_or_eqOn_zero_of_mul_eqOn_zero_positiveAxis
    {f g : Real → Real}
    (hf : AnalyticOnNhd Real f positiveAxis)
    (hg : AnalyticOnNhd Real g positiveAxis)
    (hfg : Set.EqOn (f * g) 0 positiveAxis) :
    Set.EqOn f 0 positiveAxis ∨ Set.EqOn g 0 positiveAxis := by
  apply hf.eq_zero_or_eq_zero_of_mul_eq_zero hg _ positiveAxis_isPreconnected
  intro x hx
  exact hfg hx

/-- A nonzero analytic function is nonvanishing on a codiscrete subset of the
positive axis.  This is the filter-theoretic form of the domain convention
used for quotients in Wilkie's Section 4. -/
theorem eqOn_zero_or_eventually_ne_zero_positiveAxis
    {f : Real → Real} (hf : AnalyticOnNhd Real f positiveAxis) :
    Set.EqOn f 0 positiveAxis ∨
      ∀ᶠ x in codiscreteWithin positiveAxis, f x ≠ 0 :=
  hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
    positiveAxis_isPreconnected

/-! ## Analytic functions intrinsically restricted to the positive axis -/

/-- A function on positive reals is positive-axis analytic when it is the
restriction of a real-analytic function on a neighborhood of the positive
axis. -/
def IsPositiveAnalytic (f : PositiveReal → Real) : Prop :=
  ∃ extension : Real → Real,
    AnalyticOnNhd Real extension positiveAxis ∧
      ∀ y : PositiveReal, f y = extension y.1

/-- Positive-axis analytic functions form a real subalgebra of all functions
on `PositiveReal`. -/
def positiveAnalyticSubalgebra :
    Subalgebra Real (PositiveReal → Real) where
  carrier := {f | IsPositiveAnalytic f}
  zero_mem' := ⟨0, analyticOnNhd_const, by simp⟩
  one_mem' := ⟨1, analyticOnNhd_const, by simp⟩
  add_mem' := by
    rintro f g ⟨F, hF, hfrestrict⟩ ⟨G, hG, hgrestrict⟩
    refine ⟨F + G, hF.add hG, ?_⟩
    intro y
    simp only [Pi.add_apply]
    rw [hfrestrict y, hgrestrict y]
  mul_mem' := by
    rintro f g ⟨F, hF, hfrestrict⟩ ⟨G, hG, hgrestrict⟩
    refine ⟨F * G, hF.mul hG, ?_⟩
    intro y
    simp only [Pi.mul_apply]
    rw [hfrestrict y, hgrestrict y]
  algebraMap_mem' := by
    intro r
    refine ⟨fun _ ↦ r, analyticOnNhd_const, ?_⟩
    intro y
    rfl

/-- The ring of real-valued positive-axis analytic functions. -/
abbrev PositiveAnalyticFunction := positiveAnalyticSubalgebra

namespace PositiveAnalyticFunction

/-- A chosen ambient analytic extension.  Its use is confined to definitions;
the equality-on-open-set lemma above proves that its derivative is independent
of this choice. -/
def extension (f : PositiveAnalyticFunction) : Real → Real :=
  Classical.choose f.2

theorem extension_analytic (f : PositiveAnalyticFunction) :
    AnalyticOnNhd Real (extension f) positiveAxis :=
  (Classical.choose_spec f.2).1

theorem extension_restrict (f : PositiveAnalyticFunction) (y : PositiveReal) :
    f.1 y = extension f y.1 :=
  (Classical.choose_spec f.2).2 y

/-- The bundled analytic-function ring has no zero divisors. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero
    {f g : PositiveAnalyticFunction} (hfg : f * g = 0) :
    f = 0 ∨ g = 0 := by
  have hproduct : Set.EqOn (extension f * extension g) 0 positiveAxis := by
    intro x hx
    let y : PositiveReal := ⟨x, hx⟩
    have hpoint := congrFun (congrArg Subtype.val hfg) y
    change f.1 y * g.1 y = 0 at hpoint
    change extension f y.1 * extension g y.1 = 0
    rw [← extension_restrict f y, ← extension_restrict g y]
    exact hpoint
  rcases eqOn_zero_or_eqOn_zero_of_mul_eqOn_zero_positiveAxis
      (extension_analytic f) (extension_analytic g) hproduct with hf | hg
  · left
    apply Subtype.ext
    funext y
    rw [extension_restrict f y, hf y.2]
    rfl
  · right
    apply Subtype.ext
    funext y
    rw [extension_restrict g y, hg y.2]
    rfl

instance : NoZeroDivisors PositiveAnalyticFunction where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    PositiveAnalyticFunction.eq_zero_or_eq_zero_of_mul_eq_zero

instance : IsDomain PositiveAnalyticFunction where

end PositiveAnalyticFunction

end


end Natfunbasis.Wilkie
