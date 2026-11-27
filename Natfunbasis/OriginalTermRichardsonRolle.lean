import Natfunbasis.OriginalTermAtInfinityMonotonicity
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Rolle-theoretic core of the integer-to-real bridge

Richardson's finite-zero argument repeatedly replaces a function with a
normalized derivative.  This file isolates the real-analysis part of that
argument.  In particular, unboundedly many zeros of a differentiable function
force unboundedly many zeros of its derivative.  Conversely, an eventually
nowhere-zero derivative prevents unboundedly many zeros, while an eventually
zero derivative makes the function constant on a tail.

The statements are deliberately phrased for ordinary real functions.  They
can therefore be reused by either a syntactic Richardson chain or a tower of
primitive and exponential differential-field extensions.
-/

namespace Natfunbasis.Wilkie

open Filter Set

noncomputable section

/-- A real function has zeros arbitrarily far to the right. -/
def HasUnboundedZeros (f : Real → Real) : Prop :=
  ∀ B : Real, ∃ x : Real, B < x ∧ f x = 0

/-- A real function is nowhere zero beyond some threshold. -/
def EventuallyNowhereZero (f : Real → Real) : Prop :=
  ∃ B : Real, ∀ x : Real, B < x → f x ≠ 0

/-- A real function vanishes identically beyond some threshold. -/
def EventuallyZero (f : Real → Real) : Prop :=
  ∃ B : Real, ∀ x : Real, B < x → f x = 0

/-- Negating unboundedly many zeros gives exactly eventual nonvanishing. -/
theorem not_hasUnboundedZeros_iff_eventuallyNowhereZero (f : Real → Real) :
    ¬ HasUnboundedZeros f ↔ EventuallyNowhereZero f := by
  constructor
  · intro hzero
    by_contra hnowhere
    apply hzero
    intro B
    by_contra hnone
    apply hnowhere
    refine ⟨B, ?_⟩
    intro x hx hfx
    exact hnone ⟨x, hx, hfx⟩
  · rintro ⟨B, hB⟩ hzero
    obtain ⟨x, hx, hfx⟩ := hzero B
    exact hB x hx hfx

/-- Eventual nonvanishing and unboundedly many zeros are incompatible. -/
theorem EventuallyNowhereZero.not_hasUnboundedZeros {f : Real → Real}
    (hf : EventuallyNowhereZero f) : ¬ HasUnboundedZeros f := by
  obtain ⟨B, hB⟩ := hf
  intro hzero
  obtain ⟨x, hx, hfx⟩ := hzero B
  exact (hB x hx) hfx

/-- If a differentiable function has zeros arbitrarily far to the right, so
does its derivative.  This is the precise Rolle step used in a Richardson
chain. -/
theorem HasUnboundedZeros.deriv {f : Real → Real}
    (hzero : HasUnboundedZeros f)
    (hdiff : ∀ x : Real, 0 < x → DifferentiableAt Real f x) :
    HasUnboundedZeros (deriv f) := by
  intro B
  obtain ⟨a, ha, hfa⟩ := hzero (max B 0)
  have haB : B < a := (le_max_left B 0).trans_lt ha
  have ha0 : 0 < a := (le_max_right B 0).trans_lt ha
  obtain ⟨b, hab, hfb⟩ := hzero a
  have hb0 : 0 < b := ha0.trans hab
  have hcontinuous : ContinuousOn f (Icc a b) := by
    exact (show DifferentiableOn Real f (Icc a b) from fun x hx ↦
      (hdiff x (ha0.trans_le hx.1)).differentiableWithinAt).continuousOn
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hab hcontinuous (hfa.trans hfb.symm)
  exact ⟨c, haB.trans hc.1, hdc⟩

/-- If the derivative is eventually nowhere zero, the original function
cannot have zeros arbitrarily far to the right. -/
theorem not_hasUnboundedZeros_of_deriv_eventuallyNowhereZero
    {f : Real → Real}
    (hdiff : ∀ x : Real, 0 < x → DifferentiableAt Real f x)
    (hderiv : EventuallyNowhereZero (deriv f)) :
    ¬ HasUnboundedZeros f := by
  intro hzero
  exact hderiv.not_hasUnboundedZeros (hzero.deriv hdiff)

/-- A derivative which vanishes on a right-hand tail makes the function
constant on that tail. -/
theorem eventuallyConstant_of_deriv_eventuallyZero {f : Real → Real}
    (hdiff : ∀ x : Real, 0 < x → DifferentiableAt Real f x)
    (hderiv : ∃ B : Real, ∀ x : Real, B < x → deriv f x = 0) :
    ∃ B : Real, ∃ c : Real, ∀ x : Real, B < x → f x = c := by
  obtain ⟨B₀, hB₀⟩ := hderiv
  let B := max B₀ 0
  have hopen : IsOpen (Ioi B) := isOpen_Ioi
  have hpre : IsPreconnected (Ioi B) := isPreconnected_Ioi
  have hdiffOn : DifferentiableOn Real f (Ioi B) := by
    intro x hx
    exact (hdiff x ((le_max_right B₀ 0).trans_lt hx)).differentiableWithinAt
  have hderivOn : Set.EqOn (deriv f) 0 (Ioi B) := by
    intro x hx
    exact hB₀ x ((le_max_left B₀ 0).trans_lt hx)
  obtain ⟨c, hc⟩ := hopen.exists_is_const_of_deriv_eq_zero hpre hdiffOn hderivOn
  exact ⟨B, c, fun x hx ↦ hc x hx⟩

/-- If a differentiable function has unboundedly many zeros and an eventually
zero derivative, then the function itself vanishes on a right-hand tail. -/
theorem eventuallyZero_of_unboundedZeros_of_deriv_eventuallyZero
    {f : Real → Real}
    (hzero : HasUnboundedZeros f)
    (hdiff : ∀ x : Real, 0 < x → DifferentiableAt Real f x)
    (hderiv : ∃ B : Real, ∀ x : Real, B < x → deriv f x = 0) :
    ∃ B : Real, ∀ x : Real, B < x → f x = 0 := by
  obtain ⟨B, c, hc⟩ := eventuallyConstant_of_deriv_eventuallyZero hdiff hderiv
  obtain ⟨z, hzB, hfz⟩ := hzero B
  have hcz : c = 0 := (hc z hzB).symm.trans hfz
  exact ⟨B, fun x hx ↦ (hc x hx).trans hcz⟩

/-- The Richardson induction step in dichotomy form: if the derivative is
eventually zero or eventually nowhere zero, then unbounded zeros of the
original function force the original function to vanish on a tail. -/
theorem eventuallyZero_of_unboundedZeros_of_deriv_dichotomy
    {f : Real → Real}
    (hzero : HasUnboundedZeros f)
    (hdiff : ∀ x : Real, 0 < x → DifferentiableAt Real f x)
    (hderiv :
      (∃ B : Real, ∀ x : Real, B < x → deriv f x = 0) ∨
        EventuallyNowhereZero (deriv f)) :
    ∃ B : Real, ∀ x : Real, B < x → f x = 0 := by
  rcases hderiv with hderivZero | hderivNonzero
  · exact eventuallyZero_of_unboundedZeros_of_deriv_eventuallyZero
      hzero hdiff hderivZero
  · exact False.elim
      (not_hasUnboundedZeros_of_deriv_eventuallyNowhereZero hdiff
        hderivNonzero hzero)

/-- Closure step for Richardson's derivative descent.  Once the derivative
is eventually zero or eventually nowhere zero, the same dichotomy holds for
the original function. -/
theorem eventuallyZero_or_eventuallyNowhereZero_of_deriv_dichotomy
    {f : Real → Real}
    (hdiff : ∀ x : Real, 0 < x → DifferentiableAt Real f x)
    (hderiv : EventuallyZero (deriv f) ∨
      EventuallyNowhereZero (deriv f)) :
    EventuallyZero f ∨ EventuallyNowhereZero f := by
  rcases hderiv with hderivZero | hderivNonzero
  · obtain ⟨B, c, hc⟩ := eventuallyConstant_of_deriv_eventuallyZero
      hdiff hderivZero
    by_cases hc0 : c = 0
    · exact Or.inl ⟨B, fun x hx ↦ (hc x hx).trans hc0⟩
    · exact Or.inr ⟨B, fun x hx ↦ (hc x hx).trans_ne hc0⟩
  · right
    rw [← not_hasUnboundedZeros_iff_eventuallyNowhereZero]
    exact not_hasUnboundedZeros_of_deriv_eventuallyNowhereZero hdiff
      hderivNonzero

end

end Natfunbasis.Wilkie
