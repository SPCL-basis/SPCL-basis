import Natfunbasis.OriginalTermRichardsonRolle
import Mathlib.Order.Filter.Germ.Basic

/-!
# Germs at positive infinity for the integer-to-real bridge

Richardson descent is naturally insensitive to bounded initial intervals.
This file records the corresponding elementary germ facts at `atTop`:

* ordinary differentiation respects eventual equality;
* a function which is eventually nowhere zero represents a unit germ;
* the concrete eventual-zero predicates used by the Rolle argument agree
  with equality to zero in the germ ring.

These facts let the differential-extension argument pass to fraction fields
without choosing globally defined reciprocals at the finitely many zeros that
may occur before the final tail.
-/

namespace Natfunbasis.Wilkie

open Filter Set

noncomputable section

/-- Real-valued function germs at positive infinity. -/
abbrev TailGerm := Filter.Germ (atTop : Filter Real) Real

/-- Eventual equality on the real line is preserved by differentiation at
positive infinity.  The extra room beyond the witnessing threshold supplies
a whole neighbourhood on which the representatives agree. -/
theorem eventuallyEq_deriv_atTop {f g : Real → Real}
    (hfg : f =ᶠ[atTop] g) : deriv f =ᶠ[atTop] deriv g := by
  obtain ⟨B, hB⟩ := eventually_atTop.1 hfg
  refine eventually_atTop.2 ⟨B + 1, fun x hx ↦ ?_⟩
  have hBx : B < x := by linarith
  apply Filter.EventuallyEq.deriv_eq
  exact Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hBx)
    (fun y hy ↦ hB y hy.le)

/-- Differentiation is therefore a well-defined operation on germs at
positive infinity.  It is intentionally not declared as a derivation on the
whole germ ring: product rules require eventual differentiability of the
chosen subring. -/
def TailGerm.deriv : TailGerm → TailGerm :=
  Filter.Germ.map' _root_.deriv fun _ _ hfg ↦ eventuallyEq_deriv_atTop hfg

@[simp]
theorem TailGerm.deriv_coe (f : Real → Real) :
    TailGerm.deriv (f : TailGerm) = (_root_.deriv f : TailGerm) :=
  rfl

/-- Vanishing on a right-hand tail is exactly equality to zero as a germ at
positive infinity. -/
theorem eventuallyZero_iff_tailGerm_eq_zero (f : Real → Real) :
    EventuallyZero f ↔ (f : TailGerm) = 0 := by
  change (∃ B : Real, ∀ x : Real, B < x → f x = 0) ↔ _
  change (∃ B : Real, ∀ x : Real, B < x → f x = 0) ↔
    (f : TailGerm) = ((fun _ : Real ↦ (0 : Real)) : TailGerm)
  rw [Filter.Germ.coe_eq]
  constructor
  · rintro ⟨B, hB⟩
    exact eventually_atTop.2 ⟨B + 1, fun x hx ↦
      hB x (lt_of_lt_of_le (lt_add_one B) hx)⟩
  · intro h
    obtain ⟨B, hB⟩ := eventually_atTop.1 h
    exact ⟨B, fun x hx ↦ hB x hx.le⟩

/-- An eventually nowhere-zero representative is invertible in the germ
ring.  Its pointwise reciprocal is a valid inverse after discarding the
bounded exceptional interval. -/
theorem tailGerm_isUnit_of_eventuallyNowhereZero {f : Real → Real}
    (hf : EventuallyNowhereZero f) : IsUnit (f : TailGerm) := by
  obtain ⟨B, hB⟩ := hf
  let g : Real → Real := fun x ↦ (f x)⁻¹
  have hfg : (f : TailGerm) * (g : TailGerm) = 1 := by
    apply Filter.EventuallyEq.germ_eq
    exact eventually_atTop.2 ⟨B + 1, fun x hx ↦ by
      change f x * (f x)⁻¹ = 1
      exact mul_inv_cancel₀ (hB x (lt_of_lt_of_le (lt_add_one B) hx))⟩
  have hgf : (g : TailGerm) * (f : TailGerm) = 1 := by
    simpa [mul_comm] using hfg
  exact ⟨⟨(f : TailGerm), (g : TailGerm), hfg, hgf⟩, rfl⟩

/-- Conversely, a unit germ has an eventually nowhere-zero representative.
Together with the preceding theorem, this identifies the precise algebraic
meaning of the nonzero side of Richardson's dichotomy. -/
theorem eventuallyNowhereZero_of_tailGerm_isUnit {f : Real → Real}
    (hf : IsUnit (f : TailGerm)) : EventuallyNowhereZero f := by
  obtain ⟨G, hG⟩ := hf.exists_right_inv
  induction G using Filter.Germ.inductionOn with
  | _ g =>
      change ((fun x : Real ↦ f x * g x) : TailGerm) =
        ((fun _ : Real ↦ (1 : Real)) : TailGerm) at hG
      have hfg : ∀ᶠ x in (atTop : Filter Real), f x * g x = 1 :=
        Filter.Germ.coe_eq.mp hG
      obtain ⟨B, hB⟩ := eventually_atTop.1 hfg
      refine ⟨B, fun x hx hfx ↦ ?_⟩
      have hone := hB x hx.le
      rw [hfx, zero_mul] at hone
      exact zero_ne_one hone

theorem tailGerm_isUnit_iff_eventuallyNowhereZero (f : Real → Real) :
    IsUnit (f : TailGerm) ↔ EventuallyNowhereZero f :=
  ⟨eventuallyNowhereZero_of_tailGerm_isUnit,
    tailGerm_isUnit_of_eventuallyNowhereZero⟩

end

end Natfunbasis.Wilkie
