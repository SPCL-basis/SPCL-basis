import Natfunbasis.OriginalTermTailGerm
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# The differential ring of analytic germs at positive infinity

The Richardson argument works in fields of germs rather than in rings of
globally defined functions: a reciprocal may fail at finitely many points but
is well defined on a final tail.  This file constructs the ambient
commutative differential ring of germs which admit an analytic representative
on a final tail.

No no-oscillation theorem is assumed here.  In particular, this ambient ring
is not declared to be a field.  The later Richardson closure argument will
identify subrings in which every nonzero element is a unit.
-/

namespace Natfunbasis.Wilkie

open Filter
open scoped Differential

noncomputable section

namespace TailGerm

/-- A germ has an analytic representative at every sufficiently large real
input.  Existential representatives make the definition independent of any
choice of quotient representative. -/
def EventuallyAnalytic (F : TailGerm) : Prop :=
  ∃ f : Real → Real, F = (f : TailGerm) ∧
    ∀ᶠ x in (atTop : Filter Real), AnalyticAt Real f x

theorem eventuallyAnalytic_coe {f : Real → Real}
    (hf : ∀ᶠ x in (atTop : Filter Real), AnalyticAt Real f x) :
    EventuallyAnalytic (f : TailGerm) :=
  ⟨f, rfl, hf⟩

theorem EventuallyAnalytic.zero : EventuallyAnalytic (0 : TailGerm) := by
  refine ⟨fun _ : Real ↦ 0, rfl, ?_⟩
  exact Filter.Eventually.of_forall fun _ ↦ analyticAt_const

theorem EventuallyAnalytic.one : EventuallyAnalytic (1 : TailGerm) := by
  refine ⟨fun _ : Real ↦ 1, rfl, ?_⟩
  exact Filter.Eventually.of_forall fun _ ↦ analyticAt_const

theorem EventuallyAnalytic.add {F G : TailGerm}
    (hF : EventuallyAnalytic F) (hG : EventuallyAnalytic G) :
    EventuallyAnalytic (F + G) := by
  obtain ⟨f, rfl, hf⟩ := hF
  obtain ⟨g, rfl, hg⟩ := hG
  refine ⟨fun x ↦ f x + g x, rfl, ?_⟩
  filter_upwards [hf, hg] with x hfx hgx
  exact hfx.add hgx

theorem EventuallyAnalytic.neg {F : TailGerm}
    (hF : EventuallyAnalytic F) : EventuallyAnalytic (-F) := by
  obtain ⟨f, rfl, hf⟩ := hF
  refine ⟨fun x ↦ -f x, rfl, ?_⟩
  filter_upwards [hf] with x hfx
  exact hfx.neg

theorem EventuallyAnalytic.mul {F G : TailGerm}
    (hF : EventuallyAnalytic F) (hG : EventuallyAnalytic G) :
    EventuallyAnalytic (F * G) := by
  obtain ⟨f, rfl, hf⟩ := hF
  obtain ⟨g, rfl, hg⟩ := hG
  refine ⟨fun x ↦ f x * g x, rfl, ?_⟩
  filter_upwards [hf, hg] with x hfx hgx
  exact hfx.mul hgx

/-- The analytic-at-infinity germs form a commutative subring of all real
germs at infinity. -/
def analyticSubring : Subring TailGerm where
  carrier := EventuallyAnalytic
  zero_mem' := EventuallyAnalytic.zero
  one_mem' := EventuallyAnalytic.one
  add_mem' := EventuallyAnalytic.add
  neg_mem' := EventuallyAnalytic.neg
  mul_mem' := EventuallyAnalytic.mul

/-- Differentiating an eventually analytic germ again gives an eventually
analytic germ. -/
theorem EventuallyAnalytic.deriv {F : TailGerm}
    (hF : EventuallyAnalytic F) : EventuallyAnalytic (TailGerm.deriv F) := by
  obtain ⟨f, hF, hf⟩ := hF
  refine ⟨_ , (congrArg TailGerm.deriv hF).trans (TailGerm.deriv_coe f), ?_⟩
  filter_upwards [hf] with x hfx
  exact hfx.deriv

end TailGerm

/-- The concrete ring type of eventually analytic germs. -/
abbrev AnalyticTailGerm := TailGerm.analyticSubring

namespace AnalyticTailGerm

/-- Ordinary differentiation on representatives, descended to analytic tail
germs. -/
def deriv (F : AnalyticTailGerm) : AnalyticTailGerm :=
  ⟨TailGerm.deriv F.1, F.2.deriv⟩

@[simp]
theorem coe_deriv (F : AnalyticTailGerm) :
    (deriv F : TailGerm) = TailGerm.deriv F :=
  rfl

@[simp]
theorem deriv_zero : deriv (0 : AnalyticTailGerm) = 0 := by
  apply Subtype.ext
  change TailGerm.deriv (0 : TailGerm) = 0
  apply Filter.EventuallyEq.germ_eq
  exact Filter.Eventually.of_forall fun x ↦ by simp

@[simp]
theorem deriv_add (F G : AnalyticTailGerm) :
    deriv (F + G) = deriv F + deriv G := by
  apply Subtype.ext
  change TailGerm.deriv (F.1 + G.1) =
    TailGerm.deriv F.1 + TailGerm.deriv G.1
  obtain ⟨f, hF, hf⟩ := F.2
  obtain ⟨g, hG, hg⟩ := G.2
  rw [hF, hG]
  apply Filter.EventuallyEq.germ_eq
  filter_upwards [hf, hg] with x hfx hgx
  exact _root_.deriv_add hfx.differentiableAt hgx.differentiableAt

@[simp]
theorem deriv_mul (F G : AnalyticTailGerm) :
    deriv (F * G) = deriv F * G + F * deriv G := by
  apply Subtype.ext
  change TailGerm.deriv (F.1 * G.1) =
    TailGerm.deriv F.1 * G.1 + F.1 * TailGerm.deriv G.1
  obtain ⟨f, hF, hf⟩ := F.2
  obtain ⟨g, hG, hg⟩ := G.2
  rw [hF, hG]
  apply Filter.EventuallyEq.germ_eq
  filter_upwards [hf, hg] with x hfx hgx
  simpa [add_comm, mul_comm] using
    (_root_.deriv_fun_mul hfx.differentiableAt hgx.differentiableAt)

/-- The additive homomorphism underlying germ differentiation. -/
def derivAddHom : AnalyticTailGerm →+ AnalyticTailGerm where
  toFun := deriv
  map_zero' := deriv_zero
  map_add' := deriv_add

/-- The analytic germ derivative as an integer-linear map. -/
def derivLinearMap : AnalyticTailGerm →ₗ[ℤ] AnalyticTailGerm :=
  derivAddHom.toIntLinearMap

/-- Analytic germs at positive infinity carry the expected differential-ring
structure. -/
instance instDifferential : Differential AnalyticTailGerm where
  deriv := Derivation.mk' derivLinearMap fun F G ↦ by
    change deriv (F * G) = F * deriv G + G * deriv F
    rw [deriv_mul]
    ac_rfl

@[simp]
theorem differential_deriv_eq (F : AnalyticTailGerm) : F′ = deriv F :=
  rfl

end AnalyticTailGerm

end

end Natfunbasis.Wilkie
