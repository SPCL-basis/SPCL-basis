import Natfunbasis.OriginalTermGermPolynomialExtensions
import Natfunbasis.OriginalTermAnalyticTailRing
import Natfunbasis.OriginalTermTailFractionField

/-!
# Fraction fields inside the analytic tail-germ ring

Richardson descent says that every represented polynomial is either zero as a
tail germ or eventually nowhere zero.  This file turns that dichotomy into
the algebra needed for the next extension stage:

* a unit of the ambient tail-germ ring represented by an analytic germ is
  already a unit of `AnalyticTailGerm`;
* the generic tail-germ fraction-field construction applies to the polynomial
  image;
* its embedded fraction field still consists of analytic germs.

Taking the fraction field of the image handles algebraic and transcendental
adjunctions uniformly: the kernel of polynomial evaluation is quotiented out
by the image type before fractions are formed.
-/

open scoped Differential
open Polynomial Filter

namespace Natfunbasis.Wilkie

noncomputable section

namespace TailGerm

/-- The pointwise inverse of an eventually analytic unit germ is eventually
analytic. -/
theorem EventuallyAnalytic.inv_of_isUnit {F : TailGerm}
    (hAnalytic : EventuallyAnalytic F) (hUnit : IsUnit F) :
    EventuallyAnalytic F⁻¹ := by
  obtain ⟨f, hFf, hfAnalytic⟩ := hAnalytic
  have hUnitf : IsUnit (f : TailGerm) := by
    rwa [← hFf]
  obtain ⟨B, hfNonzero⟩ :=
    eventuallyNowhereZero_of_tailGerm_isUnit hUnitf
  have hfNonzero' : ∀ᶠ x in (atTop : Filter Real), f x ≠ 0 :=
    eventually_atTop.2 ⟨B + 1, fun x hx ↦
      hfNonzero x (lt_of_lt_of_le (lt_add_one B) hx)⟩
  refine ⟨fun x ↦ (f x)⁻¹, ?_, ?_⟩
  · calc
      F⁻¹ = (f : TailGerm)⁻¹ := congrArg Inv.inv hFf
      _ = ((fun x ↦ (f x)⁻¹) : TailGerm) := rfl
  · filter_upwards [hfAnalytic, hfNonzero'] with x hfx hfx0
    exact hfx.inv hfx0

end TailGerm

namespace AnalyticTailGerm

/-- An eventually analytic germ which is invertible among all tail germs has
an eventually analytic inverse. -/
theorem isUnit_of_coe_isUnit {F : AnalyticTailGerm}
    (hF : IsUnit (F : TailGerm)) : IsUnit F := by
  obtain ⟨f, hFf, hfAnalytic⟩ := F.2
  have hUnitf : IsUnit (f : TailGerm) := by
    rwa [← hFf]
  obtain ⟨B, hfNonzero⟩ :=
    eventuallyNowhereZero_of_tailGerm_isUnit hUnitf
  have hfNonzero' : ∀ᶠ x in (atTop : Filter Real), f x ≠ 0 :=
    eventually_atTop.2 ⟨B + 1, fun x hx ↦
      hfNonzero x (lt_of_lt_of_le (lt_add_one B) hx)⟩
  let g : Real → Real := fun x ↦ (f x)⁻¹
  have hgAnalytic : ∀ᶠ x in (atTop : Filter Real), AnalyticAt Real g x := by
    filter_upwards [hfAnalytic, hfNonzero'] with x hfx hfx0
    exact hfx.inv hfx0
  let G : AnalyticTailGerm :=
    ⟨(g : TailGerm), TailGerm.eventuallyAnalytic_coe hgAnalytic⟩
  have hFG : F * G = 1 := by
    apply Subtype.ext
    change (F : TailGerm) * (g : TailGerm) = 1
    rw [hFf]
    apply Filter.EventuallyEq.germ_eq
    filter_upwards [hfNonzero'] with x hfx0
    exact mul_inv_cancel₀ hfx0
  have hGF : G * F = 1 := by
    simpa [mul_comm] using hFG
  exact ⟨⟨F, G, hFG, hGF⟩, rfl⟩

/-- Unit status for analytic tail germs can be checked after forgetting
analyticity. -/
theorem isUnit_iff_coe_isUnit (F : AnalyticTailGerm) :
    IsUnit F ↔ IsUnit (F : TailGerm) := by
  constructor
  · intro hF
    exact hF.map (TailGerm.analyticSubring.subtype)
  · exact isUnit_of_coe_isUnit

/-- A fixed analytic representative on a final tail. -/
def chosenRepresentative (F : AnalyticTailGerm) : Real → Real :=
  F.2.choose

theorem coe_chosenRepresentative (F : AnalyticTailGerm) :
    (chosenRepresentative F : TailGerm) = F :=
  F.2.choose_spec.1.symm

theorem chosenRepresentative_eventuallyAnalytic (F : AnalyticTailGerm) :
    ∀ᶠ x in (atTop : Filter Real),
      AnalyticAt Real (chosenRepresentative F) x :=
  F.2.choose_spec.2

theorem chosenRepresentative_eventuallyDifferentiable
    (F : AnalyticTailGerm) :
    ∃ B : Real, ∀ x : Real, B < x →
      DifferentiableAt Real (chosenRepresentative F) x := by
  obtain ⟨B, hB⟩ :=
    eventually_atTop.1 (chosenRepresentative_eventuallyAnalytic F)
  exact ⟨B, fun x hx ↦ (hB x hx.le).differentiableAt⟩

end AnalyticTailGerm

namespace RichardsonAnalyticFraction

variable {K : Type*} [Field K]

/-- Forget analyticity after applying a polynomial evaluation homomorphism. -/
def toTailPolynomialHom (Psi : K[X] →+* AnalyticTailGerm) :
    K[X] →+* TailGerm :=
  TailGerm.analyticSubring.subtype.comp Psi

/-- Canonical eventually analytic representatives of polynomial images. -/
def polynomialRepresentative (Psi : K[X] →+* AnalyticTailGerm)
    (p : K[X]) : Real → Real :=
  AnalyticTailGerm.chosenRepresentative (Psi p)

theorem polynomialRepresentative_represents
    (Psi : K[X] →+* AnalyticTailGerm) :
    RichardsonGermExtension.Represents (toTailPolynomialHom Psi)
      (polynomialRepresentative Psi) := by
  intro p
  exact AnalyticTailGerm.coe_chosenRepresentative (Psi p)

theorem polynomialRepresentative_eventuallyDifferentiable
    (Psi : K[X] →+* AnalyticTailGerm) :
    RichardsonGermExtension.EventuallyDifferentiable
      (polynomialRepresentative Psi) := by
  intro p
  exact AnalyticTailGerm.chosenRepresentative_eventuallyDifferentiable
    (Psi p)

/-- Differential compatibility in `AnalyticTailGerm` implies the germ-level
compatibility required by Richardson descent. -/
theorem germRealizesDerivation_of_deriv_eq
    [Differential K] (Psi : K[X] →+* AnalyticTailGerm)
    (D : K[X] → K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p)) :
    RichardsonGermExtension.GermRealizesDerivation
      (toTailPolynomialHom Psi) D := by
  intro p
  calc
    TailGerm.deriv ((toTailPolynomialHom Psi) p) =
        ((Psi p)′ : AnalyticTailGerm) := by
          symm
          exact AnalyticTailGerm.coe_deriv (Psi p)
    _ = Psi (D p) := congrArg Subtype.val (hD p)
    _ = (toTailPolynomialHom Psi) (D p) := rfl

/-- The representative dichotomy says precisely that every polynomial image
in the analytic germ ring is zero or a unit. -/
theorem isUnit_or_eq_zero_of_representativeTailDichotomy
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative) (p : K[X]) :
    IsUnit (Psi p) ∨ Psi p = 0 := by
  rcases hdich p with hpZero | hpNonzero
  · right
    apply Subtype.ext
    have hz : (representative p : TailGerm) = 0 :=
      (eventuallyZero_iff_tailGerm_eq_zero _).mp hpZero
    exact (hrep p).symm.trans hz
  · left
    apply AnalyticTailGerm.isUnit_of_coe_isUnit
    change IsUnit ((toTailPolynomialHom Psi) p)
    rw [← hrep p]
    exact tailGerm_isUnit_of_eventuallyNowhereZero hpNonzero

section DifferentialClosure

variable [Differential K]

/-- Primitive Richardson closure with canonical analytic representatives. -/
theorem analyticRepresentativeTailDichotomy_primitive
    (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c) p)) :
    RichardsonGermExtension.RepresentativeTailDichotomy
      (polynomialRepresentative Psi) := by
  apply RichardsonGermExtension.representativeTailDichotomy_primitive
    (toTailPolynomialHom Psi) (polynomialRepresentative Psi) c
  · exact polynomialRepresentative_represents Psi
  · exact polynomialRepresentative_eventuallyDifferentiable Psi
  · exact germRealizesDerivation_of_deriv_eq Psi
      (Differential.implicitDeriv (C c)) hD

/-- Exponential Richardson closure with canonical analytic representatives. -/
theorem analyticRepresentativeTailDichotomy_exponential
    (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hX : IsUnit ((toTailPolynomialHom Psi) X))
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c * X) p)) :
    RichardsonGermExtension.RepresentativeTailDichotomy
      (polynomialRepresentative Psi) := by
  apply RichardsonGermExtension.representativeTailDichotomy_exponential
    (toTailPolynomialHom Psi) (polynomialRepresentative Psi) c
  · exact polynomialRepresentative_represents Psi
  · exact polynomialRepresentative_eventuallyDifferentiable Psi
  · rw [← tailGerm_isUnit_iff_eventuallyNowhereZero]
    change IsUnit
      (AnalyticTailGerm.chosenRepresentative (Psi X) : TailGerm)
    rw [AnalyticTailGerm.coe_chosenRepresentative]
    exact hX
  · exact germRealizesDerivation_of_deriv_eq Psi
      (Differential.implicitDeriv (C c * X)) hD

end DifferentialClosure

/-- The actual polynomial-image subring inside the ambient tail-germ ring. -/
abbrev polynomialTailRange (Psi : K[X] →+* AnalyticTailGerm) :
    Subring TailGerm :=
  (toTailPolynomialHom Psi).range

/-- Every element of the polynomial tail range is eventually analytic. -/
theorem polynomialTailRange_eventuallyAnalytic
    (Psi : K[X] →+* AnalyticTailGerm)
    (a : polynomialTailRange Psi) :
    TailGerm.EventuallyAnalytic (a : TailGerm) := by
  obtain ⟨p, hp⟩ := a.property
  rw [← hp]
  exact (Psi p).2

/-- The representative dichotomy supplies the generic unit-dichotomy input
used by `OriginalTermTailFractionField`. -/
theorem polynomialTailRangeUnitDichotomy
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative) :
    TailGerm.UnitDichotomy (polynomialTailRange Psi) := by
  constructor
  intro a
  obtain ⟨p, hp⟩ := a.property
  rcases hdich p with hpZero | hpNonzero
  · left
    apply Subtype.ext
    have hz : (representative p : TailGerm) = 0 :=
      (eventuallyZero_iff_tailGerm_eq_zero _).mp hpZero
    exact hp.symm.trans ((hrep p).symm.trans hz)
  · right
    rw [← hp, ← hrep p]
    exact tailGerm_isUnit_of_eventuallyNowhereZero hpNonzero

/-- The generic injective fraction map for the polynomial tail range. -/
def polynomialTailFractionMap
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative) :
    FractionRing (polynomialTailRange Psi) →+* TailGerm := by
  letI := polynomialTailRangeUnitDichotomy Psi representative hrep hdich
  exact TailGerm.UnitDichotomy.fractionMap (polynomialTailRange Psi)

theorem polynomialTailFractionMap_injective
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative) :
    Function.Injective
      (polynomialTailFractionMap Psi representative hrep hdich) := by
  letI := polynomialTailRangeUnitDichotomy Psi representative hrep hdich
  exact TailGerm.UnitDichotomy.fractionMap_injective
    (polynomialTailRange Psi)

/-- The generic fraction map still lands in the eventually analytic
subring. -/
theorem polynomialTailFractionMap_eventuallyAnalytic
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative)
    (z : FractionRing (polynomialTailRange Psi)) :
    TailGerm.EventuallyAnalytic
      (polynomialTailFractionMap Psi representative hrep hdich z) := by
  letI := polynomialTailRangeUnitDichotomy Psi representative hrep hdich
  obtain ⟨x, y, rfl⟩ :=
    IsLocalization.exists_mk'_eq
      (nonZeroDivisors (polynomialTailRange Psi)) z
  rw [polynomialTailFractionMap,
    TailGerm.UnitDichotomy.fractionMap, IsLocalization.lift_mk']
  apply TailGerm.EventuallyAnalytic.mul
  · exact polynomialTailRange_eventuallyAnalytic Psi x
  · let u := IsUnit.liftRight
      ((TailGerm.UnitDichotomy.inclusion
        (polynomialTailRange Psi)).toMonoidHom.restrict
        (nonZeroDivisors (polynomialTailRange Psi)))
      (fun y ↦ by
        rcases TailGerm.UnitDichotomy.zero_or_isUnit
            (A := polynomialTailRange Psi) (y : polynomialTailRange Psi) with
          hy | hy
        · exact False.elim
            ((mem_nonZeroDivisors_iff_ne_zero.mp y.property) hy)
        · exact hy) y
    have huAnalytic : TailGerm.EventuallyAnalytic (u : TailGerm) := by
      change TailGerm.EventuallyAnalytic (y : TailGerm)
      exact polynomialTailRange_eventuallyAnalytic Psi y
    simpa [u] using huAnalytic.inv_of_isUnit u.isUnit

/-- Codomain restriction of the fraction map to analytic tail germs. -/
def polynomialAnalyticFractionMap
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative) :
    FractionRing (polynomialTailRange Psi) →+* AnalyticTailGerm :=
  (polynomialTailFractionMap Psi representative hrep hdich).codRestrict
    TailGerm.analyticSubring
    (polynomialTailFractionMap_eventuallyAnalytic
      Psi representative hrep hdich)

theorem polynomialAnalyticFractionMap_injective
    (Psi : K[X] →+* AnalyticTailGerm)
    (representative : K[X] → Real → Real)
    (hrep : RichardsonGermExtension.Represents
      (toTailPolynomialHom Psi) representative)
    (hdich : RichardsonGermExtension.RepresentativeTailDichotomy
      representative) :
    Function.Injective
      (polynomialAnalyticFractionMap Psi representative hrep hdich) := by
  intro x y hxy
  apply polynomialTailFractionMap_injective Psi representative hrep hdich
  exact congrArg Subtype.val hxy

end RichardsonAnalyticFraction

end

end Natfunbasis.Wilkie
