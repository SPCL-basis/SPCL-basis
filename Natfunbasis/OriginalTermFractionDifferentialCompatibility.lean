import Natfunbasis.OriginalTermTailFractionField
import Natfunbasis.WilkieFractionDifferential

/-!
# Differential compatibility of fraction-field realizations

The Richardson construction repeatedly embeds a differential integral domain
in a ring of analytic germs and then replaces it by its fraction field.  This
file proves, generically, that the localization lift still commutes with the
derivations.  The proof compares two homomorphisms into dual numbers and uses
the universal property of the fraction field, avoiding any choice of fraction
representatives.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

namespace FractionDerivation

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Apply a ring homomorphism to both coefficients of a dual number. -/
def mapDual (f : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := (f z.fst, f z.snd)
  map_zero' := by
    ext <;> simp
  map_one' := by
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp

@[simp]
theorem mapDual_fst (f : A →+* B) (z : DualNumber A) :
    (mapDual f z).fst = f z.fst :=
  rfl

@[simp]
theorem mapDual_snd (f : A →+* B) (z : DualNumber A) :
    (mapDual f z).snd = f z.snd :=
  rfl

variable [Differential B]

/-- The dual-number homomorphism `b ↦ b + b'ε` attached to the
differential-ring structure on `B`. -/
def differentialDualMap : B →+* DualNumber B where
  toFun b := (b, b′)
  map_zero' := by
    ext <;> simp
  map_one' := by
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp
  map_mul' := by
    intro x y
    ext
    · simp
    · change (x * y)′ = x * y′ + x′ * y
      rw [Differential.deriv.leibniz]
      simp only [smul_eq_mul]
      ring

@[simp]
theorem differentialDualMap_fst (b : B) :
    (differentialDualMap b).fst = b :=
  rfl

@[simp]
theorem differentialDualMap_snd (b : B) :
    (differentialDualMap b).snd = b′ :=
  rfl

variable [IsDomain A] [Differential A]

/-- A fraction-field localization lift commutes with differentiation whenever
the original coefficient homomorphism does.

This is the generic differential compatibility needed at every Richardson
primitive or exponential adjunction. -/
theorem localizationLift_extend_commutes
    (g : A →+* B)
    (hg : ∀ y : nonZeroDivisors A, IsUnit (g y))
    (hderiv : ∀ a : A, (g a)′ = g a′)
    (z : FractionRing A) :
    (IsLocalization.lift (M := nonZeroDivisors A) hg z)′ =
      IsLocalization.lift (M := nonZeroDivisors A) hg
        (FractionDerivation.extend Differential.deriv z) := by
  let L : FractionRing A →+* B :=
    IsLocalization.lift (M := nonZeroDivisors A) hg
  let viaAmbient : FractionRing A →+* DualNumber B :=
    differentialDualMap.comp L
  let viaFraction : FractionRing A →+* DualNumber B :=
    (mapDual L).comp (FractionDerivation.dualLift Differential.deriv)
  have hmaps : viaAmbient = viaFraction := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    apply RingHom.ext
    intro a
    ext
    · simp [viaAmbient, viaFraction, L]
    · simp [viaAmbient, viaFraction, L, hderiv]
  have hz := DFunLike.congr_fun hmaps z
  exact congrArg TrivSqZeroExt.snd hz

/-- The same compatibility in the conventional map-first orientation. -/
theorem localizationLift_extend_commutes'
    (g : A →+* B)
    (hg : ∀ y : nonZeroDivisors A, IsUnit (g y))
    (hderiv : ∀ a : A, (g a)′ = g a′)
    (z : FractionRing A) :
    IsLocalization.lift (M := nonZeroDivisors A) hg
        (FractionDerivation.extend Differential.deriv z) =
      (IsLocalization.lift (M := nonZeroDivisors A) hg z)′ :=
  (localizationLift_extend_commutes g hg hderiv z).symm

end FractionDerivation

end

end Natfunbasis.Wilkie
