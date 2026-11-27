import Natfunbasis.WilkieAnalyticDifferential
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The differential fraction field of positive analytic functions

A derivation on an integral domain extends canonically to its fraction field.
Mathlib does not currently provide this localization construction directly,
so this file constructs it through dual numbers.  The ring homomorphism

`a ↦ a + D(a)ε`

sends every non-zero denominator to a unit.  Its localization lift has the
form `x ↦ x + D̃(x)ε`; taking the `ε`-coefficient gives the extended
derivation.

The construction is algebraic and generic.  At the end of the file it is
specialized to the analytic-function domain from
`WilkieAnalyticPrerequisites`.  Identifying the constants of this differential
field is deliberately *not* part of this construction.
-/

namespace Natfunbasis.Wilkie

noncomputable section

namespace FractionDerivation

variable {A : Type*} [CommRing A] [IsDomain A]

private abbrev Frac := FractionRing A

/- `FractionRing A` also inherits an `Int`-algebra structure through the
localization.  We use the canonical structure attached to its ring here, so
that the resulting derivation is definitionally the one expected by
`Differential`. -/
local instance fracIntAlgebra : Algebra Int (Frac (A := A)) :=
  Ring.toIntAlgebra (Frac (A := A))

/-- The dual-number homomorphism attached to a derivation on an integral
domain. -/
def dualMap (D : Derivation Int A A) : A →+* DualNumber (Frac (A := A)) where
  toFun a :=
    (algebraMap A (Frac (A := A)) a,
      algebraMap A (Frac (A := A)) (D a))
  map_zero' := by
    ext <;> simp
  map_one' := by
    ext <;> simp
  map_add' := by
    intro a b
    ext <;> simp
  map_mul' := by
    intro a b
    ext
    · simp
    · change algebraMap A (Frac (A := A)) (D (a * b)) =
        algebraMap A (Frac (A := A)) a *
            algebraMap A (Frac (A := A)) (D b) +
          algebraMap A (Frac (A := A)) (D a) *
            algebraMap A (Frac (A := A)) b
      rw [D.leibniz]
      simp
      ring

omit [IsDomain A] in
@[simp]
theorem dualMap_fst (D : Derivation Int A A) (a : A) :
    (dualMap D a).fst = algebraMap A (Frac (A := A)) a :=
  rfl

omit [IsDomain A] in
@[simp]
theorem dualMap_snd (D : Derivation Int A A) (a : A) :
    (dualMap D a).snd = algebraMap A (Frac (A := A)) (D a) :=
  rfl

private theorem dualMap_isUnit (D : Derivation Int A A)
    (y : nonZeroDivisors A) : IsUnit (dualMap D (y : A)) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit (algebraMap A (Frac (A := A)) (y : A))
  exact isUnit_iff_ne_zero.mpr
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property)

/-- The localization lift `Frac(A) → DualNumber (Frac(A))` of
`a ↦ a + D(a)ε`. -/
def dualLift (D : Derivation Int A A) :
    Frac (A := A) →+* DualNumber (Frac (A := A)) :=
  IsLocalization.lift (M := nonZeroDivisors A) (dualMap_isUnit D)

@[simp]
theorem dualLift_algebraMap (D : Derivation Int A A) (a : A) :
    dualLift D (algebraMap A (Frac (A := A)) a) = dualMap D a := by
  exact DFunLike.congr_fun
    (IsLocalization.lift_comp (M := nonZeroDivisors A) (dualMap_isUnit D)) a

/-- The ordinary component of the dual-number lift is the identity. -/
@[simp]
theorem dualLift_fst (D : Derivation Int A A) (x : Frac (A := A)) :
    (dualLift D x).fst = x := by
  let p : Frac (A := A) →+* Frac (A := A) :=
    (TrivSqZeroExt.fstHom (Frac (A := A)) (Frac (A := A))
      (Frac (A := A))).toRingHom.comp (dualLift D)
  have hp : p = RingHom.id (Frac (A := A)) := by
    apply IsFractionRing.ringHom_ext (A := A) (K := Frac (A := A))
    intro a
    simp [p]
  change p x = x
  rw [hp]
  rfl

/-- The coefficient of `ε` in the localized dual-number homomorphism. -/
def lift (D : Derivation Int A A) (x : Frac (A := A)) : Frac (A := A) :=
  (dualLift D x).snd

@[simp]
theorem lift_algebraMap (D : Derivation Int A A) (a : A) :
    lift D (algebraMap A (Frac (A := A)) a) =
      algebraMap A (Frac (A := A)) (D a) := by
  simp [lift]

@[simp]
theorem lift_zero (D : Derivation Int A A) : lift D 0 = 0 := by
  simp [lift]

@[simp]
theorem lift_add (D : Derivation Int A A) (x y : Frac (A := A)) :
    lift D (x + y) = lift D x + lift D y := by
  simp [lift]

@[simp]
theorem lift_mul (D : Derivation Int A A) (x y : Frac (A := A)) :
    lift D (x * y) = x * lift D y + y * lift D x := by
  change (dualLift D (x * y)).snd =
    x * (dualLift D y).snd + y * (dualLift D x).snd
  rw [map_mul, DualNumber.snd_mul, dualLift_fst, dualLift_fst]
  ring

/-- The additive homomorphism underlying the localized derivation. -/
def liftAddHom (D : Derivation Int A A) :
    Frac (A := A) →+ Frac (A := A) where
  toFun := lift D
  map_zero' := lift_zero D
  map_add' := lift_add D

/-- The canonical extension of an integer-linear derivation from an integral
domain to its fraction field. -/
def extend (D : Derivation Int A A) :
    Derivation Int (Frac (A := A)) (Frac (A := A)) :=
  Derivation.mk' (liftAddHom D).toIntLinearMap (by
    intro x y
    change lift D (x * y) = x * lift D y + y * lift D x
    exact lift_mul D x y)

@[simp]
theorem extend_apply (D : Derivation Int A A) (x : Frac (A := A)) :
    extend D x = lift D x :=
  rfl

/-- The extension agrees with the original derivation on the base domain. -/
@[simp]
theorem extend_algebraMap (D : Derivation Int A A) (a : A) :
    extend D (algebraMap A (Frac (A := A)) a) =
      algebraMap A (Frac (A := A)) (D a) := by
  simp [extend_apply]

/-- The exact quotient rule on fractions represented by elements of the base
domain.  This form is valid even when `b = 0`, using the field convention
`0⁻¹ = 0`. -/
@[simp]
theorem extend_div_algebraMap (D : Derivation Int A A) (a b : A) :
    extend D
        (algebraMap A (Frac (A := A)) a /
          algebraMap A (Frac (A := A)) b) =
      (algebraMap A (Frac (A := A)) (D a) *
          algebraMap A (Frac (A := A)) b -
        algebraMap A (Frac (A := A)) a *
          algebraMap A (Frac (A := A)) (D b)) /
        (algebraMap A (Frac (A := A)) b) ^ 2 := by
  rw [(extend D).leibniz_div]
  simp only [extend_algebraMap, smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

end FractionDerivation

/-- The fraction field of the integral domain of real-analytic functions on
the positive axis. -/
abbrev PositiveAnalyticFractionField := FractionRing PositiveAnalyticFunction

namespace PositiveAnalyticFractionField

local instance intAlgebra : Algebra Int PositiveAnalyticFractionField :=
  Ring.toIntAlgebra PositiveAnalyticFractionField

/-- Ordinary differentiation, extended from positive analytic functions to
their fraction field. -/
def derivation : Derivation Int PositiveAnalyticFractionField
    PositiveAnalyticFractionField :=
  FractionDerivation.extend PositiveAnalyticFunction.derivation

@[simp]
theorem derivation_apply (x : PositiveAnalyticFractionField) :
    derivation x =
      FractionDerivation.lift PositiveAnalyticFunction.derivation x :=
  rfl

/-- Leibniz's rule for the named fraction-field derivation.  Keeping this
as a theorem avoids exposing the implementation's local `Int`-algebra
instance to downstream files. -/
theorem derivation_mul (x y : PositiveAnalyticFractionField) :
    derivation (x * y) = x * derivation y + y * derivation x := by
  exact derivation.leibniz x y

/-- Additivity of the named fraction-field derivation. -/
theorem derivation_add (x y : PositiveAnalyticFractionField) :
    derivation (x + y) = derivation x + derivation y := by
  exact map_add derivation x y

/-- Integer constants have zero derivative.  This named wrapper, like
`derivation_mul`, hides the implementation-local `Int`-algebra instance. -/
@[simp]
theorem derivation_intCast (m : Int) :
    derivation (m : PositiveAnalyticFractionField) = 0 := by
  simpa using derivation.map_intCast m

/-- Leibniz's rule for integral powers in the named analytic fraction-field
derivation. -/
theorem derivation_zpow (x : PositiveAnalyticFractionField) (m : Int) :
    derivation (x ^ m) =
      (m : PositiveAnalyticFractionField) * x ^ (m - 1) * derivation x := by
  simpa only [smul_eq_mul, zsmul_eq_mul, mul_assoc] using
    derivation.leibniz_zpow x m

@[simp]
theorem derivation_algebraMap (f : PositiveAnalyticFunction) :
    derivation (algebraMap PositiveAnalyticFunction
      PositiveAnalyticFractionField f) =
      algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
        (PositiveAnalyticFunction.derivation f) := by
  exact FractionDerivation.extend_algebraMap
    PositiveAnalyticFunction.derivation f

/-- The quotient rule for the canonical fraction-field derivation. -/
@[simp]
theorem derivation_div_algebraMap (f g : PositiveAnalyticFunction) :
    derivation
        (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField f /
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g) =
      (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
          (PositiveAnalyticFunction.derivation f) *
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g -
        algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField f *
          algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField
            (PositiveAnalyticFunction.derivation g)) /
        (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField g) ^ 2 := by
  exact FractionDerivation.extend_div_algebraMap
    PositiveAnalyticFunction.derivation f g

/-- The analytic fraction field, with its canonical differential-field
structure. -/
instance : Differential PositiveAnalyticFractionField where
  deriv := derivation

end PositiveAnalyticFractionField

end


end Natfunbasis.Wilkie
