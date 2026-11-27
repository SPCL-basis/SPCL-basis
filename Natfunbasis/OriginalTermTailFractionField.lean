import Natfunbasis.OriginalTermAnalyticTailRing
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields inside the ring of tail germs

The full ring of real-valued germs at `+∞` has zero divisors.  Richardson's
argument instead constructs subrings in which every element is either zero or
already a unit of the ambient germ ring.  This file records the elementary but
important consequence: such a subring is an integral domain, and its fraction
field embeds canonically back into the ambient germ ring.

No analytic no-oscillation result is used here.  The only input is the explicit
zero-or-unit dichotomy, which the polynomial descent proves one extension at a
time.
-/

namespace Natfunbasis.Wilkie

noncomputable section

/-- A subring of tail germs has the Richardson unit dichotomy when each of its
elements is either zero in the subring or invertible in the ambient germ ring.

The second alternative is deliberately stated in `TailGerm`, rather than in
the subring: the inverse germ need not yet belong to the subring. -/
class TailGerm.UnitDichotomy (A : Subring TailGerm) : Prop where
  zero_or_isUnit : ∀ a : A, a = 0 ∨ IsUnit (a.1 : TailGerm)

namespace TailGerm.UnitDichotomy

variable (A : Subring TailGerm) [UnitDichotomy A]

/-- A zero-or-ambient-unit subring has no zero divisors. -/
instance instNoZeroDivisors : NoZeroDivisors A where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    rcases UnitDichotomy.zero_or_isUnit a with ha | ha
    · exact Or.inl ha
    · right
      apply Subtype.ext
      apply ha.mul_right_eq_zero.mp
      exact congrArg Subtype.val hab

/-- Consequently a zero-or-ambient-unit subring is an integral domain. -/
instance instIsDomain : IsDomain A where

/-- The inclusion of the distinguished subring into all tail germs. -/
def inclusion : A →+* TailGerm := A.subtype

private theorem inclusion_isUnit (y : nonZeroDivisors A) :
    IsUnit (inclusion A y) := by
  rcases UnitDichotomy.zero_or_isUnit (y : A) with hy | hy
  · exact False.elim ((mem_nonZeroDivisors_iff_ne_zero.mp y.property) hy)
  · exact hy

/-- The fraction field of `A`, mapped into the ambient germ ring by inverting
the denominators there. -/
def fractionMap : FractionRing A →+* TailGerm :=
  IsLocalization.lift (M := nonZeroDivisors A) (inclusion_isUnit A)

@[simp]
theorem fractionMap_algebraMap (a : A) :
    fractionMap A (algebraMap A (FractionRing A) a) = (a : TailGerm) := by
  exact DFunLike.congr_fun
    (IsLocalization.lift_comp (M := nonZeroDivisors A)
      (inclusion_isUnit A)) a

/-- The fraction-field map loses no information. -/
theorem fractionMap_injective : Function.Injective (fractionMap A) := by
  unfold fractionMap
  rw [IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsFractionRing.injective A (FractionRing A)).eq_iff]
  constructor
  · rintro rfl
    rfl
  · intro h
    apply A.subtype_injective
    exact h

/-- Every element of the embedded fraction field remains either zero or a
unit in the ambient germ ring. -/
theorem fractionMap_zero_or_isUnit (z : FractionRing A) :
    fractionMap A z = 0 ∨ IsUnit (fractionMap A z) := by
  obtain ⟨x, y, rfl⟩ :=
    IsLocalization.exists_mk'_eq (nonZeroDivisors A) z
  rw [fractionMap, IsLocalization.lift_mk']
  rcases UnitDichotomy.zero_or_isUnit x with hx | hx
  · left
    simp [hx]
  · right
    exact hx.mul (Units.isUnit _)

end TailGerm.UnitDichotomy

end

end Natfunbasis.Wilkie
