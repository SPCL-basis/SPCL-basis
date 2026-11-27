import Natfunbasis.OriginalTermAnalyticGermFraction
import Natfunbasis.OriginalTermFractionDifferentialCompatibility

/-!
# Differential analytic-germ adjunctions

This file packages one Richardson adjunction as an honest differential field
embedded in the ring of analytic germs at positive infinity.  Starting from a
polynomial evaluation `Psi : K[X] -> AnalyticTailGerm` which commutes with a
polynomial derivation, we

* put the induced derivation on its actual image in `TailGerm`;
* take the fraction field of that image;
* embed the fraction field injectively in `AnalyticTailGerm`; and
* prove that this embedding commutes with the extended derivation.

The primitive and exponential constructors at the end discharge the required
zero-or-unit dichotomy by Richardson descent.  Because the construction uses
the actual polynomial image, algebraic and transcendental generators are
handled uniformly.
-/

open Filter Polynomial
open scoped Differential

namespace Natfunbasis.Wilkie

noncomputable section

namespace RichardsonAnalyticAdjunction

variable {K : Type*} [Field K]

/-- Polynomial evaluation in the analytic tail-germ ring. -/
def polynomialEvalHom (iota : K →+* AnalyticTailGerm)
    (theta : AnalyticTailGerm) : K[X] →+* AnalyticTailGerm :=
  Polynomial.eval₂RingHom iota theta

section PolynomialEvaluation

variable [Differential K]

/-- A differential coefficient embedding and a generator satisfying its
prescribed ODE make polynomial evaluation commute with the corresponding
implicit derivation. -/
theorem polynomialEvalHom_deriv_implicit
    (iota : K →+* AnalyticTailGerm) (theta : AnalyticTailGerm)
    (v : K[X])
    (hiota : ∀ a : K, (iota a)′ = iota a′)
    (htheta : theta′ = polynomialEvalHom iota theta v)
    (p : K[X]) :
    (polynomialEvalHom iota theta p)′ =
      polynomialEvalHom iota theta
        (Differential.implicitDeriv v p) := by
  letI : Algebra K AnalyticTailGerm := iota.toAlgebra
  letI : DifferentialAlgebra K AnalyticTailGerm := ⟨hiota⟩
  have h :=
    Differential.deriv_aeval_eq_implicitDeriv theta v htheta p
  rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at h
  exact h

/-- The primitive specialization of
`polynomialEvalHom_deriv_implicit`. -/
theorem polynomialEvalHom_deriv_primitive
    (iota : K →+* AnalyticTailGerm) (theta : AnalyticTailGerm)
    (c : K)
    (hiota : ∀ a : K, (iota a)′ = iota a′)
    (htheta : theta′ = iota c)
    (p : K[X]) :
    (polynomialEvalHom iota theta p)′ =
      polynomialEvalHom iota theta
        (Differential.implicitDeriv (C c) p) := by
  apply polynomialEvalHom_deriv_implicit iota theta (C c) hiota
  simpa [polynomialEvalHom] using htheta

/-- The exponential specialization of
`polynomialEvalHom_deriv_implicit`. -/
theorem polynomialEvalHom_deriv_exponential
    (iota : K →+* AnalyticTailGerm) (theta : AnalyticTailGerm)
    (c : K)
    (hiota : ∀ a : K, (iota a)′ = iota a′)
    (htheta : theta′ = iota c * theta)
    (p : K[X]) :
    (polynomialEvalHom iota theta p)′ =
      polynomialEvalHom iota theta
        (Differential.implicitDeriv (C c * X) p) := by
  apply polynomialEvalHom_deriv_implicit iota theta (C c * X) hiota
  simpa [polynomialEvalHom] using htheta

end PolynomialEvaluation

private abbrev TailRange (Psi : K[X] →+* AnalyticTailGerm) :=
  RichardsonAnalyticFraction.polynomialTailRange Psi

/- Keep the integer-algebra structure definitionally aligned with the one
used by `FractionDerivation.extend`. -/
local instance tailRangeFractionIntAlgebra
    (Psi : K[X] →+* AnalyticTailGerm) :
    Algebra Int (FractionRing (TailRange Psi)) :=
  Ring.toIntAlgebra (FractionRing (TailRange Psi))

/-- The polynomial image in tail germs, regarded again as analytic germs. -/
def rangeToAnalytic (Psi : K[X] →+* AnalyticTailGerm) :
    TailRange Psi →+* AnalyticTailGerm :=
  (TailGerm.UnitDichotomy.inclusion (TailRange Psi)).codRestrict
    TailGerm.analyticSubring
    (RichardsonAnalyticFraction.polynomialTailRange_eventuallyAnalytic Psi)

@[simp]
theorem coe_rangeToAnalytic (Psi : K[X] →+* AnalyticTailGerm)
    (a : TailRange Psi) :
    ((rangeToAnalytic Psi a : AnalyticTailGerm) : TailGerm) = a :=
  rfl

theorem rangeToAnalytic_injective (Psi : K[X] →+* AnalyticTailGerm) :
    Function.Injective (rangeToAnalytic Psi) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z : AnalyticTailGerm ↦ (z : TailGerm)) hab

@[simp]
theorem rangeToAnalytic_rangeRestrict
    (Psi : K[X] →+* AnalyticTailGerm) (p : K[X]) :
    rangeToAnalytic Psi
        ((RichardsonAnalyticFraction.toTailPolynomialHom Psi).rangeRestrict p) =
      Psi p := by
  apply Subtype.ext
  rfl

/-- The ambient analytic derivative of an element in the polynomial range
still belongs to that range, provided polynomial evaluation commutes with
`D`. -/
def rangeDerivValue (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (a : TailRange Psi) : TailRange Psi := by
  refine ⟨TailGerm.deriv a.1, ?_⟩
  obtain ⟨p, hp⟩ := a.property
  refine ⟨D p, ?_⟩
  calc
    (RichardsonAnalyticFraction.toTailPolynomialHom Psi) (D p) =
        ((Psi (D p) : AnalyticTailGerm) : TailGerm) := rfl
    _ = (((Psi p)′ : AnalyticTailGerm) : TailGerm) :=
      congrArg Subtype.val (hD p).symm
    _ = TailGerm.deriv ((Psi p : AnalyticTailGerm) : TailGerm) :=
      AnalyticTailGerm.coe_deriv (Psi p)
    _ = TailGerm.deriv a.1 := congrArg TailGerm.deriv hp

@[simp]
theorem coe_rangeDerivValue (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (a : TailRange Psi) :
    ((rangeDerivValue Psi D hD a : TailRange Psi) : TailGerm) =
      TailGerm.deriv a :=
  rfl

/-- Additive part of differentiation on the polynomial tail range. -/
def rangeDerivAddHom (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p)) :
    TailRange Psi →+ TailRange Psi where
  toFun := rangeDerivValue Psi D hD
  map_zero' := by
    apply Subtype.ext
    change TailGerm.deriv (0 : TailGerm) = 0
    exact congrArg Subtype.val AnalyticTailGerm.deriv_zero
  map_add' := by
    intro a b
    apply Subtype.ext
    change TailGerm.deriv (a.1 + b.1) =
      TailGerm.deriv a.1 + TailGerm.deriv b.1
    exact congrArg Subtype.val
      (AnalyticTailGerm.deriv_add (rangeToAnalytic Psi a)
        (rangeToAnalytic Psi b))

/-- The derivation induced on the actual polynomial image. -/
def rangeDerivation (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p)) :
    Derivation Int (TailRange Psi) (TailRange Psi) :=
  Derivation.mk' (rangeDerivAddHom Psi D hD).toIntLinearMap (by
    intro a b
    apply Subtype.ext
    change TailGerm.deriv (a.1 * b.1) =
      a.1 * TailGerm.deriv b.1 + b.1 * TailGerm.deriv a.1
    have h : TailGerm.deriv (a.1 * b.1) =
        TailGerm.deriv a.1 * b.1 + a.1 * TailGerm.deriv b.1 :=
      congrArg (fun z : AnalyticTailGerm ↦ (z : TailGerm))
        (AnalyticTailGerm.deriv_mul (rangeToAnalytic Psi a)
          (rangeToAnalytic Psi b))
    simpa [add_comm, mul_comm] using h)

@[simp]
theorem rangeDerivation_apply (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (a : TailRange Psi) :
    rangeDerivation Psi D hD a = rangeDerivValue Psi D hD a :=
  rfl

/-- The named differential-ring structure on the polynomial image. -/
@[reducible]
def rangeDifferential (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p)) :
    Differential (TailRange Psi) :=
  ⟨rangeDerivation Psi D hD⟩

/-- The inclusion of the polynomial image in analytic germs commutes with the
induced derivation. -/
theorem rangeToAnalytic_deriv (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (a : TailRange Psi) :
    (rangeToAnalytic Psi a)′ =
      rangeToAnalytic Psi (rangeDerivation Psi D hD a) := by
  apply Subtype.ext
  rfl

private theorem rangeToAnalytic_isUnit
    (Psi : K[X] →+* AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy (TailRange Psi))
    (y : nonZeroDivisors (TailRange Psi)) :
    IsUnit (rangeToAnalytic Psi y) := by
  letI := hunit
  apply AnalyticTailGerm.isUnit_of_coe_isUnit
  change IsUnit ((y : TailRange Psi) : TailGerm)
  rcases TailGerm.UnitDichotomy.zero_or_isUnit
      (A := TailRange Psi) (y : TailRange Psi) with hy | hy
  · exact False.elim
      ((mem_nonZeroDivisors_iff_ne_zero.mp y.property) hy)
  · exact hy

/-- The fraction field of the polynomial image, embedded in analytic tail
germs. -/
def fractionMap (Psi : K[X] →+* AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy (TailRange Psi)) :
    FractionRing (TailRange Psi) →+* AnalyticTailGerm :=
  IsLocalization.lift (M := nonZeroDivisors (TailRange Psi))
    (rangeToAnalytic_isUnit Psi hunit)

@[simp]
theorem fractionMap_algebraMap
    (Psi : K[X] →+* AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy (TailRange Psi))
    (a : TailRange Psi) :
    fractionMap Psi hunit
        (algebraMap (TailRange Psi) (FractionRing (TailRange Psi)) a) =
      rangeToAnalytic Psi a := by
  exact DFunLike.congr_fun
    (IsLocalization.lift_comp (M := nonZeroDivisors (TailRange Psi))
      (rangeToAnalytic_isUnit Psi hunit)) a

/-- The old coefficient field inside the new fraction field. -/
def coefficientMap (Psi : K[X] →+* AnalyticTailGerm) :
    K →+* FractionRing (TailRange Psi) :=
  (algebraMap (TailRange Psi) (FractionRing (TailRange Psi))).comp
    ((RichardsonAnalyticFraction.toTailPolynomialHom Psi).rangeRestrict.comp C)

/-- The newly adjoined polynomial generator inside the new fraction field. -/
def generator (Psi : K[X] →+* AnalyticTailGerm) :
    FractionRing (TailRange Psi) :=
  algebraMap (TailRange Psi) (FractionRing (TailRange Psi))
    ((RichardsonAnalyticFraction.toTailPolynomialHom Psi).rangeRestrict X)

@[simp]
theorem fractionMap_coefficient
    (Psi : K[X] →+* AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy (TailRange Psi)) (a : K) :
    fractionMap Psi hunit (coefficientMap Psi a) = Psi (C a) := by
  rw [coefficientMap, RingHom.comp_apply, RingHom.comp_apply,
    fractionMap_algebraMap, rangeToAnalytic_rangeRestrict]

@[simp]
theorem fractionMap_generator
    (Psi : K[X] →+* AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy (TailRange Psi)) :
    fractionMap Psi hunit (generator Psi) = Psi X := by
  rw [generator, fractionMap_algebraMap, rangeToAnalytic_rangeRestrict]

@[simp]
theorem fractionMap_polynomialEval_coefficient
    (iota : K →+* AnalyticTailGerm) (theta : AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy
      (TailRange (polynomialEvalHom iota theta))) (a : K) :
    fractionMap (polynomialEvalHom iota theta) hunit
        (coefficientMap (polynomialEvalHom iota theta) a) = iota a := by
  rw [fractionMap_coefficient]
  simp [polynomialEvalHom]

@[simp]
theorem fractionMap_polynomialEval_generator
    (iota : K →+* AnalyticTailGerm) (theta : AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy
      (TailRange (polynomialEvalHom iota theta))) :
    fractionMap (polynomialEvalHom iota theta) hunit
        (generator (polynomialEvalHom iota theta)) = theta := by
  rw [fractionMap_generator]
  simp [polynomialEvalHom]

theorem fractionMap_injective (Psi : K[X] →+* AnalyticTailGerm)
    (hunit : TailGerm.UnitDichotomy (TailRange Psi)) :
    Function.Injective (fractionMap Psi hunit) := by
  letI := hunit
  unfold fractionMap
  rw [IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsFractionRing.injective (TailRange Psi)
    (FractionRing (TailRange Psi))).eq_iff]
  constructor
  · rintro rfl
    rfl
  · intro hxy
    exact rangeToAnalytic_injective Psi hxy

/-- The induced range derivation, extended to the fraction field. -/
def fractionDerivation (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (hunit : TailGerm.UnitDichotomy (TailRange Psi)) :
    Derivation Int (FractionRing (TailRange Psi))
      (FractionRing (TailRange Psi)) := by
  letI := hunit
  exact FractionDerivation.extend (rangeDerivation Psi D hD)

/-- Extending the induced range derivation to the fraction field gives its
canonical differential-field structure. -/
@[reducible]
def fractionDifferential (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (hunit : TailGerm.UnitDichotomy (TailRange Psi)) :
    Differential (FractionRing (TailRange Psi)) :=
  ⟨fractionDerivation Psi D hD hunit⟩

/-- The analytic fraction embedding commutes with the extended derivation. -/
theorem fractionMap_extend_commutes
    (Psi : K[X] →+* AnalyticTailGerm)
    (D : Derivation Int K[X] K[X])
    (hD : ∀ p : K[X], (Psi p)′ = Psi (D p))
    (hunit : TailGerm.UnitDichotomy (TailRange Psi))
    (z : FractionRing (TailRange Psi)) :
    (fractionMap Psi hunit z)′ =
      fractionMap Psi hunit
        (fractionDerivation Psi D hD hunit z) := by
  letI := hunit
  letI : Differential (TailRange Psi) := rangeDifferential Psi D hD
  change (fractionMap Psi hunit z)′ =
    fractionMap Psi hunit
      (FractionDerivation.extend (rangeDerivation Psi D hD) z)
  exact FractionDerivation.localizationLift_extend_commutes
    (rangeToAnalytic Psi)
    (rangeToAnalytic_isUnit Psi hunit)
    (rangeToAnalytic_deriv Psi D hD) z

section RichardsonSteps

variable [Differential K]

/-- One primitive adjunction, with its zero-or-unit premise discharged by
Richardson descent. -/
theorem primitiveUnitDichotomy (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c) p)) :
    TailGerm.UnitDichotomy (TailRange Psi) :=
  RichardsonAnalyticFraction.polynomialTailRangeUnitDichotomy Psi
    (RichardsonAnalyticFraction.polynomialRepresentative Psi)
    (RichardsonAnalyticFraction.polynomialRepresentative_represents Psi)
    (RichardsonAnalyticFraction.analyticRepresentativeTailDichotomy_primitive
      Psi c hD)

/-- One exponential adjunction, with its zero-or-unit premise discharged by
Richardson descent. -/
theorem exponentialUnitDichotomy (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hX : IsUnit
      ((RichardsonAnalyticFraction.toTailPolynomialHom Psi) X))
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c * X) p)) :
    TailGerm.UnitDichotomy (TailRange Psi) :=
  RichardsonAnalyticFraction.polynomialTailRangeUnitDichotomy Psi
    (RichardsonAnalyticFraction.polynomialRepresentative Psi)
    (RichardsonAnalyticFraction.polynomialRepresentative_represents Psi)
    (RichardsonAnalyticFraction.analyticRepresentativeTailDichotomy_exponential
      Psi c hX hD)

/-- The fraction embedding after one primitive adjunction is injective. -/
theorem primitiveFractionMap_injective
    (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c) p)) :
    Function.Injective (fractionMap Psi (primitiveUnitDichotomy Psi c hD)) :=
  fractionMap_injective Psi (primitiveUnitDichotomy Psi c hD)

/-- The fraction embedding after one primitive adjunction commutes with the
extended implicit derivation. -/
theorem primitiveFractionMap_extend_commutes
    (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c) p))
    (z : FractionRing (TailRange Psi)) :
    (fractionMap Psi (primitiveUnitDichotomy Psi c hD) z)′ =
      fractionMap Psi (primitiveUnitDichotomy Psi c hD)
        (fractionDerivation Psi (Differential.implicitDeriv (C c)) hD
          (primitiveUnitDichotomy Psi c hD) z) :=
  fractionMap_extend_commutes Psi
    (Differential.implicitDeriv (C c)) hD
    (primitiveUnitDichotomy Psi c hD) z

/-- The fraction embedding after one exponential adjunction is injective. -/
theorem exponentialFractionMap_injective
    (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hX : IsUnit
      ((RichardsonAnalyticFraction.toTailPolynomialHom Psi) X))
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c * X) p)) :
    Function.Injective
      (fractionMap Psi (exponentialUnitDichotomy Psi c hX hD)) :=
  fractionMap_injective Psi (exponentialUnitDichotomy Psi c hX hD)

/-- The fraction embedding after one exponential adjunction commutes with the
extended implicit derivation. -/
theorem exponentialFractionMap_extend_commutes
    (Psi : K[X] →+* AnalyticTailGerm) (c : K)
    (hX : IsUnit
      ((RichardsonAnalyticFraction.toTailPolynomialHom Psi) X))
    (hD : ∀ p : K[X],
      (Psi p)′ = Psi (Differential.implicitDeriv (C c * X) p))
    (z : FractionRing (TailRange Psi)) :
    (fractionMap Psi (exponentialUnitDichotomy Psi c hX hD) z)′ =
      fractionMap Psi (exponentialUnitDichotomy Psi c hX hD)
        (fractionDerivation Psi
          (Differential.implicitDeriv (C c * X)) hD
          (exponentialUnitDichotomy Psi c hX hD) z) :=
  fractionMap_extend_commutes Psi
    (Differential.implicitDeriv (C c * X)) hD
    (exponentialUnitDichotomy Psi c hX hD) z

end RichardsonSteps

end RichardsonAnalyticAdjunction

end

end Natfunbasis.Wilkie
