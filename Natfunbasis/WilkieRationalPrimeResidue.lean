import Natfunbasis.WilkieFractionDifferential
import Mathlib.FieldTheory.Laurent
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Logarithmic residues in a rational coordinate

This file develops the local Laurent-series algebra behind the residue
certificate used by `FreshStageRigidityReduction`.  The residue of a
differential form is the coefficient of `X⁻¹`.  In particular, its value on
the formal derivative of any Laurent series is zero.

The eventual application at an irreducible polynomial `h` first extends
coefficients to `C[X]/(h)`, translates the chosen root to zero, and divides by
the coefficient of the ambient derivation.  Keeping the formal Laurent layer
separate makes the normalization (and especially the required division by
that coefficient) explicit.
-/

open scoped Differential LaurentSeries Polynomial

namespace Natfunbasis.Wilkie.RationalPrimeResidue

noncomputable section

/-! ## Transporting a derivation to an arbitrary fraction field -/

namespace FractionFieldDerivation

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The canonical extension of a derivation to an arbitrary chosen fraction
field.  `FractionDerivation.extend` treats the quotient implementation
`FractionRing A`; here we transport it across the canonical fraction-field
equivalence. -/
def extend (D : Derivation Int A A) : Derivation Int K K := by
  letI : Differential (FractionRing A) :=
    ⟨Natfunbasis.Wilkie.FractionDerivation.extend D⟩
  exact (Differential.equiv
    (FractionRing.algEquiv (A := A) K).symm.toRingEquiv).deriv

@[simp]
theorem extend_apply (D : Derivation Int A A) (x : K) :
    extend D x =
      FractionRing.algEquiv (A := A) K
        (Natfunbasis.Wilkie.FractionDerivation.extend D
          ((FractionRing.algEquiv (A := A) K).symm x)) :=
  rfl

@[simp]
theorem extend_algebraMap (D : Derivation Int A A) (a : A) :
    extend (K := K) D (algebraMap A K a) =
      algebraMap A K (D a) := by
  rw [extend_apply]
  simp

end FractionFieldDerivation

namespace Laurent

variable (C : Type*) [Field C]

/-- The ordinary Laurent residue, i.e. the coefficient of `X⁻¹`. -/
def residue : C⸨X⸩ →ₗ[C] C :=
  HahnSeries.coeff.linearMap (-1)

@[simp]
theorem residue_apply (f : C⸨X⸩) :
    residue C f = f.coeff (-1) :=
  rfl

local instance intAlgebra : Algebra Int C⸨X⸩ :=
  Ring.toIntAlgebra C⸨X⸩

local instance powerSeriesIntAlgebra : Algebra Int (PowerSeries C) :=
  Ring.toIntAlgebra (PowerSeries C)

/-- Power-series differentiation, viewed with its canonical integer scalar
structure.  This wrapper avoids depending on which tower-induced `Int` algebra
Lean happens to select. -/
def powerSeriesDerivation :
    Derivation Int (PowerSeries C) (PowerSeries C) :=
  Derivation.mk'
    (PowerSeries.derivative C).toLinearMap.toAddMonoidHom.toIntLinearMap (by
      intro f g
      exact (PowerSeries.derivative C).leibniz f g)

@[simp]
theorem powerSeriesDerivation_apply (f : PowerSeries C) :
    powerSeriesDerivation C f = PowerSeries.derivative C f :=
  rfl

/-- Ordinary formal differentiation on Laurent series, constructed as the
canonical extension of power-series differentiation to its fraction field. -/
def ordinaryDerivation : Derivation Int C⸨X⸩ C⸨X⸩ :=
  FractionFieldDerivation.extend (A := PowerSeries C) (K := C⸨X⸩)
    (powerSeriesDerivation C)

@[simp]
theorem ordinaryDerivation_algebraMap (f : PowerSeries C) :
    ordinaryDerivation C (algebraMap (PowerSeries C) C⸨X⸩ f) =
      algebraMap (PowerSeries C) C⸨X⸩ (PowerSeries.derivative C f) := by
  exact FractionFieldDerivation.extend_algebraMap
    (powerSeriesDerivation C) f

@[simp]
theorem ordinaryDerivation_coe (f : PowerSeries C) :
    ordinaryDerivation C (f : C⸨X⸩) =
      (PowerSeries.derivative C f : PowerSeries C) := by
  exact ordinaryDerivation_algebraMap C f

@[simp]
theorem ordinaryDerivation_X :
    ordinaryDerivation C (HahnSeries.single (1 : Int) (1 : C)) = 1 := by
  rw [← HahnSeries.ofPowerSeries_X]
  change ordinaryDerivation C
    (algebraMap (PowerSeries C) C⸨X⸩ PowerSeries.X) = 1
  rw [ordinaryDerivation_algebraMap, PowerSeries.derivative_X, map_one]

/-- The expected derivative formula for every integral Laurent monomial. -/
theorem ordinaryDerivation_single (n : Int) :
    ordinaryDerivation C (HahnSeries.single n (1 : C)) =
      (n : C⸨X⸩) * HahnSeries.single (n - 1) (1 : C) := by
  rw [RatFunc.single_zpow]
  rw [(ordinaryDerivation C).leibniz_zpow]
  rw [ordinaryDerivation_X]
  simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
  rw [← RatFunc.single_zpow]

/-- A power series, regarded as a Laurent series, has zero residue. -/
@[simp]
theorem residue_coe_powerSeries (f : PowerSeries C) :
    residue C (f : C⸨X⸩) = 0 := by
  rw [residue_apply, HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨n, hn⟩
  simp only [Nat.castOrderEmbedding_apply] at hn
  omega

theorem intCast_eq_single_zero (n : Int) :
    (n : C⸨X⸩) = HahnSeries.single 0 (n : C) := by
  rw [← HahnSeries.C_apply]
  norm_cast

/-- Formal differentiation has zero Laurent residue. -/
@[simp]
theorem residue_formalDerivative (f : C⸨X⸩) :
    residue C (LaurentSeries.derivative C f) = 0 := by
  simp [residue, LaurentSeries.derivative_apply]

/-- The fraction-field derivation constructed above has zero residue.  This
is the algebraic `residue (dv) = 0` law; unlike
`residue_formalDerivative`, its input is a bundled derivation and can
therefore be used in a `Differential` instance. -/
theorem residue_ordinaryDerivation (f : C⸨X⸩) :
    residue C (ordinaryDerivation C f) = 0 := by
  by_cases hnonneg : 0 ≤ f.order
  · have hn : ((Int.natAbs f.order : Nat) : Int) = f.order :=
      Int.natAbs_of_nonneg hnonneg
    have hf := LaurentSeries.X_order_mul_powerSeriesPart
      (f := f) hn
    rw [← hf, ordinaryDerivation_coe]
    exact residue_coe_powerSeries C _
  · rw [← f.single_order_mul_powerSeriesPart]
    rw [(ordinaryDerivation C).leibniz, ordinaryDerivation_single,
      ordinaryDerivation_coe]
    simp only [smul_eq_mul, map_add, residue_apply]
    cases horder : f.order with
    | ofNat n =>
        have hge : 0 ≤ f.order := horder.symm ▸ Int.ofNat_zero_le n
        exact (hnonneg hge).elim
    | negSucc n =>
        have hcast : (Int.negSucc n : C⸨X⸩) =
            HahnSeries.single 0 (Int.negSucc n : C) :=
          intCast_eq_single_zero C (Int.negSucc n)
        have hsecond :
            (f.powerSeriesPart : C⸨X⸩) *
                ((Int.negSucc n : C⸨X⸩) *
                  HahnSeries.single (Int.negSucc n - 1) (1 : C)) =
              HahnSeries.single 0 (Int.negSucc n : C) *
                (HahnSeries.single (Int.negSucc n - 1) (1 : C) *
                  (f.powerSeriesPart : C⸨X⸩)) := by
          rw [hcast]
          ring
        rw [hsecond]
        simp only [HahnSeries.coeff_single_mul]
        have hidx1 : (-1 : Int) - Int.negSucc n = (n : Int) := by omega
        have hidx2 : (-1 : Int) - 0 - (Int.negSucc n - 1) =
            ((n + 1 : Nat) : Int) := by
          omega
        rw [hidx1, hidx2, LaurentSeries.coeff_coe_powerSeries,
          LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_derivative]
        push_cast
        ring

/-- The logarithmic derivative of an integral Laurent monomial has residue
equal to its exponent. -/
theorem residue_logDeriv_single (n : Int) :
    residue C
        (ordinaryDerivation C (HahnSeries.single n (1 : C)) /
          HahnSeries.single n (1 : C)) = (n : C) := by
  rw [ordinaryDerivation_single, intCast_eq_single_zero]
  simp only [residue_apply, div_eq_mul_inv, HahnSeries.inv_single, inv_one,
    HahnSeries.single_mul_single, mul_one]
  have hidx : 0 + (n - 1) + -n = (-1 : Int) := by omega
  rw [hidx]
  simp

/-- A unit power series contributes no logarithmic residue. -/
theorem residue_logDeriv_powerSeries (f : PowerSeries C)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    residue C
        (ordinaryDerivation C (f : C⸨X⸩) / (f : C⸨X⸩)) = 0 := by
  have hmul : (f : C⸨X⸩) * (f⁻¹ : PowerSeries C) = 1 := by
    rw [← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel f hf]
    exact PowerSeries.coe_one
  have hinv : (f : C⸨X⸩)⁻¹ = (f⁻¹ : PowerSeries C) :=
    inv_eq_of_mul_eq_one_right hmul
  rw [ordinaryDerivation_coe, div_eq_mul_inv, hinv, ← PowerSeries.coe_mul]
  exact residue_coe_powerSeries C _

/-- The residue of a logarithmic derivative is exactly the Laurent order.
This is the integer-valued law needed in a logarithmic-residue certificate. -/
theorem residue_logDeriv (f : C⸨X⸩) (hf : f ≠ 0) :
    residue C (ordinaryDerivation C f / f) = (f.order : C) := by
  let P : PowerSeries C := f.powerSeriesPart
  let a : C⸨X⸩ := HahnSeries.single f.order (1 : C)
  have ha : a ≠ 0 := by
    simp [a]
  have hP : (P : C⸨X⸩) ≠ 0 := by
    intro h
    have hP0 : P = 0 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := Int)
      simpa using h
    apply hf
    exact (LaurentSeries.powerSeriesPart_eq_zero f).mp (by simpa [P] using hP0)
  have hPc : PowerSeries.constantCoeff P ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change f.powerSeriesPart.coeff 0 ≠ 0
    rw [LaurentSeries.powerSeriesPart_coeff]
    simpa using HahnSeries.coeff_order_ne_zero hf
  have hlog :
      ordinaryDerivation C (a * (P : C⸨X⸩)) /
          (a * (P : C⸨X⸩)) =
        ordinaryDerivation C a / a +
          ordinaryDerivation C (P : C⸨X⸩) / (P : C⸨X⸩) := by
    rw [(ordinaryDerivation C).leibniz]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hdecomp : a * (P : C⸨X⸩) = f := by
    simpa [a, P] using f.single_order_mul_powerSeriesPart
  calc
    residue C (ordinaryDerivation C f / f) =
        residue C
          (ordinaryDerivation C (a * (P : C⸨X⸩)) /
            (a * (P : C⸨X⸩))) := by rw [hdecomp]
    _ = residue C (ordinaryDerivation C a / a) +
          residue C
            (ordinaryDerivation C (P : C⸨X⸩) / (P : C⸨X⸩)) := by
      rw [hlog, map_add]
    _ = (f.order : C) := by
      change residue C
          (ordinaryDerivation C (HahnSeries.single f.order (1 : C)) /
            HahnSeries.single f.order (1 : C)) +
          residue C
            (ordinaryDerivation C (P : C⸨X⸩) / (P : C⸨X⸩)) = _
      rw [residue_logDeriv_single, residue_logDeriv_powerSeries C P hPc, add_zero]

/-! ## Weighted derivations -/

/-- The derivation `a(X) d/dX`. -/
def weightedDerivation (a : C⸨X⸩) : Derivation Int C⸨X⸩ C⸨X⸩ :=
  a • ordinaryDerivation C

@[simp]
theorem weightedDerivation_apply (a f : C⸨X⸩) :
    weightedDerivation C a f = a * ordinaryDerivation C f := by
  rfl

/-- The residue normalized for the weighted derivation `a d/dX`.
Equivalently, this is the residue of the differential form `(f/a) dX`. -/
def weightedResidue (a : C⸨X⸩) : C⸨X⸩ →ₗ[C] C :=
  { toFun := fun f ↦ residue C (f / a)
    map_add' := by
      intro f g
      rw [add_div, map_add]
    map_smul' := by
      intro c f
      change residue C ((c • f) / a) = c • residue C (f / a)
      rw [show (c • f) / a = c • (f / a) by
        rw [← HahnSeries.single_zero_mul_eq_smul,
          ← HahnSeries.single_zero_mul_eq_smul]
        ring]
      exact (residue C).map_smul c (f / a) }

@[simp]
theorem weightedResidue_apply (a f : C⸨X⸩) :
    weightedResidue C a f = residue C (f / a) := by
  rfl

/-- Weighted derivatives have zero normalized residue. -/
theorem weightedResidue_deriv (a : C⸨X⸩) (ha : a ≠ 0)
    (f : C⸨X⸩) :
    weightedResidue C a (weightedDerivation C a f) = 0 := by
  rw [weightedResidue_apply, weightedDerivation_apply]
  rw [mul_div_cancel_left₀ _ ha]
  exact residue_ordinaryDerivation C f

/-- The normalized residue of a weighted logarithmic derivative remains the
Laurent order, independently of the nonzero weight. -/
theorem weightedResidue_logDeriv (a : C⸨X⸩) (ha : a ≠ 0)
    (f : C⸨X⸩) (hf : f ≠ 0) :
    weightedResidue C a (weightedDerivation C a f / f) =
      (f.order : C) := by
  rw [weightedResidue_apply, weightedDerivation_apply]
  have heq : (a * ordinaryDerivation C f / f) / a =
      ordinaryDerivation C f / f := by
    field_simp
  rw [heq]
  exact residue_logDeriv C f hf

/-- A parameter of Laurent order one has normalized base logarithmic residue
one. -/
theorem weightedResidue_base (a : C⸨X⸩) (ha : a ≠ 0)
    (beta : C⸨X⸩) (hbeta : beta ≠ 0) (horder : beta.order = 1) :
    weightedResidue C a (weightedDerivation C a beta / beta) = 1 := by
  rw [weightedResidue_logDeriv C a ha beta hbeta, horder]
  norm_num

/-- A power series with zero constant coefficient and nonzero linear
coefficient has Laurent order exactly one. -/
theorem order_coe_powerSeries_eq_one (f : PowerSeries C)
    (hzero : PowerSeries.coeff 0 f = 0)
    (hone : PowerSeries.coeff 1 f ≠ 0) :
    ((f : C⸨X⸩).order) = 1 := by
  have hcoeffOne : (f : C⸨X⸩).coeff 1 ≠ 0 := by
    change
      (HahnSeries.ofPowerSeries Int C f).coeff ((1 : Nat) : Int) ≠ 0
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact hone
  have hne : (f : C⸨X⸩) ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hcoeffOne
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeffOne)
  by_contra hnot
  have hlt : (f : C⸨X⸩).order < 1 := lt_of_not_ge hnot
  have horderCoeff : (f : C⸨X⸩).coeff (f : C⸨X⸩).order ≠ 0 :=
    HahnSeries.coeff_order_eq_zero.not.mpr hne
  rcases lt_or_eq_of_le (show (f : C⸨X⸩).order ≤ 0 by omega) with hneg | heq
  · apply horderCoeff
    have coeff_neg (i : Int) (hi : i < 0) :
        (f : C⸨X⸩).coeff i = 0 := by
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      rintro ⟨n, rfl⟩
      simp only [Nat.castOrderEmbedding_apply] at hi
      omega
    exact coeff_neg _ hneg
  · apply horderCoeff
    rw [heq]
    change
      (HahnSeries.ofPowerSeries Int C f).coeff ((0 : Nat) : Int) = 0
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact hzero


end Laurent

/-
The following prime-expansion adapter is retained as design work but is not
part of this module yet.  Its construction needs a carefully chosen
`RatFunc (ResidueField h) →ₐ[ResidueField h] (ResidueField h)⸨X⸩`
embedding (rather than the unavailable direct algebra-map instance), plus
the corresponding scalar-tower proofs.  The compiled contribution of this
module is therefore deliberately the Laurent residue layer above.

/-! ## Expansion at an irreducible polynomial prime -/

namespace PrimeExpansion

variable {C : Type*} [Field C]

local instance polynomialIntAlgebra : Algebra Int C[X] :=
  Ring.toIntAlgebra C[X]

local instance ratFuncIntAlgebra : Algebra Int (RatFunc C) :=
  Ring.toIntAlgebra (RatFunc C)

/-- The residue field at an irreducible polynomial. -/
abbrev ResidueField (h : C[X]) := AdjoinRoot h

variable (h : C[X]) [Fact (Irreducible h)]

local instance residueLaurentIntAlgebra :
    Algebra Int (ResidueField h)⸨X⸩ :=
  Ring.toIntAlgebra (ResidueField h)⸨X⸩

/-- The polynomial derivation `w(X) d/dX`, with canonical integer
scalars. -/
def polynomialDerivation (w : C[X]) : Derivation Int C[X] C[X] :=
  Derivation.mk'
    (Polynomial.mkDerivation C w).toLinearMap.toAddMonoidHom.toIntLinearMap (by
      intro p q
      exact (Polynomial.mkDerivation C w).leibniz p q)

@[simp]
theorem polynomialDerivation_apply (w p : C[X]) :
    polynomialDerivation w p = Polynomial.derivative p * w := by
  exact Polynomial.mkDerivation_apply w p

/-- Extend `w(X) d/dX` to the rational-function field. -/
def rationalDerivation (w : C[X]) :
    Derivation Int (RatFunc C) (RatFunc C) :=
  FractionFieldDerivation.extend (A := C[X]) (K := RatFunc C)
    (polynomialDerivation w)

@[simp]
theorem rationalDerivation_algebraMap (w p : C[X]) :
    rationalDerivation w (algebraMap C[X] (RatFunc C) p) =
      algebraMap C[X] (RatFunc C) (Polynomial.derivative p * w) := by
  rw [rationalDerivation, FractionFieldDerivation.extend_algebraMap,
    polynomialDerivation_apply]

/-- Translation commutes with ordinary polynomial differentiation. -/
theorem derivative_taylor {K : Type*} [CommRing K] (r : K) (p : K[X]) :
    Polynomial.derivative (Polynomial.taylor r p) =
      Polynomial.taylor r (Polynomial.derivative p) := by
  simp [Polynomial.taylor_apply, Polynomial.derivative_comp]

/-- Extend polynomial coefficients to the residue field `C[X]/(h)`. -/
def coefficientMap : C[X] →ₐ[C] (ResidueField h)[X] :=
  Polynomial.mapAlgHom (Algebra.ofId C (ResidueField h))

theorem coefficientMap_injective : Function.Injective (coefficientMap h) := by
  exact Polynomial.map_injective _
    (FaithfulSMul.algebraMap_injective C (ResidueField h))

/-- Extend rational-function coefficients to the residue field. -/
def rationalMap : RatFunc C →ₐ[C] RatFunc (ResidueField h) :=
  RatFunc.mapAlgHom (coefficientMap h)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (coefficientMap_injective h))

/-- Laurent expansion at the distinguished root of `h` in its residue
field.  Thus the old coordinate is sent to `X + root(h)`. -/
def expansion : RatFunc C →ₐ[C] (ResidueField h)⸨X⸩ :=
  ((IsScalarTower.toAlgHom (ResidueField h) (RatFunc (ResidueField h))
      (ResidueField h)⸨X⸩).restrictScalars C).comp
    (((RatFunc.laurent (AdjoinRoot.root h)).restrictScalars C).comp
      (rationalMap h))

@[simp]
theorem expansion_algebraMap (p : C[X]) :
    expansion h (algebraMap C[X] (RatFunc C) p) =
      algebraMap (ResidueField h)[X] (ResidueField h)⸨X⸩
        (Polynomial.taylor (AdjoinRoot.root h)
          (p.map (algebraMap C (ResidueField h)))) := by
  simp [expansion, rationalMap, coefficientMap]

/-- The translated polynomial, regarded as a power series over the residue
field. -/
def expandedPowerSeries (p : C[X]) : PowerSeries (ResidueField h) :=
  (Polynomial.taylor (AdjoinRoot.root h)
    (p.map (algebraMap C (ResidueField h))) : (ResidueField h)[X])

@[simp]
theorem expansion_algebraMap_eq_coe (p : C[X]) :
    expansion h (algebraMap C[X] (RatFunc C) p) =
      (expandedPowerSeries h p : (ResidueField h)⸨X⸩) := by
  rw [expansion_algebraMap]
  exact RatFunc.coe_coe _

/-- On polynomials, expansion intertwines `w(X)d/dX` with the Laurent
derivation weighted by the expansion of `w`. -/
theorem expansion_polynomialDerivation (w p : C[X]) :
    expansion h
        (rationalDerivation w (algebraMap C[X] (RatFunc C) p)) =
      Laurent.weightedDerivation (ResidueField h)
        (expansion h (algebraMap C[X] (RatFunc C) w))
        (expansion h (algebraMap C[X] (RatFunc C) p)) := by
  rw [rationalDerivation_algebraMap, expansion_algebraMap_eq_coe,
    expansion_algebraMap_eq_coe, expansion_algebraMap_eq_coe,
    Laurent.weightedDerivation_apply, Laurent.ordinaryDerivation_coe]
  change
    (Polynomial.taylor (AdjoinRoot.root h)
        ((Polynomial.derivative p * w).map
          (algebraMap C (ResidueField h))) : (ResidueField h)[X]) =
      (Polynomial.taylor (AdjoinRoot.root h)
          (w.map (algebraMap C (ResidueField h))) : (ResidueField h)[X]) *
        Polynomial.derivative
          (Polynomial.taylor (AdjoinRoot.root h)
            (p.map (algebraMap C (ResidueField h))))
  rw [Polynomial.map_mul, Polynomial.taylor_mul, derivative_taylor]
  simp

/-- Expansion is a differential embedding for the weighted rational
derivation. -/
theorem expansion_rationalDerivation (w : C[X]) (f : RatFunc C) :
    expansion h (rationalDerivation w f) =
      Laurent.weightedDerivation (ResidueField h)
        (expansion h (algebraMap C[X] (RatFunc C) w)) (expansion h f) := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div]
      rw [(rationalDerivation w).leibniz_div,
        (Laurent.weightedDerivation (ResidueField h)
          (expansion h (algebraMap C[X] (RatFunc C) w))).leibniz_div]
      simp only [smul_eq_mul, map_mul, map_sub, map_inv₀, map_pow]
      rw [expansion_polynomialDerivation h w p,
        expansion_polynomialDerivation h w q]

/-- Pull the normalized Laurent residue back to the rational-function
field. -/
def primeResidue (w : C[X]) :
    RatFunc C →ₗ[C] ResidueField h :=
  ((Laurent.weightedResidue (ResidueField h)
      (expansion h (algebraMap C[X] (RatFunc C) w))).restrictScalars C).comp
    (expansion h).toLinearMap

@[simp]
theorem primeResidue_apply (w : C[X]) (f : RatFunc C) :
    primeResidue h w f =
      Laurent.weightedResidue (ResidueField h)
        (expansion h (algebraMap C[X] (RatFunc C) w)) (expansion h f) :=
  rfl

theorem expanded_weight_ne_zero {w : C[X]} (hw : w ≠ 0) :
    expansion h (algebraMap C[X] (RatFunc C) w) ≠ 0 := by
  apply (expansion_injective h).ne
  exact RatFunc.algebraMap_ne_zero hw

/-- The usual non-invariance condition at `h` forces the coefficient of
`d/dX` to be nonzero. -/
theorem weight_ne_zero_of_not_dvd_deriv (w : C[X])
    (hninv : ¬ h ∣ polynomialDerivation w h) : w ≠ 0 := by
  intro hw
  apply hninv
  rw [hw, polynomialDerivation_apply, mul_zero]
  exact dvd_zero h

/-- The pulled-back residue kills every derivative. -/
theorem primeResidue_deriv (w : C[X]) (hw : w ≠ 0) (f : RatFunc C) :
    primeResidue h w (rationalDerivation w f) = 0 := by
  rw [primeResidue_apply, expansion_rationalDerivation]
  exact Laurent.weightedResidue_deriv _ _
    (expanded_weight_ne_zero h hw) _

/-- Every rational logarithmic derivative has integral prime residue. -/
theorem primeResidue_logDeriv_integral (w : C[X]) (hw : w ≠ 0)
    (f : RatFunc C) (hf : f ≠ 0) :
    ∃ m : Int,
      primeResidue h w (rationalDerivation w f / f) =
        (m : ResidueField h) := by
  let m : Int := (expansion h f).order
  refine ⟨m, ?_⟩
  rw [primeResidue_apply, map_div, expansion_rationalDerivation]
  exact Laurent.weightedResidue_logDeriv _ _
    (expanded_weight_ne_zero h hw) _ ((expansion_injective h).ne hf)

variable [CharZero C]

theorem derivative_mk_ne_zero :
    AdjoinRoot.mk h (Polynomial.derivative h) ≠ 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  apply Polynomial.not_dvd_of_natDegree_lt
  · exact Polynomial.derivative_ne_zero.mpr
      (Irreducible.natDegree_pos (Fact.out : Irreducible h)).ne'
  · exact Polynomial.natDegree_derivative_lt
      (Irreducible.natDegree_pos (Fact.out : Irreducible h)).ne'

theorem derivative_at_root_ne_zero :
    (Polynomial.derivative
      (h.map (algebraMap C (ResidueField h)))).eval
        (AdjoinRoot.root h) ≠ 0 := by
  rw [Polynomial.derivative_map, Polynomial.eval_map]
  simpa [← Polynomial.aeval_def, AdjoinRoot.aeval_eq] using
    derivative_mk_ne_zero h

@[simp]
theorem expandedPowerSeries_coeff_zero :
    PowerSeries.coeff 0 (expandedPowerSeries h h) = 0 := by
  change (Polynomial.taylor (AdjoinRoot.root h)
    (h.map (algebraMap C (ResidueField h)))).coeff 0 = 0
  rw [Polynomial.taylor_coeff_zero]
  exact AdjoinRoot.eval₂_root h

theorem expandedPowerSeries_coeff_one_ne_zero :
    PowerSeries.coeff 1 (expandedPowerSeries h h) ≠ 0 := by
  change (Polynomial.taylor (AdjoinRoot.root h)
    (h.map (algebraMap C (ResidueField h)))).coeff 1 ≠ 0
  rw [Polynomial.taylor_coeff_one]
  exact derivative_at_root_ne_zero h

/-- The chosen irreducible polynomial is a uniformizer after expansion at
its distinguished residue-field root. -/
theorem expansion_base_order :
    (expansion h (algebraMap C[X] (RatFunc C) h)).order = 1 := by
  rw [expansion_algebraMap_eq_coe]
  exact Laurent.order_coe_powerSeries_eq_one _
    (expandedPowerSeries_coeff_zero h)
    (expandedPowerSeries_coeff_one_ne_zero h)

theorem rationalMap_injective : Function.Injective (rationalMap h) := by
  exact RatFunc.map_injective _ _ (coefficientMap_injective h)

theorem expansion_injective : Function.Injective (expansion h) := by
  apply Function.Injective.comp
    (algebraMap_injective (R := RatFunc (ResidueField h))
      (A := (ResidueField h)⸨X⸩))
  exact (RatFunc.laurent_injective _).comp (rationalMap_injective h)

end PrimeExpansion
-/

end

end Natfunbasis.Wilkie.RationalPrimeResidue
