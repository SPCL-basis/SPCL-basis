import Natfunbasis.WilkieFreshStageRigidityReduction
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Polynomial derivations for fresh Wilkie stages

This file constructs the common-denominator polynomial derivation required by
`FreshStagePrimeDerivationInput`.  It also isolates the two genuinely local
properties of the current W1 polynomial which remain to choose the residue
prime: squarefreeness after extending coefficients from `Int` to `Real`, and
non-invariance of one of its simple factors.
-/

open scoped Differential

namespace Natfunbasis.Wilkie.FreshStagePrimeDerivation

noncomputable section

open FreshStageRigidityReduction

/-! ## Detecting a non-invariant simple factor -/

namespace NonInvariantFactor

variable {R : Type*} [CommRing R] [IsDomain R]
  [UniqueFactorizationMonoid R]

/-- For a squarefree element, failure of the whole element to divide its
derivative is witnessed by one irreducible factor which is not invariant.

This replaces a factor-by-factor stage obligation by the single divisibility
test `base ∤ D base`. -/
theorem exists_irreducible_factor_not_dvd_deriv
    (D : Derivation Int R R) {base : R}
    (hbase0 : base ≠ 0) (hsquarefree : Squarefree base)
    (hnotdiv : ¬ base ∣ D base) :
    ∃ h : R, Irreducible h ∧ h ∣ base ∧ ¬ h ∣ D h := by
  classical
  letI : StrongNormalizationMonoid R :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  by_contra hexists
  push Not at hexists
  have hDbase0 : D base ≠ 0 := by
    intro hzero
    exact hnotdiv (hzero ▸ dvd_zero base)
  apply hnotdiv
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
    hbase0 hDbase0]
  rw [Multiset.le_iff_count]
  intro p
  by_cases hp : p ∈ UniqueFactorizationMonoid.normalizedFactors base
  · have hnodup :
        (UniqueFactorizationMonoid.normalizedFactors base).Nodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
        hbase0).mp hsquarefree
    have hpcount :
        Multiset.count p
            (UniqueFactorizationMonoid.normalizedFactors base) = 1 :=
      Multiset.count_eq_one_of_mem hnodup hp
    rw [hpcount]
    have hpirr : Irreducible p :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    have hpnormal : normalize p = p :=
      UniqueFactorizationMonoid.normalize_normalized_factor p hp
    have hpbase : p ∣ base :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
    have hpDp : p ∣ D p := hexists p hpirr hpbase
    obtain ⟨u, rfl⟩ := hpbase
    obtain ⟨v, hv⟩ := hpDp
    have hpDbase : p ∣ D (p * u) := by
      refine ⟨D u + u * v, ?_⟩
      rw [D.leibniz, hv]
      ring
    have hpmem :
        p ∈ UniqueFactorizationMonoid.normalizedFactors (D (p * u)) :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hDbase0).mpr
        ⟨hpirr, hpnormal, hpDbase⟩
    exact Multiset.one_le_count_iff_mem.mpr hpmem
  · rw [Multiset.count_eq_zero_of_notMem hp]
    exact Nat.zero_le _

end NonInvariantFactor

/-! ## The rational scalar-extension of a W1 prime -/

namespace ScalarExtension

variable {I : Type*}

/-- A nonconstant prime integer multivariate polynomial stays irreducible
after extending coefficients to the fraction field of `Int`.  This is the
localization/Gauss step in the eventual real-squarefreeness argument. -/
theorem irreducible_map_fractionRing_of_prime_of_nonconstant
    {p : MvPolynomial I Int} (hp : Prime p)
    (hnonconstant : ∀ z : Int, p ≠ MvPolynomial.C z) :
    Irreducible
      (MvPolynomial.map (algebraMap Int (FractionRing Int)) p) := by
  let R := MvPolynomial I Int
  let Q := FractionRing Int
  let RQ := MvPolynomial I Q
  let M : Submonoid R :=
    (nonZeroDivisors Int).map
      (MvPolynomial.C : Int →+* R).toMonoidHom
  have hprime : (Ideal.span ({p} : Set R)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp
  have hdisjoint : Disjoint (M : Set R) (Ideal.span ({p} : Set R) : Set R) := by
    rw [Set.disjoint_left]
    intro x hxM hxp
    obtain ⟨m, hm, hmx⟩ := hxM
    subst x
    have hpdvd : p ∣ MvPolynomial.C (m : Int) := by
      exact Ideal.mem_span_singleton.mp hxp
    obtain ⟨z, _hzunit, hpz⟩ :=
      (MvPolynomial.dvd_C_iff_exists
        (nonZeroDivisors.ne_zero hm)).mp hpdvd
    exact hnonconstant z hpz
  letI : Algebra R RQ := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization M RQ :=
    MvPolynomial.isLocalization (nonZeroDivisors Int) Q
  have hmappedPrime :
      (Ideal.map (algebraMap R RQ) (Ideal.span ({p} : Set R))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M RQ
      (Ideal.span ({p} : Set R)) hprime hdisjoint
  have hspan :
      Ideal.map (algebraMap R RQ) (Ideal.span ({p} : Set R)) =
        Ideal.span ({MvPolynomial.map
          (algebraMap Int (FractionRing Int)) p} : Set RQ) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
  rw [hspan] at hmappedPrime
  have hpmap0 :
      MvPolynomial.map (algebraMap Int (FractionRing Int)) p ≠ 0 :=
    by
      intro hzero
      apply hp.ne_zero
      apply MvPolynomial.map_injective
        (algebraMap Int (FractionRing Int))
        (IsFractionRing.injective Int (FractionRing Int))
      simpa using hzero
  exact ((Ideal.span_singleton_prime hpmap0).mp hmappedPrime).irreducible

end ScalarExtension

/-! ## Clearing the derivatives of finitely many coordinates -/

namespace CommonDenominator

variable {I : Type*} [Finite I]

private abbrev R := MvPolynomial I Real
private abbrev F := FractionRing (R (I := I))

local instance intAlgebraR : Algebra Int (R (I := I)) :=
  Ring.toIntAlgebra (R (I := I))

local instance intAlgebraF : Algebra Int (F (I := I)) :=
  Ring.toIntAlgebra (F (I := I))

/-- The integer-linear polynomial derivation having prescribed values on
the coordinate variables. -/
def polynomialDerivation (numerator : I → R (I := I)) :
    Derivation Int (R (I := I)) (R (I := I)) :=
  (MvPolynomial.mkDerivation Real numerator).restrictScalars Int

@[simp]
theorem polynomialDerivation_X (numerator : I → R (I := I)) (i : I) :
    polynomialDerivation numerator (MvPolynomial.X i) = numerator i := by
  simp [polynomialDerivation]

/-- If a prescribed polynomial scale clears the derivative of every
coordinate variable, the induced polynomial derivation has the required
scaled compatibility on the whole rational function field.  This form is
suited to an explicit W1 denominator product, where coprimality of the scale
can be proved separately. -/
theorem extend_polynomialDerivation_eq_of_generatorValues
    (delta : Derivation Real (F (I := I)) (F (I := I)))
    (scale : R (I := I)) (numerator : I → R (I := I))
    (hgenerator : ∀ i,
      algebraMap (R (I := I)) (F (I := I)) (numerator i) =
        algebraMap (R (I := I)) (F (I := I)) scale *
          delta (algebraMap (R (I := I)) (F (I := I))
            (MvPolynomial.X i))) :
    ∀ z : F (I := I),
      FractionDerivation.extend (polynomialDerivation numerator) z =
        algebraMap (R (I := I)) (F (I := I)) scale * delta z := by
  have hpoly (p : R (I := I)) :
      algebraMap (R (I := I)) (F (I := I))
          (polynomialDerivation numerator p) =
        algebraMap (R (I := I)) (F (I := I)) scale *
          delta (algebraMap (R (I := I)) (F (I := I)) p) := by
    let lhs : Derivation Real (R (I := I)) (F (I := I)) :=
      (Algebra.ofId (R (I := I)) (F (I := I))).toLinearMap.compDer
          (MvPolynomial.mkDerivation Real numerator)
    let rhs : Derivation Real (R (I := I)) (F (I := I)) :=
      algebraMap (R (I := I)) (F (I := I)) scale •
        delta.compAlgebraMap (R (I := I))
    have heq : lhs = rhs := by
      apply MvPolynomial.derivation_ext
      intro i
      simpa [lhs, rhs, Algebra.smul_def] using hgenerator i
    have hp := DFunLike.congr_fun heq p
    simpa [lhs, rhs, polynomialDerivation, Algebra.smul_def] using hp
  intro z
  obtain ⟨p, q, hq, rfl⟩ :=
    IsFractionRing.div_surjective (R (I := I)) z
  rw [(FractionDerivation.extend
    (polynomialDerivation numerator)).leibniz_div, delta.leibniz_div]
  simp only [FractionDerivation.extend_algebraMap, hpoly, Algebra.smul_def]
  ring

/-- A derivation of the rational function field in finitely many variables
has a nonzero polynomial multiple which is induced by a polynomial
derivation.  The statement keeps the multiple visible, since avoiding a
chosen residue prime is a separate stage-specific issue. -/
theorem exists_polynomialDerivation
    (delta : Derivation Real (F (I := I)) (F (I := I))) :
    ∃ (D : Derivation Int (R (I := I)) (R (I := I)))
        (scale : R (I := I)),
      scale ≠ 0 ∧
      ∀ z : F (I := I),
        FractionDerivation.extend D z =
          algebraMap (R (I := I)) (F (I := I)) scale * delta z := by
  let value : I → F (I := I) := fun i ↦
    delta (algebraMap (R (I := I)) (F (I := I)) (MvPolynomial.X i))
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (R (I := I))) value
  let numerator : I → R (I := I) := fun i ↦ (hb i).choose
  have hnumerator (i : I) :
      algebraMap (R (I := I)) (F (I := I)) (numerator i) =
        algebraMap (R (I := I)) (F (I := I)) (b : R (I := I)) *
          value i := by
    simpa only [numerator, Algebra.smul_def] using (hb i).choose_spec
  let D : Derivation Int (R (I := I)) (R (I := I)) :=
    polynomialDerivation numerator
  let scale : R (I := I) := b
  refine ⟨D, scale, ?_, ?_⟩
  · exact (nonZeroDivisors.ne_zero b.property)
  · apply extend_polynomialDerivation_eq_of_generatorValues
    intro i
    simpa only [scale, value] using hnumerator i

/-!
### Prime-avoiding common denominators

The unrestricted common-denominator theorem above cannot by itself control
any chosen prime: multiplying both the scale and the polynomial derivation by
that prime preserves the compatibility equation.  The next theorem records
the normalization which is actually valid.  If every coordinate derivative
has a displayed denominator avoiding `prime`, their product is a common
denominator which still avoids `prime`.

This conclusion deliberately does **not** claim
`¬ prime ∣ D prime`.  That stronger assertion is false for a general
derivation even when the scale is `1` (the Euler derivation sends a
homogeneous polynomial to a multiple of itself).  A stage-specific
non-tangency argument is still required for the W1 base.
-/

/-- Coordinatewise denominators avoiding a prime can be combined without
introducing that prime into the common scale. -/
theorem exists_polynomialDerivation_avoiding_prime
    (delta : Derivation Real (F (I := I)) (F (I := I)))
    (prime : R (I := I)) (hprime : Prime prime)
    (numerator denominator : I → R (I := I))
    (hdenominator_ne : ∀ i, denominator i ≠ 0)
    (hdenominator_avoid : ∀ i, ¬ prime ∣ denominator i)
    (hvalue : ∀ i,
      algebraMap (R (I := I)) (F (I := I)) (numerator i) =
        delta (algebraMap (R (I := I)) (F (I := I))
          (MvPolynomial.X i)) *
          algebraMap (R (I := I)) (F (I := I)) (denominator i)) :
    ∃ (D : Derivation Int (R (I := I)) (R (I := I)))
        (scale : R (I := I)),
      scale ≠ 0 ∧
      (¬ prime ∣ scale) ∧
      ∀ z : F (I := I),
        FractionDerivation.extend D z =
          algebraMap (R (I := I)) (F (I := I)) scale * delta z := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let scale : R (I := I) := ∏ i, denominator i
  let other : I → R (I := I) := fun i ↦
    ∏ j ∈ Finset.univ.erase i, denominator j
  let commonNumerator : I → R (I := I) := fun i ↦
    numerator i * other i
  have hscale (i : I) : denominator i * other i = scale := by
    exact Finset.mul_prod_erase Finset.univ denominator
      (Finset.mem_univ i)
  have hgenerator (i : I) :
      algebraMap (R (I := I)) (F (I := I)) (commonNumerator i) =
        algebraMap (R (I := I)) (F (I := I)) scale *
          delta (algebraMap (R (I := I)) (F (I := I))
            (MvPolynomial.X i)) := by
    change algebraMap (R (I := I)) (F (I := I))
        (numerator i * other i) = _
    rw [map_mul, hvalue i]
    rw [mul_assoc, ← map_mul, hscale i]
    ring
  refine ⟨polynomialDerivation commonNumerator, scale, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr
      (fun i _hi ↦ hdenominator_ne i)
  · exact hprime.not_dvd_finsetProd
      (fun i _hi ↦ hdenominator_avoid i)
  · exact extend_polynomialDerivation_eq_of_generatorValues
      delta scale commonNumerator hgenerator

/-- Once two compatible common denominators both avoid a prime, tangency of
that prime is independent of the chosen denominator.  Thus denominator
normalization cannot manufacture the needed non-tangency; it can only expose
an intrinsic property of the transported derivation. -/
theorem prime_dvd_apply_iff_of_compatible_avoiding_scales
    (delta : Derivation Real (F (I := I)) (F (I := I)))
    (prime : R (I := I)) (hprime : Prime prime)
    (D₁ D₂ : Derivation Int (R (I := I)) (R (I := I)))
    (scale₁ scale₂ : R (I := I))
    (hscale₁ : ¬ prime ∣ scale₁) (hscale₂ : ¬ prime ∣ scale₂)
    (hcompat₁ : ∀ z : F (I := I),
      FractionDerivation.extend D₁ z =
        algebraMap (R (I := I)) (F (I := I)) scale₁ * delta z)
    (hcompat₂ : ∀ z : F (I := I),
      FractionDerivation.extend D₂ z =
        algebraMap (R (I := I)) (F (I := I)) scale₂ * delta z) :
    (prime ∣ D₁ prime) ↔ (prime ∣ D₂ prime) := by
  have hcross : scale₂ * D₁ prime = scale₁ * D₂ prime := by
    apply IsFractionRing.injective (R (I := I)) (F (I := I))
    simp only [map_mul]
    have h₁ := hcompat₁
      (algebraMap (R (I := I)) (F (I := I)) prime)
    have h₂ := hcompat₂
      (algebraMap (R (I := I)) (F (I := I)) prime)
    simp only [FractionDerivation.extend_algebraMap] at h₁ h₂
    rw [h₁, h₂]
    ring
  constructor
  · intro hdiv
    have hleft : prime ∣ scale₂ * D₁ prime :=
      dvd_mul_of_dvd_right hdiv scale₂
    have hright : prime ∣ scale₁ * D₂ prime := hcross ▸ hleft
    exact (hprime.dvd_mul.mp hright).resolve_left hscale₁
  · intro hdiv
    have hright : prime ∣ scale₁ * D₂ prime :=
      dvd_mul_of_dvd_right hdiv scale₁
    have hleft : prime ∣ scale₂ * D₁ prime := hcross.symm ▸ hright
    exact (hprime.dvd_mul.mp hleft).resolve_left hscale₂

/-- A genuinely common prime factor of the scale and all coordinate values
can be cancelled.  This is the safe algebraic operation behind denominator
normalization.  It does not apply when the prime divides only `D prime`;
that condition is intrinsic tangency, as the preceding theorem shows. -/
theorem exists_compatible_derivation_after_cancel_prime
    (delta : Derivation Real (F (I := I)) (F (I := I)))
    (prime : R (I := I)) (hprime0 : prime ≠ 0)
    (D : Derivation Int (R (I := I)) (R (I := I)))
    (scale reducedScale : R (I := I))
    (hscale : scale = prime * reducedScale)
    (hcoordinate : ∀ i, prime ∣ D (MvPolynomial.X i))
    (hcompat : ∀ z : F (I := I),
      FractionDerivation.extend D z =
        algebraMap (R (I := I)) (F (I := I)) scale * delta z) :
    ∃ D' : Derivation Int (R (I := I)) (R (I := I)),
      ∀ z : F (I := I),
        FractionDerivation.extend D' z =
          algebraMap (R (I := I)) (F (I := I)) reducedScale * delta z := by
  let numerator : I → R (I := I) := fun i ↦ (hcoordinate i).choose
  have hnumerator (i : I) :
      D (MvPolynomial.X i) = prime * numerator i :=
    (hcoordinate i).choose_spec
  have hmapPrime0 :
      algebraMap (R (I := I)) (F (I := I)) prime ≠ 0 := by
    intro hzero
    apply hprime0
    apply IsFractionRing.injective (R (I := I)) (F (I := I))
    simpa using hzero
  have hgenerator (i : I) :
      algebraMap (R (I := I)) (F (I := I)) (numerator i) =
        algebraMap (R (I := I)) (F (I := I)) reducedScale *
          delta (algebraMap (R (I := I)) (F (I := I))
            (MvPolynomial.X i)) := by
    apply mul_left_cancel₀ hmapPrime0
    calc
      algebraMap (R (I := I)) (F (I := I)) prime *
            algebraMap (R (I := I)) (F (I := I)) (numerator i) =
          algebraMap (R (I := I)) (F (I := I))
            (D (MvPolynomial.X i)) := by
              rw [← map_mul, ← hnumerator i]
      _ = algebraMap (R (I := I)) (F (I := I)) scale *
            delta (algebraMap (R (I := I)) (F (I := I))
              (MvPolynomial.X i)) := by
              simpa only [FractionDerivation.extend_algebraMap] using
                hcompat (algebraMap (R (I := I)) (F (I := I))
                  (MvPolynomial.X i))
      _ = algebraMap (R (I := I)) (F (I := I)) prime *
            (algebraMap (R (I := I)) (F (I := I)) reducedScale *
              delta (algebraMap (R (I := I)) (F (I := I))
                (MvPolynomial.X i))) := by
              rw [hscale, map_mul]
              ring
  refine ⟨polynomialDerivation numerator, ?_⟩
  exact extend_polynomialDerivation_eq_of_generatorValues
    delta reducedScale numerator hgenerator

end CommonDenominator

/-! ## The intrinsic-tangency caveat -/

namespace NormalizationCaveat

/-- A prime-avoiding scale alone cannot imply non-invariance.  The one
variable Euler derivation has scale `1`, but preserves the prime `(X)`.
This concrete counterexample prevents the common-denominator normalization
from being misused as the missing fresh-W1 non-tangency theorem. -/
theorem exists_invariant_prime_with_avoiding_scale :
    ∃ (D : Derivation Int (MvPolynomial Unit Real)
          (MvPolynomial Unit Real))
        (prime scale : MvPolynomial Unit Real),
      Prime prime ∧ (¬ prime ∣ scale) ∧ prime ∣ D prime := by
  let prime : MvPolynomial Unit Real := MvPolynomial.X ()
  let D : Derivation Int (MvPolynomial Unit Real)
      (MvPolynomial Unit Real) :=
    CommonDenominator.polynomialDerivation (fun _ ↦ prime)
  refine ⟨D, prime, 1, ?_, ?_, ?_⟩
  · exact MvPolynomial.X_prime
  · exact (MvPolynomial.X_prime (R := Real) (i := ())).not_dvd_one
  · refine ⟨1, ?_⟩
    change CommonDenominator.polynomialDerivation
        (fun _ : Unit ↦ MvPolynomial.X ()) (MvPolynomial.X ()) =
      MvPolynomial.X () * 1
    rw [CommonDenominator.polynomialDerivation_X]
    simp

end NormalizationCaveat

end


end Natfunbasis.Wilkie.FreshStagePrimeDerivation

/-! ## The transported analytic derivation in stage coordinates -/

namespace Natfunbasis.Wilkie.GeneratorSequence

noncomputable section

open FreshStagePrimeDerivation

open BaseRationalClassification

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The current fresh W1 polynomial is irreducible after rational scalar
extension.  This is the arithmetic input to geometric squarefreeness. -/
theorem currentBasePolynomial_irreducible_fractionRing {n : Nat}
    (hfresh : S.IsFreshBase n) :
    Irreducible (MvPolynomial.map
      (algebraMap Int (FractionRing Int))
      (S.currentBasePolynomial n)) :=
  ScalarExtension.irreducible_map_fractionRing_of_prime_of_nonconstant
    (S.currentBasePolynomial_prime n)
    (S.currentBasePolynomial_ne_C hfresh)

/-- The completed set of generators at every finite stage is finite. -/
theorem stageGenerators_finite :
    ∀ n : Nat, (S.stageGenerators n).Finite := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [S.stageGenerators_succ]
      apply Set.Finite.insert
      unfold GeneratorSequence.beforeTauGenerators
      split_ifs
      · exact ih.insert _
      · exact ih

/-- Any differential `Real`-algebra has its derivative as a
`Real`-linear derivation. -/
def realDerivationOfDifferential
    (E : Type*) [Field E] [Differential E] [Algebra Real E]
    [DifferentialAlgebra Real E] : Derivation Real E E := by
  let f : E →ₗ[Real] E :=
    { toFun := fun z ↦ Differential.deriv z
      map_add' := by
        intro x y
        exact map_add Differential.deriv x y
      map_smul' := by
        intro c x
        rw [Algebra.smul_def, Differential.deriv.leibniz,
          deriv_algebraMap, deriv_real_eq_zero, map_zero]
        simp [Algebra.smul_def] }
  exact Derivation.mk' f (fun x y ↦ Differential.deriv.leibniz x y)

@[simp]
theorem realDerivationOfDifferential_apply
    (E : Type*) [Field E] [Differential E] [Algebra Real E]
    [DifferentialAlgebra Real E] (z : E) :
    realDerivationOfDifferential E z = Differential.deriv z := by
  change Differential.deriv z = Differential.deriv z
  rfl

/-- The analytic derivative transported to the canonical rational function
coordinates of a completed stage. -/
def stageCoordinateDerivation {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    Derivation Real (S.StageCoordinateField n)
      (S.StageCoordinateField n) := by
  let e := S.stageCoordinateEquiv hstage
  letI : Differential (S.StageCoordinateField n) :=
    Differential.equiv e.toRingEquiv
  letI : DifferentialAlgebra Real (S.StageCoordinateField n) :=
    DifferentialAlgebra.equiv e
  exact realDerivationOfDifferential (S.StageCoordinateField n)

/-- The coordinate derivation is exactly conjugate to analytic
differentiation by `stageCoordinateEquiv`. -/
theorem stageCoordinateDerivation_compatibility {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (z : S.StageCoordinateField n) :
    S.stageCoordinateEquiv hstage
        (S.stageCoordinateDerivation hstage z) =
      Differential.deriv (S.stageCoordinateEquiv hstage z) := by
  let e := S.stageCoordinateEquiv hstage
  change e (e.symm (Differential.deriv (e z))) =
    Differential.deriv (e z)
  exact e.apply_symm_apply _

/-- At every algebraically independent completed stage, a single nonzero
polynomial clears the denominators of the transported derivatives of all
stage coordinates. -/
theorem exists_stagePolynomialDerivation {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    ∃ (Dpoly : Derivation Int (S.StageCoordinateRing n)
          (S.StageCoordinateRing n))
        (scale : S.StageCoordinateRing n),
      scale ≠ 0 ∧
      ∀ z : S.StageCoordinateField n,
        S.stageCoordinateEquiv hstage
            (FractionDerivation.extend Dpoly z) =
          S.stageCoordinateEquiv hstage
              (algebraMap (S.StageCoordinateRing n)
                (S.StageCoordinateField n) scale) *
            Differential.deriv (S.stageCoordinateEquiv hstage z) := by
  letI : Finite (S.stageGenerators n) :=
    (S.stageGenerators_finite n).to_subtype
  obtain ⟨Dpoly, scale, hscale, hcompat⟩ :=
    CommonDenominator.exists_polynomialDerivation
      (S.stageCoordinateDerivation hstage)
  refine ⟨Dpoly, scale, hscale, ?_⟩
  intro z
  rw [hcompat z, map_mul]
  rw [S.stageCoordinateDerivation_compatibility]

/-- Stage-facing prime-avoiding normalization.  It remains only to display,
for each actual stage generator, a denominator for its derivative which is
coprime to the selected prime factor. -/
theorem exists_stagePolynomialDerivation_avoiding_prime {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (prime : S.StageCoordinateRing n) (hprime : Prime prime)
    (numerator denominator : S.stageGenerators n →
      S.StageCoordinateRing n)
    (hdenominator_ne : ∀ i, denominator i ≠ 0)
    (hdenominator_avoid : ∀ i, ¬ prime ∣ denominator i)
    (hvalue : ∀ i,
      algebraMap (S.StageCoordinateRing n)
          (S.StageCoordinateField n) (numerator i) =
        S.stageCoordinateDerivation hstage
            (algebraMap (S.StageCoordinateRing n)
              (S.StageCoordinateField n) (MvPolynomial.X i)) *
          algebraMap (S.StageCoordinateRing n)
            (S.StageCoordinateField n) (denominator i)) :
    ∃ (Dpoly : Derivation Int (S.StageCoordinateRing n)
          (S.StageCoordinateRing n))
        (scale : S.StageCoordinateRing n),
      scale ≠ 0 ∧
      (¬ prime ∣ scale) ∧
      ∀ z : S.StageCoordinateField n,
        S.stageCoordinateEquiv hstage
            (FractionDerivation.extend Dpoly z) =
          S.stageCoordinateEquiv hstage
              (algebraMap (S.StageCoordinateRing n)
                (S.StageCoordinateField n) scale) *
            Differential.deriv (S.stageCoordinateEquiv hstage z) := by
  letI : Finite (S.stageGenerators n) :=
    (S.stageGenerators_finite n).to_subtype
  obtain ⟨Dpoly, scale, hscale0, hscaleAvoid, hcompat⟩ :=
    CommonDenominator.exists_polynomialDerivation_avoiding_prime
      (S.stageCoordinateDerivation hstage) prime hprime
      numerator denominator hdenominator_ne hdenominator_avoid hvalue
  refine ⟨Dpoly, scale, hscale0, hscaleAvoid, ?_⟩
  intro z
  rw [hcompat z, map_mul]
  rw [S.stageCoordinateDerivation_compatibility]

/-- Squarefreeness and the single whole-base test `base ∤ D(base)` turn a
compatible polynomial derivation into the exact input consumed by the
prime-residue reduction. -/
def freshStagePrimeDerivationInput_of_squarefree_of_not_dvd {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hsquarefree : Squarefree (S.stageCoordinateBasePolynomial n))
    (Dpoly : Derivation Int (S.StageCoordinateRing n)
      (S.StageCoordinateRing n))
    (scale : S.StageCoordinateRing n)
    (hcompat : ∀ z : S.StageCoordinateField n,
      S.stageCoordinateEquiv hstage
          (FractionDerivation.extend Dpoly z) =
        S.stageCoordinateEquiv hstage
            (algebraMap (S.StageCoordinateRing n)
              (S.StageCoordinateField n) scale) *
          Differential.deriv (S.stageCoordinateEquiv hstage z))
    (hnotdiv : ¬ S.stageCoordinateBasePolynomial n ∣
      Dpoly (S.stageCoordinateBasePolynomial n)) :
    S.FreshStagePrimeDerivationInput hstage := by
  let hexists :=
    NonInvariantFactor.exists_irreducible_factor_not_dvd_deriv
      Dpoly (S.stageCoordinateBasePolynomial_ne_zero hstage)
        hsquarefree hnotdiv
  let h := hexists.choose
  have hirr : Irreducible h := hexists.choose_spec.1
  have hdiv : h ∣ S.stageCoordinateBasePolynomial n :=
    hexists.choose_spec.2.1
  have hnonInvariant : ¬ h ∣ Dpoly h := hexists.choose_spec.2.2
  exact FreshStagePrimeDerivationInput.ofSquarefreeFactor S
    hstage hsquarefree Dpoly scale hcompat h hirr hdiv hnonInvariant

/-- A stage-facing constructor from a compatible polynomial derivation for
which the current base does not divide its derivative.  The unrestricted
common-denominator theorem above is not enough by itself: multiplying both
the derivation and its scale by the current base would preserve compatibility
but destroy this non-divisibility condition. -/
theorem exists_freshStagePrimeDerivationInput_of_goodDerivation
    {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hsquarefree : Squarefree (S.stageCoordinateBasePolynomial n))
    (hgood : ∃
      (Dpoly : Derivation Int (S.StageCoordinateRing n)
        (S.StageCoordinateRing n))
      (scale : S.StageCoordinateRing n),
      scale ≠ 0 ∧
      (∀ z : S.StageCoordinateField n,
        S.stageCoordinateEquiv hstage
            (FractionDerivation.extend Dpoly z) =
          S.stageCoordinateEquiv hstage
              (algebraMap (S.StageCoordinateRing n)
                (S.StageCoordinateField n) scale) *
            Differential.deriv (S.stageCoordinateEquiv hstage z)) ∧
      (¬ S.stageCoordinateBasePolynomial n ∣
        Dpoly (S.stageCoordinateBasePolynomial n))) :
    Nonempty (S.FreshStagePrimeDerivationInput hstage) := by
  obtain ⟨Dpoly, scale, _hscale, hcompat, hnotdiv⟩ := hgood
  exact ⟨S.freshStagePrimeDerivationInput_of_squarefree_of_not_dvd
    hstage hsquarefree Dpoly scale hcompat hnotdiv⟩

/-- Global assembly: scalar-extension squarefreeness and the whole-base
non-divisibility test at each fresh stage imply exactly the
`FreshStageIntegralSlopeRigidity` input used by the finite-stage induction. -/
theorem freshStageIntegralSlopeRigidity_of_squarefree_of_not_dvd
    (hstage : ∀ n, AlgebraicIndepOn Real id (S.stageGenerators n))
    (hsquarefree : ∀ n, S.IsFreshBase n →
      Squarefree (S.stageCoordinateBasePolynomial n))
    (hgood : ∀ n, S.IsFreshBase n → ∃
      (Dpoly : Derivation Int (S.StageCoordinateRing n)
        (S.StageCoordinateRing n))
      (scale : S.StageCoordinateRing n),
      scale ≠ 0 ∧
      (∀ z : S.StageCoordinateField n,
        S.stageCoordinateEquiv (hstage n)
            (FractionDerivation.extend Dpoly z) =
          S.stageCoordinateEquiv (hstage n)
              (algebraMap (S.StageCoordinateRing n)
                (S.StageCoordinateField n) scale) *
            Differential.deriv
              (S.stageCoordinateEquiv (hstage n) z)) ∧
      (¬ S.stageCoordinateBasePolynomial n ∣
        Dpoly (S.stageCoordinateBasePolynomial n))) :
    S.FreshStageIntegralSlopeRigidity := by
  apply S.freshStageIntegralSlopeRigidity_of_primeDerivations hstage
  intro n hfresh
  exact (S.exists_freshStagePrimeDerivationInput_of_goodDerivation
    (hstage n) (hsquarefree n hfresh)
      (hgood n hfresh)).some

end

end Natfunbasis.Wilkie.GeneratorSequence
