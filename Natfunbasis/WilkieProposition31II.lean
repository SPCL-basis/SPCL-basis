import Natfunbasis.WilkieRationalExtension

/-!
# The logarithmic-adjunction calculation around Wilkie Proposition 3.1(ii)

This file develops the rational-function calculation for an adjunction
`alpha′ = beta′ / beta`.  In polynomial coordinates the indeterminate has
derivative `c`, so the relevant derivation is
`Differential.implicitDeriv (Polynomial.C c)`.

The pole and degree arguments below are independent of the final
integer-slope assertion in the printed Proposition 3.1(ii).  They show that
any solution of `X' = Y' X` has `X` in the base field and that `Y` is affine
linear in the new primitive, with constant slope.

The printed integer-slope conclusion is not valid from the stated
same-constants hypothesis alone.  A standard differential-rational-field
counterexample is `K = C(b)`, `b′ = b/2`, `G = K(t)`, `t′ = 1`, with
constant field `C`, `beta = b^2`, and `alpha = t`.  Then `alpha′ =
beta′/beta`; taking `X = b` and `Y = alpha/2` gives `X′ = Y′ X`, while
the coefficient `1/2` of `alpha` is not an integer.  Accordingly, this file
proves the valid affine classification and makes the additional integrality
rigidity needed for the source-shaped conclusion an explicit hypothesis.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.Proposition31II

noncomputable section

variable {F : Type*} [Field F] [Differential F]

/-- Coefficient formula for the polynomial derivation determined by
`T′ = c`. -/
lemma coeff_implicitDeriv_translation (c : F) (p : F[X]) (n : Nat) :
    (Differential.implicitDeriv (C c) p).coeff n =
      (p.coeff n)′ + (n + 1 : F) * c * p.coeff (n + 1) := by
  change (p.coeff n)′ + (C c * derivative p).coeff n = _
  rw [coeff_C_mul, coeff_derivative]
  ring

/-- A translation-type polynomial derivation does not increase degree. -/
theorem natDegree_implicitDeriv_translation_le (c : F) (p : F[X]) :
    (Differential.implicitDeriv (C c) p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_implicitDeriv_translation,
    Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  have hn' : p.natDegree < n + 1 := lt_trans hn (Nat.lt_succ_self n)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn']
  simp

/-- A polynomial dividing its translation derivative is an eigenpolynomial. -/
theorem exists_translation_eigenvalue_of_dvd
    (c : F) {p : F[X]}
    (hdiv : p ∣ Differential.implicitDeriv (C c) p) :
    ∃ a : F,
      Differential.implicitDeriv (C c) p = C a * p := by
  by_cases hD0 : Differential.implicitDeriv (C c) p = 0
  · exact ⟨0, by simp [hD0]⟩
  · have hdeg :
        (Differential.implicitDeriv (C c) p).natDegree ≤ p.natDegree :=
      natDegree_implicitDeriv_translation_le c p
    have hassoc : Associated p (Differential.implicitDeriv (C c) p) :=
      Polynomial.associated_of_dvd_of_natDegree_le hdiv hD0 hdeg
    obtain ⟨u, hu⟩ := hassoc
    obtain ⟨a, _haunit, hau⟩ := Polynomial.isUnit_iff.mp u.isUnit
    refine ⟨a, ?_⟩
    calc
      Differential.implicitDeriv (C c) p = p * (u : F[X]) := hu.symm
      _ = C a * p := by rw [hau]; ring

/-- Dividing a translation eigenpolynomial by its leading coefficient makes
it invariant under the derivation. -/
theorem implicitDeriv_monicNormalization_eq_zero
    (c a : F) {p : F[X]} (hp0 : p ≠ 0)
    (hp : Differential.implicitDeriv (C c) p = C a * p) :
    Differential.implicitDeriv (C c)
      (C (p.leadingCoeff)⁻¹ * p) = 0 := by
  have hlc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hcoeff := congrArg (fun q : F[X] ↦ q.coeff p.natDegree) hp
  have hleadDeriv :
      p.leadingCoeff′ = a * p.leadingCoeff := by
    rw [coeff_implicitDeriv_translation, coeff_C_mul] at hcoeff
    have hnext : p.coeff (p.natDegree + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    rw [hnext] at hcoeff
    simpa only [Polynomial.leadingCoeff, mul_zero, add_zero] using hcoeff
  have hinv : (p.leadingCoeff⁻¹)′ =
      -p.leadingCoeff⁻¹ ^ 2 * p.leadingCoeff′ := by
    simpa only [smul_eq_mul] using
      (Derivation.leibniz_inv (Differential.deriv : Derivation Int F F)
        p.leadingCoeff)
  rw [Derivation.leibniz, Differential.implicitDeriv_C, hp, hinv,
    hleadDeriv]
  simp only [smul_eq_mul]
  field_simp [hlc0]
  simp only [div_eq_mul_inv, map_neg, map_mul]
  ring_nf
  simp

section Extension

variable {K L : Type*} [Field K] [Field L]
  [Differential K] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L] [Differential.ContainConstants K L]

/-- In a no-new-constants primitive extension, every nonzero polynomial
eigenvector for the translation derivation is constant. -/
theorem isUnit_of_translation_eigen
    (c : K) (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L c)
    {p : K[X]} (hp0 : p ≠ 0)
    {a : K}
    (hp : Differential.implicitDeriv (C c) p = C a * p) :
    IsUnit p := by
  let q : K[X] := C (p.leadingCoeff)⁻¹ * p
  have hqzero : Differential.implicitDeriv (C c) q = 0 := by
    exact implicitDeriv_monicNormalization_eq_zero c a hp0 hp
  have hconst : (aeval alpha q)′ = 0 := by
    rw [Differential.deriv_aeval_eq_implicitDeriv alpha (C c)
      (by simpa using halphaDeriv), hqzero]
    simp
  obtain ⟨b, hb⟩ := mem_range_of_deriv_eq_zero K hconst
  have hroot : aeval alpha (q - C b) = 0 := by
    simp [hb]
  have hpoly : q - C b = 0 := by
    apply (transcendental_iff_injective.mp halpha)
    simpa using hroot
  have hqC : q = C b := sub_eq_zero.mp hpoly
  have hlc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hpC : p = C (p.leadingCoeff * b) := by
    dsimp [q] at hqC
    calc
      p = C p.leadingCoeff * (C p.leadingCoeff⁻¹ * p) := by
        rw [← mul_assoc, ← map_mul]
        simp [hlc0]
      _ = C p.leadingCoeff * C b := by rw [hqC]
      _ = C (p.leadingCoeff * b) := by rw [map_mul]
  rw [hpC]
  apply Polynomial.isUnit_C.mpr
  rw [isUnit_iff_ne_zero]
  intro hzero
  apply hp0
  rw [hpC, hzero, map_zero]

/-- A nonzero polynomial dividing its translation derivative is a unit. -/
theorem isUnit_of_dvd_implicitDeriv_translation
    (c : K) (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L c)
    {p : K[X]} (hp0 : p ≠ 0)
    (hdiv : p ∣ Differential.implicitDeriv (C c) p) :
    IsUnit p := by
  obtain ⟨a, ha⟩ := exists_translation_eigenvalue_of_dvd c hdiv
  exact isUnit_of_translation_eigen c alpha halpha halphaDeriv hp0 ha

/-- In the rational logarithmic equation for a primitive adjunction, the
reduced denominator of the primitive has no nonconstant factor. -/
theorem denominator_isUnit_of_translation_logEquation
    [CharZero K]
    (c : K) (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L c)
    {p q r s : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q) * s ^ 2 =
        (Differential.implicitDeriv (C c) r * s -
          r * Differential.implicitDeriv (C c) s) * p * q) :
    IsUnit s := by
  letI : StrongNormalizationMonoid K :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  by_contra hsunit
  obtain ⟨h, hhmem⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors hs0 hsunit
  have hhirr : Irreducible h :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor h hhmem
  have hhdivs : h ∣ s :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hhmem
  have hhdivD : h ∣ Differential.implicitDeriv (C c) h :=
    Proposition31.irreducible_dvd_deriv_of_rational_logEquation
      (Differential.implicitDeriv (C c)) hp0 hq0 hr0 hs0 hpq hrs heq
      hhirr hhdivs
  exact hhirr.not_isUnit <|
    isUnit_of_dvd_implicitDeriv_translation
      c alpha halpha halphaDeriv hhirr.ne_zero hhdivD

/-- Once the denominator of the primitive is a unit, rescale its numerator
to a polynomial primitive without changing the represented rational
function. -/
theorem exists_polynomial_primitive_of_translation_logEquation
    (c : K)
    {p q r s : K[X]}
    (hsunit : IsUnit s)
    (heq :
      (Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q) * s ^ 2 =
        (Differential.implicitDeriv (C c) r * s -
          r * Differential.implicitDeriv (C c) s) * p * q) :
    ∃ y : K[X],
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        algebraMap K[X] (RatFunc K) y ∧
      Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q =
        Differential.implicitDeriv (C c) y * p * q := by
  obtain ⟨b, hbunit, hbs⟩ := Polynomial.isUnit_iff.mp hsunit
  have hb0 : b ≠ 0 := isUnit_iff_ne_zero.mp hbunit
  let D := Differential.implicitDeriv (C c)
  let A := D p * q - p * D q
  let B := D r * C b - r * C b′
  let y := C b⁻¹ * r
  have heqC : A * (C b) ^ 2 = B * p * q := by
    have heqC := heq
    rw [← hbs] at heqC
    simp only [Differential.implicitDeriv_C] at heqC
    exact heqC
  have hscalar : C (b⁻¹ ^ 2) * (C b) ^ 2 = (1 : K[X]) := by
    rw [← map_pow, ← map_mul]
    simp [hb0]
  have hscaled : A = C (b⁻¹ ^ 2) * B * p * q := by
    calc
      A = A * 1 := by ring
      _ = A * (C (b⁻¹ ^ 2) * (C b) ^ 2) := by rw [hscalar]
      _ = C (b⁻¹ ^ 2) * (A * (C b) ^ 2) := by ring
      _ = C (b⁻¹ ^ 2) * (B * p * q) := by rw [heqC]
      _ = C (b⁻¹ ^ 2) * B * p * q := by ring
  have hbinv : b⁻¹′ = -b⁻¹ ^ 2 * b′ := by
    simpa only [smul_eq_mul] using
      (Derivation.leibniz_inv (Differential.deriv : Derivation Int K K) b)
  have hCcancel : C b⁻¹ ^ 2 * C b = (C b⁻¹ : K[X]) := by
    rw [← map_pow, ← map_mul]
    congr 1
    field_simp [hb0]
  have hDy : D y = C (b⁻¹ ^ 2) * B := by
    dsimp [y, B, D]
    rw [Derivation.leibniz, Differential.implicitDeriv_C, hbinv]
    simp only [smul_eq_mul, map_neg, map_mul, map_pow]
    linear_combination -(Differential.implicitDeriv (C c) r) * hCcancel
  have hpoly : D p * q - p * D q = D y * p * q := by
    rw [hDy]
    exact hscaled
  refine ⟨y, ?_, hpoly⟩
  calc
    algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        algebraMap K[X] (RatFunc K) r / RatFunc.C b := by
          rw [← hbs, RatFunc.algebraMap_C]
    _ = RatFunc.C b⁻¹ * algebraMap K[X] (RatFunc K) r := by
      rw [div_eq_mul_inv, ← map_inv₀]
      ring
    _ = algebraMap K[X] (RatFunc K) y := by
      simp [y, map_mul, RatFunc.algebraMap_C]

/-- If the logarithmic derivative of a reduced rational function is the
derivative of a polynomial in a primitive adjunction, then both numerator
and denominator are units. -/
theorem numerator_denominator_isUnit_of_polynomial_logEquation
    (c : K) (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L c)
    {p q y : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q =
        Differential.implicitDeriv (C c) y * p * q) :
    IsUnit p ∧ IsUnit q := by
  let D := Differential.implicitDeriv (C c)
  have hpFactor : D p * q = p * (D q + D y * q) := by
    dsimp [D]
    linear_combination hcross
  have hpDivProd : p ∣ D p * q := by
    exact ⟨D q + D y * q, hpFactor⟩
  have hpDiv : p ∣ D p := hpq.dvd_of_dvd_mul_right hpDivProd
  have hqFactor : p * D q = q * (D p - D y * p) := by
    dsimp [D]
    linear_combination -hcross
  have hqDivProd : q ∣ p * D q := by
    exact ⟨D p - D y * p, hqFactor⟩
  have hqDiv : q ∣ D q := hpq.symm.dvd_of_dvd_mul_right <| by
    simpa [mul_comm] using hqDivProd
  exact ⟨
    isUnit_of_dvd_implicitDeriv_translation
      c alpha halpha halphaDeriv hp0 hpDiv,
    isUnit_of_dvd_implicitDeriv_translation
      c alpha halpha halphaDeriv hq0 hqDiv⟩

/-- The translation derivation commutes with formal polynomial
differentiation. -/
theorem derivative_implicitDeriv_translation (c : K) (p : K[X]) :
    (Differential.implicitDeriv (C c) p).derivative =
      Differential.implicitDeriv (C c) p.derivative := by
  ext n
  rw [coeff_derivative, coeff_implicitDeriv_translation,
    coeff_implicitDeriv_translation, coeff_derivative, coeff_derivative]
  push_cast
  rw [Differential.deriv.leibniz]
  simp only [smul_eq_mul]
  simp
  ring

/-- A polynomial whose translation derivative is scalar is affine linear.
The slope is a constant of the base differential field. -/
theorem eq_affine_of_implicitDeriv_translation_eq_C
    [CharZero K]
    (c : K) (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L c)
    {y : K[X]} {d : K}
    (hy : Differential.implicitDeriv (C c) y = C d) :
    ∃ a v : K, a′ = 0 ∧ y = C a * X + C v := by
  have hDderiv :
      Differential.implicitDeriv (C c) y.derivative = 0 := by
    rw [← derivative_implicitDeriv_translation, hy, derivative_C]
  have hconst : (aeval alpha y.derivative)′ = 0 := by
    rw [Differential.deriv_aeval_eq_implicitDeriv alpha (C c)
      (by simpa using halphaDeriv), hDderiv]
    simp
  obtain ⟨a, ha⟩ := mem_range_of_deriv_eq_zero K hconst
  have hyderiv : y.derivative = C a := by
    apply (transcendental_iff_injective.mp halpha)
    simp [ha]
  have hazero : a′ = 0 := by
    have h := hDderiv
    rw [hyderiv, Differential.implicitDeriv_C] at h
    exact C_injective (by simpa using h)
  let v : K := (y - C a * X).coeff 0
  have hresidual : y - C a * X = C v := by
    apply Polynomial.eq_C_of_derivative_eq_zero
    rw [derivative_sub, hyderiv, derivative_mul, derivative_C,
      derivative_X]
    simp
  refine ⟨a, v, hazero, ?_⟩
  linear_combination hresidual

/-- Correct affine-slope form of the rational-function calculation for a
primitive adjunction.  The slope is a constant, but no integrality assertion
is made. -/
theorem rationalFunction_affine_of_polynomial_logEquation
    [CharZero K]
    (c : K) (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L c)
    {p q y : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q =
        Differential.implicitDeriv (C c) y * p * q) :
    ∃ a u v : K, a′ = 0 ∧ u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q = RatFunc.C u ∧
      y = C a * X + C v ∧
      u′ = (a * c + v′) * u := by
  obtain ⟨hpunit, hqunit⟩ :=
    numerator_denominator_isUnit_of_polynomial_logEquation
      c alpha halpha halphaDeriv hp0 hq0 hpq hcross
  obtain ⟨x, hxunit, hxp⟩ := Polynomial.isUnit_iff.mp hpunit
  obtain ⟨z, hzunit, hzq⟩ := Polynomial.isUnit_iff.mp hqunit
  have hx0 : x ≠ 0 := isUnit_iff_ne_zero.mp hxunit
  have hz0 : z ≠ 0 := isUnit_iff_ne_zero.mp hzunit
  let d : K := (x′ * z - x * z′) / (x * z)
  have hcrossC := hcross
  rw [← hxp, ← hzq, Differential.implicitDeriv_C,
    Differential.implicitDeriv_C] at hcrossC
  have hxzC0 : C x * C z ≠ (0 : K[X]) := by
    exact mul_ne_zero (by simpa using hx0) (by simpa using hz0)
  have hDy : Differential.implicitDeriv (C c) y = C d := by
    apply mul_right_cancel₀ hxzC0
    calc
      Differential.implicitDeriv (C c) y * (C x * C z) =
          (Differential.implicitDeriv (C c) y * C x) * C z := by ring
      _ = C x′ * C z - C x * C z′ := hcrossC.symm
      _ = C (x′ * z - x * z′) := by rw [map_sub, map_mul, map_mul]
      _ = C (d * (x * z)) := by
        congr 1
        dsimp [d]
        field_simp [hx0, hz0]
      _ = C d * (C x * C z) := by rw [map_mul, map_mul]
  obtain ⟨a, v, hazero, hy⟩ :=
    eq_affine_of_implicitDeriv_translation_eq_C
      c alpha halpha halphaDeriv hDy
  have hDaffine :
      Differential.implicitDeriv (C c) y = C (a * c + v′) := by
    rw [hy, map_add, Derivation.leibniz,
      Differential.implicitDeriv_C, Differential.implicitDeriv_X,
      Differential.implicitDeriv_C, hazero]
    simp only [smul_eq_mul, map_zero, mul_zero, add_zero]
    rw [← map_mul, ← map_add]
  have hd : d = a * c + v′ := by
    apply C_injective
    exact hDy.symm.trans hDaffine
  let u : K := x / z
  have hu0 : u ≠ 0 := div_ne_zero hx0 hz0
  have hfrac :
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q = RatFunc.C u := by
    rw [← hxp, ← hzq, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
    exact (map_div₀ (RatFunc.C (K := K)) x z).symm
  have huderiv : u′ = d * u := by
    dsimp [u, d]
    rw [Derivation.leibniz_div (Differential.deriv : Derivation Int K K)]
    simp only [smul_eq_mul]
    field_simp [hz0]
  refine ⟨a, u, v, hazero, hu0, hfrac, hy, ?_⟩
  rw [huderiv, hd]

/-- The strongest conclusion valid from the hypotheses printed before
Wilkie's Proposition 3.1(ii): `X` descends to the base field and `Y` is
affine linear in the primitive, with constant (not necessarily integral)
slope. -/
theorem rationalFunction_proposition31_ii_affine
    [CharZero K]
    (beta : K) (_hbeta : beta ≠ 0)
    (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L (beta′ / beta))
    {p q r s : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C (beta′ / beta)) p * q -
          p * Differential.implicitDeriv (C (beta′ / beta)) q) * s ^ 2 =
        (Differential.implicitDeriv (C (beta′ / beta)) r * s -
          r * Differential.implicitDeriv (C (beta′ / beta)) s) * p * q) :
    ∃ a u v : K, a′ = 0 ∧ u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q = RatFunc.C u ∧
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        RatFunc.C a * RatFunc.X + RatFunc.C v ∧
      u′ = (a * (beta′ / beta) + v′) * u := by
  let c : K := beta′ / beta
  have hprimitive : ∃ y : K[X],
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        algebraMap K[X] (RatFunc K) y ∧
      Differential.implicitDeriv (C c) p * q -
          p * Differential.implicitDeriv (C c) q =
        Differential.implicitDeriv (C c) y * p * q := by
    by_cases hr0 : r = 0
    · have hAsq :
          (Differential.implicitDeriv (C c) p * q -
              p * Differential.implicitDeriv (C c) q) * s ^ 2 = 0 := by
        simpa [c, hr0] using heq
      have hA :
          Differential.implicitDeriv (C c) p * q -
              p * Differential.implicitDeriv (C c) q = 0 :=
        (mul_eq_zero.mp hAsq).resolve_right (pow_ne_zero 2 hs0)
      refine ⟨0, ?_, ?_⟩
      · simp [hr0]
      · simpa using hA
    · have hsunit : IsUnit s :=
        denominator_isUnit_of_translation_logEquation
          c alpha halpha (by simpa [c] using halphaDeriv)
          hp0 hq0 hr0 hs0 hpq hrs (by simpa [c] using heq)
      exact exists_polynomial_primitive_of_translation_logEquation
        c hsunit (by simpa [c] using heq)
  obtain ⟨y, hYpoly, hcross⟩ := hprimitive
  obtain ⟨a, u, v, hazero, hu0, hX, hy, hu⟩ :=
    rationalFunction_affine_of_polynomial_logEquation
      c alpha halpha (by simpa [c] using halphaDeriv)
      hp0 hq0 hpq hcross
  have hyrat := congrArg (algebraMap K[X] (RatFunc K)) hy
  have hY :
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        RatFunc.C a * RatFunc.X + RatFunc.C v := by
    rw [hYpoly]
    simpa [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      using hyrat
  exact ⟨a, u, v, hazero, hu0, hX, hY, by simpa [c] using hu⟩

/-- The extra base-field property needed to turn a constant affine slope
into the integer asserted in the printed Proposition 3.1(ii).

This hypothesis is deliberately explicit.  It is not a consequence of a
no-new-constants primitive extension alone; in Wilkie's finite-stage
application it is supplied by the simultaneous solution-classification
invariant. -/
def IntegralSlopeRigidity (beta : K) : Prop :=
  ∀ (a u v : K), a′ = 0 → u ≠ 0 →
    u′ = (a * (beta′ / beta) + v′) * u →
    ∃ m : Int, a = (m : K)

/-- Once a slope is integral, rescaling by the corresponding integral power
of `beta` removes its logarithmic derivative. -/
theorem rescale_integral_slope
    (beta : K) (hbeta : beta ≠ 0) (m : Int)
    {u v : K} (hu0 : u ≠ 0)
    (hu : u′ = ((m : K) * (beta′ / beta) + v′) * u) :
    ∃ w : K, w ≠ 0 ∧ u = beta ^ m * w ∧ w′ = v′ * w := by
  let w : K := beta ^ (-m) * u
  have hw0 : w ≠ 0 := mul_ne_zero (zpow_ne_zero _ hbeta) hu0
  have hfactor : u = beta ^ m * w := by
    dsimp [w]
    calc
      u = 1 * u := by ring
      _ = beta ^ (m + -m) * u := by simp
      _ = (beta ^ m * beta ^ (-m)) * u := by
        rw [zpow_add₀ hbeta]
      _ = beta ^ m * (beta ^ (-m) * u) := by ring
  have hpow : beta ^ (-m - 1) = beta ^ (-m) * beta⁻¹ := by
    calc
      beta ^ (-m - 1) = beta ^ (-m + (-1)) := by congr 1
      _ = beta ^ (-m) * beta ^ (-1 : Int) := by rw [zpow_add₀ hbeta]
      _ = beta ^ (-m) * beta⁻¹ := by rw [zpow_neg_one]
  have hw : w′ = v′ * w := by
    dsimp [w]
    rw [Differential.deriv.leibniz,
      Derivation.leibniz_zpow (Differential.deriv : Derivation Int K K),
      hu, hpow]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [div_eq_mul_inv]
    ring
  exact ⟨w, hw0, hfactor, hw⟩

/-- Source-shaped integral conclusion under the missing base-field rigidity
hypothesis.  All additional mathematical content beyond the valid affine
classification is visible in `IntegralSlopeRigidity beta`. -/
theorem rationalFunction_proposition31_ii_of_integralSlopeRigidity
    [CharZero K]
    (beta : K) (hbeta : beta ≠ 0)
    (hrigid : IntegralSlopeRigidity beta)
    (alpha : L) (halpha : Transcendental K alpha)
    (halphaDeriv : alpha′ = algebraMap K L (beta′ / beta))
    {p q r s : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C (beta′ / beta)) p * q -
          p * Differential.implicitDeriv (C (beta′ / beta)) q) * s ^ 2 =
        (Differential.implicitDeriv (C (beta′ / beta)) r * s -
          r * Differential.implicitDeriv (C (beta′ / beta)) s) * p * q) :
    ∃ m : Int, ∃ w v : K, w ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q =
        RatFunc.C (beta ^ m * w) ∧
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        RatFunc.C (m : K) * RatFunc.X + RatFunc.C v ∧
      w′ = v′ * w := by
  obtain ⟨a, u, v, hazero, hu0, hX, hY, hu⟩ :=
    rationalFunction_proposition31_ii_affine
      beta hbeta alpha halpha halphaDeriv hp0 hq0 hs0 hpq hrs heq
  obtain ⟨m, ha⟩ := hrigid a u v hazero hu0 hu
  have huInt :
      u′ = ((m : K) * (beta′ / beta) + v′) * u := by
    simpa [ha] using hu
  obtain ⟨w, hw0, hfactor, hw⟩ :=
    rescale_integral_slope beta hbeta m hu0 huInt
  refine ⟨m, w, v, hw0, ?_, ?_, hw⟩
  · exact hX.trans (congrArg RatFunc.C hfactor)
  · simpa [ha] using hY

/-! ## Transport to a concrete simple extension -/

/-- The valid affine form of Proposition 3.1(ii) for rational-function
coordinates evaluated at a concrete transcendental primitive. -/
theorem simpleExtension_proposition31_ii_affine
    [CharZero K]
    (beta : K) (hbeta : beta ≠ 0)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L (beta′ / beta))
    (U V : RatFunc K) (hU0 : U ≠ 0)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (Proposition31.evalAtTranscendental z hz V)′ *
        Proposition31.evalAtTranscendental z hz U) :
    ∃ a u v : K, a′ = 0 ∧ u ≠ 0 ∧
      Proposition31.evalAtTranscendental z hz U = algebraMap K L u ∧
      Proposition31.evalAtTranscendental z hz V =
        algebraMap K L a * z + algebraMap K L v ∧
      u′ = (a * (beta′ / beta) + v′) * u := by
  have hzdPolynomial :
      z′ = Polynomial.aeval z (C (beta′ / beta)) := by
    simpa using hzd
  have hcleared := Proposition31.clearedEquation_of_evalAtTranscendental
    z hz (C (beta′ / beta)) hzdPolynomial U V heq
  obtain ⟨a, u, v, hazero, hu0, hU, hV, hu⟩ :=
    rationalFunction_proposition31_ii_affine
      beta hbeta z hz hzd
      (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
      U.isCoprime_num_denom V.isCoprime_num_denom hcleared
  refine ⟨a, u, v, hazero, hu0, ?_, ?_, hu⟩
  · have h := congrArg (Proposition31.evalAtTranscendental z hz) hU
    simpa [RatFunc.num_div_denom] using h
  · have h := congrArg (Proposition31.evalAtTranscendental z hz) hV
    simpa [RatFunc.num_div_denom] using h

/-- Subtype-valued affine classification for the actual simple intermediate
field `K(z)` in the ambient differential field. -/
theorem simpleAdjoin_proposition31_ii_affine
    [CharZero K]
    (beta : K) (hbeta : beta ≠ 0)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L (beta′ / beta))
    (X Y : IntermediateField.adjoin K {z})
    (hX0 : (X : L) ≠ 0)
    (heq : ((X : L))′ = ((Y : L))′ * (X : L)) :
    ∃ a u v : K, a′ = 0 ∧ u ≠ 0 ∧
      (X : L) = algebraMap K L u ∧
      (Y : L) = algebraMap K L a * z + algebraMap K L v ∧
      u′ = (a * (beta′ / beta) + v′) * u := by
  let e := RatFunc.algEquivOfTranscendental z hz
  let U : RatFunc K := e.symm X
  let V : RatFunc K := e.symm Y
  have hU : Proposition31.evalAtTranscendental z hz U = (X : L) := by
    simp [Proposition31.evalAtTranscendental, U, e]
  have hV : Proposition31.evalAtTranscendental z hz V = (Y : L) := by
    simp [Proposition31.evalAtTranscendental, V, e]
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hX0
    rw [← hU, hzero, map_zero]
  obtain ⟨a, u, v, hazero, hu0, hXu, hYv, hu⟩ :=
    simpleExtension_proposition31_ii_affine
      beta hbeta z hz hzd U V hU0 (by simpa [hU, hV] using heq)
  exact ⟨a, u, v, hazero, hu0, hU.symm.trans hXu,
    hV.symm.trans hYv, hu⟩

/-- Source-shaped simple-extension conclusion under the explicit integral
slope rigidity of the base field. -/
theorem simpleExtension_proposition31_ii_of_integralSlopeRigidity
    [CharZero K]
    (beta : K) (hbeta : beta ≠ 0)
    (hrigid : IntegralSlopeRigidity beta)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L (beta′ / beta))
    (U V : RatFunc K) (hU0 : U ≠ 0)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (Proposition31.evalAtTranscendental z hz V)′ *
        Proposition31.evalAtTranscendental z hz U) :
    ∃ m : Int, ∃ w v : K, w ≠ 0 ∧
      Proposition31.evalAtTranscendental z hz U =
        algebraMap K L (beta ^ m * w) ∧
      Proposition31.evalAtTranscendental z hz V =
        algebraMap K L (m : K) * z + algebraMap K L v ∧
      w′ = v′ * w := by
  obtain ⟨a, u, v, hazero, hu0, hU, hV, hu⟩ :=
    simpleExtension_proposition31_ii_affine
      beta hbeta z hz hzd U V hU0 heq
  obtain ⟨m, ha⟩ := hrigid a u v hazero hu0 hu
  have huInt :
      u′ = ((m : K) * (beta′ / beta) + v′) * u := by
    simpa [ha] using hu
  obtain ⟨w, hw0, hfactor, hw⟩ :=
    rescale_integral_slope beta hbeta m hu0 huInt
  refine ⟨m, w, v, hw0, ?_, ?_, hw⟩
  · exact hU.trans (congrArg (algebraMap K L) hfactor)
  · simpa [ha] using hV

/-- Subtype-valued source-shaped conclusion for the actual simple
intermediate field, again with the missing rigidity premise visible. -/
theorem simpleAdjoin_proposition31_ii_of_integralSlopeRigidity
    [CharZero K]
    (beta : K) (hbeta : beta ≠ 0)
    (hrigid : IntegralSlopeRigidity beta)
    (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L (beta′ / beta))
    (X Y : IntermediateField.adjoin K {z})
    (hX0 : (X : L) ≠ 0)
    (heq : ((X : L))′ = ((Y : L))′ * (X : L)) :
    ∃ m : Int, ∃ w v : K, w ≠ 0 ∧
      (X : L) = algebraMap K L (beta ^ m * w) ∧
      (Y : L) = algebraMap K L (m : K) * z + algebraMap K L v ∧
      w′ = v′ * w := by
  let e := RatFunc.algEquivOfTranscendental z hz
  let U : RatFunc K := e.symm X
  let V : RatFunc K := e.symm Y
  have hU : Proposition31.evalAtTranscendental z hz U = (X : L) := by
    simp [Proposition31.evalAtTranscendental, U, e]
  have hV : Proposition31.evalAtTranscendental z hz V = (Y : L) := by
    simp [Proposition31.evalAtTranscendental, V, e]
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hX0
    rw [← hU, hzero, map_zero]
  obtain ⟨m, w, v, hw0, hXw, hYv, hw⟩ :=
    simpleExtension_proposition31_ii_of_integralSlopeRigidity
      beta hbeta hrigid z hz hzd U V hU0 (by
        simpa [hU, hV] using heq)
  exact ⟨m, w, v, hw0, hU.symm.trans hXw,
    hV.symm.trans hYv, hw⟩

end Extension

end

end Natfunbasis.Wilkie.Proposition31II
