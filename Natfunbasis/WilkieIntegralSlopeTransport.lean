import Natfunbasis.WilkieProposition31II
import Natfunbasis.WilkieDifferentialIntermediateField

/-!
# Transport of integral-slope rigidity through exponential adjunctions

This file proves that `Proposition31II.IntegralSlopeRigidity beta` survives
adjoining a transcendental exponential `z` with `z' = b' z`, provided the
adjunction introduces no new constants.  The proof is the shifted version of
the rational-function calculation in Wilkie Proposition 3.1(i): a scalar
term from the old field does not affect the pole argument, the rational
primitive still descends to the old field, and the remaining equation is
exactly the old integral-slope rigidity hypothesis.

There is deliberately no corresponding theorem for an arbitrary primitive
adjunction.  It is false: when `z' = beta'/beta`, the choice `u = 1` and
`v = -a*z` witnesses every constant slope `a` in the enlarged field.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.IntegralSlopeTransport

noncomputable section

open Proposition31

variable {F : Type*} [Field F] [CharZero F] [Differential F]

/-! ## A scalar-shifted Euler logarithmic equation -/

/-- Adding a scalar term from the coefficient field to a rational
logarithmic equation does not change the local pole conclusion: every prime
in the reduced denominator of the primitive is invariant under the
polynomial derivation. -/
theorem irreducible_dvd_deriv_of_shifted_rational_logEquation
    (D : Derivation Int F[X] F[X]) (a : F)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      ((D p * q - p * D q) - C a * p * q) * s ^ 2 =
        (D r * s - r * D s) * p * q)
    {h : F[X]} (hh : Irreducible h) (hdivs : h ∣ s) :
    h ∣ D h := by
  by_contra hDh
  have hhprime : Prime h := hh.prime
  obtain ⟨i, hi⟩ := exists_hasExactOrder h hh hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder h hh hq0
  obtain ⟨l, hl⟩ := exists_hasExactOrder h hh hr0
  obtain ⟨e, hs⟩ := exists_hasExactOrder h hh hs0
  have hepos : 0 < e := hs.pos_of_dvd hdivs
  have hlzero : l = 0 := by
    by_contra hl0
    exact hh.not_isUnit <| hrs.isUnit_of_dvd'
      (hl.dvd_base_of_pos (Nat.pos_of_ne_zero hl0)) hdivs
  have hr : HasExactOrder h 0 r := by simpa [hlzero] using hl
  have hB : HasExactOrder h (e - 1) (D r * s - r * D s) :=
    hasExactOrder_derivCross_of_denominator
      D hhprime hDh hepos hr hs
  have hij : i = 0 ∨ j = 0 := by
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · right
      by_contra hj0
      exact hh.not_isUnit <| hpq.isUnit_of_dvd'
        (hi.dvd_base_of_pos (Nat.pos_of_ne_zero hi0))
        (hj.dvd_base_of_pos (Nat.pos_of_ne_zero hj0))
  have hs2 : HasExactOrder h (e + e) (s ^ 2) := by
    simpa [pow_two] using hs.mul hhprime hs
  let A := (D p * q - p * D q) - C a * p * q
  let B := D r * s - r * D s
  have hright : HasExactOrder h ((e - 1 + i) + j) (B * p * q) :=
    (hB.mul hhprime hi).mul hhprime hj
  have heq' : A * s ^ 2 = B * p * q := heq
  rcases hij with hi0 | hj0
  · have hi' : HasExactOrder h 0 p := by simpa [hi0] using hi
    by_cases hjzero : j = 0
    · have hj' : HasExactOrder h 0 q := by simpa [hjzero] using hj
      by_cases hA0 : A = 0
      · exact hright.ne_zero hh.ne_zero <| by
          rw [← heq', hA0]
          simp
      · obtain ⟨t, hA⟩ := exists_hasExactOrder h hh hA0
        have hleft : HasExactOrder h (t + (e + e)) (A * s ^ 2) :=
          hA.mul hhprime hs2
        have hright' :
            HasExactOrder h ((e - 1 + i) + j) (A * s ^ 2) := by
          rw [heq']
          exact hright
        have hord := hleft.unique hh.ne_zero hright'
        omega
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
      have hcross : HasExactOrder h (j - 1) (D p * q - p * D q) :=
        hasExactOrder_logCross_of_right D hhprime hDh hjpos hi' hj
      have hscalar : h ^ j ∣ C a * p * q := by
        exact dvd_mul_of_dvd_right hj.dvd (C a * p)
      have hA : HasExactOrder h (j - 1) A := by
        apply hcross.sub_of_dvd_succ
        simpa [show j - 1 + 1 = j by omega] using hscalar
      have hleft : HasExactOrder h ((j - 1) + (e + e))
          (A * s ^ 2) := hA.mul hhprime hs2
      have hright' :
          HasExactOrder h ((e - 1 + i) + j) (A * s ^ 2) := by
        rw [heq']
        exact hright
      have hord := hleft.unique hh.ne_zero hright'
      omega
  · have hj' : HasExactOrder h 0 q := by simpa [hj0] using hj
    have hipos : 0 < i := by
      by_contra hi0
      have : i = 0 := Nat.eq_zero_of_not_pos hi0
      subst i
      by_cases hA0 : A = 0
      · exact hright.ne_zero hh.ne_zero <| by
          rw [← heq', hA0]
          simp
      · obtain ⟨t, hA⟩ := exists_hasExactOrder h hh hA0
        have hleft := hA.mul hhprime hs2
        have hright' : HasExactOrder h ((e - 1 + 0) + j)
            (A * s ^ 2) := by
          rw [heq']
          simpa using hright
        have hord := hleft.unique hh.ne_zero hright'
        omega
    have hcross : HasExactOrder h (i - 1) (D p * q - p * D q) :=
      hasExactOrder_logCross_of_left D hhprime hDh hipos hi hj'
    have hscalar : h ^ i ∣ C a * p * q := by
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hi.dvd (C a)) q
    have hA : HasExactOrder h (i - 1) A := by
      apply hcross.sub_of_dvd_succ
      simpa [show i - 1 + 1 = i by omega] using hscalar
    have hleft : HasExactOrder h ((i - 1) + (e + e))
        (A * s ^ 2) := hA.mul hhprime hs2
    have hright' :
        HasExactOrder h ((e - 1 + i) + j) (A * s ^ 2) := by
      rw [heq']
      exact hright
    have hord := hleft.unique hh.ne_zero hright'
    omega

/-- For the Euler derivation, the shifted pole lemma says that the reduced
denominator of the primitive is, up to a unit, a power of `X`. -/
theorem denominator_associated_X_pow_of_shifted_logEquation
    {c a : F} (hres : NoIntegerResonance c)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      ((Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) -
            C a * p * q) * s ^ 2 =
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q) :
    ∃ e : Nat, Associated (X ^ e) s := by
  letI : StrongNormalizationMonoid F :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  apply UniqueFactorizationMonoid.exists_associated_prime_pow_of_unique_normalized_factor _ hs0
  intro h hhmem
  have hhirr : Irreducible h :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor h hhmem
  have hhdivs : h ∣ s :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hhmem
  have hhdivD : h ∣ Differential.implicitDeriv (C c * X) h :=
    irreducible_dvd_deriv_of_shifted_rational_logEquation
      (Differential.implicitDeriv (C c * X)) a hp0 hq0 hr0 hs0 hpq hrs
      heq hhirr hhdivs
  have hassoc : Associated h X :=
    irreducible_associated_X_of_dvd_implicitDeriv hres hhirr hhdivD
  exact hassoc.eq_of_normalized
    (UniqueFactorizationMonoid.normalize_normalized_factor h hhmem)
    monic_X.normalize_eq_self

/-- The possible power of `X` is also excluded.  Thus a scalar shift does
not change the denominator conclusion of Proposition 3.1(i). -/
theorem denominator_isUnit_of_shifted_logEquation
    {c a : F} (hres : NoIntegerResonance c)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      ((Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) -
            C a * p * q) * s ^ 2 =
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q) :
    IsUnit s := by
  obtain ⟨e, hse⟩ :=
    denominator_associated_X_pow_of_shifted_logEquation
      hres hp0 hq0 hr0 hs0 hpq hrs heq
  have hezero : e = 0 := by
    by_contra he0
    have hepos : 0 < e := Nat.pos_of_ne_zero he0
    have hs : HasExactOrder X e s :=
      hasExactOrder_of_associated_pow irreducible_X.prime hse
    have hXdivs : X ∣ s := hs.dvd_base_of_pos hepos
    have hXnmidr : ¬ X ∣ r := by
      intro hXdivr
      exact irreducible_X.not_isUnit (hrs.isUnit_of_dvd' hXdivr hXdivs)
    have hr : HasExactOrder X 0 r := HasExactOrder.zero hXnmidr
    have hB : HasExactOrder X e
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) :=
      hasExactOrder_X_derivCross_of_denominator hres hepos hr hs
    obtain ⟨i, hi⟩ := exists_hasExactOrder X irreducible_X hp0
    obtain ⟨j, hj⟩ := exists_hasExactOrder X irreducible_X hq0
    have hDp : X ^ i ∣ Differential.implicitDeriv (C c * X) p :=
      X_pow_dvd_implicitDeriv_euler c hi.dvd
    have hDq : X ^ j ∣ Differential.implicitDeriv (C c * X) q :=
      X_pow_dvd_implicitDeriv_euler c hj.dvd
    have hfirst : X ^ (i + j) ∣
        Differential.implicitDeriv (C c * X) p * q := by
      simpa [pow_add] using mul_dvd_mul hDp hj.dvd
    have hsecond : X ^ (i + j) ∣
        p * Differential.implicitDeriv (C c * X) q := by
      simpa [pow_add] using mul_dvd_mul hi.dvd hDq
    have hcross : X ^ (i + j) ∣
        Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q :=
      dvd_sub hfirst hsecond
    have hpqdiv : X ^ (i + j) ∣ C a * p * q := by
      rw [pow_add]
      exact mul_dvd_mul (dvd_mul_of_dvd_right hi.dvd (C a)) hj.dvd
    have hA : X ^ (i + j) ∣
        (Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) -
            C a * p * q := dvd_sub hcross hpqdiv
    have hs2 : HasExactOrder X (e + e) (s ^ 2) := by
      simpa [pow_two] using hs.mul irreducible_X.prime hs
    have hleft : X ^ ((i + j) + (e + e)) ∣
        ((Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) -
            C a * p * q) * s ^ 2 := by
      simpa [pow_add] using mul_dvd_mul hA hs2.dvd
    have hright : HasExactOrder X ((e + i) + j)
        ((Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q) :=
      (hB.mul irreducible_X.prime hi).mul irreducible_X.prime hj
    have hlarge : X ^ ((i + j) + (e + e)) ∣
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q := by
      rw [← heq]
      exact hleft
    have hstep : (X : F[X]) ^ (((e + i) + j) + 1) ∣
        (X : F[X]) ^ ((i + j) + (e + e)) :=
      pow_dvd_pow (X : F[X]) (by omega)
    exact hright.not_dvd_succ X_ne_zero (hstep.trans hlarge)
  subst e
  obtain ⟨u, hu⟩ := hse
  have hus : (u : F[X]) = s := by simpa using hu
  exact hus ▸ u.isUnit

/-- The degree-at-infinity argument is likewise insensitive to an added
scalar: a polynomial primitive in a shifted Euler logarithmic equation is
constant. -/
theorem eq_C_of_shifted_logCross_eq_implicitDeriv_mul
    {c a : F} (hres : NoIntegerResonance c)
    {p q y : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (heq :
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        (C a + Differential.implicitDeriv (C c * X) y) * p * q) :
    ∃ γ : F, y = C γ := by
  have hydeg : y.natDegree = 0 := by
    by_contra hy0
    have hypos : 0 < y.natDegree := Nat.pos_of_ne_zero hy0
    have hDydeg := natDegree_implicitDeriv_euler_eq_of_pos hres hypos
    have hDy0 : Differential.implicitDeriv (C c * X) y ≠ 0 := by
      intro hDy
      rw [hDy] at hDydeg
      simp at hDydeg
      omega
    have hC_lt : (C a).natDegree <
        (Differential.implicitDeriv (C c * X) y).natDegree := by
      rw [hDydeg]
      simpa using hypos
    have hsumdeg :
        (C a + Differential.implicitDeriv (C c * X) y).natDegree =
          y.natDegree := by
      rw [natDegree_add_eq_right_of_natDegree_lt hC_lt, hDydeg]
    have hsum0 :
        C a + Differential.implicitDeriv (C c * X) y ≠ 0 := by
      intro hzero
      rw [hzero] at hsumdeg
      simp at hsumdeg
      omega
    have hleftdeg :
        (Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q).natDegree ≤
            p.natDegree + q.natDegree := by
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact Polynomial.natDegree_mul_le.trans <|
          add_le_add (natDegree_implicitDeriv_euler_le c p) le_rfl
      · exact Polynomial.natDegree_mul_le.trans <|
          add_le_add le_rfl (natDegree_implicitDeriv_euler_le c q)
    have hrightdeg :
        ((C a + Differential.implicitDeriv (C c * X) y) * p * q).natDegree =
          y.natDegree + p.natDegree + q.natDegree := by
      rw [Polynomial.natDegree_mul (mul_ne_zero hsum0 hp0) hq0,
        Polynomial.natDegree_mul hsum0 hp0, hsumdeg]
    have hdegrees := congrArg Polynomial.natDegree heq
    rw [hrightdeg] at hdegrees
    omega
  exact ⟨y.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hydeg⟩

/-- Full shifted pole reduction: the rational primitive belongs to the base
field, and the residual scalar logarithmic derivative is recorded for the
Euler eigenfunction classification. -/
theorem shifted_rational_primitive_eq_base_of_logEquation
    {c a : F} (hres : NoIntegerResonance c)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      ((Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) -
            C a * p * q) * s ^ 2 =
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q) :
    ∃ γ : F,
      algebraMap F[X] (RatFunc F) r /
          algebraMap F[X] (RatFunc F) s = RatFunc.C γ ∧
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        C (a + γ′) * p * q := by
  have hsunit : IsUnit s :=
    denominator_isUnit_of_shifted_logEquation
      hres hp0 hq0 hr0 hs0 hpq hrs heq
  obtain ⟨b, hbunit, hbs⟩ := Polynomial.isUnit_iff.mp hsunit
  have hb0 : b ≠ 0 := isUnit_iff_ne_zero.mp hbunit
  let D := Differential.implicitDeriv (C c * X)
  let A := (D p * q - p * D q) - C a * p * q
  let B := D r * C b - r * C b′
  let y := C b⁻¹ * r
  have heqC : A * (C b) ^ 2 = B * p * q := by
    have heqC := heq
    rw [← hbs] at heqC
    simp only [Differential.implicitDeriv_C] at heqC
    exact heqC
  have hscalar : C (b⁻¹ ^ 2) * (C b) ^ 2 = (1 : F[X]) := by
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
      (Derivation.leibniz_inv (Differential.deriv : Derivation Int F F) b)
  have hCcancel : C b⁻¹ ^ 2 * C b = (C b⁻¹ : F[X]) := by
    rw [← map_pow, ← map_mul]
    congr 1
    field_simp [hb0]
  have hDy : D y = C (b⁻¹ ^ 2) * B := by
    dsimp [y, B, D]
    rw [Derivation.leibniz, Differential.implicitDeriv_C, hbinv]
    simp only [smul_eq_mul, map_neg, map_mul, map_pow]
    linear_combination
      -(Differential.implicitDeriv (C c * X) r) * hCcancel
  have hpoly :
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        (C a + Differential.implicitDeriv (C c * X) y) * p * q := by
    have hshift : A = D y * p * q := by
      rw [hDy]
      exact hscaled
    dsimp [A, D] at hshift ⊢
    linear_combination hshift
  obtain ⟨γ, hy⟩ :=
    eq_C_of_shifted_logCross_eq_implicitDeriv_mul
      hres hp0 hq0 hpoly
  have hyrat := congrArg (algebraMap F[X] (RatFunc F)) hy
  have hyrat' : RatFunc.C b⁻¹ * algebraMap F[X] (RatFunc F) r =
      RatFunc.C γ := by
    simpa [y, map_mul, RatFunc.algebraMap_C] using hyrat
  refine ⟨γ, ?_, ?_⟩
  · calc
      algebraMap F[X] (RatFunc F) r /
            algebraMap F[X] (RatFunc F) s =
          algebraMap F[X] (RatFunc F) r / RatFunc.C b := by
            rw [← hbs, RatFunc.algebraMap_C]
      _ = RatFunc.C b⁻¹ * algebraMap F[X] (RatFunc F) r := by
        rw [div_eq_mul_inv, ← map_inv₀]
        ring
      _ = RatFunc.C γ := hyrat'
  · rw [hy, Differential.implicitDeriv_C] at hpoly
    simpa [map_add] using hpoly

/-! ## Integral slope in exponential rational coordinates -/

section ExponentialExtension

variable {E : Type*} [Field E] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E] [Differential.ContainConstants F E]

/-- Once the rational primitive has descended to the coefficient field, the
old rigidity hypothesis applies to the residual leading coefficient. -/
theorem integer_slope_of_shifted_euler_crossEquation
    (beta : F) (hrigid : Proposition31II.IntegralSlopeRigidity beta)
    (b : F) (hres : NoIntegerResonance b′)
    (a γ : F) (ha : a′ = 0)
    {p q : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C b′ * X) p * q -
          p * Differential.implicitDeriv (C b′ * X) q =
        C (a * (beta′ / beta) + γ′) * p * q) :
    ∃ m : Int, a = (m : F) := by
  obtain ⟨k, w, hw0, _hfrac, hw⟩ :=
    ratFunc_classification_of_isCoprime_crossEquation
      hres hp0 hq0 hpq hcross
  let v₀ : F := γ - (k : F) * b
  have hv₀ : v₀′ = γ′ - (k : F) * b′ := by
    dsimp [v₀]
    rw [map_sub, Differential.deriv.leibniz, Derivation.map_intCast]
    ring
  apply hrigid a w v₀ ha hw0
  rw [hw, hv₀]
  ring

/-- Coordinate form of rigidity transport through a transcendental
exponential adjunction.  The displayed equation is the completely cleared
form of

`U' = (a * beta'/beta + V') * U`.
-/
theorem rationalFunction_integralSlopeRigidity_euler
    (beta : F) (hrigid : Proposition31II.IntegralSlopeRigidity beta)
    (b : F) (hres : NoIntegerResonance b′)
    (a : F) (ha : a′ = 0)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      ((Differential.implicitDeriv (C b′ * X) p * q -
          p * Differential.implicitDeriv (C b′ * X) q) -
            C (a * (beta′ / beta)) * p * q) * s ^ 2 =
        (Differential.implicitDeriv (C b′ * X) r * s -
          r * Differential.implicitDeriv (C b′ * X) s) * p * q) :
    ∃ m : Int, a = (m : F) := by
  by_cases hr0 : r = 0
  · have hshift :
        (Differential.implicitDeriv (C b′ * X) p * q -
          p * Differential.implicitDeriv (C b′ * X) q) -
            C (a * (beta′ / beta)) * p * q = 0 := by
      have hmul :
          ((Differential.implicitDeriv (C b′ * X) p * q -
            p * Differential.implicitDeriv (C b′ * X) q) -
              C (a * (beta′ / beta)) * p * q) * s ^ 2 = 0 := by
        simpa [hr0] using heq
      exact (mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 2 hs0)
    apply integer_slope_of_shifted_euler_crossEquation
      beta hrigid b hres a 0 ha hp0 hq0 hpq
    simpa only [map_zero, add_zero] using sub_eq_zero.mp hshift
  · obtain ⟨γ, _hV, hcross⟩ :=
      shifted_rational_primitive_eq_base_of_logEquation
        hres hp0 hq0 hr0 hs0 hpq hrs heq
    exact integer_slope_of_shifted_euler_crossEquation
      beta hrigid b hres a γ ha hp0 hq0 hpq hcross

/-- Transcendence and no new constants supply the nonresonance hypothesis
needed by `rationalFunction_integralSlopeRigidity_euler`. -/
theorem rationalFunction_integralSlopeRigidity_exponential
    (beta : F) (hrigid : Proposition31II.IntegralSlopeRigidity beta)
    (b : F) (z : E) (hz : Transcendental F z)
    (hzd : z′ = algebraMap F E b′ * z)
    (a : F) (ha : a′ = 0)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      ((Differential.implicitDeriv (C b′ * X) p * q -
          p * Differential.implicitDeriv (C b′ * X) q) -
            C (a * (beta′ / beta)) * p * q) * s ^ 2 =
        (Differential.implicitDeriv (C b′ * X) r * s -
          r * Differential.implicitDeriv (C b′ * X) s) * p * q) :
    ∃ m : Int, a = (m : F) := by
  apply rationalFunction_integralSlopeRigidity_euler
    beta hrigid b
    (noIntegerResonance_deriv_of_transcendental_solution b z hz hzd)
    a ha hp0 hq0 hs0 hpq hrs heq

/-- Clearing denominators for a rational logarithmic equation with one
additional scalar from the coefficient field. -/
theorem clearedShiftedEquation_of_evalAtTranscendental
    (z : E) (hz : Transcendental F z) (w : F[X])
    (hzd : z′ = Polynomial.aeval z w)
    (a : F) (U V : RatFunc F)
    (heq : (evalAtTranscendental z hz U)′ =
      (algebraMap F E a + (evalAtTranscendental z hz V)′) *
        evalAtTranscendental z hz U) :
    ((Differential.implicitDeriv w U.num * U.denom -
        U.num * Differential.implicitDeriv w U.denom) -
          C a * U.num * U.denom) * V.denom ^ 2 =
      (Differential.implicitDeriv w V.num * V.denom -
        V.num * Differential.implicitDeriv w V.denom) *
          U.num * U.denom := by
  apply (transcendental_iff_injective.mp hz)
  have hUden : Polynomial.aeval z U.denom ≠ 0 :=
    aeval_ne_zero_of_transcendental z hz U.denom_ne_zero
  have hVden : Polynomial.aeval z V.denom ≠ 0 :=
    aeval_ne_zero_of_transcendental z hz V.denom_ne_zero
  have hUnumDeriv :
      (Polynomial.aeval z U.num)′ =
        Polynomial.aeval z (Differential.implicitDeriv w U.num) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd U.num
  have hUdenDeriv :
      (Polynomial.aeval z U.denom)′ =
        Polynomial.aeval z (Differential.implicitDeriv w U.denom) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd U.denom
  have hVnumDeriv :
      (Polynomial.aeval z V.num)′ =
        Polynomial.aeval z (Differential.implicitDeriv w V.num) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd V.num
  have hVdenDeriv :
      (Polynomial.aeval z V.denom)′ =
        Polynomial.aeval z (Differential.implicitDeriv w V.denom) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd V.denom
  rw [evalAtTranscendental_num_div_denom,
    evalAtTranscendental_num_div_denom] at heq
  rw [Derivation.leibniz_div, Derivation.leibniz_div] at heq
  simp only [smul_eq_mul] at heq
  rw [hUnumDeriv, hUdenDeriv, hVnumDeriv, hVdenDeriv] at heq
  simp only [map_mul, map_sub, map_pow, aeval_C]
  field_simp [hUden, hVden] at heq ⊢
  linear_combination heq

/-- Evaluation-level form of rigidity transport. -/
theorem evalAtTranscendental_integralSlopeRigidity_exponential
    (beta : F) (hrigid : Proposition31II.IntegralSlopeRigidity beta)
    (b : F) (z : E) (hz : Transcendental F z)
    (hzd : z′ = algebraMap F E b′ * z)
    (a : F) (ha : a′ = 0) (U V : RatFunc F) (hU0 : U ≠ 0)
    (heq : (evalAtTranscendental z hz U)′ =
      (algebraMap F E (a * (beta′ / beta)) +
        (evalAtTranscendental z hz V)′) *
          evalAtTranscendental z hz U) :
    ∃ m : Int, a = (m : F) := by
  apply rationalFunction_integralSlopeRigidity_exponential
    beta hrigid b z hz hzd a ha
    (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
    U.isCoprime_num_denom V.isCoprime_num_denom
  have hzdPolynomial :
      z′ = Polynomial.aeval z (C b′ * X) := by
    simpa using hzd
  exact clearedShiftedEquation_of_evalAtTranscendental
    z hz (C b′ * X) hzdPolynomial (a * (beta′ / beta)) U V heq

/-! ## Transport to an actual differential simple extension -/

/-- Integral-slope rigidity is preserved by a transcendental exponential
simple adjunction with no new constants.

This is the tower-facing form: `G` is a differential intermediate field
whose underlying field is exactly `F(z)`.  The base whose rigidity is being
transported is the image of `beta`; the exponential may be governed by an
unrelated element `b`. -/
theorem differentialSimpleExtension_integralSlopeRigidity_exponential
    (G : DifferentialIntermediateField F E)
    (beta : F) (hrigid : Proposition31II.IntegralSlopeRigidity beta)
    (b : F) (z : E) (hz : Transcendental F z)
    (hzd : z′ = algebraMap F E b′ * z)
    (hG : G.toIntermediateField = IntermediateField.adjoin F {z}) :
    Proposition31II.IntegralSlopeRigidity (algebraMap F G beta) := by
  intro a u v ha hu0 hu
  obtain ⟨a₀, ha₀⟩ := mem_range_of_deriv_eq_zero F ha
  have ha₀zero : a₀′ = 0 := by
    apply (algebraMap F G).injective
    simpa only [deriv_algebraMap, ha, map_zero] using
      congrArg (fun x : G ↦ x′) ha₀
  let e := RatFunc.algEquivOfTranscendental z hz
  let uI : IntermediateField.adjoin F {z} :=
    ⟨(u : E), by
      rw [← hG]
      exact u.2⟩
  let vI : IntermediateField.adjoin F {z} :=
    ⟨(v : E), by
      rw [← hG]
      exact v.2⟩
  let U : RatFunc F := e.symm uI
  let V : RatFunc F := e.symm vI
  have hU : evalAtTranscendental z hz U = (u : E) := by
    simp [evalAtTranscendental, U, uI, e]
  have hV : evalAtTranscendental z hz V = (v : E) := by
    simp [evalAtTranscendental, V, vI, e]
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hu0
    apply Subtype.ext
    simpa using (show (u : E) = 0 by rw [← hU, hzero, map_zero])
  have haE : (a : E) = algebraMap F E a₀ := by
    rw [← DifferentialIntermediateField.coe_algebraMap_base G a₀]
    exact congrArg (fun y : G ↦ (y : E)) ha₀.symm
  have hbetaE : ((algebraMap F G beta : G) : E) =
      algebraMap F E beta :=
    DifferentialIntermediateField.coe_algebraMap_base G beta
  have hbetaDerivE : (((algebraMap F G beta : G)′ : G) : E) =
      algebraMap F E beta′ := by
    rw [DifferentialIntermediateField.coe_deriv, hbetaE, deriv_algebraMap]
  have coeMul (p q : G) : (((p * q : G) : E)) = (p : E) * (q : E) := rfl
  have coeAdd (p q : G) : (((p + q : G) : E)) = (p : E) + (q : E) := rfl
  have coeDiv (p q : G) : (((p / q : G) : E)) = (p : E) / (q : E) := rfl
  have huE := congrArg (fun y : G ↦ (y : E)) hu
  simp only [DifferentialIntermediateField.coe_deriv, coeMul, coeAdd,
    coeDiv] at huE
  have heval : (evalAtTranscendental z hz U)′ =
      (algebraMap F E (a₀ * (beta′ / beta)) +
        (evalAtTranscendental z hz V)′) *
          evalAtTranscendental z hz U := by
    rw [hU, hV, map_mul, map_div₀]
    rw [← haE, ← hbetaDerivE, ← hbetaE]
    exact huE
  obtain ⟨m, hm⟩ :=
    evalAtTranscendental_integralSlopeRigidity_exponential
      beta hrigid b z hz hzd a₀ ha₀zero U V hU0 heval
  refine ⟨m, ?_⟩
  rw [← ha₀, hm]
  exact map_intCast (algebraMap F G) m

end ExponentialExtension

/-! ## Why primitive transport needs a stronger invariant -/

/-- A logarithmic primitive for the very base under consideration destroys
`IntegralSlopeRigidity`: `u = 1` and `v = -a*z` cancel any prescribed
constant slope.  Thus no primitive-adjunction analogue of the exponential
transport theorem follows from no-new-constants alone. -/
theorem not_integralSlopeRigidity_of_logarithmicPrimitive
    (beta z a : F) (ha : a′ = 0)
    (hzd : z′ = beta′ / beta)
    (haNotInt : ¬ ∃ m : Int, a = (m : F)) :
    ¬ Proposition31II.IntegralSlopeRigidity beta := by
  intro hr
  have heq : (1 : F)′ =
      (a * (beta′ / beta) + (-a * z)′) * (1 : F) := by
    simp only [Derivation.leibniz, map_neg, ha, hzd, smul_eq_mul]
    simp
  exact haNotInt (hr a 1 (-a * z) ha one_ne_zero heq)

end

end Natfunbasis.Wilkie.IntegralSlopeTransport
