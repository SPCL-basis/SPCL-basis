import Natfunbasis.WilkieProposition31
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The pole step in Wilkie's Proposition 3.1(i)

This file continues `WilkieProposition31`.  It develops the local
prime-factor calculation needed to treat an arbitrary rational primitive,
rather than assuming from the outset that its derivative belongs to the base
field.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.Proposition31

noncomputable section

variable {F : Type*} [Field F]

/-- `HasExactOrder h n f` says that `h^n` is the exact power of `h`
dividing `f`.  This factorization-oriented formulation is convenient for
local pole calculations and avoids choosing a normalization of `h`. -/
def HasExactOrder (h : F[X]) (n : Nat) (f : F[X]) : Prop :=
  ∃ u, f = h ^ n * u ∧ ¬ h ∣ u

namespace HasExactOrder

variable {h : F[X]} {m n : Nat} {f g : F[X]}

theorem ne_zero (hh : h ≠ 0) (hf : HasExactOrder h n f) : f ≠ 0 := by
  obtain ⟨u, rfl, hu⟩ := hf
  exact mul_ne_zero (pow_ne_zero _ hh)
    fun hu0 ↦ hu (hu0 ▸ dvd_zero h)

theorem dvd (hf : HasExactOrder h n f) : h ^ n ∣ f := by
  obtain ⟨u, rfl, -⟩ := hf
  exact dvd_mul_right _ _

theorem zero (hf : ¬ h ∣ f) : HasExactOrder h 0 f := by
  exact ⟨f, by simp, hf⟩

theorem not_dvd_succ (hh : h ≠ 0) (hf : HasExactOrder h n f) :
    ¬ h ^ (n + 1) ∣ f := by
  obtain ⟨u, hfu, hu⟩ := hf
  rintro ⟨v, hv⟩
  have heq : u = h * v := by
    apply mul_left_cancel₀ (pow_ne_zero n hh)
    calc
      h ^ n * u = f := hfu.symm
      _ = h ^ (n + 1) * v := hv
      _ = h ^ n * (h * v) := by rw [pow_succ, mul_assoc]
  exact hu ⟨v, heq⟩

theorem unique (hh : h ≠ 0) (hf : HasExactOrder h m f)
    (hg : HasExactOrder h n f) : m = n := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact False.elim <| hf.not_dvd_succ hh <|
      (pow_dvd_pow h hmn).trans hg.dvd
  · exact hmn
  · exact False.elim <| hg.not_dvd_succ hh <|
      (pow_dvd_pow h hnm).trans hf.dvd

theorem mul (hh : Prime h) (hf : HasExactOrder h m f)
    (hg : HasExactOrder h n g) : HasExactOrder h (m + n) (f * g) := by
  obtain ⟨u, rfl, hu⟩ := hf
  obtain ⟨v, rfl, hv⟩ := hg
  refine ⟨u * v, ?_, ?_⟩
  · rw [pow_add]
    ring
  · exact fun hd ↦ (hh.dvd_mul.mp hd).elim hu hv

theorem sub_of_dvd_succ (hf : HasExactOrder h n f)
    (hg : h ^ (n + 1) ∣ g) : HasExactOrder h n (f - g) := by
  obtain ⟨u, hfu, hu⟩ := hf
  obtain ⟨v, hgv⟩ := hg
  refine ⟨u - h * v, ?_, ?_⟩
  · rw [hfu, hgv, pow_succ']
    ring
  · intro hd
    apply hu
    have hhv : h ∣ h * v := dvd_mul_right _ _
    simpa only [sub_add_cancel] using dvd_add hd hhv

theorem neg (hf : HasExactOrder h n f) : HasExactOrder h n (-f) := by
  obtain ⟨u, rfl, hu⟩ := hf
  refine ⟨-u, by ring, ?_⟩
  simpa only [dvd_neg] using hu

theorem sub_of_dvd_succ_right (hg : HasExactOrder h n g)
    (hf : h ^ (n + 1) ∣ f) : HasExactOrder h n (f - g) := by
  have := sub_of_dvd_succ (f := g) (g := f) hg hf
  simpa only [neg_sub] using this.neg

end HasExactOrder

/-- Leibniz expansion after extracting a positive power of a prime factor. -/
theorem deriv_pow_mul_factor (D : Derivation Int F[X] F[X])
    (h u : F[X]) {n : Nat} (hn : 0 < n) :
    D (h ^ n * u) = h ^ (n - 1) *
      ((n : F[X]) * D h * u + h * D u) := by
  rw [D.leibniz, D.leibniz_pow]
  simp only [nsmul_eq_mul]
  rw [show h ^ n = h ^ (n - 1) * h by
    nth_rewrite 1 [show n = (n - 1) + 1 by omega]
    rw [pow_succ]]
  ring

/-- The residual factor in `deriv_pow_mul_factor` is not divisible by `h`
when `h` does not divide either the cofactor or its own derivative. -/
theorem not_dvd_deriv_pow_mul_residual (D : Derivation Int F[X] F[X])
    [CharZero F]
    {h u : F[X]} (hh : Prime h) {n : Nat} (hn : 0 < n)
    (hDh : ¬ h ∣ D h) (hu : ¬ h ∣ u) :
    ¬ h ∣ (n : F[X]) * D h * u + h * D u := by
  intro hd
  have hfirst : h ∣ (n : F[X]) * D h * u := by
    have hsecond : h ∣ h * D u := dvd_mul_right _ _
    simpa only [add_sub_cancel_right] using dvd_sub hd hsecond
  rcases hh.dvd_mul.mp hfirst with hleft | hu'
  · rcases hh.dvd_mul.mp hleft with hncast | hDh'
    · have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hnunit : IsUnit (n : F[X]) := by
        rw [← C_eq_natCast]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hnF)
      exact hh.not_unit (isUnit_of_dvd_unit hncast hnunit)
    · exact hDh hDh'
  · exact hu hu'

/-- Differentiation lowers the exact order at a non-invariant prime by one. -/
theorem hasExactOrder_deriv_pow_mul (D : Derivation Int F[X] F[X])
    [CharZero F]
    {h u : F[X]} (hh : Prime h) {n : Nat} (hn : 0 < n)
    (hDh : ¬ h ∣ D h) (hu : ¬ h ∣ u) :
    HasExactOrder h (n - 1) (D (h ^ n * u)) := by
  refine ⟨(n : F[X]) * D h * u + h * D u,
    deriv_pow_mul_factor D h u hn, ?_⟩
  exact not_dvd_deriv_pow_mul_residual D hh hn hDh hu

/-- Every nonzero polynomial has an exact order at an irreducible factor. -/
theorem exists_hasExactOrder (h : F[X]) (hh : Irreducible h)
    {f : F[X]} (hf : f ≠ 0) : ∃ n, HasExactOrder h n f := by
  obtain ⟨n, u, hu, hfu⟩ := WfDvdMonoid.max_power_factor hf hh
  exact ⟨n, u, hfu, hu⟩

/-- A divisor has positive exact order. -/
theorem HasExactOrder.pos_of_dvd {h f : F[X]} {n : Nat}
    (hf : HasExactOrder h n f)
    (hdiv : h ∣ f) : 0 < n := by
  obtain ⟨u, hfu, hu⟩ := hf
  cases n with
  | zero =>
      simp only [pow_zero, one_mul] at hfu
      exact False.elim (hu (hfu ▸ hdiv))
  | succ n => exact Nat.succ_pos n

theorem HasExactOrder.dvd_base_of_pos {h f : F[X]} {n : Nat}
    (hf : HasExactOrder h n f) (hn : 0 < n) : h ∣ f := by
  have hpow : h ^ 1 ∣ h ^ n := pow_dvd_pow h hn
  simpa only [pow_one] using hpow.trans hf.dvd

/-- Differentiation lowers a positive exact order at a non-invariant prime. -/
theorem HasExactOrder.deriv {h f : F[X]} {n : Nat}
    [CharZero F] (D : Derivation Int F[X] F[X])
    (hh : Prime h) (hDh : ¬ h ∣ D h) (hf : HasExactOrder h n f)
    (hn : 0 < n) : HasExactOrder h (n - 1) (D f) := by
  obtain ⟨u, hfu, hu⟩ := hf
  rw [hfu]
  exact hasExactOrder_deriv_pow_mul D hh hn hDh hu

/-- If the numerator has positive order and the denominator has order zero,
the logarithmic cross numerator has order one less than the numerator. -/
theorem hasExactOrder_logCross_of_left
    [CharZero F] (D : Derivation Int F[X] F[X]) (hh : Prime h)
    (hDh : ¬ h ∣ D h)
    {p q : F[X]} {i : Nat} (hi : 0 < i)
    (hp : HasExactOrder h i p) (hq : HasExactOrder h 0 q) :
    HasExactOrder h (i - 1) (D p * q - p * D q) := by
  have hDp := hp.deriv D hh hDh hi
  have hfirst : HasExactOrder h (i - 1) (D p * q) := by
    simpa using hDp.mul hh hq
  apply hfirst.sub_of_dvd_succ
  have hpi : h ^ i ∣ p := hp.dvd
  have htarget : h ^ i ∣ p * D q := dvd_mul_of_dvd_left hpi _
  simpa [show i - 1 + 1 = i by omega] using htarget

/-- Symmetric denominator case for the logarithmic cross numerator. -/
theorem hasExactOrder_logCross_of_right
    [CharZero F] (D : Derivation Int F[X] F[X]) (hh : Prime h)
    (hDh : ¬ h ∣ D h)
    {p q : F[X]} {j : Nat} (hj : 0 < j)
    (hp : HasExactOrder h 0 p) (hq : HasExactOrder h j q) :
    HasExactOrder h (j - 1) (D p * q - p * D q) := by
  have hDq := hq.deriv D hh hDh hj
  have hsecond : HasExactOrder h (j - 1) (p * D q) := by
    simpa [Nat.zero_add] using hp.mul hh hDq
  apply hsecond.sub_of_dvd_succ_right
  have hqj : h ^ j ∣ q := hq.dvd
  have htarget : h ^ j ∣ D p * q := dvd_mul_of_dvd_right hqj _
  simpa [show j - 1 + 1 = j by omega] using htarget

/-- If `r/s` is reduced and `s` has positive order at a non-invariant prime,
then the derivative cross numerator has exact order one less than `s`. -/
theorem hasExactOrder_derivCross_of_denominator
    [CharZero F] (D : Derivation Int F[X] F[X]) (hh : Prime h)
    (hDh : ¬ h ∣ D h)
    {r s : F[X]} {e : Nat} (he : 0 < e)
    (hr : HasExactOrder h 0 r) (hs : HasExactOrder h e s) :
    HasExactOrder h (e - 1) (D r * s - r * D s) := by
  have hDs := hs.deriv D hh hDh he
  have hsecond : HasExactOrder h (e - 1) (r * D s) := by
    simpa [Nat.zero_add] using hr.mul hh hDs
  apply hsecond.sub_of_dvd_succ_right
  have hse : h ^ e ∣ s := hs.dvd
  have htarget : h ^ e ∣ D r * s := dvd_mul_of_dvd_right hse _
  simpa [show e - 1 + 1 = e by omega] using htarget

/-- Local pole-order lemma.  In a differential rational-function equation,
every irreducible factor of the reduced denominator of the primitive must be
invariant under the derivation. -/
theorem irreducible_dvd_deriv_of_rational_logEquation
    [CharZero F] (D : Derivation Int F[X] F[X])
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (D p * q - p * D q) * s ^ 2 =
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
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    exact hh.not_isUnit <|
      hrs.isUnit_of_dvd' (hl.dvd_base_of_pos hlpos) hdivs
  have hr : HasExactOrder h 0 r := by simpa [hlzero] using hl
  have hB : HasExactOrder h (e - 1) (D r * s - r * D s) :=
    hasExactOrder_derivCross_of_denominator D hhprime hDh hepos hr hs
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
  let A := D p * q - p * D q
  let B := D r * s - r * D s
  have hB' : HasExactOrder h (e - 1) B := hB
  have hright : HasExactOrder h ((e - 1 + i) + j) (B * p * q) :=
    (hB'.mul hhprime hi).mul hhprime hj
  have heq' : A * s ^ 2 = B * p * q := heq
  rcases hij with hi0 | hj0
  · have hi' : HasExactOrder h 0 p := by simpa [hi0] using hi
    by_cases hjzero : j = 0
    · have hj' : HasExactOrder h 0 q := by simpa [hjzero] using hj
      by_cases hA0 : A = 0
      · exact hright.ne_zero hh.ne_zero <| by
          rw [← heq', hA0]
          simp
      · obtain ⟨a, hA⟩ := exists_hasExactOrder h hh hA0
        have hleft : HasExactOrder h (a + (e + e)) (A * s ^ 2) :=
          hA.mul hhprime hs2
        have hright' :
            HasExactOrder h ((e - 1 + i) + j) (A * s ^ 2) := by
          rw [heq']
          exact hright
        have hord := hleft.unique hh.ne_zero hright'
        omega
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
      have hA : HasExactOrder h (j - 1) A :=
        hasExactOrder_logCross_of_right D hhprime hDh hjpos hi' hj
      have hleft : HasExactOrder h ((j - 1) + (e + e)) (A * s ^ 2) :=
        hA.mul hhprime hs2
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
      -- This branch was already handled by the left disjunct.
      subst i
      have hA0or : A = 0 ∨ A ≠ 0 := eq_or_ne A 0
      rcases hA0or with hA0 | hA0
      · exact hright.ne_zero hh.ne_zero <| by
          rw [← heq', hA0]
          simp
      · obtain ⟨a, hA⟩ := exists_hasExactOrder h hh hA0
        have hleft := hA.mul hhprime hs2
        have hright' :
            HasExactOrder h ((e - 1 + 0) + j) (A * s ^ 2) := by
          rw [heq']
          simpa using hright
        have hord := hleft.unique hh.ne_zero hright'
        omega
    have hA : HasExactOrder h (i - 1) A :=
      hasExactOrder_logCross_of_left D hhprime hDh hipos hi hj'
    have hleft : HasExactOrder h ((i - 1) + (e + e)) (A * s ^ 2) :=
      hA.mul hhprime hs2
    have hright' :
        HasExactOrder h ((e - 1 + i) + j) (A * s ^ 2) := by
      rw [heq']
      exact hright
    have hord := hleft.unique hh.ne_zero hright'
    omega

/-- Under integer nonresonance, the only irreducible polynomials invariant
under the Euler derivation `T' = cT` are associates of `T`. -/
theorem irreducible_associated_X_of_dvd_implicitDeriv
    [Differential F] {c : F} (hres : NoIntegerResonance c) {h : F[X]}
    (hh : Irreducible h)
    (hdiv : h ∣ Differential.implicitDeriv (C c * X) h) :
    Associated h X := by
  have hdiv' : h ∣
      Differential.implicitDeriv (C c * X) h - C 0 * h := by
    simpa using hdiv
  obtain ⟨a, ha⟩ :=
    exists_implicitDeriv_eigenvalue_of_dvd_sub c 0 hdiv'
  obtain ⟨n, u, hu0, hhu, -⟩ :=
    implicitDeriv_eigen_classification hres hh.ne_zero ha
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [monomial_zero_left] at hhu
    exact hh.not_isUnit <| hhu.symm ▸
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu0)
  have hXdiv : X ∣ h := by
    refine ⟨C u * X ^ (n - 1), ?_⟩
    rw [hhu, ← C_mul_X_pow_eq_monomial]
    nth_rewrite 1 [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    ring
  exact (irreducible_X.associated_of_dvd hh hXdiv).symm

/-- Finite-pole conclusion: the reduced denominator of the primitive is,
up to a unit, a power of `T`. -/
theorem denominator_associated_X_pow_of_rational_logEquation
    [CharZero F] [Differential F]
    {c : F} (hres : NoIntegerResonance c)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) * s ^ 2 =
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
    irreducible_dvd_deriv_of_rational_logEquation
      (Differential.implicitDeriv (C c * X)) hp0 hq0 hr0 hs0 hpq hrs
      heq hhirr hhdivs
  have hassoc : Associated h X :=
    irreducible_associated_X_of_dvd_implicitDeriv hres hhirr hhdivD
  exact hassoc.eq_of_normalized
    (UniqueFactorizationMonoid.normalize_normalized_factor h hhmem)
    monic_X.normalize_eq_self

/-- Factoring a power of `T` commutes with the Euler derivation, with the
expected logarithmic correction on the cofactor. -/
theorem implicitDeriv_X_pow_mul [Differential F]
    (c : F) (u : F[X]) (n : Nat) :
    Differential.implicitDeriv (C c * X) (X ^ n * u) =
      X ^ n *
        (Differential.implicitDeriv (C c * X) u + C ((n : F) * c) * u) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Derivation.leibniz, Derivation.leibniz_pow,
        Differential.implicitDeriv_X]
      simp only [nsmul_eq_mul]
      push_cast
      rw [pow_succ]
      simp only [smul_eq_mul, map_add, map_mul, map_one]
      rw [C_eq_natCast]
      ring

/-- An associate of `h^n` has exact `h`-order `n`. -/
theorem hasExactOrder_of_associated_pow {h s : F[X]} (hh : Prime h)
    {n : Nat} (hs : Associated (h ^ n) s) : HasExactOrder h n s := by
  obtain ⟨u, hu⟩ := hs
  refine ⟨(u : F[X]), hu.symm, ?_⟩
  intro hdiv
  exact hh.not_unit (isUnit_of_dvd_unit hdiv u.isUnit)

/-- At `T`, nonresonance replaces the usual one-order drop: if a reduced
primitive has denominator of exact positive `T`-order `e`, then its derivative
cross numerator has exact order `e`. -/
theorem hasExactOrder_X_derivCross_of_denominator [Differential F]
    {c : F} (hres : NoIntegerResonance c)
    {r s : F[X]} {e : Nat} (he : 0 < e)
    (hr : HasExactOrder X 0 r) (hs : HasExactOrder X e s) :
    HasExactOrder X e
      (Differential.implicitDeriv (C c * X) r * s -
        r * Differential.implicitDeriv (C c * X) s) := by
  obtain ⟨r₀, hrr₀, hr₀⟩ := hr
  simp only [pow_zero, one_mul] at hrr₀
  subst r
  obtain ⟨u, hsu, hu⟩ := hs
  rw [hsu]
  let D := Differential.implicitDeriv (C c * X)
  let residual := D r₀ * u -
    r₀ * (D u + C ((e : F) * c) * u)
  refine ⟨residual, ?_, ?_⟩
  · dsimp [residual, D]
    rw [implicitDeriv_X_pow_mul]
    ring
  · rw [Polynomial.X_dvd_iff]
    intro hcoeff
    have hrcoeff : r₀.coeff 0 ≠ 0 := by
      intro hz
      exact hr₀ (Polynomial.X_dvd_iff.mpr hz)
    have hucoeff : u.coeff 0 ≠ 0 := by
      intro hz
      exact hu (Polynomial.X_dvd_iff.mpr hz)
    have hscalar :
        (r₀.coeff 0)′ * u.coeff 0 -
            r₀.coeff 0 * ((u.coeff 0)′ +
              (e : F) * c * u.coeff 0) = 0 := by
      simpa [residual, D, coeff_implicitDeriv_euler] using hcoeff
    let w : F := r₀.coeff 0 / u.coeff 0
    have hw0 : w ≠ 0 := div_ne_zero hrcoeff hucoeff
    have hw : w′ = (e : F) * c * w := by
      dsimp [w]
      rw [Derivation.leibniz_div (Differential.deriv : Derivation Int F F)]
      simp only [smul_eq_mul]
      field_simp [hucoeff]
      linear_combination hscalar
    exact hres w hw0 (e : Int) (by exact_mod_cast he.ne') (by simpa using hw)

/-- The Euler derivation preserves divisibility by every power of `T`. -/
theorem X_pow_dvd_implicitDeriv_euler [Differential F]
    (c : F) {p : F[X]} {n : Nat} (hp : X ^ n ∣ p) :
    X ^ n ∣ Differential.implicitDeriv (C c * X) p := by
  rw [Polynomial.X_pow_dvd_iff] at hp ⊢
  intro d hd
  rw [coeff_implicitDeriv_euler, hp d hd]
  simp

/-- The possible power of `T` left by the finite-pole argument is also
excluded by nonresonance.  Thus the reduced denominator of the primitive is
a unit. -/
theorem denominator_isUnit_of_rational_logEquation
    [CharZero F] [Differential F]
    {c : F} (hres : NoIntegerResonance c)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) * s ^ 2 =
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q) :
    IsUnit s := by
  obtain ⟨e, hse⟩ :=
    denominator_associated_X_pow_of_rational_logEquation
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
    have hA : X ^ (i + j) ∣
        Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q :=
      dvd_sub hfirst hsecond
    have hs2 : HasExactOrder X (e + e) (s ^ 2) := by
      simpa [pow_two] using hs.mul irreducible_X.prime hs
    have hleft : X ^ ((i + j) + (e + e)) ∣
        (Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) * s ^ 2 := by
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

/-- Under nonresonance, the Euler derivation preserves the degree of every
positive-degree polynomial.  This is the pole-at-infinity analogue of the
constant-coefficient argument at `T`. -/
theorem natDegree_implicitDeriv_euler_eq_of_pos
    [Differential F] {c : F} (hres : NoIntegerResonance c)
    {p : F[X]} (hpdeg : 0 < p.natDegree) :
    (Differential.implicitDeriv (C c * X) p).natDegree = p.natDegree := by
  apply le_antisymm (natDegree_implicitDeriv_euler_le c p)
  apply Polynomial.le_natDegree_of_ne_zero
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hpdeg
  have hlead : p.coeff p.natDegree ≠ 0 := by
    simpa only [Polynomial.leadingCoeff] using
      (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  intro hDlead
  have heq :
      (p.coeff p.natDegree)′ =
        ((-(p.natDegree : Int) : Int) : F) * c *
          p.coeff p.natDegree := by
    rw [coeff_implicitDeriv_euler] at hDlead
    push_cast
    linear_combination hDlead
  exact hres (p.coeff p.natDegree) hlead (-(p.natDegree : Int))
    (neg_ne_zero.mpr (by exact_mod_cast hpdeg.ne')) heq

/-- A polynomial primitive of a rational logarithmic derivative is constant.
The proof compares degrees at infinity. -/
theorem eq_C_of_logCross_eq_implicitDeriv_mul
    [Differential F] {c : F} (hres : NoIntegerResonance c)
    {p q y : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (heq :
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        Differential.implicitDeriv (C c * X) y * p * q) :
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
    have hAdeg :
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
        (Differential.implicitDeriv (C c * X) y * p * q).natDegree =
          y.natDegree + p.natDegree + q.natDegree := by
      rw [Polynomial.natDegree_mul (mul_ne_zero hDy0 hp0) hq0,
        Polynomial.natDegree_mul hDy0 hp0, hDydeg]
    have hdegrees := congrArg Polynomial.natDegree heq
    rw [hrightdeg] at hdegrees
    omega
  exact ⟨y.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hydeg⟩

/-- Full pole reduction for a nonzero reduced primitive: an arbitrary
rational primitive occurring in the logarithmic equation belongs to the base
field.  The second conjunct records the resulting cleared equation. -/
theorem rational_primitive_eq_base_of_logEquation
    [CharZero F] [Differential F]
    {c : F} (hres : NoIntegerResonance c)
    {p q r s : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q) * s ^ 2 =
        (Differential.implicitDeriv (C c * X) r * s -
          r * Differential.implicitDeriv (C c * X) s) * p * q) :
    ∃ γ : F,
      algebraMap F[X] (RatFunc F) r /
          algebraMap F[X] (RatFunc F) s = RatFunc.C γ ∧
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        C γ′ * p * q := by
  have hsunit : IsUnit s :=
    denominator_isUnit_of_rational_logEquation
      hres hp0 hq0 hr0 hs0 hpq hrs heq
  obtain ⟨b, hbunit, hbs⟩ := Polynomial.isUnit_iff.mp hsunit
  have hb0 : b ≠ 0 := isUnit_iff_ne_zero.mp hbunit
  let D := Differential.implicitDeriv (C c * X)
  let A := D p * q - p * D q
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
  have hbinv : (b⁻¹)′ = -b⁻¹ ^ 2 * b′ := by
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
    linear_combination -(D r) * hCcancel
  have hpoly : D p * q - p * D q = D y * p * q := by
    rw [hDy]
    exact hscaled
  obtain ⟨γ, hy⟩ :=
    eq_C_of_logCross_eq_implicitDeriv_mul hres hp0 hq0 hpoly
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
  · dsimp [A, D] at hpoly
    rw [hy, Differential.implicitDeriv_C] at hpoly
    exact hpoly

/-- Wilkie's Proposition 3.1(i), in exact rational-function coordinates.

The reduced fractions `p/q` and `r/s` represent the source's elements
`X,Y ∈ K(x)`.  The displayed hypothesis is precisely the
cleared-denominator form of `X' = Y'X` for the derivation determined by
`x' = β'x`.  The conclusion reads

`X = x^k w`, `Y = kβ + v`, and `w' = v'w`.

Only the direction of "same constants" used in the proof is assumed:
`Differential.ContainConstants K L` says that every constant of `L` comes
from `K`.
-/
theorem rationalFunction_proposition31_i
    {K L : Type*} [Field K] [CharZero K] [Field L]
    [Differential K] [Differential L] [Algebra K L]
    [DifferentialAlgebra K L] [Differential.ContainConstants K L]
    (β : K) (x : L) (hx : Transcendental K x)
    (hxd : x′ = algebraMap K L β′ * x)
    {p q r s : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (heq :
      (Differential.implicitDeriv (C β′ * X) p * q -
          p * Differential.implicitDeriv (C β′ * X) q) * s ^ 2 =
        (Differential.implicitDeriv (C β′ * X) r * s -
          r * Differential.implicitDeriv (C β′ * X) s) * p * q) :
    ∃ k : Int, ∃ w v : K, w ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q =
        RatFunc.C w * RatFunc.X ^ k ∧
      algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) s =
        RatFunc.C ((k : K) * β + v) ∧
      w′ = v′ * w := by
  have hres : NoIntegerResonance (β′) :=
    noIntegerResonance_deriv_of_transcendental_solution β x hx hxd
  by_cases hr0 : r = 0
  · have hA :
        Differential.implicitDeriv (C β′ * X) p * q -
            p * Differential.implicitDeriv (C β′ * X) q = 0 := by
      have hAsq :
          (Differential.implicitDeriv (C β′ * X) p * q -
              p * Differential.implicitDeriv (C β′ * X) q) * s ^ 2 = 0 := by
        simpa [hr0] using heq
      exact (mul_eq_zero.mp hAsq).resolve_right (pow_ne_zero 2 hs0)
    have hcross :
        Differential.implicitDeriv (C β′ * X) p * q -
            p * Differential.implicitDeriv (C β′ * X) q =
          C (0 : K)′ * p * q := by
      simpa using hA
    obtain ⟨k, w, v, hw0, hX, hzero, hw⟩ :=
      ratFunc_classification_of_crossEquation_of_base_primitive
        β 0 x hx hxd hp0 hq0 hpq hcross
    refine ⟨k, w, v, hw0, hX, ?_, hw⟩
    rw [hr0, map_zero, zero_div, ← hzero]
    simp
  · obtain ⟨γ, hY, hcross⟩ :=
      rational_primitive_eq_base_of_logEquation
        hres hp0 hq0 hr0 hs0 hpq hrs heq
    obtain ⟨k, w, v, hw0, hX, hγ, hw⟩ :=
      ratFunc_classification_of_crossEquation_of_base_primitive
        β γ x hx hxd hp0 hq0 hpq hcross
    exact ⟨k, w, v, hw0, hX, hY.trans (congrArg RatFunc.C hγ), hw⟩

end

end Natfunbasis.Wilkie.Proposition31
