import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# A rational-function core of Wilkie's Proposition 3.1(i)

Wilkie's Proposition 3.1(i) considers differential fields `F ⊆ G` with the
same constants, an element `α` transcendental over `F`, and `β ∈ F` such
that `α' = β' α`.  Its full conclusion says that, for `X,Y ∈ F(α)`
satisfying `X' = Y' X`, there are `m ∈ ℤ` and `u,v ∈ F` such that

`X = α^m u`, `Y = mβ + v`, and `u' = v'u`.

This file proves the algebraic eigenfunction part of that statement.  More
precisely, if a reduced rational function `p/q` has logarithmic derivative
`a ∈ F` for the derivation determined by `T' = β'T`, then `p/q` is
`w T^m`, and `w' = (a - mβ')w`.  The hypothesis that the extension has no
new constants is used to derive the required nonresonance condition from the
transcendence of `α`.

The remaining part of Wilkie's proposition is the pole/principal-part
argument proving, from arbitrary `Y ∈ F(α)`, that `Y-mβ` lies in `F`.
That assertion is intentionally not postulated here.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.Proposition31

noncomputable section

variable {F : Type*} [Field F] [Differential F]

/-- Coefficient formula for the polynomial derivation determined by
`T' = cT`. -/
lemma coeff_implicitDeriv_euler (c : F) (p : F[X]) (n : Nat) :
    (Differential.implicitDeriv (C c * X) p).coeff n =
      (p.coeff n)′ + (n : F) * c * p.coeff n := by
  change (p.coeff n)′ + (C c * X * derivative p).coeff n = _
  cases n with
  | zero => simp
  | succ n =>
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast
      ring

/-- The Euler-type polynomial derivation does not increase degree. -/
theorem natDegree_implicitDeriv_euler_le (c : F) (p : F[X]) :
    (Differential.implicitDeriv (C c * X) p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_implicitDeriv_euler]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp

/-- A polynomial dividing its Euler derivative minus a scalar multiple of
itself is an eigenvector for the Euler derivation. -/
theorem exists_implicitDeriv_eigenvalue_of_dvd_sub
    (c a : F) {p : F[X]}
    (hdiv : p ∣ Differential.implicitDeriv (C c * X) p - C a * p) :
    ∃ s : F, Differential.implicitDeriv (C c * X) p = C s * p := by
  let r := Differential.implicitDeriv (C c * X) p - C a * p
  have hrdeg : r.natDegree ≤ p.natDegree := by
    exact (Polynomial.natDegree_sub_le _ _).trans <|
      max_le (natDegree_implicitDeriv_euler_le c p)
        (Polynomial.natDegree_C_mul_le a p)
  by_cases hr0 : r = 0
  · refine ⟨a, ?_⟩
    exact sub_eq_zero.mp hr0
  · have hassoc : Associated p r :=
      Polynomial.associated_of_dvd_of_natDegree_le hdiv hr0 hrdeg
    obtain ⟨z, hz⟩ := hassoc
    obtain ⟨s, _hsunit, hs⟩ := Polynomial.isUnit_iff.mp z.isUnit
    refine ⟨a + s, ?_⟩
    have hr : r = p * C s := by
      rw [hs]
      exact hz.symm
    dsimp [r] at hr
    rw [map_add]
    linear_combination hr

/-- In a reduced logarithmic-derivative equation, the numerator and
denominator are separately eigenpolynomials. -/
theorem eigenPolynomials_of_isCoprime_crossEquation
    (c a : F) {p q : F[X]} (hp0 : p ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        C a * p * q) :
    ∃ sp sq : F,
      Differential.implicitDeriv (C c * X) p = C sp * p ∧
      Differential.implicitDeriv (C c * X) q = C sq * q ∧
      sp - sq = a := by
  have hfactor :
      (Differential.implicitDeriv (C c * X) p - C a * p) * q =
        p * Differential.implicitDeriv (C c * X) q := by
    linear_combination hcross
  have hdivprod : p ∣
      (Differential.implicitDeriv (C c * X) p - C a * p) * q := by
    exact ⟨Differential.implicitDeriv (C c * X) q, hfactor⟩
  have hdiv : p ∣ Differential.implicitDeriv (C c * X) p - C a * p :=
    hpq.dvd_of_dvd_mul_right hdivprod
  obtain ⟨sp, hp⟩ := exists_implicitDeriv_eigenvalue_of_dvd_sub c a hdiv
  have hqmul : p *
      (Differential.implicitDeriv (C c * X) q - C (sp - a) * q) = 0 := by
    rw [map_sub]
    rw [hp] at hcross
    linear_combination -hcross
  have hqzero :
      Differential.implicitDeriv (C c * X) q - C (sp - a) * q = 0 :=
    (mul_eq_zero.mp hqmul).resolve_left hp0
  refine ⟨sp, sp - a, hp, sub_eq_zero.mp hqzero, ?_⟩
  ring

/-- No nonzero element has logarithmic derivative a nonzero integral
multiple of `c`. -/
def NoIntegerResonance (c : F) : Prop :=
  ∀ (u : F), u ≠ 0 → ∀ n : Int, n ≠ 0 →
    u′ ≠ (n : F) * c * u

/-- Under nonresonance, an Euler eigenpolynomial has at most one nonzero
coefficient. -/
theorem support_card_le_one_of_implicitDeriv_eigen
    {c a : F} (hres : NoIntegerResonance c) (p : F[X])
    (hp : Differential.implicitDeriv (C c * X) p = C a * p) :
    p.support.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hij
  have hpi : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hpj : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hieq : (p.coeff i)′ + (i : F) * c * p.coeff i =
      a * p.coeff i := by
    have h := congrArg (fun q : F[X] ↦ q.coeff i) hp
    rw [coeff_implicitDeriv_euler, Polynomial.coeff_C_mul] at h
    exact h
  have hjeq : (p.coeff j)′ + (j : F) * c * p.coeff j =
      a * p.coeff j := by
    have h := congrArg (fun q : F[X] ↦ q.coeff j) hp
    rw [coeff_implicitDeriv_euler, Polynomial.coeff_C_mul] at h
    exact h
  have hieq' : (p.coeff i)′ = (a - (i : F) * c) * p.coeff i := by
    calc
      (p.coeff i)′ = a * p.coeff i - (i : F) * c * p.coeff i :=
        eq_sub_of_add_eq hieq
      _ = (a - (i : F) * c) * p.coeff i := by ring
  have hjeq' : (p.coeff j)′ = (a - (j : F) * c) * p.coeff j := by
    calc
      (p.coeff j)′ = a * p.coeff j - (j : F) * c * p.coeff j :=
        eq_sub_of_add_eq hjeq
      _ = (a - (j : F) * c) * p.coeff j := by ring
  let u : F := p.coeff i / p.coeff j
  have hu0 : u ≠ 0 := div_ne_zero hpi hpj
  have hn0 : (j : Int) - (i : Int) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast Ne.symm hij)
  have hueq : u′ = (((j : Int) - (i : Int) : Int) : F) * c * u := by
    dsimp [u]
    rw [Derivation.leibniz_div (Differential.deriv : Derivation Int F F)]
    simp only [smul_eq_mul]
    field_simp [hpj]
    rw [hieq', hjeq']
    push_cast
    ring
  exact hres u hu0 ((j : Int) - (i : Int)) hn0 hueq

/-- Under nonresonance, every Euler eigenpolynomial is a monomial. -/
theorem eq_monomial_of_implicitDeriv_eigen
    {c a : F} (hres : NoIntegerResonance c) (p : F[X])
    (hp : Differential.implicitDeriv (C c * X) p = C a * p) :
    ∃ n u, p = monomial n u :=
  Polynomial.card_support_le_one_iff_monomial.mp
    (support_card_le_one_of_implicitDeriv_eigen hres p hp)

/-- Classification of nonzero Euler eigenpolynomials under nonresonance. -/
theorem implicitDeriv_eigen_classification
    {c a : F} (hres : NoIntegerResonance c) {p : F[X]} (hp0 : p ≠ 0)
    (hp : Differential.implicitDeriv (C c * X) p = C a * p) :
    ∃ n u, u ≠ 0 ∧ p = monomial n u ∧
      u′ = (a - (n : F) * c) * u := by
  obtain ⟨n, u, hpu⟩ := eq_monomial_of_implicitDeriv_eigen hres p hp
  have hu0 : u ≠ 0 := by
    intro hu
    apply hp0
    rw [hpu, hu, monomial_zero_right]
  have hcoeff := congrArg (fun q : F[X] ↦ q.coeff n) hp
  rw [coeff_implicitDeriv_euler, Polynomial.coeff_C_mul] at hcoeff
  rw [hpu] at hcoeff
  simp only [coeff_monomial, if_pos] at hcoeff
  refine ⟨n, u, hu0, hpu, ?_⟩
  calc
    u′ = a * u - (n : F) * c * u := eq_sub_of_add_eq hcoeff
    _ = (a - (n : F) * c) * u := by ring

/-- A nonzero integral power of a transcendental element remains
transcendental. -/
theorem transcendental_zpow {K L : Type*} [Field K] [Field L]
    [Algebra K L] {x : L} (hx : Transcendental K x) {n : Int}
    (hn : n ≠ 0) : Transcendental K (x ^ n) := by
  cases n with
  | ofNat n =>
      have hnpos : 0 < n := Nat.pos_of_ne_zero (by simpa using hn)
      simpa using hx.pow hnpos
  | negSucc n =>
      have heq : x ^ (Int.negSucc n) = (x ^ (n + 1))⁻¹ := by simp
      rw [heq]
      intro halg
      exact hx.pow (Nat.succ_pos n) (IsAlgebraic.inv_iff.mp halg)

section Extension

variable {K L : Type*} [Field K] [Field L]
  [Differential K] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L] [Differential.ContainConstants K L]

/-- Transcendence of a solution `x' = β'x`, together with the assertion
that the extension has no new constants, implies integer nonresonance in the
base field. -/
theorem noIntegerResonance_deriv_of_transcendental_solution
    (β : K) (x : L) (hx : Transcendental K x)
    (hxd : x′ = algebraMap K L β′ * x) :
    NoIntegerResonance (β′) := by
  intro u hu n hn hun
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hx
    rw [hzero]
    exact isAlgebraic_zero
  have hconstant : (algebraMap K L u * x ^ (-n))′ = 0 := by
    rw [Differential.deriv.leibniz]
    rw [deriv_algebraMap, hun,
      Derivation.leibniz_zpow (Differential.deriv : Derivation Int L L), hxd]
    simp only [smul_eq_mul, zsmul_eq_mul, map_mul, map_intCast]
    have hxp : x ^ (-n - 1) * x = x ^ (-n) := by
      rw [← zpow_add_one₀ hx0]
      congr 2
      omega
    push_cast
    calc
      algebraMap K L u *
            ((-n : L) * (x ^ (-n - 1) * ((algebraMap K L β)′ * x))) +
          x ^ (-n) * ((n : L) * (algebraMap K L β)′ *
            algebraMap K L u) =
          algebraMap K L u * (-n : L) *
              (algebraMap K L β)′ * (x ^ (-n - 1) * x) +
            x ^ (-n) * ((n : L) * (algebraMap K L β)′ *
              algebraMap K L u) := by ring
      _ = 0 := by rw [hxp]; ring
  obtain ⟨v, hv⟩ := mem_range_of_deriv_eq_zero K hconstant
  have huG : algebraMap K L u ≠ 0 := by simpa using hu
  have hpow : x ^ (-n) = algebraMap K L (v / u) := by
    rw [map_div₀]
    apply (eq_div_iff huG).2
    rw [hv]
    ring
  have halg : IsAlgebraic K (x ^ (-n)) := by
    rw [hpow]
    exact isAlgebraic_algebraMap (v / u)
  exact transcendental_zpow hx (neg_ne_zero.mpr hn) halg

/-- The polynomial eigenfunction classification, with nonresonance obtained
from a transcendental exponential solution in a no-new-constants extension. -/
theorem implicitDeriv_eigen_classification_of_transcendental_solution
    (β : K) (x : L) (hx : Transcendental K x)
    (hxd : x′ = algebraMap K L β′ * x) {a : K} {p : K[X]}
    (hp0 : p ≠ 0)
    (hp : Differential.implicitDeriv (C β′ * X) p = C a * p) :
    ∃ n u, u ≠ 0 ∧ p = monomial n u ∧
      u′ = (a - (n : K) * β′) * u :=
  implicitDeriv_eigen_classification
    (noIntegerResonance_deriv_of_transcendental_solution β x hx hxd) hp0 hp

end Extension

omit [Differential F] in
/-- The quotient of two polynomial monomials, viewed in the rational-function
field, is a scalar times an integral power of the indeterminate. -/
theorem ratFunc_div_monomial_eq (n m : Nat) (u v : F) :
    algebraMap F[X] (RatFunc F) (monomial n u) /
        algebraMap F[X] (RatFunc F) (monomial m v) =
      RatFunc.C (u / v) * RatFunc.X ^ ((n : Int) - (m : Int)) := by
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [div_eq_mul_inv, mul_inv_rev]
  simp only [← zpow_natCast, ← zpow_neg]
  rw [show RatFunc.C (u / v) = RatFunc.C u * (RatFunc.C v)⁻¹ by
    rw [← div_eq_mul_inv]
    exact map_div₀ (RatFunc.C (K := F)) u v]
  calc
    RatFunc.C u * RatFunc.X ^ (n : Int) *
          (RatFunc.X ^ (-(m : Int)) * (RatFunc.C v)⁻¹) =
        (RatFunc.C u * (RatFunc.C v)⁻¹) *
          (RatFunc.X ^ (n : Int) * RatFunc.X ^ (-(m : Int))) := by ring
    _ = (RatFunc.C u * (RatFunc.C v)⁻¹) *
          RatFunc.X ^ ((n : Int) + -(m : Int)) := by
      rw [zpow_add₀ RatFunc.X_ne_zero]
    _ = (RatFunc.C u * (RatFunc.C v)⁻¹) *
          RatFunc.X ^ ((n : Int) - (m : Int)) := by rfl

/-- A quotient of nonzero Euler eigenpolynomials is a Laurent monomial times
a base-field scalar. -/
theorem ratFunc_eigenFraction_classification
    {c ap aq : F} (hres : NoIntegerResonance c)
    {p q : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : Differential.implicitDeriv (C c * X) p = C ap * p)
    (hq : Differential.implicitDeriv (C c * X) q = C aq * q) :
    ∃ k : Int, ∃ w : F, w ≠ 0 ∧
      algebraMap F[X] (RatFunc F) p /
          algebraMap F[X] (RatFunc F) q =
        RatFunc.C w * RatFunc.X ^ k ∧
      w′ = ((ap - aq) - (k : F) * c) * w := by
  obtain ⟨n, u, hu0, hpu, hu⟩ :=
    implicitDeriv_eigen_classification hres hp0 hp
  obtain ⟨m, v, hv0, hqv, hv⟩ :=
    implicitDeriv_eigen_classification hres hq0 hq
  refine ⟨(n : Int) - (m : Int), u / v, div_ne_zero hu0 hv0, ?_, ?_⟩
  · rw [hpu, hqv]
    exact ratFunc_div_monomial_eq n m u v
  · rw [Derivation.leibniz_div (Differential.deriv : Derivation Int F F)]
    simp only [smul_eq_mul]
    field_simp [hv0]
    rw [hu, hv]
    push_cast
    ring

/-- Cleared-denominator classification for a reduced rational Euler
eigenfunction. -/
theorem ratFunc_classification_of_isCoprime_crossEquation
    {c a : F} (hres : NoIntegerResonance c)
    {p q : F[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C c * X) p * q -
          p * Differential.implicitDeriv (C c * X) q =
        C a * p * q) :
    ∃ k : Int, ∃ w : F, w ≠ 0 ∧
      algebraMap F[X] (RatFunc F) p /
          algebraMap F[X] (RatFunc F) q =
        RatFunc.C w * RatFunc.X ^ k ∧
      w′ = (a - (k : F) * c) * w := by
  obtain ⟨sp, sq, hp, hq, hspq⟩ :=
    eigenPolynomials_of_isCoprime_crossEquation c a hp0 hpq hcross
  obtain ⟨k, w, hw0, hfrac, hw⟩ :=
    ratFunc_eigenFraction_classification hres hp0 hq0 hp hq
  rw [hspq] at hw
  exact ⟨k, w, hw0, hfrac, hw⟩

section ExtensionRatFunc

variable {K L : Type*} [Field K] [Field L]
  [Differential K] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L] [Differential.ContainConstants K L]

/-- Main result of this file: the rational eigenfunction part of Wilkie's
Proposition 3.1(i), stated as an exact cleared-denominator theorem.

`Differential.ContainConstants K L` is the direction of the shared-constants
hypothesis actually used in the proof: every constant of `L` comes from `K`.
-/
theorem ratFunc_classification_of_crossEquation_of_transcendental_solution
    (β : K) (x : L) (hx : Transcendental K x)
    (hxd : x′ = algebraMap K L β′ * x)
    {a : K} {p q : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C β′ * X) p * q -
          p * Differential.implicitDeriv (C β′ * X) q =
        C a * p * q) :
    ∃ k : Int, ∃ w : K, w ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q =
        RatFunc.C w * RatFunc.X ^ k ∧
      w′ = (a - (k : K) * β′) * w :=
  ratFunc_classification_of_isCoprime_crossEquation
    (noIntegerResonance_deriv_of_transcendental_solution β x hx hxd)
    hp0 hq0 hpq hcross

/-- Source-shaped special case in which the scalar logarithmic derivative is
already the derivative of an element `γ` of the base field.  Besides the
Laurent-monomial description, this records the residual primitive
`v = γ - kβ` and the equation `w' = v'w` appearing in Wilkie's
Proposition 3.1(i). -/
theorem ratFunc_classification_of_crossEquation_of_base_primitive
    (β γ : K) (x : L) (hx : Transcendental K x)
    (hxd : x′ = algebraMap K L β′ * x)
    {p q : K[X]} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpq : IsCoprime p q)
    (hcross :
      Differential.implicitDeriv (C β′ * X) p * q -
          p * Differential.implicitDeriv (C β′ * X) q =
        C γ′ * p * q) :
    ∃ k : Int, ∃ w v : K, w ≠ 0 ∧
      algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q =
        RatFunc.C w * RatFunc.X ^ k ∧
      γ = (k : K) * β + v ∧ w′ = v′ * w := by
  obtain ⟨k, w, hw0, hfrac, hw⟩ :=
    ratFunc_classification_of_crossEquation_of_transcendental_solution
      β x hx hxd hp0 hq0 hpq hcross
  refine ⟨k, w, γ - (k : K) * β, hw0, hfrac, ?_, ?_⟩
  · ring
  · rw [hw, map_sub, Differential.deriv.leibniz]
    rw [Derivation.map_intCast]
    ring

end ExtensionRatFunc

end

end Natfunbasis.Wilkie.Proposition31
