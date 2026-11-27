import Natfunbasis.WilkieDifferentialIntermediateField
import Mathlib.FieldTheory.Differential.Basic

/-!
# Wilkie's Proposition 3.2: algebraic differential extensions

Wilkie's Proposition 3.2 assumes differential rings `F ⊆ G`, with `F` a
field and with the same fields of constants, and an element `α ∈ G` algebraic
over `F`.  Its two clauses are:

1. if `β ∈ F` and `α' = β' α`, then there are `m ∈ ℤ \ {0}` and `u,v ∈ F`
   such that `α^m = u`, `mβ = v`, and `u' = v'u`;
2. if `β ∈ F \ {0}` and `α' = β'/β`, then `α ∈ F`.

This module develops the algebraic-extension part of those statements for
fields in characteristic zero.  `Differential.ContainConstants F G` is the
direction of the common-constants hypothesis actually used: every constant of
`G` lies in the image of `F`.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.Proposition32

noncomputable section

variable {F G : Type*} [Field F] [CharZero F] [Field G]
  [Differential F] [Differential G] [Algebra F G]
  [DifferentialAlgebra F G]

omit [CharZero F] in
/-- Coefficient-wise differentiation strictly lowers the degree of a
positive-degree monic polynomial. -/
lemma natDegree_mapCoeffs_lt_of_monic {p : F[X]}
    (hp : p.Monic) (hdegree : 0 < p.natDegree) :
    (Differential.mapCoeffs p).natDegree < p.natDegree := by
  have hle : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [Differential.coeff_mapCoeffs,
      coeff_eq_zero_of_natDegree_lt hn, map_zero]
  have hlead : (Differential.mapCoeffs p).coeff p.natDegree = 0 := by
    rw [Differential.coeff_mapCoeffs, hp.coeff_natDegree]
    simp
  have hpred := natDegree_le_pred hle hlead
  omega

omit [CharZero F] in
/-- If an algebraic element has derivative in the base field, the implicit
derivative of its minimal polynomial vanishes. -/
lemma implicitDeriv_C_minpoly_eq_zero {α : G} (hα : IsAlgebraic F α)
    (d : F) (hderiv : α′ = algebraMap F G d) :
    Differential.implicitDeriv (C d) (minpoly F α) = 0 := by
  let p : F[X] := minpoly F α
  have hpmonic : p.Monic := minpoly.monic hα.isIntegral
  have hpdegree : 0 < p.natDegree := minpoly.natDegree_pos hα.isIntegral
  have hroot :
      aeval α (Differential.implicitDeriv (C d) p) = 0 := by
    rw [← Differential.deriv_aeval_eq_implicitDeriv α (C d) (by simpa using hderiv) p]
    simp [p]
  have hdvd : p ∣ Differential.implicitDeriv (C d) p := by
    simpa [p] using minpoly.dvd F α hroot
  apply eq_zero_of_dvd_of_natDegree_lt hdvd
  change (Differential.mapCoeffs p + C d * derivative p).natDegree < p.natDegree
  refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · exact natDegree_mapCoeffs_lt_of_monic hpmonic hpdegree
  · exact (natDegree_C_mul_le d (derivative p)).trans_lt
      (natDegree_derivative_lt hpdegree.ne')

/-- Characteristic-zero algebraic descent for primitives: if an algebraic
element has derivative in the base field and the extension has no new
constants, then the element itself lies in the base field. -/
theorem mem_range_of_isAlgebraic_of_deriv_eq_algebraMap
    [Differential.ContainConstants F G]
    {α : G} (hα : IsAlgebraic F α) (d : F)
    (hderiv : α′ = algebraMap F G d) :
    α ∈ (algebraMap F G).range := by
  let p : F[X] := minpoly F α
  let n : Nat := p.natDegree
  have hpmonic : p.Monic := minpoly.monic hα.isIntegral
  have hn : 0 < n := minpoly.natDegree_pos hα.isIntegral
  have hzero : Differential.implicitDeriv (C d) p = 0 := by
    simpa [p] using implicitDeriv_C_minpoly_eq_zero hα d hderiv
  have hcoeff := congrArg (fun q : F[X] ↦ q.coeff (n - 1)) hzero
  have hnstep : n - 1 + 1 = n := by omega
  have hncast : ((n - 1 : Nat) : F) + 1 = (n : F) := by
    exact_mod_cast hnstep
  have hrelation :
      (p.coeff (n - 1))′ + (n : F) * d = 0 := by
    change
      (Differential.mapCoeffs p + C d * derivative p).coeff (n - 1) =
        (0 : F[X]).coeff (n - 1) at hcoeff
    simp only [coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul,
      coeff_derivative, coeff_zero] at hcoeff
    rw [hnstep, hpmonic.coeff_natDegree, hncast] at hcoeff
    simpa [mul_comm] using hcoeff
  let b : F := -(n : F)⁻¹ * p.coeff (n - 1)
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hb : b′ = d := by
    dsimp [b]
    have hnconstant : ((n : F)′) = 0 := by simp
    rw [Differential.deriv.leibniz]
    simp only [map_neg, Derivation.leibniz_inv, hnconstant, smul_eq_mul,
      mul_zero, neg_zero]
    apply (mul_left_cancel₀ hnF)
    field_simp [hnF]
    linear_combination -hrelation
  have hconstant : (α - algebraMap F G b)′ = 0 := by
    rw [map_sub, hderiv, deriv_algebraMap, hb, sub_self]
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero F hconstant
  refine ⟨c + b, ?_⟩
  rw [map_add, hc]
  ring

/-- Wilkie Proposition 3.2(ii), in field-extension form.  The source assumes
`β ≠ 0`; the descent proof only needs the displayed derivative identity. -/
theorem proposition32_ii [Differential.ContainConstants F G]
    {α : G} (hα : IsAlgebraic F α) {β : F} (_hβ : β ≠ 0)
    (hderiv : α′ = algebraMap F G (β′ / β)) :
    α ∈ (algebraMap F G).range :=
  mem_range_of_isAlgebraic_of_deriv_eq_algebraMap hα (β′ / β) hderiv

/-- The minimal polynomial of an algebraic solution of `α' = dα` is an
eigenvector for the Euler derivation, with eigenvalue `n d`, where `n` is its
degree. -/
lemma implicitDeriv_C_mul_X_minpoly_eq
    {α : G} (hα : IsAlgebraic F α) (d : F)
    (hderiv : α′ = algebraMap F G d * α) :
    Differential.implicitDeriv (C d * X) (minpoly F α) =
      C (((minpoly F α).natDegree : F) * d) * minpoly F α := by
  let p : F[X] := minpoly F α
  let n : Nat := p.natDegree
  have hpmonic : p.Monic := minpoly.monic hα.isIntegral
  have hn : 0 < n := minpoly.natDegree_pos hα.isIntegral
  let q : F[X] := Differential.implicitDeriv (C d * X) p
  let r : F[X] := q - C ((n : F) * d) * p
  have hqroot : aeval α q = 0 := by
    dsimp [q]
    rw [← Differential.deriv_aeval_eq_implicitDeriv α (C d * X)
      (by simpa using hderiv) p]
    simp [p]
  have hrroot : aeval α r = 0 := by
    simp [r, hqroot, p]
  have hdiv : p ∣ r := by
    simpa [p] using minpoly.dvd F α hrroot
  have hmaplt : (Differential.mapCoeffs p).natDegree < n := by
    exact natDegree_mapCoeffs_lt_of_monic hpmonic hn
  have hderlt : (derivative p).natDegree < n :=
    natDegree_derivative_lt hn.ne'
  have hlinear : (C d * X : F[X]).natDegree ≤ 1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le d 1
  have htermle : ((C d * X) * derivative p).natDegree ≤ n := by
    calc
      ((C d * X) * derivative p).natDegree ≤
          (C d * X : F[X]).natDegree + (derivative p).natDegree :=
        natDegree_mul_le
      _ ≤ 1 + (n - 1) := add_le_add hlinear (by omega)
      _ = n := by omega
  have hqle : q.natDegree ≤ n := by
    change (Differential.mapCoeffs p + (C d * X) * derivative p).natDegree ≤ n
    exact (natDegree_add_le _ _).trans
      (max_le (Nat.le_of_lt hmaplt) htermle)
  have hscalarle : (C ((n : F) * d) * p).natDegree ≤ n := by
    exact (natDegree_C_mul_le ((n : F) * d) p).trans (by rfl)
  have hrle : r.natDegree ≤ n := by
    exact (natDegree_sub_le _ _).trans (max_le hqle hscalarle)
  have hnstep : n - 1 + 1 = n := by omega
  have hncast : ((n - 1 : Nat) : F) + 1 = (n : F) := by
    exact_mod_cast hnstep
  have hrcoeff : r.coeff n = 0 := by
    change
      (Differential.mapCoeffs p + (C d * X) * derivative p -
        C ((n : F) * d) * p).coeff n = 0
    rw [coeff_sub, coeff_add, Differential.coeff_mapCoeffs,
      hpmonic.coeff_natDegree]
    rw [show ((1 : F)′) = 0 by simp]
    simp only [coeff_C_mul]
    rw [show (C d * X : F[X]) * derivative p =
      C d * (X * derivative p) by ring, coeff_C_mul,
      show n = (n - 1) + 1 by omega, coeff_X_mul, coeff_derivative,
      hnstep, hpmonic.coeff_natDegree, hncast]
    ring
  have hrlt : r.natDegree < n := by
    have := natDegree_le_pred hrle hrcoeff
    omega
  have hrzero : r = 0 := eq_zero_of_dvd_of_natDegree_lt hdiv hrlt
  change q = C ((n : F) * d) * p
  exact sub_eq_zero.mp hrzero

/-- The constant coefficient of the minimal polynomial satisfies the same
logarithmic differential equation as the `n`-th power of the algebraic
solution. -/
lemma deriv_minpoly_coeff_zero_of_deriv_eq_mul
    {α : G} (hα : IsAlgebraic F α) (d : F)
    (hderiv : α′ = algebraMap F G d * α) :
    ((minpoly F α).coeff 0)′ =
      (((minpoly F α).natDegree : F) * d) * (minpoly F α).coeff 0 := by
  let p : F[X] := minpoly F α
  let n : Nat := p.natDegree
  have hpoly := implicitDeriv_C_mul_X_minpoly_eq hα d hderiv
  have hcoeff := congrArg (fun q : F[X] ↦ q.coeff 0) hpoly
  change
    (Differential.mapCoeffs p + (C d * X) * derivative p).coeff 0 =
      (C ((n : F) * d) * p).coeff 0 at hcoeff
  rw [coeff_add, Differential.coeff_mapCoeffs,
    show (C d * X : F[X]) * derivative p =
      C d * (X * derivative p) by ring,
    coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero, coeff_C_mul] at hcoeff
  exact hcoeff

/-- Power descent for an algebraic solution of `α' = dα`.  The exponent is
the positive degree of the minimal polynomial (or `1` in the zero case), and
the descended base-field element retains the expected differential equation. -/
theorem exists_power_mem_range_of_isAlgebraic_of_deriv_eq_mul
    [Differential.ContainConstants F G]
    {α : G} (hα : IsAlgebraic F α) (d : F)
    (hderiv : α′ = algebraMap F G d * α) :
    ∃ n : Nat, 0 < n ∧ ∃ u : F,
      α ^ n = algebraMap F G u ∧ u′ = (n : F) * d * u := by
  by_cases hαzero : α = 0
  · refine ⟨1, Nat.zero_lt_one, 0, ?_, ?_⟩
    · simp [hαzero]
    · simp
  let p : F[X] := minpoly F α
  let n : Nat := p.natDegree
  let a : F := p.coeff 0
  have hn : 0 < n := minpoly.natDegree_pos hα.isIntegral
  have ha : a ≠ 0 := by
    exact minpoly.coeff_zero_ne_zero hα.isIntegral hαzero
  have haderiv : a′ = (n : F) * d * a := by
    simpa [p, n, a] using
      deriv_minpoly_coeff_zero_of_deriv_eq_mul hα d hderiv
  have hnstep : n - 1 + 1 = n := by omega
  have hpowderiv : (α ^ n)′ = algebraMap F G ((n : F) * d) * α ^ n := by
    rw [Differential.deriv.leibniz_pow, hderiv]
    simp only [nsmul_eq_mul, smul_eq_mul]
    calc
      (n : G) * (α ^ (n - 1) * (algebraMap F G d * α)) =
          (n : G) * algebraMap F G d * (α ^ (n - 1) * α) := by ring
      _ = (n : G) * algebraMap F G d * α ^ n := by rw [← pow_succ, hnstep]
      _ = algebraMap F G ((n : F) * d) * α ^ n := by
        rw [map_mul, map_natCast]
  let z : G := α ^ n * (algebraMap F G a)⁻¹
  have haG : algebraMap F G a ≠ 0 := by
    intro h
    apply ha
    apply (algebraMap F G).injective
    simpa using h
  have hinvderiv :
      ((algebraMap F G a)⁻¹)′ =
        -(algebraMap F G a)⁻¹ ^ 2 * (algebraMap F G a)′ := by
    simpa only [smul_eq_mul] using
      (Derivation.leibniz_inv (R := Int) (M := G)
        Differential.deriv (algebraMap F G a))
  have hzderiv : z′ = 0 := by
    dsimp [z]
    rw [Differential.deriv.leibniz, hpowderiv,
      hinvderiv, deriv_algebraMap, haderiv]
    simp only [smul_eq_mul, map_mul, map_natCast]
    field_simp [haG]
    ring
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero F hzderiv
  have hcderiv : c′ = 0 := by
    apply (algebraMap F G).injective
    rw [← deriv_algebraMap, hc, hzderiv, map_zero]
  let u : F := c * a
  refine ⟨n, hn, u, ?_, ?_⟩
  · calc
      α ^ n = (α ^ n * (algebraMap F G a)⁻¹) * algebraMap F G a := by
        rw [mul_assoc, inv_mul_cancel₀ haG, mul_one]
      _ = z * algebraMap F G a := rfl
      _ = algebraMap F G c * algebraMap F G a := by rw [← hc]
      _ = algebraMap F G u := by simp [u]
  · dsimp [u]
    rw [Differential.deriv.leibniz, hcderiv, haderiv]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring

/-- Wilkie Proposition 3.2(i), in field-extension form.  We choose the
positive integer `m` given by the degree of the minimal polynomial (with
`m = 1` when `α = 0`). -/
theorem proposition32_i [Differential.ContainConstants F G]
    {α : G} (hα : IsAlgebraic F α) (β : F)
    (hderiv : α′ = algebraMap F G β′ * α) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ u v : F,
      α ^ m = algebraMap F G u ∧
      (m : F) * β = v ∧ u′ = v′ * u := by
  obtain ⟨n, hn, u, hpower, huderiv⟩ :=
    exists_power_mem_range_of_isAlgebraic_of_deriv_eq_mul hα β′ hderiv
  have hnzero : (n : ℤ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hvderiv : (((n : F) * β)′) = (n : F) * β′ := by
    rw [Differential.deriv.leibniz]
    simp only [smul_eq_mul]
    simp
  refine ⟨(n : ℤ), hnzero, u, (n : F) * β, ?_, ?_, ?_⟩
  · simpa only [zpow_natCast] using hpower
  · simp
  · rw [hvderiv]
    exact huderiv

end

end Natfunbasis.Wilkie.Proposition32
