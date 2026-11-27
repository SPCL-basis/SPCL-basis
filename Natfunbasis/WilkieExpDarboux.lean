import Mathlib

/-!
# Exponential Darboux non-tangency

Let `R₀` be a domain mapping into a differential field `K` by `ev₀`, and let
`t ∈ K` satisfy `c·t′ = ev₀(N)·t` while `c·(ev₀ a)′ = ev₀(D₀ a)` on `R₀`, for a
nonzero `c`.  The operator

  `Δ (∑ aₖ Tᵏ) = ∑ (D₀ aₖ + k·N·aₖ) Tᵏ`

then realizes `c·(d/dx)` on polynomial expressions in `t`.  If evaluation at
`t` is injective and `K` has only real constants, no polynomial `P` of positive
degree with nonzero constant term divides `Δ P`.

This is the whole-polynomial special-polynomial argument used for the fresh
Wilkie base at its top variable.
-/

open Polynomial
open scoped Differential

namespace Natfunbasis.ExpDarboux

noncomputable section

variable {R₀ : Type*} [CommRing R₀]

/-- The exponential Darboux operator. -/
def expDarboux (D₀ : R₀ →+ R₀) (N : R₀) (P : R₀[X]) : R₀[X] :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    monomial k (D₀ (P.coeff k) + (k : R₀) * N * P.coeff k)

theorem coeff_expDarboux (D₀ : R₀ →+ R₀) (N : R₀) (P : R₀[X]) (j : ℕ) :
    (expDarboux D₀ N P).coeff j =
      D₀ (P.coeff j) + (j : R₀) * N * P.coeff j := by
  rw [expDarboux, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hj
    simp only [Finset.mem_range, not_lt] at hj
    have : P.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [this]

theorem natDegree_expDarboux_le (D₀ : R₀ →+ R₀) (N : R₀) (P : R₀[X]) :
    (expDarboux D₀ N P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_expDarboux, coeff_eq_zero_of_natDegree_lt hj]
  simp

/-- The Darboux identity forced by `P ∣ Δ P`. -/
theorem darboux_identity [IsDomain R₀] (D₀ : R₀ →+ R₀) (N : R₀)
    {P : R₀[X]} (hP : P ≠ 0) (hdvd : P ∣ expDarboux D₀ N P) :
    P.coeff 0 * D₀ P.leadingCoeff - P.leadingCoeff * D₀ (P.coeff 0) +
      (P.natDegree : R₀) * N * P.leadingCoeff * P.coeff 0 = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  have htop := congrArg (fun p : R₀[X] ↦ p.coeff P.natDegree) hq
  have hbot := congrArg (fun p : R₀[X] ↦ p.coeff 0) hq
  simp only [coeff_expDarboux] at htop hbot
  by_cases hq0 : q = 0
  · subst hq0
    simp only [mul_zero, coeff_zero, Nat.cast_zero, zero_mul, add_zero] at htop hbot
    rw [hbot]
    have : D₀ P.leadingCoeff = -((P.natDegree : R₀) * N * P.leadingCoeff) := by
      rw [leadingCoeff]; linear_combination htop
    rw [this]
    ring
  · have hdeg : q.natDegree = 0 := by
      have h1 := natDegree_expDarboux_le D₀ N P
      rw [hq, natDegree_mul hP hq0] at h1
      omega
    rw [eq_C_of_natDegree_eq_zero hdeg] at htop hbot
    rw [coeff_mul_C] at htop hbot
    simp only [Nat.cast_zero, zero_mul, add_zero] at hbot
    rw [leadingCoeff]
    linear_combination (P.coeff 0) * htop - P.coeff P.natDegree * hbot

/-! ## Evaluation -/

variable {K : Type*} [Field K] [Differential K]

theorem deriv_mul_pow_mul (c a t : K) (k : ℕ) (N : K) (hN : N * t = c * t′) :
    c * (a * t ^ k)′ = (c * a′ + (k : K) * N * a) * t ^ k := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul,
    nsmul_eq_mul, smul_eq_mul]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have ht : t ^ k = t ^ (k - 1) * t := by
      rw [← pow_succ]; congr 1; omega
    rw [ht]
    linear_combination (-(↑k * a * t ^ (k - 1))) * hN

variable (ev₀ : R₀ →+* K) (t : K)

/-- `Δ` realizes `c·(d/dx)` on polynomial expressions in `t`. -/
theorem eval₂_expDarboux (D₀ : R₀ →+ R₀) (N : R₀) (c : K)
    (hD₀ : ∀ a, ev₀ (D₀ a) = c * (ev₀ a)′) (hN : ev₀ N * t = c * t′)
    (P : R₀[X]) :
    (expDarboux D₀ N P).eval₂ ev₀ t = c * (P.eval₂ ev₀ t)′ := by
  rw [expDarboux, eval₂_finsetSum, eval₂_eq_sum_range, map_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval₂_monomial, deriv_mul_pow_mul c (ev₀ (P.coeff k)) t k (ev₀ N) hN,
    map_add, map_mul, map_mul, hD₀, map_natCast]

/-- **Non-tangency.** -/
theorem not_dvd_expDarboux [IsDomain R₀] [Algebra ℝ R₀] [Algebra ℝ K]
    (ev₀ : R₀ →ₐ[ℝ] K) (t : K)
    (hev : Function.Injective (Polynomial.eval₂RingHom ev₀.toRingHom t))
    (hconst : ∀ z : K, z′ = 0 → ∃ r : ℝ, z = algebraMap ℝ K r)
    (D₀ : R₀ →+ R₀) (N : R₀) (c : K) (hc : c ≠ 0)
    (hD₀ : ∀ a, ev₀ (D₀ a) = c * (ev₀ a)′) (hN : ev₀ N * t = c * t′)
    {P : R₀[X]} (hdeg : 0 < P.natDegree) (h0 : P.coeff 0 ≠ 0) :
    ¬ P ∣ expDarboux D₀ N P := by
  intro hdvd
  have hP : P ≠ 0 := by rintro rfl; simp at hdeg
  have hid := darboux_identity D₀ N hP hdvd
  set d := P.natDegree
  set ad := P.leadingCoeff
  set a0 := P.coeff 0
  have hevC : ∀ a : R₀, Polynomial.eval₂RingHom ev₀.toRingHom t (C a) = ev₀ a := by
    intro a; simp
  have ha0 : ev₀ a0 ≠ 0 := by
    intro h
    apply h0
    have h' : Polynomial.eval₂RingHom ev₀.toRingHom t (C a0) =
        Polynomial.eval₂RingHom ev₀.toRingHom t 0 := by
      rw [hevC, h, map_zero]
    exact C_eq_zero.1 (hev h')
  -- the identity, evaluated
  have hidK := congrArg ev₀ hid
  simp only [map_add, map_sub, map_mul, map_natCast, map_zero, hD₀] at hidK
  -- `(ad t^d / a0)′ = 0`
  have hz : (ev₀ ad * t ^ d / ev₀ a0)′ = 0 := by
    have hnum : ev₀ a0 * (ev₀ ad * t ^ d)′ - ev₀ ad * t ^ d * (ev₀ a0)′ = 0 := by
      apply (mul_right_injective₀ hc)
      simp only [mul_zero]
      have h1 := deriv_mul_pow_mul c (ev₀ ad) t d (ev₀ N) hN
      have h2 : c * (ev₀ ad * t ^ d * (ev₀ a0)′) =
          ev₀ ad * t ^ d * (c * (ev₀ a0)′) := by ring
      rw [mul_sub, mul_left_comm, h1, h2]
      linear_combination (t ^ d) * hidK
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul] at hnum ⊢
    rw [hnum, mul_zero]
  obtain ⟨r, hr⟩ := hconst _ hz
  have hrel : ev₀ ad * t ^ d = ev₀ (algebraMap ℝ R₀ r * a0) := by
    rw [map_mul, AlgHom.commutes, ← hr]
    field_simp
  -- the relation is a nonzero polynomial vanishing at `t`
  have hQ : C ad * X ^ d - C (algebraMap ℝ R₀ r * a0) = 0 := by
    apply hev
    simp only [map_sub, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_zero]
    rw [hrel]
    simp
  have hcoeff := congrArg (fun p : R₀[X] ↦ p.coeff d) hQ
  simp only [coeff_sub, coeff_C_mul_X_pow, coeff_C,
    if_neg (Nat.pos_iff_ne_zero.1 hdeg), sub_zero, coeff_zero] at hcoeff
  exact (leadingCoeff_ne_zero.2 hP) hcoeff

end

end Natfunbasis.ExpDarboux
