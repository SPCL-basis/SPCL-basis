import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Elementary polynomial invariants

These are the algebraic facts behind the proposed constant-coefficient and
weight arguments.  This module makes no claim that a natural expression has a
canonical Wilkie normal form; that separate dependency is still unresolved.
-/

namespace Natfunbasis.NormalPolynomial

open MvPolynomial

noncomputable section

variable {Var : Type*}

/-- Constant coefficient of a multivariate polynomial over `Nat`. -/
def constant (p : MvPolynomial Var Nat) : Nat :=
  constantCoeff p

/-- Sum of all coefficients, implemented by evaluating every variable at one. -/
def weight (p : MvPolynomial Var Nat) : Nat :=
  eval (fun _ ↦ 1) p

@[simp]
theorem constant_add (p q : MvPolynomial Var Nat) :
    constant (p + q) = constant p + constant q := by
  simp [constant]

@[simp]
theorem constant_mul (p q : MvPolynomial Var Nat) :
    constant (p * q) = constant p * constant q := by
  simp [constant]

@[simp]
theorem constant_pow (p : MvPolynomial Var Nat) (n : Nat) :
    constant (p ^ n) = constant p ^ n := by
  simp [constant]

@[simp]
theorem weight_add (p q : MvPolynomial Var Nat) :
    weight (p + q) = weight p + weight q := by
  simp [weight]

@[simp]
theorem weight_mul (p q : MvPolynomial Var Nat) :
    weight (p * q) = weight p * weight q := by
  simp [weight]

@[simp]
theorem weight_monomial_one (m : Var →₀ Nat) :
    weight (monomial m 1 : MvPolynomial Var Nat) = 1 := by
  simp [weight, eval_monomial]

/-- A nonzero polynomial with natural coefficients has positive weight. -/
theorem weight_pos {p : MvPolynomial Var Nat} (hp : p ≠ 0) : 0 < weight p := by
  classical
  rw [weight, eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  apply Finset.sum_pos'
  · intro m hm
    exact Nat.zero_le _
  · obtain ⟨m, hm⟩ := support_nonempty.mpr hp
    refine ⟨m, hm, ?_⟩
    exact Nat.pos_of_ne_zero (mem_support_iff.mp hm)

theorem one_le_weight {p : MvPolynomial Var Nat} (hp : p ≠ 0) :
    1 ≤ weight p :=
  weight_pos hp

/-- A weight-one nonzero polynomial cannot split into two nonzero
natural-coefficient polynomials. -/
theorem weight_one_forbids_add {p q r : MvPolynomial Var Nat}
    (hp : p = q + r) (hq : q ≠ 0) (hr : r ≠ 0) (hw : weight p = 1) : False := by
  have hqpos := weight_pos hq
  have hrpos := weight_pos hr
  rw [hp, weight_add] at hw
  omega

end

end Natfunbasis.NormalPolynomial
