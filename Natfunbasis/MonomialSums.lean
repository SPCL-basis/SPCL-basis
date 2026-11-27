import Natfunbasis.PolynomialInvariants
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.Count

/-!
# Finite sums of coefficient-one monomials

This module isolates the elementary coefficient comparison used in uniqueness
of additive basis expansions.  It is independent of the unresolved Wilkie
normal-form construction.
-/

namespace Natfunbasis.NormalPolynomial

open MvPolynomial

noncomputable section

variable {Var : Type*}

/-- The polynomial obtained by adding one copy of each monomial in `support`.
Repeated entries produce the corresponding natural-number coefficient. -/
def monomialSum (support : List (Var →₀ Nat)) : MvPolynomial Var Nat :=
  (support.map fun m ↦ monomial m 1).sum

/-- A coefficient of `monomialSum` is exactly the multiplicity of that
monomial in the defining list. -/
theorem coeff_monomialSum [DecidableEq Var]
    (m : Var →₀ Nat) (support : List (Var →₀ Nat)) :
    coeff m (monomialSum support) =
      Multiset.count m (support : Multiset (Var →₀ Nat)) := by
  classical
  induction support with
  | nil => simp [monomialSum]
  | cons a support ih =>
      change coeff m (monomial a 1 + monomialSum support) =
        Multiset.count m (a ::ₘ (support : Multiset (Var →₀ Nat)))
      by_cases h : a = m
      · subst a
        simp [ih, Nat.add_comm]
      · simp [h, ih]

/-- Two finite sums of coefficient-one monomials are equal exactly when their
lists of monomials agree up to permutation. -/
theorem monomialSum_eq_iff_perm (left right : List (Var →₀ Nat)) :
    monomialSum left = monomialSum right ↔ left.Perm right := by
  classical
  constructor
  · intro h
    apply Multiset.coe_eq_coe.mp
    apply Multiset.ext'
    intro m
    simpa [coeff_monomialSum] using congrArg (coeff m) h
  · intro h
    have hmultiset : (left : Multiset (Var →₀ Nat)) = right :=
      Multiset.coe_eq_coe.mpr h
    ext m
    rw [coeff_monomialSum, coeff_monomialSum]
    exact congrArg (Multiset.count m) hmultiset

end

end Natfunbasis.NormalPolynomial
