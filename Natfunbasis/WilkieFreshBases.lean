import Natfunbasis.WilkieGenerators

/-!
# Fresh bases in a Wilkie generator sequence

Wilkie's induction separates constant bases, the original variable, and the
first occurrence of every other base.  This file formalizes that bookkeeping
for an arbitrary generator sequence.  It is independent of the analytic and
differential-algebraic arguments used later in the induction.

Equality here is literal equality of the common-variable polynomial
presentations.  This is the appropriate formulation for the concrete
`equalityDerivability` sequence used by the canonical normalizer.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The common-variable polynomial underlying the base at index `k`. -/
def baseGlobal (k : Nat) : GlobalPolynomial :=
  (S.pair k).base.toGlobal

/-- The base at `k` is a constant integer polynomial. -/
def IsConstantBase (k : Nat) : Prop :=
  ∃ c : Int, S.baseGlobal k = C c

/-- The base at `k` is the distinguished original variable. -/
def IsOriginalBase (k : Nat) : Prop :=
  S.baseGlobal k = originalPolynomial

/-- A nonconstant, non-original base occurring for the first time at `k`. -/
def IsFreshBase (k : Nat) : Prop :=
  ¬ S.IsConstantBase k ∧
    ¬ S.IsOriginalBase k ∧
    ∀ j < k, S.baseGlobal j ≠ S.baseGlobal k

/-- The first index whose base polynomial agrees with the base at `k`. -/
def firstBaseIndex (k : Nat) : Nat :=
  Nat.find (show ∃ j, S.baseGlobal j = S.baseGlobal k from ⟨k, rfl⟩)

theorem firstBaseIndex_spec (k : Nat) :
    S.baseGlobal (S.firstBaseIndex k) = S.baseGlobal k := by
  exact Nat.find_spec (show ∃ j, S.baseGlobal j = S.baseGlobal k from ⟨k, rfl⟩)

theorem firstBaseIndex_le (k : Nat) : S.firstBaseIndex k ≤ k := by
  exact Nat.find_min'
    (show ∃ j, S.baseGlobal j = S.baseGlobal k from ⟨k, rfl⟩) rfl

theorem firstBaseIndex_minimal (k : Nat) {j : Nat}
    (hj : j < S.firstBaseIndex k) :
    S.baseGlobal j ≠ S.baseGlobal k := by
  exact Nat.find_min
    (show ∃ i, S.baseGlobal i = S.baseGlobal k from ⟨k, rfl⟩) hj

theorem isConstantBase_of_base_eq {i j : Nat}
    (hij : S.baseGlobal i = S.baseGlobal j) (hi : S.IsConstantBase i) :
    S.IsConstantBase j := by
  obtain ⟨c, hc⟩ := hi
  exact ⟨c, hij.symm.trans hc⟩

theorem isOriginalBase_of_base_eq {i j : Nat}
    (hij : S.baseGlobal i = S.baseGlobal j) (hi : S.IsOriginalBase i) :
    S.IsOriginalBase j :=
  hij.symm.trans hi

/-- The first occurrence of a nonconstant, non-original base is fresh. -/
theorem isFreshBase_firstBaseIndex {k : Nat}
    (hconstant : ¬ S.IsConstantBase k)
    (horiginal : ¬ S.IsOriginalBase k) :
    S.IsFreshBase (S.firstBaseIndex k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hfirst
    exact hconstant (S.isConstantBase_of_base_eq (S.firstBaseIndex_spec k) hfirst)
  · intro hfirst
    exact horiginal (S.isOriginalBase_of_base_eq (S.firstBaseIndex_spec k) hfirst)
  · intro j hj heq
    exact S.firstBaseIndex_minimal k hj
      (heq.trans (S.firstBaseIndex_spec k))

/-- Every nonconstant, non-original base has an earlier-or-equal fresh
representative with exactly the same global polynomial. -/
theorem exists_freshBase_le {k : Nat}
    (hconstant : ¬ S.IsConstantBase k)
    (horiginal : ¬ S.IsOriginalBase k) :
    ∃ j ≤ k, S.IsFreshBase j ∧ S.baseGlobal j = S.baseGlobal k := by
  exact ⟨S.firstBaseIndex k, S.firstBaseIndex_le k,
    S.isFreshBase_firstBaseIndex hconstant horiginal, S.firstBaseIndex_spec k⟩

/-- Two fresh indices cannot present the same base polynomial. -/
theorem freshBase_unique {i j : Nat}
    (hi : S.IsFreshBase i) (hj : S.IsFreshBase j)
    (hbase : S.baseGlobal i = S.baseGlobal j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hj.2.2 i hij hbase)
  · exact hij
  · exact False.elim (hi.2.2 j hij hbase.symm)

/-- Exact four-way classification of every index: its base is constant, is
the original variable, is fresh, or repeats a unique earlier fresh base. -/
theorem constant_original_fresh_or_repeated (k : Nat) :
    S.IsConstantBase k ∨
      S.IsOriginalBase k ∨
      S.IsFreshBase k ∨
      ∃! j : Nat, j < k ∧ S.IsFreshBase j ∧
        S.baseGlobal j = S.baseGlobal k := by
  by_cases hconstant : S.IsConstantBase k
  · exact Or.inl hconstant
  by_cases horiginal : S.IsOriginalBase k
  · exact Or.inr (Or.inl horiginal)
  let j := S.firstBaseIndex k
  have hjfresh : S.IsFreshBase j :=
    S.isFreshBase_firstBaseIndex hconstant horiginal
  have hjle : j ≤ k := S.firstBaseIndex_le k
  rcases hjle.eq_or_lt with hjEq | hjlt
  · exact Or.inr (Or.inr (Or.inl (by simpa [hjEq] using hjfresh)))
  · refine Or.inr (Or.inr (Or.inr ⟨j, ⟨hjlt, hjfresh,
      S.firstBaseIndex_spec k⟩, ?_⟩))
    intro other hother
    exact S.freshBase_unique hother.2.1 hjfresh
      (hother.2.2.trans (S.firstBaseIndex_spec k).symm)

end GeneratorSequence

end

end Natfunbasis.Wilkie
