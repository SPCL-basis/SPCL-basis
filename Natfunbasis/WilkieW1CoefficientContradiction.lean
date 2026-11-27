import Natfunbasis.WilkieFreshBases
import Natfunbasis.PowerBranchEvaluation

/-!
# The coefficient contradiction supplied by W1.3

After algebraic independence turns Wilkie's primitive relation into a
polynomial identity, the coefficient of the current exponent monomial must
be contributed by an earlier occurrence of that same monomial.  If those
terms have the same base, W1.3 rules the occurrence out.  This file packages
that elementary but repeatedly used final step.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

/-! ## A coefficient-one monomial lemma -/

/-- A nonzero scalar multiple of one nonconstant coefficient-one monomial
cannot be a constant plus a finite linear combination of other such
monomials unless one summand has the same exponent and a nonzero
coefficient. -/
theorem exists_matching_monomial_of_linearCombination
    {J I : Type*}
    (target : J →₀ Nat) (htarget : target ≠ 0)
    (exponents : I → J →₀ Nat) (coefficients : I → Int)
    (s : Finset I) (constant slope : Int) (hslope : slope ≠ 0)
    (hpoly :
      C constant +
          ∑ i ∈ s, C (coefficients i) * monomial (exponents i) 1 =
        C slope * monomial target 1) :
    ∃ i ∈ s, exponents i = target ∧ coefficients i ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hcoeff := congrArg (MvPolynomial.coeff target) hpoly
  have hsumzero :
      ∑ i ∈ s, (if exponents i = target then coefficients i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs with heq
    · exact hnone i hi heq
    · rfl
  have heq :
      ∑ i ∈ s, (if exponents i = target then coefficients i else 0) =
        slope := by
    have hzeroTarget : (0 : J →₀ Nat) ≠ target := Ne.symm htarget
    simpa only [coeff_add, coeff_C, if_neg hzeroTarget, zero_add,
      coeff_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one,
      mul_zero, if_true] using hcoeff
  exact hslope (hsumzero.symm.trans heq).symm

namespace NonconstantMonomial

/-- The common-variable exponent vector underlying a staged monomial. -/
def globalExponents {k : Nat} (m : NonconstantMonomial k) :
    GlobalVar →₀ Nat :=
  m.exponents.mapDomain (stageVarEmbedding k)

theorem globalExponents_ne_zero {k : Nat} (m : NonconstantMonomial k) :
    m.globalExponents ≠ 0 := by
  have hinjective : Function.Injective (stageVarEmbedding k) := by
    intro i j hij
    apply Fin.ext
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp_all [stageVarEmbedding]
  intro hzero
  apply m.nonzero
  apply Finsupp.mapDomain_injective hinjective
  simpa [globalExponents] using hzero

theorem toGlobal_eq_monomial_globalExponents {k : Nat}
    (m : NonconstantMonomial k) :
    m.toGlobal = monomial m.globalExponents 1 := by
  simp [toGlobal, polynomial, StagePolynomial.toGlobal, globalExponents,
    MvPolynomial.rename_monomial]

end NonconstantMonomial

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The global coefficient-one monomial used as the exponent at index `k`. -/
def exponentGlobal (k : Nat) : GlobalPolynomial :=
  (S.pair k).exponent.toGlobal

theorem exponentGlobal_eq_monomial (k : Nat) :
    S.exponentGlobal k =
      monomial (S.pair k).exponent.globalExponents 1 :=
  (S.pair k).exponent.toGlobal_eq_monomial_globalExponents

/-- W1.3 forbids a nonzero coefficient of the current exponent monomial
from being assembled out of earlier terms carrying the same base. -/
theorem no_currentExponent_linearCombination_of_sameBase
    (n : Nat) (indices : Finset Nat) (coefficients : Nat → Int)
    (constant slope : Int) (hslope : slope ≠ 0)
    (hindices : ∀ j ∈ indices, j < n)
    (hbases : ∀ j ∈ indices, S.baseGlobal j = S.baseGlobal n)
    (hpoly :
      C constant + ∑ j ∈ indices,
          C (coefficients j) * S.exponentGlobal j =
        C slope * S.exponentGlobal n) :
    False := by
  classical
  have hpoly' :
      C constant + ∑ j ∈ indices,
          C (coefficients j) *
            monomial (S.pair j).exponent.globalExponents 1 =
        C slope *
          monomial (S.pair n).exponent.globalExponents 1 := by
    simpa only [← S.exponentGlobal_eq_monomial] using hpoly
  obtain ⟨j, hj, hexponent, _hjcoeff⟩ :=
    exists_matching_monomial_of_linearCombination
      (S.pair n).exponent.globalExponents
      (S.pair n).exponent.globalExponents_ne_zero
      (fun j ↦ (S.pair j).exponent.globalExponents)
      coefficients indices constant slope hslope hpoly'
  have hexponentGlobal :
      S.exponentGlobal j = S.exponentGlobal n := by
    rw [S.exponentGlobal_eq_monomial,
      S.exponentGlobal_eq_monomial, hexponent]
  apply S.w1_noRepeatedPair (Nat.ne_of_lt (hindices j hj))
  constructor
  · have hbase := hbases j hj
    change (S.pair j).base.toGlobal =
      (S.pair n).base.toGlobal at hbase
    rw [hbase]
    exact PolynomialSemEq.refl _
  · change (S.pair j).exponent.toGlobal =
      (S.pair n).exponent.toGlobal at hexponentGlobal
    rw [hexponentGlobal]
    exact PolynomialSemEq.refl _

end GeneratorSequence

end

end Natfunbasis.Wilkie
