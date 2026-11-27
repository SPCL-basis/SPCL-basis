import Natfunbasis.WilkieBeforeTauPolynomialCoordinates
import Natfunbasis.WilkieConstantBasePrimes

/-!
# Polynomial reification of finite structured primitives

Immediately before adjoining `tau_n`, every ingredient of a flattened
`PrimitiveCoefficients n (n + 1)` expression is a polynomial in the actual
generator set `beforeTauGenerators n`.  Constant W1 logarithms become real
scalar coefficients; all nonconstant W1 logarithms become variables.  A tau
primitive is the product of its already-reified exponent and base logarithm.

This file records the constructions and their exact evaluation laws.  It
does not perform coefficient extraction.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial
open scoped BigOperators

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The distinguished `log x` generator, regarded as an index in the
pre-`tau_n` generator set. -/
def beforeTauLogXIndex (n : Nat) : S.beforeTauGenerators n :=
  ⟨OneVariableBaseField.logX, S.logX_mem_beforeTauGenerators n⟩

@[simp]
theorem coe_beforeTauLogXIndex (n : Nat) :
    ((S.beforeTauLogXIndex n : S.beforeTauGenerators n) : K) =
      OneVariableBaseField.logX :=
  rfl

/-- Polynomial representative of the logarithm of the W1 base at `j`, in
the pre-`tau_n` generator variables.  A constant base contributes the real
scalar `log p`; every nonconstant base logarithm is an actual variable. -/
def beforeTauLogPolynomial (n j : Nat) (hj : j ≤ n) :
    MvPolynomial (S.beforeTauGenerators n) Real := by
  classical
  exact if hconstant : S.IsConstantBase j then
      C (Real.log (S.constantBasePrime hconstant : Real))
    else
      X (S.beforeTauLogIndex hj hconstant)

/-- Exact evaluation law for a reified W1-base logarithm. -/
theorem aeval_beforeTauLogPolynomial (n j : Nat) (hj : j ≤ n) :
    MvPolynomial.aeval
        ((↑) : S.beforeTauGenerators n → K)
        (S.beforeTauLogPolynomial n j hj) =
      ι (S.logBaseAnalytic j) := by
  by_cases hconstant : S.IsConstantBase j
  · rw [beforeTauLogPolynomial, dif_pos hconstant,
      MvPolynomial.aeval_C,
      S.logBaseAnalytic_eq_constantBasePrime hconstant]
    exact (IsScalarTower.algebraMap_apply Real A K _).symm
  · rw [beforeTauLogPolynomial, dif_neg hconstant,
      MvPolynomial.aeval_X, S.coe_beforeTauLogIndex]

/-- Polynomial representative of `tauPrimitive j = exponent_j * log(base_j)`
in the pre-`tau_n` generator variables. -/
def beforeTauTauPrimitivePolynomial (n j : Nat) (hj : j ≤ n) :
    MvPolynomial (S.beforeTauGenerators n) Real :=
  S.beforeTauExponentPolynomial n j hj *
    S.beforeTauLogPolynomial n j hj

/-- Exact evaluation law for a reified tau primitive. -/
theorem aeval_beforeTauTauPrimitivePolynomial (n j : Nat) (hj : j ≤ n) :
    MvPolynomial.aeval
        ((↑) : S.beforeTauGenerators n → K)
        (S.beforeTauTauPrimitivePolynomial n j hj) =
      (S.tauPrimitive j : K) := by
  rw [beforeTauTauPrimitivePolynomial, map_mul,
    S.aeval_beforeTauExponentPolynomial,
    S.aeval_beforeTauLogPolynomial]
  rfl

/-- The real polynomial representing the complete flattened pre-`tau_n`
primitive expression encoded by `C`. -/
def beforeTauPrimitiveCoefficientsPolynomial (n : Nat)
    (coeffs : S.PrimitiveCoefficients n (n + 1)) :
    MvPolynomial (S.beforeTauGenerators n) Real :=
  C coeffs.constantCoeff +
    C (coeffs.logXCoeff : Real) * X (S.beforeTauLogXIndex n) +
    ∑ j : Fin n,
      C (coeffs.tauCoeff j : Real) *
        S.beforeTauTauPrimitivePolynomial n j.1 (Nat.le_of_lt j.2) +
    ∑ j : Fin (n + 1),
      C (coeffs.freshLogCoeff j : Real) *
        S.beforeTauLogPolynomial n j.1 (Nat.lt_succ_iff.mp j.2)

/-- Evaluation of the full reified polynomial is exactly
`PrimitiveCoefficients.evaluate`. -/
theorem aeval_beforeTauPrimitiveCoefficientsPolynomial (n : Nat)
    (coeffs : S.PrimitiveCoefficients n (n + 1)) :
    MvPolynomial.aeval
        ((↑) : S.beforeTauGenerators n → K)
        (S.beforeTauPrimitiveCoefficientsPolynomial n coeffs) =
      coeffs.evaluate := by
  simp only [beforeTauPrimitiveCoefficientsPolynomial,
    PrimitiveCoefficients.evaluate, map_add, map_mul, map_sum,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    S.coe_beforeTauLogXIndex,
    S.aeval_beforeTauTauPrimitivePolynomial,
    S.aeval_beforeTauLogPolynomial]
  simp only [map_intCast]

end GeneratorSequence

end

end Natfunbasis.Wilkie
