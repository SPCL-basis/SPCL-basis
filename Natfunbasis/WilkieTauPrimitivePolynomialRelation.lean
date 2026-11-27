import Natfunbasis.WilkiePrimitivePolynomialReification

/-!
# Polynomial form of a Wilkie primitive relation

This file turns an equality in the analytic fraction field into an equality
of real multivariate polynomials in the algebraically-independent pre-`tau`
generators.  Coefficient extraction is kept in downstream files.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- A relation between a nonzero multiple of the current tau primitive and
a flattened structured primitive reflects to an exact polynomial identity. -/
theorem beforeTau_polynomial_relation_of_primitiveCoefficients_relation
    {n : Nat} (hbefore : AlgebraicIndepOn Real id
      (S.beforeTauGenerators n))
    (m : Int) (c : Real)
    (coeffs : S.PrimitiveCoefficients n (n + 1))
    (hrelation :
      (m : K) * (S.tauPrimitive n : K) =
        algebraMap Real K c + coeffs.evaluate) :
    C (m : Real) * S.beforeTauTauPrimitivePolynomial n n le_rfl =
      C c + S.beforeTauPrimitiveCoefficientsPolynomial n coeffs := by
  change AlgebraicIndependent Real
    ((↑) : S.beforeTauGenerators n → K) at hbefore
  apply (algebraicIndependent_iff_injective_aeval.mp hbefore)
  rw [map_mul, MvPolynomial.aeval_C,
    S.aeval_beforeTauTauPrimitivePolynomial,
    map_add, MvPolynomial.aeval_C,
    S.aeval_beforeTauPrimitiveCoefficientsPolynomial]
  simpa using hrelation

/-- The same reflection starting from the recursive `BeforeTauPrimitive`
predicate rather than already flattened coefficient data. -/
theorem beforeTau_polynomial_relation_of_primitive_relation
    {n : Nat} (hbefore : AlgebraicIndepOn Real id
      (S.beforeTauGenerators n))
    (m : Int) (L : K) (hL : S.BeforeTauPrimitive n L) (c : Real)
    (hrelation :
      (m : K) * (S.tauPrimitive n : K) = algebraMap Real K c + L) :
    ∃ coeffs : S.PrimitiveCoefficients n (n + 1),
      L = coeffs.evaluate ∧
      C (m : Real) * S.beforeTauTauPrimitivePolynomial n n le_rfl =
        C c + S.beforeTauPrimitiveCoefficientsPolynomial n coeffs := by
  obtain ⟨coeffs, hcoeffs⟩ :=
    S.beforeTauPrimitive_exists_coefficients hL
  refine ⟨coeffs, hcoeffs, ?_⟩
  apply S.beforeTau_polynomial_relation_of_primitiveCoefficients_relation
    hbefore m c coeffs
  simpa [hcoeffs] using hrelation

end GeneratorSequence

end

end Natfunbasis.Wilkie
