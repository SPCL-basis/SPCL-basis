import Natfunbasis.WilkieFreshBaseExclusion

/-!
# Recovering W1 base presentations from logarithm coordinates

For positive substituted bases, equality of their analytic logarithms implies
equality of the bases.  Finite-coordinate algebraic independence then
reflects that analytic equality back to equality of the original global
integer-polynomial presentations.  This is the bridge from coefficient
matching in Wilkie's primitive identity to the base half of W1.3.
-/

namespace Natfunbasis.Wilkie

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Equality of positive analytic logarithms recovers equality of the
underlying substituted bases. -/
theorem baseAnalytic_eq_of_logBaseAnalytic_eq {i j : Nat}
    (hlog : S.logBaseAnalytic i = S.logBaseAnalytic j) :
    S.baseAnalytic i = S.baseAnalytic j := by
  apply Subtype.ext
  funext y
  have hpoint := congrArg (fun f : A ↦ f.1 y) hlog
  change Real.log ((S.baseAnalytic i).1 y) =
    Real.log ((S.baseAnalytic j).1 y) at hpoint
  exact Real.log_injOn_pos
    (S.baseAnalytic_pos i y) (S.baseAnalytic_pos j y) hpoint

/-- Equality after embedding the logarithms in the analytic fraction field
also recovers equality of the bundled bases. -/
theorem baseAnalytic_eq_of_logBaseFraction_eq {i j : Nat}
    (hlog : ι (S.logBaseAnalytic i) = ι (S.logBaseAnalytic j)) :
    S.baseAnalytic i = S.baseAnalytic j := by
  apply S.baseAnalytic_eq_of_logBaseAnalytic_eq
  exact IsFractionRing.injective A K hlog

/-- Under labeled finite-coordinate independence, equality of two
substituted bases reflects to equality of their global polynomial
presentations. -/
theorem baseGlobal_eq_of_baseAnalytic_eq {i j n : Nat}
    (hi : i ≤ n) (hj : j ≤ n)
    (hcoord : AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r)))
    (hbase : S.baseAnalytic i = S.baseAnalytic j) :
    S.baseGlobal i = S.baseGlobal j := by
  have heval :
      S.stagePolynomialEval n (S.basePolynomialAtStage n i hi) =
        S.stagePolynomialEval n (S.basePolynomialAtStage n j hj) := by
    rw [S.stagePolynomialEval_basePolynomialAtStage,
      S.stagePolynomialEval_basePolynomialAtStage, hbase]
  have hpoly :=
    S.stagePolynomialEval_injective_of_algebraicIndependent hcoord heval
  calc
    S.baseGlobal i =
        (S.basePolynomialAtStage n i hi).toGlobal :=
      (S.basePolynomialAtStage_toGlobal n i hi).symm
    _ = (S.basePolynomialAtStage n j hj).toGlobal := by rw [hpoly]
    _ = S.baseGlobal j := S.basePolynomialAtStage_toGlobal n j hj

/-- The form used after a logarithm-variable coefficient match. -/
theorem baseGlobal_eq_of_logBaseFraction_eq {i j n : Nat}
    (hi : i ≤ n) (hj : j ≤ n)
    (hcoord : AlgebraicIndependent Real
      (fun r : StageVar n ↦ ι (S.analyticAssignment n r)))
    (hlog : ι (S.logBaseAnalytic i) = ι (S.logBaseAnalytic j)) :
    S.baseGlobal i = S.baseGlobal j :=
  S.baseGlobal_eq_of_baseAnalytic_eq hi hj hcoord
    (S.baseAnalytic_eq_of_logBaseFraction_eq hlog)

end GeneratorSequence

end

end Natfunbasis.Wilkie
