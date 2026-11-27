import Natfunbasis.PowerBranchEvaluation
import Natfunbasis.WilkieFreshBases
import Natfunbasis.WilkieOneVariableBaseField

/-!
# Field relations among Wilkie generator bases

This file connects the literal common-polynomial bookkeeping of
`WilkieFreshBases` with the analytic differential field.  It proves that
equal global base presentations define equal bundled analytic functions and
that stage-polynomial substitutions lie in every intermediate field which
contains the input coordinate and the required earlier generators.

These are algebraic membership facts.  No transcendence or algebraic
independence statement is used.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Literal equality of global base polynomials gives equality of their
bundled analytic substitutions, even when the two presentations use
different finite stages. -/
theorem baseAnalytic_eq_of_baseGlobal_eq {i j : Nat}
    (h : S.baseGlobal i = S.baseGlobal j) :
    S.baseAnalytic i = S.baseAnalytic j := by
  apply Subtype.ext
  funext y
  rw [S.baseAnalytic_apply, S.baseAnalytic_apply]
  apply evalReal_eq_of_toGlobal_eq S.canonicalRealization y
  simpa [baseGlobal, Base.toGlobal] using h

/-- Equal base polynomials also give equal chosen logarithms. -/
theorem logBaseAnalytic_eq_of_baseGlobal_eq {i j : Nat}
    (h : S.baseGlobal i = S.baseGlobal j) :
    S.logBaseAnalytic i = S.logBaseAnalytic j := by
  apply Subtype.ext
  funext y
  rw [S.logBaseAnalytic_apply, S.logBaseAnalytic_apply,
    S.baseAnalytic_eq_of_baseGlobal_eq h]

/-- A constant global base evaluates to the corresponding bundled real
constant. -/
theorem baseAnalytic_eq_const {k : Nat} {c : Int}
    (hc : S.baseGlobal k = C c) :
    S.baseAnalytic k = algebraMap Real A (c : Real) := by
  apply Subtype.ext
  funext y
  rw [S.baseAnalytic_apply]
  let q : StagePolynomial 0 := C c
  have hglobal : (S.pair k).base.polynomial.toGlobal = q.toGlobal := by
    simpa [q, StagePolynomial.toGlobal, baseGlobal, Base.toGlobal] using hc
  have heval := evalReal_eq_of_toGlobal_eq S.canonicalRealization y hglobal
  calc
    (S.pair k).base.polynomial.evalReal
          (recursiveAssignment S.realTau (S.pair k).baseStage y) =
        q.evalReal (recursiveAssignment S.realTau 0 y) := by
      simpa [GeneratorSequence.canonicalRealization] using heval
    _ = (c : Real) := by
      change StagePolynomial.evalReal (C c : StagePolynomial 0)
        (recursiveAssignment S.realTau 0 y) = (c : Real)
      rw [StagePolynomial.evalReal, MvPolynomial.eval₂_C]
      rfl

/-- The logarithm of a constant base is a real scalar in the analytic
fraction field. -/
theorem logBase_mem_of_isConstantBase
    (F : DifferentialIntermediateField Real K) {k : Nat}
    (hconstant : S.IsConstantBase k) :
    ι (S.logBaseAnalytic k) ∈ F := by
  obtain ⟨c, hc⟩ := hconstant
  have hlogA : S.logBaseAnalytic k =
      algebraMap Real A (Real.log (c : Real)) := by
    apply Subtype.ext
    funext y
    rw [S.logBaseAnalytic_apply, S.baseAnalytic_eq_const hc]
    rfl
  have hlog : ι (S.logBaseAnalytic k) =
      algebraMap Real K (Real.log (c : Real)) := by
    rw [hlogA]
    exact IsScalarTower.algebraMap_apply Real A K _
  rw [hlog]
  exact F.algebraMap_mem _

/-- An original-variable base evaluates to the bundled input coordinate. -/
theorem baseAnalytic_eq_input_of_isOriginalBase {k : Nat}
    (horiginal : S.IsOriginalBase k) :
    S.baseAnalytic k = inputAnalyticFunction := by
  apply Subtype.ext
  funext y
  rw [S.baseAnalytic_apply]
  let q : StagePolynomial 0 := X 0
  have hglobal : (S.pair k).base.polynomial.toGlobal = q.toGlobal := by
    calc
      (S.pair k).base.polynomial.toGlobal = originalPolynomial := by
        simpa [IsOriginalBase, baseGlobal, Base.toGlobal] using horiginal
      _ = q.toGlobal := by
        simp [q, StagePolynomial.toGlobal, originalPolynomial]
  have heval := evalReal_eq_of_toGlobal_eq S.canonicalRealization y hglobal
  simpa [GeneratorSequence.canonicalRealization, q,
    StagePolynomial.evalReal] using heval

/-- The logarithm of an original-variable base is the distinguished `logX`
element of the initial field. -/
theorem logBase_eq_logX_of_isOriginalBase {k : Nat}
    (horiginal : S.IsOriginalBase k) :
    ι (S.logBaseAnalytic k) = OneVariableBaseField.logX := by
  apply congrArg ι
  apply Subtype.ext
  funext y
  rw [S.logBaseAnalytic_apply,
    S.baseAnalytic_eq_input_of_isOriginalBase horiginal]
  rfl

/-- Evaluation of an integer stage polynomial belongs to any intermediate
field containing all substituted coordinates. -/
theorem evalAnalytic_mem
    (F : DifferentialIntermediateField Real K) {stage : Nat}
    (p : StagePolynomial stage)
    (hassignment : ∀ i : StageVar stage,
      ι (S.analyticAssignment stage i) ∈ F) :
    ι (p.evalAnalytic (S.analyticAssignment stage)) ∈ F := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [StagePolynomial.evalAnalytic, MvPolynomial.eval₂_C]
      change ι ((c : Int) : A) ∈ F
      convert F.algebraMap_mem (c : Real) using 1
      all_goals simp [IsScalarTower.algebraMap_apply Real A K]
  | add p q hp hq =>
      simpa [StagePolynomial.evalAnalytic] using add_mem hp hq
  | mul_X p i hp =>
      simpa [StagePolynomial.evalAnalytic] using
        mul_mem hp (hassignment i)

/-- The substituted W1 base at stage `k` belongs to every field containing
`x` and all earlier W3 generators. -/
theorem baseAnalytic_mem
    (F : DifferentialIntermediateField Real K) {k : Nat}
    (hx : OneVariableBaseField.x ∈ F)
    (htau : ∀ j < k, ι (S.realTauAnalyticFunction j) ∈ F) :
    ι (S.baseAnalytic k) ∈ F := by
  apply S.evalAnalytic_mem F
  intro i
  refine Fin.cases ?_ ?_ i
  · exact hx
  · intro j
    exact htau j.1 (j.2.trans_le (S.pair k).baseStage_le)

/-- The substituted W1 exponent at stage `k` belongs to every field
containing `x` and all earlier W3 generators. -/
theorem exponentAnalytic_mem
    (F : DifferentialIntermediateField Real K) {k : Nat}
    (hx : OneVariableBaseField.x ∈ F)
    (htau : ∀ j < k, ι (S.realTauAnalyticFunction j) ∈ F) :
    ι (S.exponentAnalytic k) ∈ F := by
  apply S.evalAnalytic_mem F
  intro i
  refine Fin.cases ?_ ?_ i
  · exact hx
  · intro j
    exact htau j.1 (j.2.trans_le (S.pair k).exponentStage_le)

/-- If a field contains `log x` and the logarithms of all fresh bases up to
`k`, it contains the logarithm of the base at `k`.  Constant, original, and
repeated bases are discharged by the V0/V1/V2 classification. -/
theorem logBaseAnalytic_mem_of_fresh_le
    (F : DifferentialIntermediateField Real K) {k : Nat}
    (hlogX : OneVariableBaseField.logX ∈ F)
    (hfresh : ∀ j ≤ k, S.IsFreshBase j →
      ι (S.logBaseAnalytic j) ∈ F) :
    ι (S.logBaseAnalytic k) ∈ F := by
  rcases S.constant_original_fresh_or_repeated k with
      hconstant | horiginal | hfreshk | hrepeated
  · exact S.logBase_mem_of_isConstantBase F hconstant
  · rw [S.logBase_eq_logX_of_isOriginalBase horiginal]
    exact hlogX
  · exact hfresh k le_rfl hfreshk
  · obtain ⟨j, ⟨hj, hjfresh, hbase⟩, -⟩ := hrepeated
    rw [← S.logBaseAnalytic_eq_of_baseGlobal_eq hbase]
    exact hfresh j hj.le hjfresh

end GeneratorSequence

end

end Natfunbasis.Wilkie
