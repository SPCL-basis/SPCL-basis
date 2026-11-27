import Natfunbasis.WilkieAnalyticPowerDifferential

/-!
# Differential equations for the W3 generators

This module bundles the base and exponent polynomials at each stage of a
triangular Wilkie generator sequence as positive-axis analytic functions.  It
then specializes the generic logarithm/power calculus to the defining W3
equation.  Thus the analytic fraction field contains elements `u_k`, `s_k`,
`tau_k`, and `log u_k` satisfying the exact logarithmic differential equation
used in Wilkie's Theorem 4.4.

No transcendence or algebraic-independence statement is used.
-/

namespace Natfunbasis.Wilkie

noncomputable section

namespace StagePolynomial

/-- Evaluation of a bundled analytic function at one positive-real point,
as a ring homomorphism. -/
def analyticEvaluation (y : PositiveReal) :
    PositiveAnalyticFunction →+* Real :=
  (Pi.evalRingHom (fun _ : PositiveReal ↦ Real) y).comp
    positiveAnalyticSubalgebra.val.toRingHom

@[simp]
theorem analyticEvaluation_apply (y : PositiveReal)
    (f : PositiveAnalyticFunction) :
    analyticEvaluation y f = f.1 y :=
  rfl

/-- Evaluate a stage polynomial in bundled positive-axis analytic
functions. -/
def evalAnalytic {k : Nat} (p : StagePolynomial k)
    (assignment : StageVar k → PositiveAnalyticFunction) :
    PositiveAnalyticFunction :=
  MvPolynomial.eval₂ (Int.castRingHom PositiveAnalyticFunction)
    assignment p

@[simp]
theorem evalAnalytic_apply {k : Nat} (p : StagePolynomial k)
    (assignment : StageVar k → PositiveAnalyticFunction)
    (y : PositiveReal) :
    (p.evalAnalytic assignment).1 y =
      p.evalReal (fun i ↦ (assignment i).1 y) := by
  change analyticEvaluation y (p.evalAnalytic assignment) = _
  rw [evalAnalytic, MvPolynomial.hom_eval₂]
  change MvPolynomial.eval₂
      ((analyticEvaluation y).comp
        (Int.castRingHom PositiveAnalyticFunction))
      (fun i ↦ (assignment i).1 y) p = _
  congr 2

end StagePolynomial

/-- The original input coordinate, bundled as a positive-axis analytic
function. -/
def inputAnalyticFunction : PositiveAnalyticFunction :=
  ⟨fun y ↦ y.1, input_isPositiveAnalytic⟩

@[simp]
theorem inputAnalyticFunction_apply (y : PositiveReal) :
    inputAnalyticFunction.1 y = y.1 :=
  rfl

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The bundled analytic assignment available at stage `k`: the original
input followed by the already constructed generators. -/
def analyticAssignment (k : Nat) :
    StageVar k → PositiveAnalyticFunction :=
  Fin.cases inputAnalyticFunction
    (fun j ↦ S.realTauAnalyticFunction j.1)

@[simp]
theorem analyticAssignment_zero (k : Nat) :
    S.analyticAssignment k 0 = inputAnalyticFunction :=
  rfl

@[simp]
theorem analyticAssignment_succ {k : Nat} (j : Fin k) :
    S.analyticAssignment k j.succ = S.realTauAnalyticFunction j.1 :=
  rfl

@[simp]
theorem analyticAssignment_apply (k : Nat) (i : StageVar k)
    (y : PositiveReal) :
    (S.analyticAssignment k i).1 y =
      recursiveAssignment S.realTau k y i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Wilkie's `u_k`: the positive irreducible base after substitution of all
earlier generators. -/
def baseAnalytic (k : Nat) : PositiveAnalyticFunction :=
  (S.pair k).base.polynomial.evalAnalytic
    (S.analyticAssignment (S.pair k).baseStage)

/-- Wilkie's `s_k`: the nonconstant monomial exponent after substitution of
all earlier generators. -/
def exponentAnalytic (k : Nat) : PositiveAnalyticFunction :=
  (S.pair k).exponent.polynomial.evalAnalytic
    (S.analyticAssignment (S.pair k).exponentStage)

@[simp]
theorem baseAnalytic_apply (k : Nat) (y : PositiveReal) :
    (S.baseAnalytic k).1 y =
      (S.pair k).base.polynomial.evalReal
        (recursiveAssignment S.realTau (S.pair k).baseStage y) := by
  simp [baseAnalytic]

@[simp]
theorem exponentAnalytic_apply (k : Nat) (y : PositiveReal) :
    (S.exponentAnalytic k).1 y =
      (S.pair k).exponent.polynomial.evalReal
        (recursiveAssignment S.realTau (S.pair k).exponentStage y) := by
  simp [exponentAnalytic]

/-- Every substituted W1 base remains strictly positive. -/
theorem baseAnalytic_pos (k : Nat) (y : PositiveReal) :
    0 < (S.baseAnalytic k).1 y := by
  rw [baseAnalytic_apply]
  apply (S.pair k).base.positiveOnOrthant
  intro i
  refine Fin.cases y.2 ?_ i
  intro j
  exact S.canonicalRealization.tau_pos j.1 y

/-- Every substituted W1 exponent monomial is strictly positive. -/
theorem exponentAnalytic_pos (k : Nat) (y : PositiveReal) :
    0 < (S.exponentAnalytic k).1 y := by
  rw [exponentAnalytic_apply]
  apply (S.pair k).exponent.evalReal_pos
  intro i
  refine Fin.cases y.2 ?_ i
  intro j
  exact S.canonicalRealization.tau_pos j.1 y

/-- The bundled W3 generator is literally the bundled positive real power of
its substituted base by its substituted exponent. -/
theorem realTauAnalyticFunction_eq_rpow (k : Nat) :
    S.realTauAnalyticFunction k =
      PositiveAnalyticFunction.rpow (S.baseAnalytic k)
        (S.exponentAnalytic k) (S.baseAnalytic_pos k) := by
  apply Subtype.ext
  funext y
  simp only [realTauAnalyticFunction_apply,
    PositiveAnalyticFunction.rpow_apply, baseAnalytic_apply,
    exponentAnalytic_apply]
  exact S.realTau_eq k y

/-- Wilkie's `log u_k`, bundled in the analytic-function domain. -/
def logBaseAnalytic (k : Nat) : PositiveAnalyticFunction :=
  PositiveAnalyticFunction.log (S.baseAnalytic k) (S.baseAnalytic_pos k)

@[simp]
theorem logBaseAnalytic_apply (k : Nat) (y : PositiveReal) :
    (S.logBaseAnalytic k).1 y = Real.log ((S.baseAnalytic k).1 y) :=
  rfl

end GeneratorSequence

namespace PositiveAnalyticFractionField

local notation "ι" =>
  (algebraMap PositiveAnalyticFunction PositiveAnalyticFractionField)

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Field-level logarithmic derivative of a substituted W1 base. -/
theorem derivation_logBaseAnalytic (k : Nat) :
    derivation (ι (S.logBaseAnalytic k)) =
      derivation (ι (S.baseAnalytic k)) / ι (S.baseAnalytic k) := by
  exact derivation_log (S.baseAnalytic k) (S.baseAnalytic_pos k)

/-- The exact field-level W3 differential equation

`tau_k' = tau_k * (s_k' log u_k + s_k u_k' / u_k)`.

This is the analytic equation fed into the exponential-extension case of
Wilkie's differential-algebra induction. -/
theorem derivation_realTauAnalyticFunction (k : Nat) :
    derivation (ι (S.realTauAnalyticFunction k)) =
      ι (S.realTauAnalyticFunction k) *
        (derivation (ι (S.exponentAnalytic k)) *
            ι (S.logBaseAnalytic k) +
          ι (S.exponentAnalytic k) *
              derivation (ι (S.baseAnalytic k)) /
            ι (S.baseAnalytic k)) := by
  rw [S.realTauAnalyticFunction_eq_rpow k]
  exact derivation_rpow (S.baseAnalytic k) (S.exponentAnalytic k)
    (S.baseAnalytic_pos k)

end PositiveAnalyticFractionField

end

end Natfunbasis.Wilkie
