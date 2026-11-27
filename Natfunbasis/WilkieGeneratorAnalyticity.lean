import Natfunbasis.OriginalTermAnalyticity
import Natfunbasis.WilkieAnalyticDifferential

/-!
# Analyticity of the canonical Wilkie generators

The triangular W3 recursion is built from integer polynomials and positive
real exponentiation.  This file proves, by strong induction on the generator
index, that every recursively defined auxiliary function has an analytic
extension to a neighborhood of the positive real axis.  Consequently every
member of the concrete coordinate family `Y, tau_1, tau_2, ...` is a
`PositiveAnalyticFunction`.

This is an unconditional analytic-closure result.  It does not assert the
differential-algebraic independence conclusion of Wilkie's Theorem 4.4.
-/

namespace Natfunbasis.Wilkie

open Set

noncomputable section

/-! ## Elementary closure lemmas -/

/-- The identity coordinate on the positive axis is positive analytic. -/
theorem input_isPositiveAnalytic :
    IsPositiveAnalytic (fun y : PositiveReal ↦ y.1) := by
  exact ⟨id, analyticOnNhd_id, fun _ ↦ rfl⟩

namespace IsPositiveAnalytic

/-- Positive-axis analytic functions are closed under addition. -/
theorem add {f g : PositiveReal → Real}
    (hf : IsPositiveAnalytic f) (hg : IsPositiveAnalytic g) :
    IsPositiveAnalytic (f + g) :=
  positiveAnalyticSubalgebra.add_mem hf hg

/-- Positive-axis analytic functions are closed under multiplication. -/
theorem mul {f g : PositiveReal → Real}
    (hf : IsPositiveAnalytic f) (hg : IsPositiveAnalytic g) :
    IsPositiveAnalytic (f * g) :=
  positiveAnalyticSubalgebra.mul_mem hf hg

/-- Every constant real-valued function is positive analytic. -/
theorem const (c : Real) :
    IsPositiveAnalytic (fun _ : PositiveReal ↦ c) :=
  positiveAnalyticSubalgebra.algebraMap_mem c

/-- Positive real exponentiation preserves positive-axis analyticity when
the base function is everywhere positive. -/
theorem rpow {f g : PositiveReal → Real}
    (hf : IsPositiveAnalytic f) (hg : IsPositiveAnalytic g)
    (hfPositive : ∀ y, 0 < f y) :
    IsPositiveAnalytic (fun y ↦ Real.rpow (f y) (g y)) := by
  obtain ⟨F, hF, hFrestrict⟩ := hf
  obtain ⟨G, hG, hGrestrict⟩ := hg
  let H : Real → Real := fun x ↦ Real.exp (Real.log (F x) * G x)
  have hFPositiveOn : ∀ x ∈ positiveAxis, 0 < F x := by
    intro x hx
    let y : PositiveReal := ⟨x, hx⟩
    rw [← hFrestrict y]
    exact hfPositive y
  have hlogF :
      AnalyticOnNhd Real (fun x ↦ Real.log (F x)) positiveAxis := by
    intro x hx
    exact (analyticAt_log (hFPositiveOn x hx)).comp (hF x hx)
  have hH : AnalyticOnNhd Real H positiveAxis := by
    exact (hlogF.mul hG).rexp
  refine ⟨H, hH, ?_⟩
  intro y
  change (f y) ^ (g y) =
    Real.exp (Real.log (F y.1) * G y.1)
  rw [Real.rpow_def_of_pos (hfPositive y),
    hFrestrict y, hGrestrict y]

end IsPositiveAnalytic

/-! ## The differential equation for the power extension -/

/-- The analytic extension used for a positive real power `F ^ G`. -/
def positiveRpowExtension (F G : Real → Real) : Real → Real :=
  fun x ↦ Real.exp (Real.log (F x) * G x)

/-- The chain/product-rule calculation behind the differential equation for
Wilkie's generators.  On any region where `F` is positive,
`positiveRpowExtension F G` is the ordinary real power `F ^ G`.

The displayed logarithmic derivative is the form used in the induction of
Wilkie's Theorem 4.4. -/
theorem hasDerivAt_positiveRpowExtension {F G : Real → Real} {x : Real}
    (hF : DifferentiableAt Real F x) (hG : DifferentiableAt Real G x)
    (hFne : F x ≠ 0) :
    HasDerivAt (positiveRpowExtension F G)
      (positiveRpowExtension F G x *
        (((F x)⁻¹ * deriv F x) * G x +
          Real.log (F x) * deriv G x)) x := by
  have hlogF : HasDerivAt (fun z ↦ Real.log (F z))
      ((F x)⁻¹ * deriv F x) x :=
    (Real.hasDerivAt_log hFne).comp x hF.hasDerivAt
  have hproduct := hlogF.mul hG.hasDerivAt
  change HasDerivAt (fun z ↦ Real.exp (Real.log (F z) * G z))
    (Real.exp (Real.log (F x) * G x) *
      (((F x)⁻¹ * deriv F x) * G x +
        Real.log (F x) * deriv G x)) x
  simpa only [Pi.mul_apply] using hproduct.exp

/-- Derivative form of `hasDerivAt_positiveRpowExtension`. -/
theorem deriv_positiveRpowExtension {F G : Real → Real} {x : Real}
    (hF : DifferentiableAt Real F x) (hG : DifferentiableAt Real G x)
    (hFne : F x ≠ 0) :
    deriv (positiveRpowExtension F G) x =
      positiveRpowExtension F G x *
        (((F x)⁻¹ * deriv F x) * G x +
          Real.log (F x) * deriv G x) :=
  (hasDerivAt_positiveRpowExtension hF hG hFne).deriv

/-- Denominator-free form of the same equation.  This is the ring identity
convenient when the analytic functions are embedded into their differential
fraction field. -/
theorem mul_deriv_positiveRpowExtension {F G : Real → Real} {x : Real}
    (hF : DifferentiableAt Real F x) (hG : DifferentiableAt Real G x)
    (hFne : F x ≠ 0) :
    F x * deriv (positiveRpowExtension F G) x =
      positiveRpowExtension F G x *
        (deriv F x * G x +
          F x * Real.log (F x) * deriv G x) := by
  rw [deriv_positiveRpowExtension hF hG hFne]
  field_simp

/-! ## Polynomial substitution preserves analyticity -/

/-- Evaluating an integer stage polynomial at positive-analytic coordinate
functions gives another positive-analytic function. -/
theorem StagePolynomial.evalReal_isPositiveAnalytic {k : Nat}
    (p : StagePolynomial k) (assignment : StageVar k → PositiveReal → Real)
    (hassignment : ∀ i, IsPositiveAnalytic (assignment i)) :
    IsPositiveAnalytic
      (fun y ↦ p.evalReal (fun i ↦ assignment i y)) := by
  induction p using MvPolynomial.induction_on with
  | C coefficient =>
      convert IsPositiveAnalytic.const (coefficient : Real) using 1
      funext y
      change
        MvPolynomial.eval₂Hom (Int.castRingHom Real)
            (fun i ↦ assignment i y)
            (coefficient : StagePolynomial k) =
          (coefficient : Real)
      simp
  | add p q hp hq =>
      convert hp.add hq using 1
      funext y
      simp [StagePolynomial.evalReal]
  | mul_X p i hp =>
      convert hp.mul (hassignment i) using 1
      funext y
      simp [StagePolynomial.evalReal]

/-! ## Strong induction along the triangular W3 recursion -/

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Every recursively defined W3 auxiliary function is positive analytic.
The proof uses only triangularity, positivity of W1 bases, and the defining
W3 recursion. -/
theorem realTau_isPositiveAnalytic (k : Nat) :
    IsPositiveAnalytic (S.realTau k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hassignment (stage : Nat) (hstage : stage ≤ k) :
          ∀ i : StageVar stage,
            IsPositiveAnalytic
              (fun y ↦ recursiveAssignment S.realTau stage y i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact input_isPositiveAnalytic
        · intro j
          exact ih j.1 (j.2.trans_le hstage)
      have hbase : IsPositiveAnalytic
          (fun y ↦ (S.pair k).base.polynomial.evalReal
            (recursiveAssignment S.realTau (S.pair k).baseStage y)) :=
        (S.pair k).base.polynomial.evalReal_isPositiveAnalytic _
          (hassignment (S.pair k).baseStage (S.pair k).baseStage_le)
      have hexponent : IsPositiveAnalytic
          (fun y ↦ (S.pair k).exponent.polynomial.evalReal
            (recursiveAssignment S.realTau (S.pair k).exponentStage y)) :=
        (S.pair k).exponent.polynomial.evalReal_isPositiveAnalytic _
          (hassignment (S.pair k).exponentStage
            (S.pair k).exponentStage_le)
      have hbasePositive : ∀ y : PositiveReal,
          0 < (S.pair k).base.polynomial.evalReal
            (recursiveAssignment S.realTau (S.pair k).baseStage y) := by
        intro y
        apply (S.pair k).base.positiveOnOrthant
        intro i
        refine Fin.cases y.2 ?_ i
        intro j
        exact S.canonicalRealization.tau_pos j.1 y
      have hpower := hbase.rpow hexponent hbasePositive
      rw [show S.realTau k =
        (fun y ↦ Real.rpow
          ((S.pair k).base.polynomial.evalReal
            (recursiveAssignment S.realTau (S.pair k).baseStage y))
          ((S.pair k).exponent.polynomial.evalReal
            (recursiveAssignment S.realTau (S.pair k).exponentStage y))) by
              funext y
              exact S.realTau_eq k y]
      exact hpower

/-- The `k`th recursively defined generator, bundled in the analytic
function domain used to construct Wilkie's differential field. -/
def realTauAnalyticFunction (k : Nat) : PositiveAnalyticFunction :=
  ⟨S.realTau k, S.realTau_isPositiveAnalytic k⟩

@[simp]
theorem realTauAnalyticFunction_apply (k : Nat) (y : PositiveReal) :
    (S.realTauAnalyticFunction k).1 y = S.realTau k y :=
  rfl

end GeneratorSequence

/-! ## The concrete canonical family -/

/-- Every auxiliary function in the concrete equality-based generator
sequence is positive analytic. -/
theorem canonicalRealTau_isPositiveAnalytic (k : Nat) :
    IsPositiveAnalytic (canonicalGeneratorSequence.realTau k) :=
  canonicalGeneratorSequence.realTau_isPositiveAnalytic k

/-- Every member of the concrete real coordinate family is positive
analytic. -/
theorem canonicalRealCoordinates_isPositiveAnalytic (i : Nat) :
    IsPositiveAnalytic (canonicalRealCoordinates i) := by
  cases i with
  | zero => exact input_isPositiveAnalytic
  | succ k => exact canonicalRealTau_isPositiveAnalytic k

/-- The complete canonical coordinate family, bundled in the analytic
function domain. -/
def canonicalAnalyticCoordinates (i : Nat) : PositiveAnalyticFunction :=
  ⟨canonicalRealCoordinates i,
    canonicalRealCoordinates_isPositiveAnalytic i⟩

@[simp]
theorem canonicalAnalyticCoordinates_apply (i : Nat) (y : PositiveReal) :
    (canonicalAnalyticCoordinates i).1 y = canonicalRealCoordinates i y :=
  rfl

end

end Natfunbasis.Wilkie
