import Natfunbasis.WilkieBaseRationalClassification
import Natfunbasis.WilkieProposition31Full

/-!
# Integral logarithmic residues in `Real(x)`

This file proves the missing base-field rigidity needed by the integral form
of Wilkie's Proposition 3.1(ii).  The algebraic core is the elementary fact
that the residue at `T = 0` of the logarithmic derivative of a rational
function is its integral order of vanishing, whereas the derivative of a
rational function has residue zero.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.BaseLogRigidity

noncomputable section

open Proposition31

variable {F : Type*} [Field F] [CharZero F]

/-- Multiplication by `X` removes the apparent exceptional case at exponent
zero in the derivative of `X^n u`. -/
lemma X_mul_derivative_pow_mul (n : Nat) (u : F[X]) :
    X * derivative (X ^ n * u) =
      X ^ n * (C (n : F) * u + X * derivative u) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [derivative_mul, derivative_X_pow]
      simp only [Nat.succ_sub_one]
      push_cast
      ring

/-- Factoring the orders of numerator and denominator exposes the integral
residue of their logarithmic derivative. -/
lemma X_mul_logCross_factor
    {p q : F[X]} {i j : Nat}
    (hp : HasExactOrder X i p) (hq : HasExactOrder X j q) :
    ∃ P Q : F[X],
      p = X ^ i * P ∧ q = X ^ j * Q ∧
      ¬ X ∣ P ∧ ¬ X ∣ Q ∧
      X * (derivative p * q - p * derivative q) =
        X ^ (i + j) *
          (C ((i : F) - (j : F)) * P * Q +
            X * (derivative P * Q - P * derivative Q)) := by
  obtain ⟨P, hp, hP⟩ := hp
  obtain ⟨Q, hq, hQ⟩ := hq
  refine ⟨P, Q, hp, hq, hP, hQ, ?_⟩
  rw [hp, hq]
  calc
    X * (derivative (X ^ i * P) * (X ^ j * Q) -
        X ^ i * P * derivative (X ^ j * Q)) =
        (X * derivative (X ^ i * P)) * (X ^ j * Q) -
          (X ^ i * P) * (X * derivative (X ^ j * Q)) := by ring
    _ = _ := by
      rw [X_mul_derivative_pow_mul, X_mul_derivative_pow_mul, pow_add]
      rw [map_sub]
      ring

/-- In particular, `X^(i+j)` divides `X` times the logarithmic cross
numerator. -/
lemma X_pow_add_dvd_X_mul_logCross
    {p q : F[X]} {i j : Nat}
    (hp : HasExactOrder X i p) (hq : HasExactOrder X j q) :
    X ^ (i + j) ∣ X * (derivative p * q - p * derivative q) := by
  obtain ⟨P, Q, -, -, -, -, h⟩ := X_mul_logCross_factor hp hq
  rw [h]
  exact dvd_mul_right _ _

/-- A rational derivative cannot have a pole of order at least two at the
origin when it appears beside logarithmic derivatives.  This is the
pole-order part of the residue argument. -/
lemma denominator_not_dvd_X_of_logarithmic_identity
    (a : F) {p q r s : F[X]}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s)
    (heq :
      X * (derivative p * q - p * derivative q) * s ^ 2 =
        (C a * s ^ 2 + X * (derivative r * s - r * derivative s)) * p * q) :
    ¬ X ∣ s := by
  intro hXs
  obtain ⟨i, hi⟩ := exists_hasExactOrder X irreducible_X hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder X irreducible_X hq0
  obtain ⟨l, hl⟩ := exists_hasExactOrder X irreducible_X hr0
  obtain ⟨e, hs⟩ := exists_hasExactOrder X irreducible_X hs0
  have hepos : 0 < e := hs.pos_of_dvd hXs
  have hlzero : l = 0 := by
    by_contra hl0
    exact prime_X.not_unit <| hrs.isUnit_of_dvd'
      (hl.dvd_base_of_pos (Nat.pos_of_ne_zero hl0)) hXs
  have hr : HasExactOrder X 0 r := by simpa [hlzero] using hl
  let D : Derivation Int F[X] F[X] := derivative'.restrictScalars Int
  have hDX : ¬ X ∣ D X := by
    simp [D, derivative'_apply, X_dvd_iff]
  have hB : HasExactOrder X (e - 1)
      (derivative r * s - r * derivative s) := by
    simpa [D, derivative'_apply] using
      (hasExactOrder_derivCross_of_denominator D prime_X hDX hepos hr hs)
  have hX : HasExactOrder X 1 (X : F[X]) := by
    refine ⟨1, by simp, ?_⟩
    simp [X_dvd_iff]
  have hXB : HasExactOrder X e
      (X * (derivative r * s - r * derivative s)) := by
    have := hX.mul prime_X hB
    simpa [show 1 + (e - 1) = e by omega] using this
  have hs2 : HasExactOrder X (e + e) (s ^ 2) := by
    simpa [pow_two] using hs.mul prime_X hs
  have hCa : X ^ (e + 1) ∣ C a * s ^ 2 := by
    have hpow : (X : F[X]) ^ (e + 1) ∣ X ^ (e + e) :=
      pow_dvd_pow (X : F[X]) (by omega)
    exact dvd_mul_of_dvd_right (hpow.trans hs2.dvd) _
  have hsum : HasExactOrder X e
      (C a * s ^ 2 + X * (derivative r * s - r * derivative s)) := by
    have hneg := hXB.neg
    have := hneg.sub_of_dvd_succ_right hCa
    simpa only [sub_neg_eq_add] using this
  have hright : HasExactOrder X ((e + i) + j)
      ((C a * s ^ 2 + X * (derivative r * s - r * derivative s)) * p * q) :=
    (hsum.mul prime_X hi).mul prime_X hj
  have hXA : X ^ (i + j) ∣
      X * (derivative p * q - p * derivative q) :=
    X_pow_add_dvd_X_mul_logCross hi hj
  have hleftBig : X ^ ((i + j) + (e + e)) ∣
      X * (derivative p * q - p * derivative q) * s ^ 2 := by
    rw [pow_add]
    exact mul_dvd_mul hXA hs2.dvd
  have hnext : X ^ (((e + i) + j) + 1) ∣
      X * (derivative p * q - p * derivative q) * s ^ 2 := by
    exact (pow_dvd_pow X (by omega)).trans hleftBig
  apply hright.not_dvd_succ X_ne_zero
  rw [← heq]
  exact hnext

/-- Once the primitive is regular at the origin, evaluation of the factored
identity computes the slope as the difference between the numerator and
denominator orders of the logarithmic derivative. -/
theorem integer_slope_of_logarithmic_identity_of_regular_primitive
    (a : F) {p q r s : F[X]}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hXs : ¬ X ∣ s)
    (heq :
      X * (derivative p * q - p * derivative q) * s ^ 2 =
        (C a * s ^ 2 + X * (derivative r * s - r * derivative s)) * p * q) :
    ∃ m : Int, a = (m : F) := by
  obtain ⟨i, hi⟩ := exists_hasExactOrder X irreducible_X hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder X irreducible_X hq0
  obtain ⟨P, Q, hp, hq, hP, hQ, hA⟩ := X_mul_logCross_factor hi hj
  let R : F[X] :=
    C ((i : F) - (j : F)) * P * Q +
      X * (derivative P * Q - P * derivative Q)
  have hcancel :
      R * s ^ 2 =
        (C a * s ^ 2 + X * (derivative r * s - r * derivative s)) * P * Q := by
    apply mul_left_cancel₀ (pow_ne_zero (i + j) (X_ne_zero : (X : F[X]) ≠ 0))
    calc
      X ^ (i + j) * (R * s ^ 2) =
          (X ^ (i + j) * R) * s ^ 2 := by ring
      _ = X * (derivative p * q - p * derivative q) * s ^ 2 := by
        rw [← hA]
      _ = (C a * s ^ 2 +
          X * (derivative r * s - r * derivative s)) * p * q := heq
      _ = X ^ (i + j) *
          ((C a * s ^ 2 + X * (derivative r * s - r * derivative s)) *
            P * Q) := by
        rw [hp, hq, pow_add]
        ring
  have hEval := congrArg (Polynomial.eval (0 : F)) hcancel
  have hscalar :
      ((i : F) - (j : F)) *
          (Polynomial.eval 0 P * Polynomial.eval 0 Q *
            (Polynomial.eval 0 s) ^ 2) =
        a * (Polynomial.eval 0 P * Polynomial.eval 0 Q *
          (Polynomial.eval 0 s) ^ 2) := by
    dsimp [R] at hEval
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
      zero_mul, add_zero] at hEval
    convert hEval using 1 <;> ring
  have hP0 : Polynomial.eval (0 : F) P ≠ 0 := by
    intro hzero
    apply hP
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact hzero
  have hQ0 : Polynomial.eval (0 : F) Q ≠ 0 := by
    intro hzero
    apply hQ
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact hzero
  have hsEval0 : Polynomial.eval (0 : F) s ≠ 0 := by
    intro hzero
    apply hXs
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact hzero
  have hfactor : Polynomial.eval (0 : F) P * Polynomial.eval 0 Q *
      (Polynomial.eval 0 s) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hP0 hQ0) (pow_ne_zero 2 hsEval0)
  have ha : (i : F) - (j : F) = a :=
    mul_right_cancel₀ hfactor hscalar
  refine ⟨(i : Int) - (j : Int), ?_⟩
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  exact ha.symm

/-- Rational-coordinate residue theorem.  In a logarithmic-derivative
identity, the coefficient of `1 / X` is an integer. -/
theorem integer_slope_of_logarithmic_identity
    (a : F) {p q r s : F[X]}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s)
    (heq :
      X * (derivative p * q - p * derivative q) * s ^ 2 =
        (C a * s ^ 2 + X * (derivative r * s - r * derivative s)) * p * q) :
    ∃ m : Int, a = (m : F) := by
  by_cases hr0 : r = 0
  · have hbase :
        X * (derivative p * q - p * derivative q) = C a * p * q := by
      apply mul_right_cancel₀ (pow_ne_zero 2 hs0)
      calc
        X * (derivative p * q - p * derivative q) * s ^ 2 =
            (C a * s ^ 2 + X * (derivative r * s - r * derivative s)) *
              p * q := heq
        _ = (C a * p * q) * s ^ 2 := by
          rw [hr0, derivative_zero]
          ring
    apply integer_slope_of_logarithmic_identity_of_regular_primitive
      (r := 0) (s := 1) a hp0 hq0 (by simp [X_dvd_iff])
    simpa using hbase
  · exact integer_slope_of_logarithmic_identity_of_regular_primitive
      a hp0 hq0
      (denominator_not_dvd_X_of_logarithmic_identity
        a hp0 hq0 hr0 hs0 hrs heq)
      heq

/-! ## Rational functions and transport to the analytic coordinate -/

open BaseRationalClassification

/-- Clearing denominators in
`U' = (a / z + V') U` gives the polynomial identity used by the residue
theorem above. -/
theorem clearedLogResidueEquation_of_evalAtTranscendental
    {E : Type*} [Field E] [Differential E] [Algebra Real E]
    [DifferentialAlgebra Real E]
    (z : E) (hz : Transcendental Real z) (hzd : z′ = 1)
    (a : Real) (U V : RatFunc Real)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (algebraMap Real E a / z +
        (Proposition31.evalAtTranscendental z hz V)′) *
          Proposition31.evalAtTranscendental z hz U) :
    X * (derivative U.num * U.denom - U.num * derivative U.denom) *
          V.denom ^ 2 =
      (C a * V.denom ^ 2 +
          X * (derivative V.num * V.denom - V.num * derivative V.denom)) *
        U.num * U.denom := by
  apply (transcendental_iff_injective.mp hz)
  have hz0 : z ≠ 0 := by
    simpa using (Proposition31.aeval_ne_zero_of_transcendental z hz
      (X_ne_zero : (X : Real[X]) ≠ 0))
  have hUden : Polynomial.aeval z U.denom ≠ 0 :=
    Proposition31.aeval_ne_zero_of_transcendental z hz U.denom_ne_zero
  have hVden : Polynomial.aeval z V.denom ≠ 0 :=
    Proposition31.aeval_ne_zero_of_transcendental z hz V.denom_ne_zero
  have hderiv (p : Real[X]) :
      (Polynomial.aeval z p)′ = Polynomial.aeval z (derivative p) := by
    have h := Differential.deriv_aeval_eq_implicitDeriv z (C 1)
      (by simpa using hzd) p
    have hmap : Differential.mapCoeffs p = 0 := by
      ext n
      simp [deriv_real_eq_zero]
    simpa [Differential.implicitDeriv, hmap, derivative'_apply] using h
  rw [Proposition31.evalAtTranscendental_num_div_denom,
    Proposition31.evalAtTranscendental_num_div_denom] at heq
  rw [Derivation.leibniz_div, Derivation.leibniz_div] at heq
  simp only [smul_eq_mul] at heq
  rw [hderiv, hderiv, hderiv, hderiv] at heq
  simp only [map_mul, map_sub, map_add, map_pow, aeval_X, aeval_C]
  field_simp [hz0, hUden, hVden] at heq ⊢
  linear_combination heq

/-- Evaluation-level integral-residue theorem over `Real(T)`. -/
theorem realRationalFunction_integralSlope
    {E : Type*} [Field E] [Differential E] [Algebra Real E]
    [DifferentialAlgebra Real E]
    (z : E) (hz : Transcendental Real z) (hzd : z′ = 1)
    (a : Real) (U V : RatFunc Real) (hU0 : U ≠ 0)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (algebraMap Real E a / z +
        (Proposition31.evalAtTranscendental z hz V)′) *
          Proposition31.evalAtTranscendental z hz U) :
    ∃ m : Int, a = (m : Real) := by
  apply integer_slope_of_logarithmic_identity a
    (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
    V.isCoprime_num_denom
  exact clearedLogResidueEquation_of_evalAtTranscendental z hz hzd a U V heq

/-! ## The differential field `Real(x)` inside the analytic fraction field -/

local notation "A" => PositiveAnalyticFractionField
local notation "x" => OneVariableBaseField.x

private theorem analyticX_deriv_generator
    (z : A) (hz : z ∈ ({x} : Set A)) :
    z′ ∈ IntermediateField.adjoin Real ({x} : Set A) := by
  have hz' : z = x := by simpa using hz
  subst z
  rw [OneVariableBaseField.deriv_x]
  exact one_mem _

/-- The derivative-closed copy of `Real(x)` in the analytic fraction
field.  Its underlying intermediate field is definitionally
`IntermediateField.adjoin Real {x}`. -/
def analyticXField : DifferentialIntermediateField Real A :=
  DifferentialIntermediateField.adjoinOfConstants ({x} : Set A)
    PositiveAnalyticFractionField.derivation_algebraMap_real
    analyticX_deriv_generator

/-- The coordinate as an element of the differential field `Real(x)`. -/
def analyticXCoordinate : analyticXField :=
  ⟨x, IntermediateField.subset_adjoin Real ({x} : Set A) (by simp)⟩

@[simp]
theorem coe_analyticXCoordinate : (analyticXCoordinate : A) = x :=
  rfl

@[simp]
theorem deriv_analyticXCoordinate : analyticXCoordinate′ = 1 := by
  apply Subtype.ext
  simp [analyticXCoordinate]

theorem analyticXCoordinate_ne_zero : analyticXCoordinate ≠ 0 := by
  intro h
  apply OneVariableBaseField.x_ne_zero
  exact congrArg (fun y : analyticXField ↦ (y : A)) h

/-- The integral-slope rigidity required by Proposition 3.1(ii) holds for
the coordinate in the differential rational field `Real(x)`. -/
theorem analyticX_integralSlopeRigidity :
    Proposition31II.IntegralSlopeRigidity analyticXCoordinate := by
  intro a u v ha hu0 hu
  obtain ⟨c, hc⟩ :=
    (Differential.ContainConstants.mem_range_of_deriv_eq_zero ha :
      a ∈ (algebraMap Real analyticXField).range)
  let e := RatFunc.algEquivOfTranscendental x
    OneVariableBaseField.x_transcendental
  let uI : IntermediateField.adjoin Real ({x} : Set A) := ⟨u.1, u.2⟩
  let vI : IntermediateField.adjoin Real ({x} : Set A) := ⟨v.1, v.2⟩
  let U : RatFunc Real := e.symm uI
  let V : RatFunc Real := e.symm vI
  have hU : Proposition31.evalAtTranscendental x
      OneVariableBaseField.x_transcendental U = (u : A) := by
    simp [Proposition31.evalAtTranscendental, U, uI, e]
  have hV : Proposition31.evalAtTranscendental x
      OneVariableBaseField.x_transcendental V = (v : A) := by
    simp [Proposition31.evalAtTranscendental, V, vI, e]
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hu0
    apply Subtype.ext
    simpa using (show (u : A) = 0 by rw [← hU, hzero, map_zero])
  have hcoordAmbient : ((analyticXCoordinate : analyticXField) : A) = x := rfl
  have huAmbient : (u : A)′ =
      ((a : A) * (((analyticXCoordinate : analyticXField) : A)′ /
          ((analyticXCoordinate : analyticXField) : A)) + (v : A)′) * (u : A) := by
    exact congrArg (fun y : analyticXField ↦ (y : A)) hu
  rw [hcoordAmbient] at huAmbient
  have hcAmbient : (a : A) = algebraMap Real A c := by
    rw [← DifferentialIntermediateField.coe_algebraMap_base analyticXField c]
    exact congrArg (fun y : analyticXField ↦ (y : A)) hc.symm
  have heq : (Proposition31.evalAtTranscendental x
        OneVariableBaseField.x_transcendental U)′ =
      (algebraMap Real A c / x +
        (Proposition31.evalAtTranscendental x
          OneVariableBaseField.x_transcendental V)′) *
        Proposition31.evalAtTranscendental x
          OneVariableBaseField.x_transcendental U := by
    rw [hU, hV]
    simpa [hcAmbient, deriv_analyticXCoordinate,
      div_eq_mul_inv] using huAmbient
  obtain ⟨m, hcm⟩ := realRationalFunction_integralSlope
    x OneVariableBaseField.x_transcendental
    OneVariableBaseField.deriv_x c U V hU0 heq
  refine ⟨m, ?_⟩
  apply Subtype.ext
  rw [hcAmbient, hcm]
  norm_num

end

end Natfunbasis.Wilkie.BaseLogRigidity
