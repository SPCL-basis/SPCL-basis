import Natfunbasis.WilkieOneVariableBaseField
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Algebraic independence of `x` and `log x`

This file proves the base case of Wilkie's one-variable induction directly
by exponential-polynomial asymptotics.  A polynomial relation in `x` and
`log x`, after substituting `x = exp t`, is a finite sum

`sum_i a_i(t) exp(t)^i`.

Dividing by the largest occurring exponential and sending `t` to infinity
forces its nonzero polynomial coefficient to tend to zero, a contradiction.
-/

namespace Natfunbasis.Wilkie

open Filter Topology Real
open Polynomial
open scoped Topology

noncomputable section

namespace OneVariableBaseField

/-! ## Polynomial coefficients are negligible relative to an exponential -/

theorem Polynomial.tendsto_eval_div_exp_mul_atTop (p : Real[X])
    {b : Real} (hb : 0 < b) :
    Tendsto (fun t : Real ↦ p.eval t / Real.exp (b * t))
      atTop (nhds 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa [Polynomial.eval_add, add_div] using hp.add hq
  | monomial n c =>
      have h :=
        (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left c
      simpa [Polynomial.eval_monomial, mul_div_assoc] using
        h.tendsto_div_nhds_zero

/-- Every lower exponential term becomes negligible after division by the
largest exponential. -/
theorem Polynomial.tendsto_eval_mul_exp_pow_div_exp_pow_atTop
    (p : Real[X]) {i d : Nat} (hid : i < d) :
    Tendsto
      (fun t : Real ↦ p.eval t * Real.exp t ^ i / Real.exp t ^ d)
      atTop (nhds 0) := by
  have hb : 0 < ((d - i : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hid
  have h := Polynomial.tendsto_eval_div_exp_mul_atTop p hb
  convert h using 1
  funext t
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  field_simp [Real.exp_ne_zero]
  have hnat : d - i + i = d := Nat.sub_add_cancel hid.le
  calc
    p.eval t * Real.exp ((i : Real) * t) *
          Real.exp (t * (d - i : Nat)) =
        p.eval t *
          (Real.exp ((i : Real) * t) *
            Real.exp ((d - i : Nat) * t)) := by ring_nf
    _ = p.eval t * Real.exp
        ((i : Real) * t + (d - i : Nat) * t) := by
      rw [Real.exp_add]
    _ = p.eval t * Real.exp (t * (d : Real)) := by
      congr 2
      have hcast : ((d - i : Nat) : Real) + (i : Real) = (d : Real) := by
        exact_mod_cast hnat
      rw [← hcast]
      ring

/-! ## Exponential polynomials -/

/-- Regard a coefficient in the remaining single multivariable-polynomial
coordinate as an ordinary real polynomial. -/
def coefficientPolynomial
    (q : Polynomial (MvPolynomial (Fin 1) Real)) (i : Nat) : Real[X] :=
  MvPolynomial.uniqueAlgEquiv Real (Fin 1) (q.coeff i)

@[simp]
theorem coefficientPolynomial_eval
    (q : Polynomial (MvPolynomial (Fin 1) Real)) (i : Nat) (t : Real) :
    (coefficientPolynomial q i).eval t =
      MvPolynomial.eval (fun _ : Fin 1 ↦ t) (q.coeff i) := by
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv
    (R := Real) (S := Real) (f := q.coeff i)
    (φ := RingHom.id Real) (a := t)

/-- Expanding a bivariate polynomial after the substitution
`(X₀,X₁) = (exp t,t)` gives its finite exponential-polynomial sum. -/
theorem eval_exp_log_eq_sum
    (p : MvPolynomial (Fin 2) Real) (t : Real) :
    MvPolynomial.eval
        (Fin.cases (Real.exp t) (fun _ : Fin 1 ↦ t)) p =
      ∑ i ∈ Finset.range
          ((MvPolynomial.finSuccEquiv Real 1 p).natDegree + 1),
        (coefficientPolynomial (MvPolynomial.finSuccEquiv Real 1 p) i).eval t *
          Real.exp t ^ i := by
  calc
    MvPolynomial.eval
          (Fin.cases (Real.exp t) (fun _ : Fin 1 ↦ t)) p =
        MvPolynomial.eval (fun _ : Fin 1 ↦ t)
          (Polynomial.eval (MvPolynomial.C (Real.exp t))
            (MvPolynomial.finSuccEquiv Real 1 p)) := by
      symm
      simpa using
        (MvPolynomial.eval_polynomial_eval_finSuccEquiv
          (R := Real) (x := fun _ : Fin 1 ↦ t) p
          (MvPolynomial.C (Real.exp t)))
    _ = _ := by
      rw [Polynomial.eval_eq_sum_range]
      simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
        MvPolynomial.eval_C]
      apply Finset.sum_congr rfl
      intro i hi
      rw [coefficientPolynomial_eval]

/-- No nonzero bivariate real polynomial vanishes on the curve
`t ↦ (exp t,t)`. -/
theorem eq_zero_of_eval_exp_log_eq_zero
    (p : MvPolynomial (Fin 2) Real)
    (hzero : ∀ t : Real,
      MvPolynomial.eval
        (Fin.cases (Real.exp t) (fun _ : Fin 1 ↦ t)) p = 0) :
    p = 0 := by
  by_contra hp0
  let q : Polynomial (MvPolynomial (Fin 1) Real) :=
    MvPolynomial.finSuccEquiv Real 1 p
  let d : Nat := q.natDegree
  let a : Real[X] := coefficientPolynomial q d
  have hq0 : q ≠ 0 := by
    intro hq
    apply hp0
    apply (MvPolynomial.finSuccEquiv Real 1).injective
    simpa [q] using hq
  have hcoeff0 : q.coeff d ≠ 0 := by
    dsimp [d]
    simpa only [_root_.Polynomial.leadingCoeff] using
      (_root_.Polynomial.leadingCoeff_ne_zero.mpr hq0)
  have ha0 : a ≠ 0 := by
    intro ha
    apply hcoeff0
    apply (MvPolynomial.uniqueAlgEquiv Real (Fin 1)).injective
    simpa [a, coefficientPolynomial] using ha
  have hsum (t : Real) :
      ∑ i ∈ Finset.range (d + 1),
          (coefficientPolynomial q i).eval t * Real.exp t ^ i = 0 := by
    calc
      (∑ i ∈ Finset.range (d + 1),
          (coefficientPolynomial q i).eval t * Real.exp t ^ i) =
          MvPolynomial.eval
            (Fin.cases (Real.exp t) (fun _ : Fin 1 ↦ t)) p := by
        simpa [q, d] using (eval_exp_log_eq_sum p t).symm
      _ = 0 := hzero t
  have haeq (t : Real) :
      a.eval t =
        -∑ i ∈ Finset.range d,
          ((coefficientPolynomial q i).eval t * Real.exp t ^ i /
            Real.exp t ^ d) := by
    have hs := hsum t
    rw [Finset.sum_range_succ] at hs
    have hexp : Real.exp t ^ d ≠ 0 :=
      pow_ne_zero d (Real.exp_ne_zero t)
    have hdiv : a.eval t =
        -(∑ i ∈ Finset.range d,
          (coefficientPolynomial q i).eval t * Real.exp t ^ i) /
            Real.exp t ^ d := by
      apply (eq_div_iff hexp).2
      simpa [a] using (eq_neg_of_add_eq_zero_right hs)
    rw [hdiv, neg_div, Finset.sum_div]
  have hlower : Tendsto
      (fun t : Real ↦
        ∑ i ∈ Finset.range d,
          ((coefficientPolynomial q i).eval t * Real.exp t ^ i /
            Real.exp t ^ d)) atTop (nhds 0) := by
    have hterms := tendsto_finsetSum (Finset.range d)
      (fun i hi ↦
        Polynomial.tendsto_eval_mul_exp_pow_div_exp_pow_atTop
          (coefficientPolynomial q i) (Finset.mem_range.mp hi))
    simpa using hterms
  have halim : Tendsto (fun t : Real ↦ a.eval t) atTop (nhds 0) := by
    have hneg := hlower.neg
    have heq :
        (fun t : Real ↦
          -∑ i ∈ Finset.range d,
            ((coefficientPolynomial q i).eval t * Real.exp t ^ i /
              Real.exp t ^ d)) =ᶠ[atTop]
          (fun t : Real ↦ a.eval t) :=
      Filter.Eventually.of_forall fun t ↦ (haeq t).symm
    simpa only [neg_zero] using hneg.congr' heq
  have halead : a.leadingCoeff = 0 :=
    (_root_.Polynomial.tendsto_nhds_iff a).mp halim |>.1
  exact ha0 (_root_.Polynomial.leadingCoeff_eq_zero.mp halead)

/-! ## The analytic and fraction-field base pairs -/

/-- Evaluation of a polynomial in the bundled functions `x` and `log x` is
pointwise ordinary bivariate polynomial evaluation. -/
theorem aeval_input_log_apply (p : MvPolynomial (Fin 2) Real)
    (y : PositiveReal) :
    (MvPolynomial.aeval ![inputAnalyticFunction,
        logInputAnalyticFunction] p : PositiveAnalyticFunction).1 y =
      MvPolynomial.eval ![y.1, Real.log y.1] p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      fin_cases i <;>
        simp [hp, inputAnalyticFunction_apply,
          logInputAnalyticFunction_apply]

/-- The bundled positive-axis functions `x` and `log x` are algebraically
independent over the real constants. -/
theorem input_log_algebraicIndependent :
    AlgebraicIndependent Real
      ![inputAnalyticFunction, logInputAnalyticFunction] := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro p q hpq
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_exp_log_eq_zero
  intro t
  let y : PositiveReal := ⟨Real.exp t, Real.exp_pos t⟩
  have hdiff : MvPolynomial.aeval
      ![inputAnalyticFunction, logInputAnalyticFunction] (p - q) = 0 := by
    simp only [map_sub, hpq, sub_self]
  have hpoint := congrArg
    (fun f : PositiveAnalyticFunction ↦ f.1 y) hdiff
  have hassignment :
      (![Real.exp t, t] : Fin 2 → Real) =
        Fin.cases (Real.exp t) (fun _ : Fin 1 ↦ t) := by
    funext i
    fin_cases i <;> rfl
  rw [← hassignment]
  simpa [aeval_input_log_apply, y] using hpoint

/-- Wilkie's initial fraction-field elements `x` and `log x` are
algebraically independent over `Real`. -/
theorem x_logX_algebraicIndependent :
    AlgebraicIndependent Real ![x, logX] := by
  let inclusion : PositiveAnalyticFunction →ₐ[Real]
      PositiveAnalyticFractionField :=
    IsScalarTower.toAlgHom Real PositiveAnalyticFunction
      PositiveAnalyticFractionField
  have hmap := input_log_algebraicIndependent.map'
    (f := inclusion)
    (IsFractionRing.injective PositiveAnalyticFunction
      PositiveAnalyticFractionField)
  have hcoordinates :
      inclusion ∘ ![inputAnalyticFunction, logInputAnalyticFunction] =
        ![x, logX] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoordinates] at hmap
  exact hmap

end OneVariableBaseField

end

end Natfunbasis.Wilkie
