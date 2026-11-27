import Natfunbasis.WilkieProposition31Full

/-!
# Passing Wilkie's rational-function calculations to a simple extension

Propositions 3.1(i) and 3.1(ii) are proved in polynomial coordinates over
`RatFunc K`.  Wilkie's induction, however, uses concrete simple extensions
inside one ambient differential field.  This file supplies the exact bridge:
an equation between the evaluations of two rational functions at a
transcendental differential element yields the cleared polynomial equation
used by the coordinate theorems.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.Proposition31

noncomputable section

variable {K L : Type*} [Field K] [CharZero K] [Field L]
  [Differential K] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L]

/-- Evaluation of a rational function at a transcendental element, regarded
in the ambient field rather than in the bundled simple intermediate field. -/
def evalAtTranscendental (z : L) (hz : Transcendental K z) :
    RatFunc K →ₐ[K] L :=
  (IsScalarTower.toAlgHom K (IntermediateField.adjoin K {z}) L).comp
    (RatFunc.algEquivOfTranscendental z hz).toAlgHom

omit [CharZero K] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
@[simp]
theorem evalAtTranscendental_X (z : L) (hz : Transcendental K z) :
    evalAtTranscendental z hz RatFunc.X = z := by
  simp [evalAtTranscendental]

omit [CharZero K] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
@[simp]
theorem evalAtTranscendental_algebraMap (z : L)
    (hz : Transcendental K z) (p : K[X]) :
    evalAtTranscendental z hz (algebraMap K[X] (RatFunc K) p) =
      Polynomial.aeval z p := by
  simp [evalAtTranscendental]

omit [CharZero K] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
@[simp]
theorem evalAtTranscendental_C (z : L) (hz : Transcendental K z)
    (a : K) :
    evalAtTranscendental z hz (RatFunc.C a) = algebraMap K L a := by
  rw [← RatFunc.algebraMap_C]
  simpa using evalAtTranscendental_algebraMap z hz (C a)

omit [CharZero K] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
/-- The evaluated numerator/denominator presentation of a rational
function. -/
theorem evalAtTranscendental_num_div_denom (z : L)
    (hz : Transcendental K z) (u : RatFunc K) :
    evalAtTranscendental z hz u =
      Polynomial.aeval z u.num / Polynomial.aeval z u.denom := by
  conv_lhs => rw [← RatFunc.num_div_denom u]
  rw [map_div₀, evalAtTranscendental_algebraMap,
    evalAtTranscendental_algebraMap]

omit [CharZero K] [Differential K] [Differential L]
  [DifferentialAlgebra K L] in
/-- A nonzero polynomial cannot vanish at a transcendental element. -/
theorem aeval_ne_zero_of_transcendental (z : L)
    (hz : Transcendental K z) {p : K[X]} (hp : p ≠ 0) :
    Polynomial.aeval z p ≠ 0 := by
  intro h
  apply hp
  apply (transcendental_iff_injective.mp hz)
  simpa using h

omit [CharZero K] in
/-- Cleared-denominator transport for the equation `X' = Y' X`.

The polynomial `w` is the prescribed derivative of the new generator:
`z' = aeval z w`.  The result is precisely the hypothesis expected by the
coordinate forms of Wilkie Proposition 3.1. -/
theorem clearedEquation_of_evalAtTranscendental
    (z : L) (hz : Transcendental K z) (w : K[X])
    (hzd : z′ = Polynomial.aeval z w)
    (U V : RatFunc K)
    (heq : (evalAtTranscendental z hz U)′ =
      (evalAtTranscendental z hz V)′ *
        evalAtTranscendental z hz U) :
    (Differential.implicitDeriv w U.num * U.denom -
          U.num * Differential.implicitDeriv w U.denom) * V.denom ^ 2 =
      (Differential.implicitDeriv w V.num * V.denom -
          V.num * Differential.implicitDeriv w V.denom) * U.num * U.denom := by
  apply (transcendental_iff_injective.mp hz)
  have hUden : Polynomial.aeval z U.denom ≠ 0 :=
    aeval_ne_zero_of_transcendental z hz U.denom_ne_zero
  have hVden : Polynomial.aeval z V.denom ≠ 0 :=
    aeval_ne_zero_of_transcendental z hz V.denom_ne_zero
  have hUnumDeriv :
      (Polynomial.aeval z U.num)′ =
        Polynomial.aeval z (Differential.implicitDeriv w U.num) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd U.num
  have hUdenDeriv :
      (Polynomial.aeval z U.denom)′ =
        Polynomial.aeval z (Differential.implicitDeriv w U.denom) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd U.denom
  have hVnumDeriv :
      (Polynomial.aeval z V.num)′ =
        Polynomial.aeval z (Differential.implicitDeriv w V.num) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd V.num
  have hVdenDeriv :
      (Polynomial.aeval z V.denom)′ =
        Polynomial.aeval z (Differential.implicitDeriv w V.denom) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd V.denom
  rw [evalAtTranscendental_num_div_denom,
    evalAtTranscendental_num_div_denom] at heq
  rw [Derivation.leibniz_div, Derivation.leibniz_div] at heq
  simp only [smul_eq_mul] at heq
  rw [hUnumDeriv, hUdenDeriv, hVnumDeriv, hVdenDeriv] at heq
  simp only [map_mul, map_sub, map_pow]
  field_simp [hUden, hVden] at heq ⊢
  linear_combination heq

/-- Wilkie Proposition 3.1(i) for two elements of a concrete simple
extension, expressed through their unique rational-function coordinates.

This is the form consumed by the stage induction: it removes all explicit
numerator/denominator hypotheses from the caller. -/
theorem simpleExtension_proposition31_i
    [Differential.ContainConstants K L]
    (β : K) (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L β′ * z)
    (U V : RatFunc K) (hU0 : U ≠ 0)
    (heq : (evalAtTranscendental z hz U)′ =
      (evalAtTranscendental z hz V)′ *
        evalAtTranscendental z hz U) :
    ∃ k : Int, ∃ u v : K, u ≠ 0 ∧
      evalAtTranscendental z hz U =
        algebraMap K L u * z ^ k ∧
      evalAtTranscendental z hz V =
        algebraMap K L ((k : K) * β + v) ∧
      u′ = v′ * u := by
  have hzdPolynomial :
      z′ = Polynomial.aeval z (C β′ * X) := by
    simpa using hzd
  have hcleared := clearedEquation_of_evalAtTranscendental
    z hz (C β′ * X) hzdPolynomial U V heq
  obtain ⟨k, u, v, hu0, hU, hV, huv⟩ :=
    rationalFunction_proposition31_i β z hz hzd
      (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
      U.isCoprime_num_denom V.isCoprime_num_denom hcleared
  refine ⟨k, u, v, hu0, ?_, ?_, huv⟩
  · have h := congrArg (evalAtTranscendental z hz) hU
    simpa [RatFunc.num_div_denom] using h
  · have h := congrArg (evalAtTranscendental z hz) hV
    simpa [RatFunc.num_div_denom] using h

/-- Subtype-valued version of `simpleExtension_proposition31_i` for the
actual simple intermediate field `K(z)` inside the ambient field. -/
theorem simpleAdjoin_proposition31_i
    [Differential.ContainConstants K L]
    (β : K) (z : L) (hz : Transcendental K z)
    (hzd : z′ = algebraMap K L β′ * z)
    (X Y : IntermediateField.adjoin K {z})
    (hX0 : (X : L) ≠ 0)
    (heq : ((X : L))′ = ((Y : L))′ * (X : L)) :
    ∃ k : Int, ∃ u v : K, u ≠ 0 ∧
      (X : L) = algebraMap K L u * z ^ k ∧
      (Y : L) = algebraMap K L ((k : K) * β + v) ∧
      u′ = v′ * u := by
  let e := RatFunc.algEquivOfTranscendental z hz
  let U : RatFunc K := e.symm X
  let V : RatFunc K := e.symm Y
  have hU : evalAtTranscendental z hz U = (X : L) := by
    simp [evalAtTranscendental, U, e]
  have hV : evalAtTranscendental z hz V = (Y : L) := by
    simp [evalAtTranscendental, V, e]
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hX0
    rw [← hU, hzero, map_zero]
  obtain ⟨k, u, v, hu0, hXu, hYv, huv⟩ :=
    simpleExtension_proposition31_i β z hz hzd U V hU0 (by
      simpa [hU, hV] using heq)
  exact ⟨k, u, v, hu0, hU.symm.trans hXu,
    hV.symm.trans hYv, huv⟩

end

end Natfunbasis.Wilkie.Proposition31
