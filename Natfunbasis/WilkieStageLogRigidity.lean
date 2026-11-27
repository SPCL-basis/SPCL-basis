import Natfunbasis.WilkieBaseLogRigidity
import Natfunbasis.WilkieStageClassification

/-!
# Prime-residue rigidity for finite-stage logarithms

At a fresh logarithmic adjunction, integrality of the affine slope is a
local residue statement at the irreducible polynomial defining the current
base.  This file proves the required algebraic residue theorem for an
arbitrary irreducible polynomial and an arbitrary polynomial derivation.

The remaining stage-specific task is coordinate transport: realize the
finite-stage field as a rational function field in algebraically independent
generators, prove that the substituted fresh base remains irreducible in the
chosen polynomial coordinate, and prove that it does not divide its own
derivative.  No such premises are hidden in the theorem below.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.StageLogRigidity

noncomputable section

open Proposition31

variable {F : Type*} [Field F] [CharZero F]

/-- Multiplication by the prime removes the exceptional exponent-zero case
in the derivative of `h^n u`. -/
lemma prime_mul_deriv_pow_mul (D : Derivation Int F[X] F[X])
    (h : F[X]) (n : Nat) (u : F[X]) :
    h * D (h ^ n * u) =
      h ^ n * ((n : F[X]) * D h * u + h * D u) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [deriv_pow_mul_factor D h u (Nat.succ_pos n), pow_succ]
      simp only [Nat.succ_sub_one]
      push_cast
      ring

/-- Factoring the exact prime orders of a numerator and denominator exposes
the integral coefficient in their logarithmic derivative. -/
lemma prime_mul_logCross_factor
    (D : Derivation Int F[X] F[X]) {h p q : F[X]} {i j : Nat}
    (hp : HasExactOrder h i p) (hq : HasExactOrder h j q) :
    ∃ P Q : F[X],
      p = h ^ i * P ∧ q = h ^ j * Q ∧
      ¬ h ∣ P ∧ ¬ h ∣ Q ∧
      h * (D p * q - p * D q) =
        h ^ (i + j) *
          (C ((i : F) - (j : F)) * D h * P * Q +
            h * (D P * Q - P * D Q)) := by
  obtain ⟨P, hp, hP⟩ := hp
  obtain ⟨Q, hq, hQ⟩ := hq
  refine ⟨P, Q, hp, hq, hP, hQ, ?_⟩
  rw [hp, hq]
  calc
    h * (D (h ^ i * P) * (h ^ j * Q) -
        h ^ i * P * D (h ^ j * Q)) =
        (h * D (h ^ i * P)) * (h ^ j * Q) -
          (h ^ i * P) * (h * D (h ^ j * Q)) := by ring
    _ = _ := by
      rw [prime_mul_deriv_pow_mul, prime_mul_deriv_pow_mul, pow_add]
      rw [map_sub]
      rw [C_eq_natCast, C_eq_natCast]
      ring

/-- Consequently `h^(i+j)` divides `h` times the logarithmic cross
numerator. -/
lemma prime_pow_add_dvd_prime_mul_logCross
    (D : Derivation Int F[X] F[X]) {h p q : F[X]} {i j : Nat}
    (hp : HasExactOrder h i p) (hq : HasExactOrder h j q) :
    h ^ (i + j) ∣ h * (D p * q - p * D q) := by
  obtain ⟨P, Q, -, -, -, -, hfactor⟩ :=
    prime_mul_logCross_factor D hp hq
  rw [hfactor]
  exact dvd_mul_right _ _

/-- In a logarithmic-residue identity, a reduced primitive cannot have a
pole at a prime which does not divide its own derivative. -/
lemma denominator_not_dvd_prime_of_logarithmic_identity
    (D : Derivation Int F[X] F[X])
    {h : F[X]} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (a : F) {p q r s : F[X]}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s)
    (heq :
      h * (D p * q - p * D q) * s ^ 2 =
        (C a * D h * s ^ 2 + h * (D r * s - r * D s)) * p * q) :
    ¬ h ∣ s := by
  intro hhs
  obtain ⟨i, hi⟩ := exists_hasExactOrder h hh hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder h hh hq0
  obtain ⟨l, hl⟩ := exists_hasExactOrder h hh hr0
  obtain ⟨e, hs⟩ := exists_hasExactOrder h hh hs0
  have hepos : 0 < e := hs.pos_of_dvd hhs
  have hlzero : l = 0 := by
    by_contra hl0
    exact hh.not_isUnit <| hrs.isUnit_of_dvd'
      (hl.dvd_base_of_pos (Nat.pos_of_ne_zero hl0)) hhs
  have hr : HasExactOrder h 0 r := by simpa [hlzero] using hl
  have hB : HasExactOrder h (e - 1) (D r * s - r * D s) :=
    hasExactOrder_derivCross_of_denominator
      D hh.prime hDh hepos hr hs
  have hhOrder : HasExactOrder h 1 h := by
    refine ⟨1, by simp, ?_⟩
    exact hh.prime.not_dvd_one
  have hhB : HasExactOrder h e (h * (D r * s - r * D s)) := by
    have := hhOrder.mul hh.prime hB
    simpa [show 1 + (e - 1) = e by omega] using this
  have hs2 : HasExactOrder h (e + e) (s ^ 2) := by
    simpa [pow_two] using hs.mul hh.prime hs
  have hcoefficient :
      h ^ (e + 1) ∣ C a * D h * s ^ 2 := by
    have hpow : h ^ (e + 1) ∣ h ^ (e + e) :=
      pow_dvd_pow h (by omega)
    exact dvd_mul_of_dvd_right (hpow.trans hs2.dvd) (C a * D h)
  have hsum : HasExactOrder h e
      (C a * D h * s ^ 2 + h * (D r * s - r * D s)) := by
    have hneg := hhB.neg
    have := hneg.sub_of_dvd_succ_right hcoefficient
    simpa only [sub_neg_eq_add] using this
  have hright : HasExactOrder h ((e + i) + j)
      ((C a * D h * s ^ 2 + h * (D r * s - r * D s)) * p * q) :=
    (hsum.mul hh.prime hi).mul hh.prime hj
  have hprimeCross : h ^ (i + j) ∣
      h * (D p * q - p * D q) :=
    prime_pow_add_dvd_prime_mul_logCross D hi hj
  have hleftBig : h ^ ((i + j) + (e + e)) ∣
      h * (D p * q - p * D q) * s ^ 2 := by
    rw [pow_add]
    exact mul_dvd_mul hprimeCross hs2.dvd
  have hnext : h ^ (((e + i) + j) + 1) ∣
      h * (D p * q - p * D q) * s ^ 2 :=
    (pow_dvd_pow h (by omega)).trans hleftBig
  apply hright.not_dvd_succ hh.ne_zero
  rw [← heq]
  exact hnext

/-- Prime-residue theorem when the primitive is regular at the chosen
prime.  The slope is the difference of the numerator and denominator orders,
and hence is an integer. -/
theorem integer_slope_of_prime_logarithmic_identity_of_regular_primitive
    (D : Derivation Int F[X] F[X])
    {h : F[X]} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (a : F) {p q r s : F[X]}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hhs : ¬ h ∣ s)
    (heq :
      h * (D p * q - p * D q) * s ^ 2 =
        (C a * D h * s ^ 2 + h * (D r * s - r * D s)) * p * q) :
    ∃ m : Int, a = (m : F) := by
  obtain ⟨i, hi⟩ := exists_hasExactOrder h hh hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder h hh hq0
  obtain ⟨P, Q, hp, hq, hP, hQ, hcross⟩ :=
    prime_mul_logCross_factor D hi hj
  let R : F[X] :=
    C ((i : F) - (j : F)) * D h * P * Q +
      h * (D P * Q - P * D Q)
  have hcancel :
      R * s ^ 2 =
        (C a * D h * s ^ 2 + h * (D r * s - r * D s)) * P * Q := by
    apply mul_left_cancel₀ (pow_ne_zero (i + j) hh.ne_zero)
    calc
      h ^ (i + j) * (R * s ^ 2) =
          (h ^ (i + j) * R) * s ^ 2 := by ring
      _ = h * (D p * q - p * D q) * s ^ 2 := by
        rw [← hcross]
      _ = (C a * D h * s ^ 2 + h * (D r * s - r * D s)) * p * q := heq
      _ = h ^ (i + j) *
          ((C a * D h * s ^ 2 + h * (D r * s - r * D s)) *
            P * Q) := by
        rw [hp, hq, pow_add]
        ring
  let B : F[X] := D r * s - r * D s
  let E : F[X] := D P * Q - P * D Q
  have hdiv : h ∣
      (C ((i : F) - (j : F)) - C a) * D h * P * Q * s ^ 2 := by
    refine ⟨B * P * Q - E * s ^ 2, ?_⟩
    dsimp [R, B, E] at hcancel ⊢
    linear_combination hcancel
  have hrest : ¬ h ∣ D h * P * Q * s ^ 2 := by
    apply hh.prime.not_dvd_mul
    · apply hh.prime.not_dvd_mul
      · exact hh.prime.not_dvd_mul hDh hP
      · exact hQ
    · intro hs2
      exact hhs (hh.prime.dvd_of_dvd_pow hs2)
  have hdiv' : h ∣
      (C ((i : F) - (j : F)) - C a) * (D h * P * Q * s ^ 2) := by
    simpa [mul_assoc] using hdiv
  have hC : h ∣ C ((i : F) - (j : F)) - C a :=
    (hh.prime.dvd_mul.mp hdiv').resolve_right hrest
  have ha : (i : F) - (j : F) = a := by
    by_contra hne
    have hunit : IsUnit (C ((i : F) - (j : F)) - C a) := by
      rw [← map_sub]
      exact Polynomial.isUnit_C.mpr
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    exact hh.not_isUnit (isUnit_of_dvd_unit hC hunit)
  refine ⟨(i : Int) - (j : Int), ?_⟩
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  exact ha.symm

/-- Fully reduced polynomial-coordinate prime-residue theorem. -/
theorem integer_slope_of_prime_logarithmic_identity
    (D : Derivation Int F[X] F[X])
    {h : F[X]} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (a : F) {p q r s : F[X]}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hrs : IsCoprime r s)
    (heq :
      h * (D p * q - p * D q) * s ^ 2 =
        (C a * D h * s ^ 2 + h * (D r * s - r * D s)) * p * q) :
    ∃ m : Int, a = (m : F) := by
  by_cases hr0 : r = 0
  · have hbase :
        h * (D p * q - p * D q) = C a * D h * p * q := by
      apply mul_right_cancel₀ (pow_ne_zero 2 hs0)
      calc
        h * (D p * q - p * D q) * s ^ 2 =
            (C a * D h * s ^ 2 + h * (D r * s - r * D s)) * p * q := heq
        _ = (C a * D h * p * q) * s ^ 2 := by
          rw [hr0, map_zero]
          ring
    apply integer_slope_of_prime_logarithmic_identity_of_regular_primitive
      D hh hDh (r := 0) (s := 1) a hp0 hq0 hh.prime.not_dvd_one
    simpa using hbase
  · exact integer_slope_of_prime_logarithmic_identity_of_regular_primitive
      D hh hDh a hp0 hq0
      (denominator_not_dvd_prime_of_logarithmic_identity
        D hh hDh a hp0 hq0 hr0 hs0 hrs heq)
      heq

/-! ## Transport through a transcendental rational coordinate -/

/-- Clearing denominators in a logarithmic-derivative equation at an
arbitrary polynomial prime produces exactly the prime-residue identity
above. -/
theorem clearedPrimeResidueEquation_of_evalAtTranscendental
    {E : Type*} [Field E] [Differential F] [Differential E] [Algebra F E]
    [DifferentialAlgebra F E]
    (z : E) (hz : Transcendental F z) (w : F[X])
    (hzd : z′ = Polynomial.aeval z w)
    (h : F[X]) (hh0poly : h ≠ 0) (a : F) (U V : RatFunc F)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (algebraMap F E a *
          ((Polynomial.aeval z h)′ / Polynomial.aeval z h) +
        (Proposition31.evalAtTranscendental z hz V)′) *
          Proposition31.evalAtTranscendental z hz U) :
    h *
        (Differential.implicitDeriv w U.num * U.denom -
          U.num * Differential.implicitDeriv w U.denom) * V.denom ^ 2 =
      (C a * Differential.implicitDeriv w h * V.denom ^ 2 +
          h * (Differential.implicitDeriv w V.num * V.denom -
            V.num * Differential.implicitDeriv w V.denom)) *
        U.num * U.denom := by
  apply (transcendental_iff_injective.mp hz)
  have hh0 : Polynomial.aeval z h ≠ 0 :=
    Proposition31.aeval_ne_zero_of_transcendental z hz
      hh0poly
  have hUden : Polynomial.aeval z U.denom ≠ 0 :=
    Proposition31.aeval_ne_zero_of_transcendental z hz U.denom_ne_zero
  have hVden : Polynomial.aeval z V.denom ≠ 0 :=
    Proposition31.aeval_ne_zero_of_transcendental z hz V.denom_ne_zero
  have hderiv (p : F[X]) :
      (Polynomial.aeval z p)′ =
        Polynomial.aeval z (Differential.implicitDeriv w p) :=
    Differential.deriv_aeval_eq_implicitDeriv z w hzd p
  rw [Proposition31.evalAtTranscendental_num_div_denom,
    Proposition31.evalAtTranscendental_num_div_denom] at heq
  rw [Derivation.leibniz_div, Derivation.leibniz_div] at heq
  simp only [smul_eq_mul] at heq
  rw [hderiv, hderiv, hderiv, hderiv, hderiv] at heq
  simp only [map_mul, map_sub, map_add, map_pow, aeval_C]
  field_simp [hh0, hUden, hVden] at heq ⊢
  linear_combination heq

/-- Evaluation-level integral-slope theorem at an arbitrary non-invariant
irreducible polynomial.  This is the form needed after choosing one
transcendental coordinate in a finite-stage rational-function presentation.
-/
theorem simpleExtension_integralSlope_at_prime
    {E : Type*} [Field E] [Differential F] [Differential E] [Algebra F E]
    [DifferentialAlgebra F E]
    (z : E) (hz : Transcendental F z) (w : F[X])
    (hzd : z′ = Polynomial.aeval z w)
    (h : F[X]) (hh : Irreducible h)
    (hDh : ¬ h ∣ Differential.implicitDeriv w h)
    (a : F) (U V : RatFunc F) (hU0 : U ≠ 0)
    (heq : (Proposition31.evalAtTranscendental z hz U)′ =
      (algebraMap F E a *
          ((Polynomial.aeval z h)′ / Polynomial.aeval z h) +
        (Proposition31.evalAtTranscendental z hz V)′) *
          Proposition31.evalAtTranscendental z hz U) :
    ∃ m : Int, a = (m : F) := by
  apply integer_slope_of_prime_logarithmic_identity
    (Differential.implicitDeriv w) hh hDh a
    (RatFunc.num_ne_zero hU0) U.denom_ne_zero V.denom_ne_zero
    V.isCoprime_num_denom
  exact clearedPrimeResidueEquation_of_evalAtTranscendental
    z hz w hzd h hh.ne_zero a U V heq

/-- A differential simple extension inherits `IntegralSlopeRigidity` for a
base represented by an irreducible polynomial whose derivative is not
divisible by that polynomial.

This theorem isolates the exact coordinate facts still required at a fresh
finite stage: an identification with a simple rational extension, a
polynomial representative of the current base, irreducibility, and
non-invariance under the transported derivation. -/
theorem differentialSimpleExtension_integralSlopeRigidity
    {E : Type*} [Field E] [Differential F] [Differential E] [Algebra F E]
    [DifferentialAlgebra F E]
    (G : DifferentialIntermediateField F E)
    [Differential.ContainConstants F G]
    (z : E) (hz : Transcendental F z) (w : F[X])
    (hzd : z′ = Polynomial.aeval z w)
    (hG : G.toIntermediateField = IntermediateField.adjoin F {z})
    (h : F[X]) (hh : Irreducible h)
    (hDh : ¬ h ∣ Differential.implicitDeriv w h)
    (beta : G) (hbeta : (beta : E) = Polynomial.aeval z h) :
    Proposition31II.IntegralSlopeRigidity beta := by
  intro a u v ha hu0 hu
  obtain ⟨a₀, ha₀⟩ := mem_range_of_deriv_eq_zero F ha
  let e := RatFunc.algEquivOfTranscendental z hz
  let uI : IntermediateField.adjoin F {z} :=
    ⟨(u : E), by
      rw [← hG]
      exact u.2⟩
  let vI : IntermediateField.adjoin F {z} :=
    ⟨(v : E), by
      rw [← hG]
      exact v.2⟩
  let U : RatFunc F := e.symm uI
  let V : RatFunc F := e.symm vI
  have hU : Proposition31.evalAtTranscendental z hz U = (u : E) := by
    simp [Proposition31.evalAtTranscendental, U, uI, e]
  have hV : Proposition31.evalAtTranscendental z hz V = (v : E) := by
    simp [Proposition31.evalAtTranscendental, V, vI, e]
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hu0
    apply Subtype.ext
    simpa using (show (u : E) = 0 by rw [← hU, hzero, map_zero])
  have haE : (a : E) = algebraMap F E a₀ := by
    rw [← DifferentialIntermediateField.coe_algebraMap_base G a₀]
    exact congrArg (fun y : G ↦ (y : E)) ha₀.symm
  have coeMul (p q : G) : (((p * q : G) : E)) = (p : E) * (q : E) := rfl
  have coeAdd (p q : G) : (((p + q : G) : E)) = (p : E) + (q : E) := rfl
  have coeDiv (p q : G) : (((p / q : G) : E)) = (p : E) / (q : E) := rfl
  have huE := congrArg (fun y : G ↦ (y : E)) hu
  simp only [DifferentialIntermediateField.coe_deriv, coeMul, coeAdd,
    coeDiv] at huE
  have heval :
      (Proposition31.evalAtTranscendental z hz U)′ =
        (algebraMap F E a₀ *
            ((Polynomial.aeval z h)′ / Polynomial.aeval z h) +
          (Proposition31.evalAtTranscendental z hz V)′) *
            Proposition31.evalAtTranscendental z hz U := by
    rw [hU, hV]
    rw [← hbeta, ← haE]
    exact huE
  obtain ⟨m, hm⟩ := simpleExtension_integralSlope_at_prime
    z hz w hzd h hh hDh a₀ U V hU0 heval
  refine ⟨m, ?_⟩
  rw [← ha₀, hm]
  exact map_intCast (algebraMap F G) m

end

end Natfunbasis.Wilkie.StageLogRigidity

namespace Natfunbasis.Wilkie

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The current W1 base as an element of the completed finite-stage field.
This is the element for which the fresh-stage rigidity theorem is required.
-/
def currentBaseElement (n : Nat) : S.finiteStageField n :=
  ⟨ι (S.baseAnalytic n), S.baseAnalytic_mem_finiteStageField n⟩

@[simp]
theorem currentBaseElement_coe (n : Nat) :
    (S.currentBaseElement n : K) = ι (S.baseAnalytic n) :=
  rfl

theorem currentBaseElement_ne_zero (n : Nat) :
    S.currentBaseElement n ≠ 0 := by
  have hbaseA : S.baseAnalytic n ≠ 0 := by
    intro hbase
    have hpos := S.baseAnalytic_pos n ⟨1, zero_lt_one⟩
    rw [hbase] at hpos
    simp at hpos
  have hambient : ι (S.baseAnalytic n) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hbaseA)
  intro hzero
  exact hambient (congrArg Subtype.val hzero)

end GeneratorSequence

end

end Natfunbasis.Wilkie
