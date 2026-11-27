import Natfunbasis.WilkieFiniteStageFields
import Natfunbasis.WilkieProposition32

/-!
# Algebraic-to-rigidity reductions in the finite-stage tower

This module applies Wilkie Proposition 3.2 to the concrete analytic stage
fields.  It isolates the exact remaining obligations in Theorem 4.4:

* a fresh `log u_n` is transcendental as soon as it is proved not to belong
  to the preceding stage;
* if `tau_n` were algebraic over the pre-`tau` stage, Proposition 3.2(i)
  would produce the integer-power/logarithmic relation used in Wilkie's
  contradiction.

No non-membership or contradiction is assumed or proved here.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace DifferentialIntermediateField

variable {C E : Type*} [Field C] [Field E] [Algebra C E]
  [Differential E]

/-- If the ambient field has no constants beyond `C`, then it has no
constants beyond any intermediate differential field over `C` either. -/
theorem containConstantsAmbient (F : DifferentialIntermediateField C E)
    [Differential.ContainConstants C E] :
    Differential.ContainConstants F E := by
  refine ⟨?_⟩
  intro z hz
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero C hz
  let y : F := algebraMap C F c
  refine ⟨y, ?_⟩
  exact (F.coe_algebraMap_base c).trans hc

end DifferentialIntermediateField

namespace Proposition32

variable {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
  [Differential E] [Differential.ContainConstants C E]

/-- Proposition 3.2(ii) in the membership form used at a logarithmic
adjunction. -/
theorem transcendental_of_not_mem_of_deriv_eq_logDeriv
    (F : DifferentialIntermediateField C E)
    {alpha : E} (beta : F) (hbeta : beta ≠ 0)
    (hderiv : alpha′ = algebraMap F E (beta′ / beta))
    (hnotmem : alpha ∉ F) :
    Transcendental F alpha := by
  letI : CharZero F := CharZero.of_addMonoidHom
    (algebraMap C F).toAddMonoidHom (by simp)
      (algebraMap C F).injective
  letI : Differential.ContainConstants F E :=
    F.containConstantsAmbient
  intro halgebraic
  have hrange := proposition32_ii halgebraic (β := beta) hbeta hderiv
  obtain ⟨z, hz⟩ := hrange
  apply hnotmem
  rw [← hz]
  exact z.2

/-- Proposition 3.2(i), restated for an ambient element over a concrete
differential intermediate field. -/
theorem powerRelation_of_isAlgebraic
    (F : DifferentialIntermediateField C E)
    {alpha : E} (halgebraic : IsAlgebraic F alpha) (beta : F)
    (hderiv : alpha′ = algebraMap F E beta′ * alpha) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ u v : F,
      alpha ^ m = algebraMap F E u ∧
      (m : F) * beta = v ∧ u′ = v′ * u := by
  letI : CharZero F := CharZero.of_addMonoidHom
    (algebraMap C F).toAddMonoidHom (by simp)
      (algebraMap C F).injective
  letI : Differential.ContainConstants F E :=
    F.containConstantsAmbient
  exact proposition32_i halgebraic beta hderiv

end Proposition32

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

private theorem base_ne_zero (n : Nat) : ι (S.baseAnalytic n) ≠ 0 := by
  have hbaseA : S.baseAnalytic n ≠ 0 := by
    intro hzero
    have hpos := S.baseAnalytic_pos n ⟨1, zero_lt_one⟩
    rw [hzero] at hpos
    simp at hpos
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hbaseA)

/-- A fresh logarithm is transcendental over the old stage once the
stage-specific logarithmic-rigidity argument proves non-membership.  This is
exactly the use of Wilkie Proposition 3.2(ii) in Theorem 4.4. -/
theorem freshLog_transcendental_of_not_mem {n : Nat}
    (hnotmem : ι (S.logBaseAnalytic n) ∉ S.finiteStageField n) :
    Transcendental (S.finiteStageField n)
      (ι (S.logBaseAnalytic n)) := by
  let beta : S.finiteStageField n :=
    ⟨ι (S.baseAnalytic n),
      S.baseAnalytic_mem (S.finiteStageField n)
        (S.x_mem_finiteStageField n)
        (fun j hj ↦ S.tau_mem_finiteStageField hj)⟩
  have hbeta : beta ≠ 0 := by
    intro hzero
    apply S.base_ne_zero n
    exact congrArg Subtype.val hzero
  apply Proposition32.transcendental_of_not_mem_of_deriv_eq_logDeriv
    (S.finiteStageField n) beta hbeta
  · change PositiveAnalyticFractionField.derivation
        (ι (S.logBaseAnalytic n)) =
      PositiveAnalyticFractionField.derivation
          (ι (S.baseAnalytic n)) /
        ι (S.baseAnalytic n)
    exact PositiveAnalyticFractionField.derivation_logBaseAnalytic S n
  · exact hnotmem

/-- The exponent-times-logarithm primitive whose exponential is `tau_n`. -/
def tauPrimitive (n : Nat) : S.finiteStageBeforeTau n :=
  ⟨ι (S.exponentAnalytic n) * ι (S.logBaseAnalytic n),
    mul_mem (S.differentialStage n).exponent_mem_beforeTau
      (S.logBase_mem_finiteStageBeforeTau n)⟩

/-- The concrete W3 differential equation in the form
`tau_n' = (s_n log u_n)' tau_n` required by Proposition 3.2(i). -/
theorem deriv_tau_eq_tauPrimitive_deriv_mul (n : Nat) :
    (ι (S.realTauAnalyticFunction n))′ =
      algebraMap (S.finiteStageBeforeTau n) K
          ((S.tauPrimitive n)′) *
        ι (S.realTauAnalyticFunction n) := by
  change PositiveAnalyticFractionField.derivation
      (ι (S.realTauAnalyticFunction n)) =
    PositiveAnalyticFractionField.derivation
        (ι (S.exponentAnalytic n) * ι (S.logBaseAnalytic n)) *
      ι (S.realTauAnalyticFunction n)
  rw [PositiveAnalyticFractionField.derivation_realTauAnalyticFunction]
  have hlog :
      PositiveAnalyticFractionField.derivation
          (ι (S.logBaseAnalytic n)) =
        PositiveAnalyticFractionField.derivation
            (ι (S.baseAnalytic n)) /
          ι (S.baseAnalytic n) :=
    PositiveAnalyticFractionField.derivation_logBaseAnalytic S n
  rw [PositiveAnalyticFractionField.derivation_mul, hlog]
  ring

/-- If the current W3 generator were algebraic over the pre-`tau` stage,
Wilkie Proposition 3.2(i) would force the displayed nonzero integral-power
relation.  Ruling out precisely this relation is the remaining
stage-specific transcendence argument. -/
theorem tau_powerRelation_of_isAlgebraic {n : Nat}
    (halgebraic : IsAlgebraic (S.finiteStageBeforeTau n)
      (ι (S.realTauAnalyticFunction n))) :
    ∃ m : ℤ, m ≠ 0 ∧
      ∃ u v : S.finiteStageBeforeTau n,
        (ι (S.realTauAnalyticFunction n)) ^ m =
            algebraMap (S.finiteStageBeforeTau n) K u ∧
        (m : S.finiteStageBeforeTau n) * S.tauPrimitive n = v ∧
        u′ = v′ * u := by
  exact Proposition32.powerRelation_of_isAlgebraic
    (S.finiteStageBeforeTau n) halgebraic (S.tauPrimitive n)
      (S.deriv_tau_eq_tauPrimitive_deriv_mul n)

end GeneratorSequence

end

end Natfunbasis.Wilkie
