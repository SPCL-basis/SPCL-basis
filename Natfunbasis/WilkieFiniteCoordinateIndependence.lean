import Natfunbasis.WilkieInfiniteIndependence

/-!
# Labeled finite coordinate independence

The set-valued finite-stage invariant deliberately forgets how often a
generator is listed.  Wilkie's coefficient comparisons, on the other hand,
use the labeled tuple

`x, tau_0, ..., tau_(n-1)`.

This file supplies the small bridge between the two formulations.  Earlier
power-generator transcendence rules out repetitions in the labeled tuple;
the stage-set algebraic-independence invariant can then be pulled back along
that injection.
-/

namespace Natfunbasis.Wilkie

open Set

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The labeled coordinates available at completed stage `n`: coordinate
zero is `x`, and coordinate `j+1` is `tau_j`. -/
def finiteFractionCoordinates (n : Nat) : StageVar n → K :=
  fun i ↦ S.fractionCoordinates i.1

@[simp]
theorem finiteFractionCoordinates_zero (n : Nat) :
    S.finiteFractionCoordinates n 0 = OneVariableBaseField.x := by
  simp [finiteFractionCoordinates, fractionCoordinates, analyticCoordinates,
    OneVariableBaseField.x]

@[simp]
theorem finiteFractionCoordinates_succ {n : Nat} (j : Fin n) :
    S.finiteFractionCoordinates n j.succ =
      ι (S.realTauAnalyticFunction j.1) := by
  simp [finiteFractionCoordinates, fractionCoordinates, analyticCoordinates]

/-- Every labeled finite coordinate occurs in the corresponding stage
generator set. -/
theorem finiteFractionCoordinate_mem_stageGenerators (n : Nat)
    (i : StageVar n) :
    S.finiteFractionCoordinates n i ∈ S.stageGenerators n := by
  cases i using Fin.cases with
  | zero =>
      apply S.stageGenerators_mono (Nat.zero_le n)
      simp [finiteFractionCoordinates, fractionCoordinates,
        analyticCoordinates, OneVariableBaseField.x, stageGenerators]
  | succ j =>
      apply S.stageGenerators_mono (Nat.succ_le_iff.mpr j.2)
      simpa [finiteFractionCoordinates, fractionCoordinates,
        analyticCoordinates] using S.tau_mem_stageGenerators_succ j.1

/-- Local power-generator transcendence makes the finite labeled coordinate
tuple injective.  Only indices strictly below the current stage are needed. -/
theorem finiteFractionCoordinates_injective_of_tauTranscendence {n : Nat}
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j))) :
    Function.Injective (S.finiteFractionCoordinates n) := by
  have hne_of_lt : ∀ {i j : StageVar n}, i.1 < j.1 →
      S.finiteFractionCoordinates n i ≠
        S.finiteFractionCoordinates n j := by
    intro i j hij heq
    cases j using Fin.cases with
    | zero =>
        simp at hij
    | succ q =>
        have hiq : i.1 ≤ q.1 := Nat.lt_succ_iff.mp hij
        have hqn : q.1 < n := q.2
        let u : S.finiteStageBeforeTau q.1 :=
          ⟨S.fractionCoordinates i.1,
            S.earlier_analyticCoordinate_mem_beforeTau hiq⟩
        apply htau q.1 hqn
        have halgebraic : IsAlgebraic (S.finiteStageBeforeTau q.1)
            (algebraMap (S.finiteStageBeforeTau q.1) K u) :=
          isAlgebraic_algebraMap u
        have halgebraic' : IsAlgebraic (S.finiteStageBeforeTau q.1)
            (S.fractionCoordinates i.1) := by
          simpa [u] using halgebraic
        change IsAlgebraic (S.finiteStageBeforeTau q.1)
          (S.fractionCoordinates (q.1 + 1))
        have heq' : S.fractionCoordinates i.1 =
            S.fractionCoordinates (q.1 + 1) := by
          simpa [finiteFractionCoordinates] using heq
        rw [← heq']
        exact halgebraic'
  intro i j hij
  apply Fin.ext
  rcases lt_trichotomy i.1 j.1 with hijlt | hijEq | hjilt
  · exact False.elim (hne_of_lt hijlt hij)
  · exact hijEq
  · exact False.elim (hne_of_lt hjilt hij.symm)

/-- Pull algebraic independence of the stage generator set back to the
labeled tuple `x, tau_0, ..., tau_(n-1)`. -/
theorem algebraicIndependent_finiteFractionCoordinates {n : Nat}
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    AlgebraicIndependent Real (S.finiteFractionCoordinates n) := by
  let f : StageVar n → S.stageGenerators n := fun i ↦
    ⟨S.finiteFractionCoordinates n i,
      S.finiteFractionCoordinate_mem_stageGenerators n i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply S.finiteFractionCoordinates_injective_of_tauTranscendence htau
    exact congrArg Subtype.val hij
  have hcomp := hstage.comp f hf
  simpa [f, Function.comp_def] using hcomp

/-- The labeled fraction coordinates are exactly the analytic stage
assignment followed by the inclusion into the fraction field. -/
theorem finiteFractionCoordinates_eq_analyticAssignment (n : Nat)
    (i : StageVar n) :
    S.finiteFractionCoordinates n i =
      ι (S.analyticAssignment n i) := by
  cases i using Fin.cases <;> rfl

/-- Algebraic independence of the labeled coordinates reflects equality of
integer-coefficient stage polynomials.  This is the precise coefficient
comparison principle used in Wilkie's induction. -/
theorem stagePolynomial_eval₂_injective_of_algebraicIndependent {n : Nat}
    (hcoord : AlgebraicIndependent Real
      (S.finiteFractionCoordinates n)) :
    Function.Injective
      (MvPolynomial.eval₂Hom (Int.castRingHom K)
        (S.finiteFractionCoordinates n)) := by
  intro p q hpq
  change MvPolynomial.eval₂ (Int.castRingHom K)
      (S.finiteFractionCoordinates n) p =
    MvPolynomial.eval₂ (Int.castRingHom K)
      (S.finiteFractionCoordinates n) q at hpq
  apply MvPolynomial.map_injective (Int.castRingHom Real)
    Int.cast_injective
  apply (algebraicIndependent_iff_injective_aeval.mp hcoord)
  have hcast :
      (algebraMap Real K).comp (Int.castRingHom Real) =
        Int.castRingHom K := by
    ext z
    simp
  simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
    hcast] using hpq

/-- Combined local form: the stage invariant and earlier `tau`
transcendence make analytic evaluation of integer stage polynomials
injective. -/
theorem stagePolynomial_eval₂_injective {n : Nat}
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    Function.Injective
      (MvPolynomial.eval₂Hom (Int.castRingHom K)
        (S.finiteFractionCoordinates n)) :=
  S.stagePolynomial_eval₂_injective_of_algebraicIndependent
    (S.algebraicIndependent_finiteFractionCoordinates htau hstage)

end GeneratorSequence

end

end Natfunbasis.Wilkie
