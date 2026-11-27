import Natfunbasis.WilkieStageAlgebraicIndependence
import Natfunbasis.CanonicalWilkieCoordinates

/-!
# From finite-stage independence to the canonical coordinate family

Wilkie's induction is formulated for finite sets containing `x`, `log x`,
the auxiliary power generators, and the logarithms of fresh bases.  The
normalizer needs only the countable family `(x, tau_0, tau_1, ...)`.

This file proves the elementary passage between those formulations.  Thus,
after the local transcendence obligations in Theorem 4.4 have been proved,
there is no further compactness or infinite-support argument left implicit.
-/

namespace Natfunbasis.Wilkie

open Set

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The bundled analytic coordinates associated with a generator sequence:
the original input followed by its recursively constructed powers. -/
def analyticCoordinates : Nat → A
  | 0 => inputAnalyticFunction
  | n + 1 => S.realTauAnalyticFunction n

/-- The same coordinates embedded in the ambient analytic fraction field. -/
def fractionCoordinates (i : Nat) : K :=
  ι (S.analyticCoordinates i)

/-! ## The increasing union of finite stages -/

/-- Every completed generator stage is contained in its successor. -/
theorem stageGenerators_subset_succ (n : Nat) :
    S.stageGenerators n ⊆ S.stageGenerators (n + 1) := by
  rw [stageGenerators_succ]
  intro z hz
  simp only [Set.mem_insert_iff]
  right
  classical
  by_cases hfresh : S.IsFreshBase n
  · rw [beforeTauGenerators_eq_of_fresh S hfresh]
    exact Set.mem_insert_of_mem _ hz
  · simpa [beforeTauGenerators_eq_of_not_fresh S hfresh] using hz

/-- The finite-stage generator sets form a monotone sequence. -/
theorem stageGenerators_mono : Monotone S.stageGenerators :=
  monotone_nat_of_le_succ S.stageGenerators_subset_succ

/-- Algebraic independence at every finite stage implies algebraic
independence of their increasing union. -/
theorem algebraicIndepOn_iUnion_stageGenerators
    (hstage : ∀ n, AlgebraicIndepOn Real id (S.stageGenerators n)) :
    AlgebraicIndepOn Real id (⋃ n, S.stageGenerators n) := by
  apply algebraicIndependent_iUnion_of_directed
  · exact S.stageGenerators_mono.directed_le
  · exact hstage

/-! ## The coordinate family is contained in the union -/

/-- The original coordinate belongs to the union of completed stages. -/
theorem x_mem_iUnion_stageGenerators :
    OneVariableBaseField.x ∈ ⋃ n, S.stageGenerators n := by
  apply Set.mem_iUnion.mpr
  refine ⟨0, ?_⟩
  simp [stageGenerators]

/-- The `n`th auxiliary power generator belongs to completed stage `n+1`. -/
theorem tau_mem_stageGenerators_succ (n : Nat) :
    ι (S.realTauAnalyticFunction n) ∈ S.stageGenerators (n + 1) := by
  rw [stageGenerators_succ]
  exact Set.mem_insert _ _

/-- The analytic fraction-field image of every coordinate lies in the union
of the finite-stage generator sets. -/
theorem analyticCoordinate_mem_iUnion_stageGenerators (i : Nat) :
    S.fractionCoordinates i ∈ ⋃ n, S.stageGenerators n := by
  cases i with
  | zero =>
      simpa [fractionCoordinates, analyticCoordinates,
        OneVariableBaseField.x] using S.x_mem_iUnion_stageGenerators
  | succ n =>
      apply Set.mem_iUnion.mpr
      refine ⟨n + 1, ?_⟩
      change ι (S.realTauAnalyticFunction n) ∈
        S.stageGenerators (n + 1)
      exact S.tau_mem_stageGenerators_succ n

/-- Finite-stage algebraic independence already implies algebraic
independence of the unbundled family `(x, tau_0, tau_1, ...)` in the ambient
fraction field. -/
theorem algebraicIndependent_fractionCoordinates_of_stage
    (hinj : Function.Injective S.fractionCoordinates)
    (hstage : ∀ n, AlgebraicIndepOn Real id (S.stageGenerators n)) :
    AlgebraicIndependent Real S.fractionCoordinates := by
  let U : Set K := ⋃ n, S.stageGenerators n
  have hU : AlgebraicIndependent Real ((↑) : U → K) := by
    exact S.algebraicIndepOn_iUnion_stageGenerators hstage
  let f : Nat → K := S.fractionCoordinates
  have hfU : Set.range f ⊆ U := by
    rintro z ⟨i, rfl⟩
    exact S.analyticCoordinate_mem_iUnion_stageGenerators i
  have hrange : AlgebraicIndependent Real ((↑) : Set.range f → K) :=
    hU.mono hfU
  exact (algebraicIndependent_subtype_range hinj).mp hrange

/-- Every coordinate strictly before `tau_n` belongs to the actual field
over which `tau_n` is adjoined. -/
theorem earlier_analyticCoordinate_mem_beforeTau {i n : Nat} (hi : i ≤ n) :
    S.fractionCoordinates i ∈ S.finiteStageBeforeTau n := by
  cases i with
  | zero =>
      simpa [fractionCoordinates, analyticCoordinates,
        OneVariableBaseField.x] using
        S.finiteStageField_le_beforeTau n (S.x_mem_finiteStageField n)
  | succ j =>
      have hj : j < n := by omega
      simpa [fractionCoordinates, analyticCoordinates] using
        S.finiteStageField_le_beforeTau n
          (S.tau_mem_finiteStageField hj)

/-- Transcendence of each newly adjoined power generator forces the indexed
coordinate family to have no repetitions. -/
theorem analyticFractionCoordinates_injective_of_tauTranscendence
    (htau : ∀ n,
      Transcendental (S.finiteStageBeforeTau n).toIntermediateField
        (ι (S.realTauAnalyticFunction n))) :
    Function.Injective S.fractionCoordinates := by
  have hne_of_lt : ∀ {i j : Nat}, i < j →
      S.fractionCoordinates i ≠ S.fractionCoordinates j := by
    intro i j hij heq
    cases j with
    | zero => omega
    | succ n =>
        have hi : i ≤ n := Nat.lt_succ_iff.mp hij
        let u : S.finiteStageBeforeTau n :=
          ⟨S.fractionCoordinates i,
            S.earlier_analyticCoordinate_mem_beforeTau hi⟩
        apply htau n
        have halgebraic : IsAlgebraic (S.finiteStageBeforeTau n)
            (algebraMap (S.finiteStageBeforeTau n) K u) :=
          isAlgebraic_algebraMap u
        have halgebraic' : IsAlgebraic (S.finiteStageBeforeTau n)
            (S.fractionCoordinates i) := by
          simpa [u] using halgebraic
        change IsAlgebraic (S.finiteStageBeforeTau n)
          (S.fractionCoordinates (n + 1))
        rw [← heq]
        exact halgebraic'
  intro i j hij
  rcases lt_trichotomy i j with hijlt | hijEq | hjilt
  · exact False.elim (hne_of_lt hijlt hij)
  · exact hijEq
  · exact False.elim (hne_of_lt hjilt hij.symm)

/-- The local logarithm and power transcendence statements of the finite
stage induction imply algebraic independence of the entire fraction-field
coordinate family. -/
theorem algebraicIndependent_fractionCoordinates_of_transcendence
    (hlog : ∀ n, S.IsFreshBase n →
      Transcendental (S.finiteStageField n).toIntermediateField
        (ι (S.logBaseAnalytic n)))
    (htau : ∀ n,
      Transcendental (S.finiteStageBeforeTau n).toIntermediateField
        (ι (S.realTauAnalyticFunction n))) :
    AlgebraicIndependent Real S.fractionCoordinates := by
  apply S.algebraicIndependent_fractionCoordinates_of_stage
    (S.analyticFractionCoordinates_injective_of_tauTranscendence htau)
  exact S.algebraicIndepOn_stageGenerators_of_transcendence hlog htau

end GeneratorSequence

/-! ## Specialization to the fixed canonical sequence -/

/-- The coercion from bundled positive-axis analytic functions to ordinary
functions is an injective real-algebra homomorphism. -/
def PositiveAnalyticFunction.coeAlgHom :
    PositiveAnalyticFunction →ₐ[Real] PositiveRealFunction :=
  positiveAnalyticSubalgebra.val

theorem PositiveAnalyticFunction.coeAlgHom_injective :
    Function.Injective PositiveAnalyticFunction.coeAlgHom :=
  by
    intro f g hfg
    exact Subtype.ext hfg

/-- The generic coordinate family for the fixed sequence is the already
named canonical bundled analytic family. -/
theorem canonical_analyticCoordinates_eq :
    canonicalGeneratorSequence.analyticCoordinates =
      canonicalAnalyticCoordinates := by
  funext i
  cases i with
  | zero =>
      apply Subtype.ext
      rfl
  | succ n =>
      apply Subtype.ext
      rfl

/-- Consequently their fraction-field images agree pointwise. -/
theorem canonical_fractionCoordinates_eq (i : Nat) :
    canonicalGeneratorSequence.fractionCoordinates i =
      algebraMap A K (canonicalAnalyticCoordinates i) := by
  change algebraMap A K
      (canonicalGeneratorSequence.analyticCoordinates i) = _
  rw [canonical_analyticCoordinates_eq]

theorem canonical_fractionCoordinates_eq_family :
    canonicalGeneratorSequence.fractionCoordinates =
      fun i ↦ algebraMap A K (canonicalAnalyticCoordinates i) := by
  funext i
  exact canonical_fractionCoordinates_eq i

theorem coe_canonicalAnalyticCoordinates_eq_family :
    PositiveAnalyticFunction.coeAlgHom ∘ canonicalAnalyticCoordinates =
      canonicalRealCoordinates := by
  funext i
  rfl

/-- The precise finite-to-infinite conclusion used by the normalizer: proving
all finite stages of the canonical Wilkie induction proves
`CanonicalWilkieIndependence`. -/
theorem canonicalWilkieIndependence_of_stage
    (hinj : Function.Injective
      canonicalGeneratorSequence.fractionCoordinates)
    (hstage : ∀ n,
      AlgebraicIndepOn Real id
        (canonicalGeneratorSequence.stageGenerators n)) :
    CanonicalWilkieIndependence := by
  let inclusion : A →ₐ[Real] K :=
    IsScalarTower.toAlgHom Real A K
  have hfraction :=
    canonicalGeneratorSequence.algebraicIndependent_fractionCoordinates_of_stage
      hinj hstage
  have hanalytic : AlgebraicIndependent Real canonicalAnalyticCoordinates := by
    apply AlgebraicIndependent.of_comp inclusion
    change AlgebraicIndependent Real
      (fun i ↦ algebraMap A K (canonicalAnalyticCoordinates i))
    rw [← canonical_fractionCoordinates_eq_family]
    exact hfraction
  have hfunctions := hanalytic.map'
    PositiveAnalyticFunction.coeAlgHom_injective
  rw [coe_canonicalAnalyticCoordinates_eq_family] at hfunctions
  exact hfunctions

/-- Fully local finite-stage handoff: the two transcendence inputs isolated
by Wilkie's induction imply the exact canonical independence proposition.
This theorem adds no further mathematical premise. -/
theorem canonicalWilkieIndependence_of_transcendence
    (hlog : ∀ n, canonicalGeneratorSequence.IsFreshBase n →
      Transcendental
        (canonicalGeneratorSequence.finiteStageField n).toIntermediateField
        (ι (canonicalGeneratorSequence.logBaseAnalytic n)))
    (htau : ∀ n,
      Transcendental
        (canonicalGeneratorSequence.finiteStageBeforeTau n).toIntermediateField
        (ι (canonicalGeneratorSequence.realTauAnalyticFunction n))) :
    CanonicalWilkieIndependence := by
  let inclusion : A →ₐ[Real] K :=
    IsScalarTower.toAlgHom Real A K
  have hfraction :=
    canonicalGeneratorSequence.algebraicIndependent_fractionCoordinates_of_transcendence
      hlog htau
  have hanalytic : AlgebraicIndependent Real canonicalAnalyticCoordinates := by
    apply AlgebraicIndependent.of_comp inclusion
    change AlgebraicIndependent Real
      (fun i ↦ algebraMap A K (canonicalAnalyticCoordinates i))
    rw [← canonical_fractionCoordinates_eq_family]
    exact hfraction
  have hfunctions := hanalytic.map'
    PositiveAnalyticFunction.coeAlgHom_injective
  rw [coe_canonicalAnalyticCoordinates_eq_family] at hfunctions
  exact hfunctions

end

end Natfunbasis.Wilkie
