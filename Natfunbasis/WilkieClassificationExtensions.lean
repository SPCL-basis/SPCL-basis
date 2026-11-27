import Natfunbasis.WilkieStageClassification
import Natfunbasis.WilkieProposition31II
import Natfunbasis.WilkieStageTranscendenceReductions

/-!
# Transporting clause `(II)` through one differential adjunction

These are generic extension lemmas behind Wilkie's simultaneous induction.
Proposition 3.1(i) transports a logarithmic-derivative classification through
an exponential adjunction.  The valid, source-shaped part of Proposition
3.1(ii) does the same for a primitive logarithm adjunction once the necessary
integral-slope rigidity of the particular base field is supplied explicitly.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "K" => PositiveAnalyticFractionField

namespace GeneratorSequence

/-! ## Generic one-step transports -/

/-- Transport a logarithmic-derivative classification through a
transcendental exponential adjunction.  This is the exact abstract use of
Wilkie Proposition 3.1(i). -/
theorem logDerivClassification_adjoin_exponential
    (F : DifferentialIntermediateField Real K)
    (M M' : K → Prop)
    (beta : F) (z : K) (hz : Transcendental F z)
    (hzd : z′ = algebraMap F K beta′ * z)
    (hgenerator : ∀ x ∈ ({z} : Set K),
      x′ ∈ IntermediateField.adjoin F {z})
    (hbase : LogDerivClassification F M)
    (hstep : ∀ (m : Int) {u : K}, M u → M' (u * z ^ m)) :
    LogDerivClassification (F.adjoinOver {z} hgenerator) M' := by
  letI : Differential.ContainConstants F K :=
    F.containConstantsAmbient
  intro X Y hX0 heq
  let X' : IntermediateField.adjoin F {z} :=
    ⟨(X : K), X.2⟩
  let Y' : IntermediateField.adjoin F {z} :=
    ⟨(Y : K), Y.2⟩
  obtain ⟨m, u, v, hu0, hXu, _hYv, huv⟩ :=
    Proposition31.simpleAdjoin_proposition31_i
      beta z hz hzd X' Y' hX0 heq
  have huvAmbient : ((u : K))′ = ((v : K))′ * (u : K) := by
    have h := congrArg (fun q : F ↦ (q : K)) huv
    simpa using h
  have huM : M (u : K) := hbase u v (by simpa using hu0) huvAmbient
  rw [show (X : K) = (u : K) * z ^ m by simpa [X'] using hXu]
  exact hstep m huM

/-- Transport a logarithmic-derivative classification through a
transcendental primitive/logarithm adjunction.  The explicit rigidity premise
is precisely the extra property needed to recover the integral conclusion of
the printed Proposition 3.1(ii). -/
theorem logDerivClassification_adjoin_logarithm
    (F : DifferentialIntermediateField Real K)
    (M M' : K → Prop)
    (beta : F) (hbeta : beta ≠ 0)
    (hrigid : Proposition31II.IntegralSlopeRigidity beta)
    (z : K) (hz : Transcendental F z)
    (hzd : z′ = algebraMap F K (beta′ / beta))
    (hgenerator : ∀ x ∈ ({z} : Set K),
      x′ ∈ IntermediateField.adjoin F {z})
    (hbase : LogDerivClassification F M)
    (hstep : ∀ (m : Int) {u : K}, M u →
      M' (((beta ^ m : F) : K) * u)) :
    LogDerivClassification (F.adjoinOver {z} hgenerator) M' := by
  letI : Differential.ContainConstants F K :=
    F.containConstantsAmbient
  intro X Y hX0 heq
  let X' : IntermediateField.adjoin F {z} :=
    ⟨(X : K), X.2⟩
  let Y' : IntermediateField.adjoin F {z} :=
    ⟨(Y : K), Y.2⟩
  obtain ⟨m, u, v, hu0, hXu, _hYv, huv⟩ :=
    Proposition31II.simpleAdjoin_proposition31_ii_of_integralSlopeRigidity
      beta hbeta hrigid z hz hzd X' Y' hX0 heq
  have huvAmbient : ((u : K))′ = ((v : K))′ * (u : K) := by
    have h := congrArg (fun q : F ↦ (q : K)) huv
    simpa using h
  have huM : M (u : K) := hbase u v (by simpa using hu0) huvAmbient
  rw [show (X : K) = ((beta ^ m : F) : K) * (u : K) by
    simpa [X'] using hXu]
  exact hstep m huM

end GeneratorSequence

end

end Natfunbasis.Wilkie
