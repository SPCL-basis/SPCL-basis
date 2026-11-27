import Natfunbasis.WilkieGeneratorFieldRelations

/-!
# Recursive finite-stage differential fields for a Wilkie generator sequence

This file formalizes the field-membership part of Wilkie's induction.  The
initial field is `Real(x, log x)`.  At stage `k` we first adjoin
`log u_k` exactly when the base `u_k` is fresh, and then adjoin the power
generator `tau_k`.

The analytic differential equations prove that both adjunctions remain
closed under differentiation.  The resulting stage contains the input,
`log x`, every earlier power generator, and the logarithm of every earlier
fresh base.  No algebraic-independence assertion is made here.
-/

namespace Natfunbasis.Wilkie

open Set
open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- A differential field after `n` power-generator stages, together with
the cumulative membership invariants used by the next stage. -/
structure DifferentialStage (n : Nat) where
  field : DifferentialIntermediateField Real K
  x_mem : OneVariableBaseField.x ∈ field
  logX_mem : OneVariableBaseField.logX ∈ field
  tau_mem : ∀ j < n, ι (S.realTauAnalyticFunction j) ∈ field
  freshLog_mem : ∀ j < n, S.IsFreshBase j →
    ι (S.logBaseAnalytic j) ∈ field

namespace DifferentialStage

/-- Stage zero is the concrete differential field `Real(x, log x)`. -/
def initial : S.DifferentialStage 0 where
  field := OneVariableBaseField.F0
  x_mem := OneVariableBaseField.x_mem_F0
  logX_mem := OneVariableBaseField.logX_mem_F0
  tau_mem := by
    intro j hj
    exact (Nat.not_lt_zero j hj).elim
  freshLog_mem := by
    intro j hj
    exact (Nat.not_lt_zero j hj).elim

variable {S}

private theorem base_deriv_mem (P : S.DifferentialStage n) :
    (ι (S.baseAnalytic n))′ ∈ P.field := by
  apply P.field.deriv_mem
  exact S.baseAnalytic_mem P.field P.x_mem P.tau_mem

/-- Before adjoining `tau_n`, adjoin the new logarithm precisely when its
base polynomial is fresh. -/
def beforeTau (P : S.DifferentialStage n) :
    DifferentialIntermediateField Real K := by
  classical
  exact if hfresh : S.IsFreshBase n then
    P.field.adjoinOver {ι (S.logBaseAnalytic n)} (by
      intro z hz
      have hz' : z = ι (S.logBaseAnalytic n) := by simpa using hz
      subst z
      change PositiveAnalyticFractionField.derivation
        (ι (S.logBaseAnalytic n)) ∈
          IntermediateField.adjoin P.field
            {ι (S.logBaseAnalytic n)}
      rw [PositiveAnalyticFractionField.derivation_logBaseAnalytic]
      have hquot :
          (ι (S.baseAnalytic n))′ / ι (S.baseAnalytic n) ∈ P.field :=
        div_mem (base_deriv_mem P)
          (S.baseAnalytic_mem P.field P.x_mem P.tau_mem)
      let q : P.field := ⟨_, hquot⟩
      exact IntermediateField.algebraMap_mem
        (IntermediateField.adjoin P.field {ι (S.logBaseAnalytic n)}) q)
  else
    P.field

/-- The old stage embeds in the pre-`tau` field. -/
theorem le_beforeTau (P : S.DifferentialStage n) :
    P.field ≤ P.beforeTau := by
  classical
  by_cases hfresh : S.IsFreshBase n
  · rw [beforeTau, dif_pos hfresh]
    exact P.field.le_adjoinOver _ _
  · rw [beforeTau, dif_neg hfresh]

/-- A fresh logarithm at the current index belongs to the pre-`tau` field. -/
theorem current_log_mem_beforeTau (P : S.DifferentialStage n)
    (hfresh : S.IsFreshBase n) :
    ι (S.logBaseAnalytic n) ∈ P.beforeTau := by
  rw [beforeTau, dif_pos hfresh]
  exact P.field.subset_adjoinOver _ _ (by simp)

/-- The logarithm of the current base belongs to the pre-`tau` field whether
the base is constant, original, fresh, or a repetition of an earlier fresh
base. -/
theorem logBase_mem_beforeTau (P : S.DifferentialStage n) :
    ι (S.logBaseAnalytic n) ∈ P.beforeTau := by
  apply S.logBaseAnalytic_mem_of_fresh_le P.beforeTau
  · exact P.le_beforeTau P.logX_mem
  · intro j hj hjfresh
    by_cases hjn : j = n
    · subst j
      exact P.current_log_mem_beforeTau hjfresh
    · exact P.le_beforeTau
        (P.freshLog_mem j (lt_of_le_of_ne hj hjn) hjfresh)

/-- The current substituted base belongs already to the pre-`tau` field. -/
theorem base_mem_beforeTau (P : S.DifferentialStage n) :
    ι (S.baseAnalytic n) ∈ P.beforeTau :=
  S.baseAnalytic_mem P.beforeTau
    (P.le_beforeTau P.x_mem)
    (fun j hj ↦ P.le_beforeTau (P.tau_mem j hj))

/-- The current substituted exponent belongs already to the pre-`tau`
field. -/
theorem exponent_mem_beforeTau (P : S.DifferentialStage n) :
    ι (S.exponentAnalytic n) ∈ P.beforeTau :=
  S.exponentAnalytic_mem P.beforeTau
    (P.le_beforeTau P.x_mem)
    (fun j hj ↦ P.le_beforeTau (P.tau_mem j hj))

private theorem tau_deriv_mem_adjoin (P : S.DifferentialStage n) :
    (ι (S.realTauAnalyticFunction n))′ ∈
      IntermediateField.adjoin P.beforeTau
        {ι (S.realTauAnalyticFunction n)} := by
  change PositiveAnalyticFractionField.derivation
    (ι (S.realTauAnalyticFunction n)) ∈
      IntermediateField.adjoin P.beforeTau
        {ι (S.realTauAnalyticFunction n)}
  rw [PositiveAnalyticFractionField.derivation_realTauAnalyticFunction]
  let E : IntermediateField P.beforeTau K :=
    IntermediateField.adjoin P.beforeTau
      {ι (S.realTauAnalyticFunction n)}
  have hle {z : K} (hz : z ∈ P.beforeTau) : z ∈ E := by
    let z' : P.beforeTau := ⟨z, hz⟩
    exact IntermediateField.algebraMap_mem E z'
  have htau : ι (S.realTauAnalyticFunction n) ∈ E :=
    IntermediateField.subset_adjoin P.beforeTau _ (by simp)
  have hbase : ι (S.baseAnalytic n) ∈ E :=
    hle P.base_mem_beforeTau
  have hexponent : ι (S.exponentAnalytic n) ∈ E :=
    hle P.exponent_mem_beforeTau
  have hlog : ι (S.logBaseAnalytic n) ∈ E :=
    hle P.logBase_mem_beforeTau
  have hdbase : (ι (S.baseAnalytic n))′ ∈ E :=
    hle (P.beforeTau.deriv_mem P.base_mem_beforeTau)
  have hdexponent : (ι (S.exponentAnalytic n))′ ∈ E :=
    hle (P.beforeTau.deriv_mem P.exponent_mem_beforeTau)
  exact mul_mem htau <| add_mem
    (mul_mem hdexponent hlog)
    (div_mem (mul_mem hexponent hdbase) hbase)

/-- Adjoin the current power generator after the optional logarithm step. -/
def nextField (P : S.DifferentialStage n) :
    DifferentialIntermediateField Real K :=
  P.beforeTau.adjoinOver {ι (S.realTauAnalyticFunction n)} (by
    intro z hz
    have hz' : z = ι (S.realTauAnalyticFunction n) := by simpa using hz
    subst z
    exact tau_deriv_mem_adjoin P)

/-- The pre-`tau` field embeds in the completed next stage. -/
theorem beforeTau_le_nextField (P : S.DifferentialStage n) :
    P.beforeTau ≤ P.nextField :=
  P.beforeTau.le_adjoinOver _ _

/-- The current power generator belongs to the completed next stage. -/
theorem current_tau_mem_nextField (P : S.DifferentialStage n) :
    ι (S.realTauAnalyticFunction n) ∈ P.nextField :=
  P.beforeTau.subset_adjoinOver _ _ (by simp)

/-- One complete logarithm/power adjunction step, with all cumulative
membership invariants transported to stage `n + 1`. -/
def next (P : S.DifferentialStage n) : S.DifferentialStage (n + 1) where
  field := P.nextField
  x_mem := P.beforeTau_le_nextField (P.le_beforeTau P.x_mem)
  logX_mem := P.beforeTau_le_nextField (P.le_beforeTau P.logX_mem)
  tau_mem := by
    intro j hj
    by_cases hjn : j = n
    · subst j
      exact P.current_tau_mem_nextField
    · exact P.beforeTau_le_nextField
        (P.le_beforeTau (P.tau_mem j (by omega)))
  freshLog_mem := by
    intro j hj hjfresh
    by_cases hjn : j = n
    · subst j
      exact P.beforeTau_le_nextField
        (P.current_log_mem_beforeTau hjfresh)
    · exact P.beforeTau_le_nextField
        (P.le_beforeTau (P.freshLog_mem j (by omega) hjfresh))

end DifferentialStage

/-! ## The recursively constructed tower -/

/-- The packaged differential field after the first `n` generators. -/
def differentialStage : (n : Nat) → S.DifferentialStage n
  | 0 => DifferentialStage.initial S
  | n + 1 => (differentialStage n).next

/-- The differential intermediate field after the first `n` generators. -/
def finiteStageField (n : Nat) : DifferentialIntermediateField Real K :=
  (S.differentialStage n).field

/-- The optional fresh-logarithm field immediately before adjoining
`tau_n`. -/
def finiteStageBeforeTau (n : Nat) :
    DifferentialIntermediateField Real K :=
  (S.differentialStage n).beforeTau

@[simp]
theorem finiteStageField_zero :
    S.finiteStageField 0 = OneVariableBaseField.F0 :=
  rfl

theorem finiteStageField_le_beforeTau (n : Nat) :
    S.finiteStageField n ≤ S.finiteStageBeforeTau n :=
  (S.differentialStage n).le_beforeTau

theorem finiteStageBeforeTau_le_succ (n : Nat) :
    S.finiteStageBeforeTau n ≤ S.finiteStageField (n + 1) :=
  (S.differentialStage n).beforeTau_le_nextField

theorem finiteStageField_mono_step (n : Nat) :
    S.finiteStageField n ≤ S.finiteStageField (n + 1) :=
  (S.finiteStageField_le_beforeTau n).trans
    (S.finiteStageBeforeTau_le_succ n)

@[simp]
theorem x_mem_finiteStageField (n : Nat) :
    OneVariableBaseField.x ∈ S.finiteStageField n :=
  (S.differentialStage n).x_mem

@[simp]
theorem logX_mem_finiteStageField (n : Nat) :
    OneVariableBaseField.logX ∈ S.finiteStageField n :=
  (S.differentialStage n).logX_mem

theorem tau_mem_finiteStageField {j n : Nat} (hj : j < n) :
    ι (S.realTauAnalyticFunction j) ∈ S.finiteStageField n :=
  (S.differentialStage n).tau_mem j hj

theorem freshLog_mem_finiteStageField {j n : Nat} (hj : j < n)
    (hfresh : S.IsFreshBase j) :
    ι (S.logBaseAnalytic j) ∈ S.finiteStageField n :=
  (S.differentialStage n).freshLog_mem j hj hfresh

theorem current_log_mem_finiteStageBeforeTau {n : Nat}
    (hfresh : S.IsFreshBase n) :
    ι (S.logBaseAnalytic n) ∈ S.finiteStageBeforeTau n :=
  (S.differentialStage n).current_log_mem_beforeTau hfresh

theorem logBase_mem_finiteStageBeforeTau (n : Nat) :
    ι (S.logBaseAnalytic n) ∈ S.finiteStageBeforeTau n :=
  (S.differentialStage n).logBase_mem_beforeTau

theorem current_tau_mem_finiteStageField (n : Nat) :
    ι (S.realTauAnalyticFunction n) ∈ S.finiteStageField (n + 1) :=
  (S.differentialStage n).current_tau_mem_nextField

/-- Every finite stage is closed under the ambient analytic derivation. -/
theorem deriv_mem_finiteStageField {n : Nat} {z : K}
    (hz : z ∈ S.finiteStageField n) : z′ ∈ S.finiteStageField n :=
  (S.finiteStageField n).deriv_mem hz

end GeneratorSequence

end

end Natfunbasis.Wilkie
