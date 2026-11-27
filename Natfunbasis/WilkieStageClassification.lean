import Natfunbasis.WilkieInfiniteIndependence
import Natfunbasis.WilkieRationalExtension

/-!
# The logarithmic-derivative classification invariant at finite stages

Clause `(II)_n` of Wilkie's Theorem 4.4 says that every nonzero solution of
`X' = Y' X` in the `n`th differential field is, up to a nonzero real scalar,
an integral monomial in the generators accumulated so far.  This file gives
that assertion a compact recursive Lean formulation.

The recursive form mirrors the two adjunctions exactly: a fresh base may be
inserted before `tau_n`, and `tau_n` is then inserted to form stage `n+1`.
It avoids choosing and transporting explicit exponent vectors at every
stage, while retaining their complete mathematical content.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-! ## Recursive integral monomials -/

/-- Integral monomials available after the first `n` power adjunctions.

At stage zero these are `c * x^m`.  At a successor, an optional fresh base
factor is inserted first, followed by an integral power of `tau_n`. -/
def StageMonomial (S : GeneratorSequence D) : (n : Nat) → K → Prop
  | 0, X => ∃ c : Real, c ≠ 0 ∧ ∃ m : Int,
      X = algebraMap Real K c * OneVariableBaseField.x ^ m
  | n + 1, X => ∃ k : Int, ∃ w : K,
      ((S.IsFreshBase n ∧
          ∃ m : Int, ∃ u : K, S.StageMonomial n u ∧
            w = ι (S.baseAnalytic n) ^ m * u) ∨
        (¬ S.IsFreshBase n ∧ S.StageMonomial n w)) ∧
      X = w * ι (S.realTauAnalyticFunction n) ^ k

/-- Integral monomials in the field immediately before adjoining `tau_n`.
In the fresh case this adds an integral power of the current base; otherwise
it is exactly the completed-stage predicate. -/
def BeforeTauMonomial (S : GeneratorSequence D) (n : Nat) (X : K) : Prop :=
  (S.IsFreshBase n ∧
      ∃ m : Int, ∃ u : K, S.StageMonomial n u ∧
        X = ι (S.baseAnalytic n) ^ m * u) ∨
    (¬ S.IsFreshBase n ∧ S.StageMonomial n X)

@[simp]
theorem stageMonomial_zero_iff {X : K} :
    S.StageMonomial 0 X ↔
      ∃ c : Real, c ≠ 0 ∧ ∃ m : Int,
        X = algebraMap Real K c * OneVariableBaseField.x ^ m :=
  Iff.rfl

@[simp]
theorem stageMonomial_succ_iff {n : Nat} {X : K} :
    S.StageMonomial (n + 1) X ↔
      ∃ k : Int, ∃ w : K, S.BeforeTauMonomial n w ∧
        X = w * ι (S.realTauAnalyticFunction n) ^ k :=
  Iff.rfl

theorem beforeTauMonomial_iff_of_fresh {n : Nat}
    (hfresh : S.IsFreshBase n) {X : K} :
    S.BeforeTauMonomial n X ↔
      ∃ m : Int, ∃ u : K, S.StageMonomial n u ∧
        X = ι (S.baseAnalytic n) ^ m * u := by
  constructor
  · rintro (⟨_, h⟩ | ⟨hnot, _⟩)
    · exact h
    · exact False.elim (hnot hfresh)
  · intro h
    exact Or.inl ⟨hfresh, h⟩

theorem beforeTauMonomial_iff_of_not_fresh {n : Nat}
    (hfresh : ¬ S.IsFreshBase n) {X : K} :
    S.BeforeTauMonomial n X ↔ S.StageMonomial n X := by
  constructor
  · rintro (⟨hf, _⟩ | ⟨_, h⟩)
    · exact False.elim (hfresh hf)
    · exact h
  · intro h
    exact Or.inr ⟨hfresh, h⟩

theorem beforeTauMonomial_of_stage (n : Nat) {X : K}
    (hX : S.StageMonomial n X) : S.BeforeTauMonomial n X := by
  classical
  by_cases hfresh : S.IsFreshBase n
  · rw [S.beforeTauMonomial_iff_of_fresh hfresh]
    exact ⟨0, X, hX, by simp⟩
  · rwa [S.beforeTauMonomial_iff_of_not_fresh hfresh]

theorem beforeTauMonomial_mul_base_zpow {n : Nat}
    (hfresh : S.IsFreshBase n) {X : K}
    (hX : S.StageMonomial n X) (m : Int) :
    S.BeforeTauMonomial n (ι (S.baseAnalytic n) ^ m * X) := by
  rw [S.beforeTauMonomial_iff_of_fresh hfresh]
  exact ⟨m, X, hX, rfl⟩

theorem stageMonomial_succ_mul_tau_zpow {n : Nat} {X : K}
    (hX : S.BeforeTauMonomial n X) (m : Int) :
    S.StageMonomial (n + 1)
      (X * ι (S.realTauAnalyticFunction n) ^ m) := by
  rw [stageMonomial_succ_iff]
  exact ⟨m, X, hX, rfl⟩

/-! ## Membership in the corresponding differential fields -/

/-- The substituted current base belongs to the completed current stage. -/
theorem baseAnalytic_mem_finiteStageField (n : Nat) :
    ι (S.baseAnalytic n) ∈ S.finiteStageField n :=
  S.baseAnalytic_mem (S.finiteStageField n)
    (S.x_mem_finiteStageField n)
    (fun _ hj ↦ S.tau_mem_finiteStageField hj)

/-- Every recursively described monomial lies in the field whose generators
occur in its description; likewise for the pre-`tau` predicate. -/
theorem stageMonomial_mem_and_beforeTauMonomial_mem : ∀ n : Nat,
    (∀ {X : K}, S.StageMonomial n X → X ∈ S.finiteStageField n) ∧
    (∀ {X : K}, S.BeforeTauMonomial n X →
      X ∈ S.finiteStageBeforeTau n) := by
  intro n
  induction n with
  | zero =>
      have hstage : ∀ {X : K}, S.StageMonomial 0 X →
          X ∈ S.finiteStageField 0 := by
        intro X hX
        obtain ⟨c, _hc, m, rfl⟩ := hX
        exact mul_mem ((S.finiteStageField 0).algebraMap_mem c)
          (zpow_mem (S.x_mem_finiteStageField 0) m)
      refine ⟨hstage, ?_⟩
      intro X hX
      classical
      by_cases hfresh : S.IsFreshBase 0
      · rw [S.beforeTauMonomial_iff_of_fresh hfresh] at hX
        obtain ⟨m, u, hu, rfl⟩ := hX
        apply mul_mem
        · exact zpow_mem
            (S.finiteStageField_le_beforeTau 0
              (S.baseAnalytic_mem_finiteStageField 0)) m
        · exact S.finiteStageField_le_beforeTau 0 (hstage hu)
      · rw [S.beforeTauMonomial_iff_of_not_fresh hfresh] at hX
        exact S.finiteStageField_le_beforeTau 0 (hstage hX)
  | succ n ih =>
      have hstage : ∀ {X : K}, S.StageMonomial (n + 1) X →
          X ∈ S.finiteStageField (n + 1) := by
        intro X hX
        rw [stageMonomial_succ_iff] at hX
        obtain ⟨m, w, hw, rfl⟩ := hX
        apply mul_mem
        · exact S.finiteStageBeforeTau_le_succ n (ih.2 hw)
        · exact zpow_mem (S.current_tau_mem_finiteStageField n) m
      refine ⟨hstage, ?_⟩
      intro X hX
      classical
      by_cases hfresh : S.IsFreshBase (n + 1)
      · rw [S.beforeTauMonomial_iff_of_fresh hfresh] at hX
        obtain ⟨m, u, hu, rfl⟩ := hX
        apply mul_mem
        · exact zpow_mem
            (S.finiteStageField_le_beforeTau (n + 1)
              (S.baseAnalytic_mem_finiteStageField (n + 1))) m
        · exact S.finiteStageField_le_beforeTau (n + 1) (hstage hu)
      · rw [S.beforeTauMonomial_iff_of_not_fresh hfresh] at hX
        exact S.finiteStageField_le_beforeTau (n + 1) (hstage hX)

theorem stageMonomial_mem {n : Nat} {X : K}
    (hX : S.StageMonomial n X) : X ∈ S.finiteStageField n :=
  (S.stageMonomial_mem_and_beforeTauMonomial_mem n).1 hX

theorem beforeTauMonomial_mem {n : Nat} {X : K}
    (hX : S.BeforeTauMonomial n X) :
    X ∈ S.finiteStageBeforeTau n :=
  (S.stageMonomial_mem_and_beforeTauMonomial_mem n).2 hX

/-! ## Clause `(II)` as a reusable predicate -/

/-- Logarithmic-derivative classification for a specified differential
intermediate field and a specified ambient monomial predicate. -/
def LogDerivClassification
    (F : DifferentialIntermediateField Real K) (M : K → Prop) : Prop :=
  ∀ (X Y : F), (X : K) ≠ 0 →
    ((X : K))′ = ((Y : K))′ * (X : K) → M (X : K)

/-- Wilkie clause `(II)_n` for the completed `n`th stage. -/
def StageLogDerivClassification (n : Nat) : Prop :=
  LogDerivClassification (S.finiteStageField n) (S.StageMonomial n)

/-- The corresponding classification immediately before adjoining
`tau_n`. -/
def BeforeTauLogDerivClassification (n : Nat) : Prop :=
  LogDerivClassification (S.finiteStageBeforeTau n)
    (S.BeforeTauMonomial n)

end GeneratorSequence

end

end Natfunbasis.Wilkie
