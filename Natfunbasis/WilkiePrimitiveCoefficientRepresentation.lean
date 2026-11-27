import Natfunbasis.WilkieMonomialPrimitives
import Natfunbasis.WilkieFiniteCoordinateIndependence
import Natfunbasis.WilkieW1CoefficientContradiction

/-!
# Finite coefficient representations of structured primitives

`StagePrimitive` and `BeforeTauPrimitive` are recursive predicates.  This
file flattens that recursion into the exact finite coefficient data needed by
later coefficient comparisons.

At completed stage `n`, a primitive is a real constant plus integral
multiples of `logX`, `tauPrimitive j` for `j < n`, and `logBaseAnalytic j`
for fresh `j < n`.  Immediately before adjoining `tau_n`, the same statement
holds with the possible fresh logarithm at index `n` added.  Coefficients of
non-fresh logarithms are required to be zero, so the representation does not
silently introduce spurious coordinates.
-/

namespace Natfunbasis.Wilkie

open scoped BigOperators

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Coefficients for a finite primitive expression.  `tauCount` bounds the
power-generator primitive indices and `logCount` bounds the fresh-logarithm
indices. -/
structure PrimitiveCoefficients (tauCount logCount : Nat) where
  constantCoeff : Real
  logXCoeff : Int
  tauCoeff : Fin tauCount → Int
  freshLogCoeff : Fin logCount → Int
  freshLogCoeff_eq_zero :
    ∀ j : Fin logCount, ¬ S.IsFreshBase j.1 → freshLogCoeff j = 0

namespace PrimitiveCoefficients

/-- Evaluate finite primitive coefficient data in the ambient analytic
fraction field. -/
def evaluate {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) : K :=
  algebraMap Real K C.constantCoeff +
    (C.logXCoeff : K) * OneVariableBaseField.logX +
    ∑ j : Fin tauCount,
      (C.tauCoeff j : K) * (S.tauPrimitive j.1 : K) +
    ∑ j : Fin logCount,
      (C.freshLogCoeff j : K) * ι (S.logBaseAnalytic j.1)

/-- Extend the finite tau-coefficient vector by zero to all natural indices.
This is the coefficient function shape consumed by the W1 contradiction
lemma. -/
def tauCoeffNat {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) : Nat → Int :=
  fun j ↦ if hj : j < tauCount then C.tauCoeff ⟨j, hj⟩ else 0

@[simp]
theorem tauCoeffNat_of_lt {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount)
    {j : Nat} (hj : j < tauCount) :
    tauCoeffNat S C j = C.tauCoeff ⟨j, hj⟩ := by
  simp [tauCoeffNat, hj]

@[simp]
theorem tauCoeffNat_of_fin {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) (j : Fin tauCount) :
    tauCoeffNat S C j.1 = C.tauCoeff j := by
  simp [tauCoeffNat, j.2]

@[simp]
theorem tauCoeffNat_of_ge {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount)
    {j : Nat} (hj : tauCount ≤ j) : tauCoeffNat S C j = 0 := by
  simp [tauCoeffNat, Nat.not_lt.mpr hj]

/-- Extend the finite fresh-log coefficient vector by zero to all natural
indices. -/
def freshLogCoeffNat {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) : Nat → Int :=
  fun j ↦ if hj : j < logCount then C.freshLogCoeff ⟨j, hj⟩ else 0

@[simp]
theorem freshLogCoeffNat_of_fin {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) (j : Fin logCount) :
    freshLogCoeffNat S C j.1 = C.freshLogCoeff j := by
  simp [freshLogCoeffNat, j.2]

@[simp]
theorem freshLogCoeffNat_of_ge {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount)
    {j : Nat} (hj : logCount ≤ j) : freshLogCoeffNat S C j = 0 := by
  simp [freshLogCoeffNat, Nat.not_lt.mpr hj]

theorem freshLogCoeffNat_eq_zero_of_not_fresh
    {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) {j : Nat}
    (hnot : ¬ S.IsFreshBase j) : freshLogCoeffNat S C j = 0 := by
  by_cases hj : j < logCount
  · rw [freshLogCoeffNat, dif_pos hj]
    exact C.freshLogCoeff_eq_zero ⟨j, hj⟩ hnot
  · simp [freshLogCoeffNat, hj]

/-- Reindex the tau part of `evaluate` by `Finset.range`, matching the natural
index set used by W1.3. -/
theorem tauSum_eq_sum_range {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) :
    (∑ j : Fin tauCount,
        (C.tauCoeff j : K) * (S.tauPrimitive j.1 : K)) =
      ∑ j ∈ Finset.range tauCount,
        (tauCoeffNat S C j : K) * (S.tauPrimitive j : K) := by
  simpa using Fin.sum_univ_eq_sum_range
    (fun j : Nat ↦
      (tauCoeffNat S C j : K) * (S.tauPrimitive j : K)) tauCount

/-- Reindex the fresh-log part of `evaluate` by `Finset.range`. -/
theorem freshLogSum_eq_sum_range {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) :
    (∑ j : Fin logCount,
        (C.freshLogCoeff j : K) * ι (S.logBaseAnalytic j.1)) =
      ∑ j ∈ Finset.range logCount,
        (freshLogCoeffNat S C j : K) * ι (S.logBaseAnalytic j) := by
  simpa using Fin.sum_univ_eq_sum_range
    (fun j : Nat ↦
      (freshLogCoeffNat S C j : K) * ι (S.logBaseAnalytic j)) logCount

/-- `evaluate` written entirely with natural-indexed finite sums. -/
theorem evaluate_eq_range_sums {tauCount logCount : Nat}
    (C : S.PrimitiveCoefficients tauCount logCount) :
    C.evaluate =
      algebraMap Real K C.constantCoeff +
        (C.logXCoeff : K) * OneVariableBaseField.logX +
        ∑ j ∈ Finset.range tauCount,
          (tauCoeffNat S C j : K) * (S.tauPrimitive j : K) +
        ∑ j ∈ Finset.range logCount,
          (freshLogCoeffNat S C j : K) *
            ι (S.logBaseAnalytic j) := by
  rw [evaluate, tauSum_eq_sum_range, freshLogSum_eq_sum_range]

/-- The stage-zero coefficient vector. -/
def base (c : Real) (m : Int) : S.PrimitiveCoefficients 0 0 where
  constantCoeff := c
  logXCoeff := m
  tauCoeff := Fin.elim0
  freshLogCoeff := Fin.elim0
  freshLogCoeff_eq_zero := fun j ↦ Fin.elim0 j

@[simp]
theorem evaluate_base (c : Real) (m : Int) :
    (base S c m).evaluate =
      algebraMap Real K c + (m : K) * OneVariableBaseField.logX := by
  simp [evaluate, base]

/-- Append the coefficient of `tauPrimitive n`.  Before `tau_n` there are
`n` previous tau primitives and `n+1` possible fresh-log slots; afterward
both bounds are `n+1`. -/
def appendTau {n : Nat} (C : S.PrimitiveCoefficients n (n + 1))
    (k : Int) : S.PrimitiveCoefficients (n + 1) (n + 1) where
  constantCoeff := C.constantCoeff
  logXCoeff := C.logXCoeff
  tauCoeff := Fin.snoc C.tauCoeff k
  freshLogCoeff := C.freshLogCoeff
  freshLogCoeff_eq_zero := C.freshLogCoeff_eq_zero

@[simp]
theorem evaluate_appendTau {n : Nat}
    (C : S.PrimitiveCoefficients n (n + 1)) (k : Int) :
    (appendTau S C k).evaluate =
      C.evaluate + (k : K) * (S.tauPrimitive n : K) := by
  simp [evaluate, appendTau, Fin.sum_univ_castSucc]
  ring

/-- Append the current logarithm coefficient.  The side condition says that
the new coefficient must vanish if the current base is not fresh. -/
def appendLog {n : Nat} (C : S.PrimitiveCoefficients n n)
    (m : Int) (hm : ¬ S.IsFreshBase n → m = 0) :
    S.PrimitiveCoefficients n (n + 1) where
  constantCoeff := C.constantCoeff
  logXCoeff := C.logXCoeff
  tauCoeff := C.tauCoeff
  freshLogCoeff := Fin.snoc C.freshLogCoeff m
  freshLogCoeff_eq_zero := by
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · intro hnot
      simpa using hm hnot
    · rw [Fin.snoc_castSucc]
      exact C.freshLogCoeff_eq_zero i

@[simp]
theorem evaluate_appendLog {n : Nat}
    (C : S.PrimitiveCoefficients n n) (m : Int)
    (hm : ¬ S.IsFreshBase n → m = 0) :
    (appendLog S C m hm).evaluate =
      (m : K) * ι (S.logBaseAnalytic n) + C.evaluate := by
  simp [evaluate, appendLog, Fin.sum_univ_castSucc]
  ring

end PrimitiveCoefficients

/-- Earlier indices carrying the same global base polynomial as the current
index.  This is exactly the finite index set used by W1.3 after collecting
the coefficient of the current logarithm. -/
def priorSameBaseIndices (n : Nat) : Finset Nat := by
  classical
  exact (Finset.range n).filter
    (fun j ↦ S.baseGlobal j = S.baseGlobal n)

@[simp]
theorem mem_priorSameBaseIndices {n j : Nat} :
    j ∈ S.priorSameBaseIndices n ↔
      j < n ∧ S.baseGlobal j = S.baseGlobal n := by
  classical
  simp [priorSameBaseIndices]

theorem priorSameBaseIndices_lt {n j : Nat}
    (hj : j ∈ S.priorSameBaseIndices n) : j < n :=
  (S.mem_priorSameBaseIndices.mp hj).1

theorem priorSameBaseIndices_base_eq {n j : Nat}
    (hj : j ∈ S.priorSameBaseIndices n) :
    S.baseGlobal j = S.baseGlobal n :=
  (S.mem_priorSameBaseIndices.mp hj).2

/-- Direct adapter from a primitive's finite tau coefficients to the W1.3
coefficient contradiction. -/
theorem no_currentExponent_linearCombination_of_primitiveTauCoefficients
    {n logCount : Nat} (coeffs : S.PrimitiveCoefficients n logCount)
    (constant slope : Int) (hslope : slope ≠ 0)
    (hpoly :
      MvPolynomial.C constant +
          ∑ j ∈ S.priorSameBaseIndices n,
            MvPolynomial.C (PrimitiveCoefficients.tauCoeffNat S coeffs j) *
              S.exponentGlobal j =
        MvPolynomial.C slope * S.exponentGlobal n) :
    False :=
  S.no_currentExponent_linearCombination_of_sameBase n
    (S.priorSameBaseIndices n)
    (PrimitiveCoefficients.tauCoeffNat S coeffs)
    constant slope hslope
    (fun _j hj ↦ S.priorSameBaseIndices_lt hj)
    (fun _j hj ↦ S.priorSameBaseIndices_base_eq hj)
    hpoly

/-! ## Flattening the recursive primitive predicates -/

/-- Simultaneous finite-coefficient representation of completed-stage and
pre-`tau` primitives. -/
theorem stagePrimitive_exists_coefficients_and_beforeTauPrimitive_exists_coefficients :
    ∀ n : Nat,
      (∀ {L : K}, S.StagePrimitive n L →
        ∃ C : S.PrimitiveCoefficients n n, L = C.evaluate) ∧
      (∀ {L : K}, S.BeforeTauPrimitive n L →
        ∃ C : S.PrimitiveCoefficients n (n + 1), L = C.evaluate) := by
  intro n
  induction n with
  | zero =>
      have hstage : ∀ {L : K}, S.StagePrimitive 0 L →
          ∃ C : S.PrimitiveCoefficients 0 0, L = C.evaluate := by
        intro L hL
        rw [S.stagePrimitive_zero_iff] at hL
        obtain ⟨c, m, rfl⟩ := hL
        exact ⟨PrimitiveCoefficients.base S c m,
          (PrimitiveCoefficients.evaluate_base S c m).symm⟩
      refine ⟨hstage, ?_⟩
      intro L hL
      classical
      by_cases hfresh : S.IsFreshBase 0
      · rw [S.beforeTauPrimitive_iff_of_fresh hfresh] at hL
        obtain ⟨m, U, hU, rfl⟩ := hL
        obtain ⟨C, hUC⟩ := hstage hU
        let hm : ¬ S.IsFreshBase 0 → m = 0 :=
          fun hnot ↦ False.elim (hnot hfresh)
        refine ⟨PrimitiveCoefficients.appendLog S C m hm, ?_⟩
        rw [PrimitiveCoefficients.evaluate_appendLog S, ← hUC]
      · rw [S.beforeTauPrimitive_iff_of_not_fresh hfresh] at hL
        obtain ⟨C, hLC⟩ := hstage hL
        let hm : ¬ S.IsFreshBase 0 → (0 : Int) = 0 := fun _ ↦ rfl
        refine ⟨PrimitiveCoefficients.appendLog S C 0 hm, ?_⟩
        rw [PrimitiveCoefficients.evaluate_appendLog S, ← hLC]
        simp
  | succ n ih =>
      have hstage : ∀ {L : K}, S.StagePrimitive (n + 1) L →
          ∃ C : S.PrimitiveCoefficients (n + 1) (n + 1),
            L = C.evaluate := by
        intro L hL
        rw [S.stagePrimitive_succ_iff] at hL
        obtain ⟨k, W, hW, rfl⟩ := hL
        obtain ⟨C, hWC⟩ := ih.2 hW
        refine ⟨PrimitiveCoefficients.appendTau S C k, ?_⟩
        rw [PrimitiveCoefficients.evaluate_appendTau S, ← hWC]
      refine ⟨hstage, ?_⟩
      intro L hL
      classical
      by_cases hfresh : S.IsFreshBase (n + 1)
      · rw [S.beforeTauPrimitive_iff_of_fresh hfresh] at hL
        obtain ⟨m, U, hU, rfl⟩ := hL
        obtain ⟨C, hUC⟩ := hstage hU
        let hm : ¬ S.IsFreshBase (n + 1) → m = 0 :=
          fun hnot ↦ False.elim (hnot hfresh)
        refine ⟨PrimitiveCoefficients.appendLog S C m hm, ?_⟩
        rw [PrimitiveCoefficients.evaluate_appendLog S, ← hUC]
      · rw [S.beforeTauPrimitive_iff_of_not_fresh hfresh] at hL
        obtain ⟨C, hLC⟩ := hstage hL
        let hm : ¬ S.IsFreshBase (n + 1) → (0 : Int) = 0 := fun _ ↦ rfl
        refine ⟨PrimitiveCoefficients.appendLog S C 0 hm, ?_⟩
        rw [PrimitiveCoefficients.evaluate_appendLog S, ← hLC]
        simp

/-- Every completed-stage primitive has the flattened finite coefficient
representation. -/
theorem stagePrimitive_exists_coefficients {n : Nat} {L : K}
    (hL : S.StagePrimitive n L) :
    ∃ C : S.PrimitiveCoefficients n n, L = C.evaluate :=
  (S.stagePrimitive_exists_coefficients_and_beforeTauPrimitive_exists_coefficients n).1 hL

/-- Every pre-`tau` primitive has the flattened representation, including the
current logarithm exactly when its base is fresh. -/
theorem beforeTauPrimitive_exists_coefficients {n : Nat} {L : K}
    (hL : S.BeforeTauPrimitive n L) :
    ∃ C : S.PrimitiveCoefficients n (n + 1), L = C.evaluate :=
  (S.stagePrimitive_exists_coefficients_and_beforeTauPrimitive_exists_coefficients n).2 hL

/-- Unbundled completed-stage representation with natural-indexed coefficient
functions.  Both coefficient functions are zero outside their finite stage,
and the logarithm coefficients also vanish at every non-fresh index. -/
theorem stagePrimitive_exists_range_coefficients {n : Nat} {L : K}
    (hL : S.StagePrimitive n L) :
    ∃ (c : Real) (m : Int) (tauCoefficients freshLogCoefficients : Nat → Int),
      (∀ j : Nat, n ≤ j → tauCoefficients j = 0) ∧
      (∀ j : Nat, n ≤ j → freshLogCoefficients j = 0) ∧
      (∀ j : Nat, ¬ S.IsFreshBase j → freshLogCoefficients j = 0) ∧
      L = algebraMap Real K c +
        (m : K) * OneVariableBaseField.logX +
        ∑ j ∈ Finset.range n,
          (tauCoefficients j : K) * (S.tauPrimitive j : K) +
        ∑ j ∈ Finset.range n,
          (freshLogCoefficients j : K) *
            ι (S.logBaseAnalytic j) := by
  obtain ⟨C, hC⟩ := S.stagePrimitive_exists_coefficients hL
  refine ⟨C.constantCoeff, C.logXCoeff,
    PrimitiveCoefficients.tauCoeffNat S C,
    PrimitiveCoefficients.freshLogCoeffNat S C, ?_, ?_, ?_, ?_⟩
  · exact fun j hj ↦ PrimitiveCoefficients.tauCoeffNat_of_ge S C hj
  · exact fun j hj ↦ PrimitiveCoefficients.freshLogCoeffNat_of_ge S C hj
  · exact fun _j hnot ↦
      PrimitiveCoefficients.freshLogCoeffNat_eq_zero_of_not_fresh S C hnot
  · exact hC.trans (PrimitiveCoefficients.evaluate_eq_range_sums S C)

/-- Unbundled pre-`tau` representation.  Tau coefficients are supported below
`n`; fresh-log coefficients are supported below `n+1`, permitting precisely
the current fresh logarithm in addition to the earlier ones. -/
theorem beforeTauPrimitive_exists_range_coefficients {n : Nat} {L : K}
    (hL : S.BeforeTauPrimitive n L) :
    ∃ (c : Real) (m : Int) (tauCoefficients freshLogCoefficients : Nat → Int),
      (∀ j : Nat, n ≤ j → tauCoefficients j = 0) ∧
      (∀ j : Nat, n + 1 ≤ j → freshLogCoefficients j = 0) ∧
      (∀ j : Nat, ¬ S.IsFreshBase j → freshLogCoefficients j = 0) ∧
      L = algebraMap Real K c +
        (m : K) * OneVariableBaseField.logX +
        ∑ j ∈ Finset.range n,
          (tauCoefficients j : K) * (S.tauPrimitive j : K) +
        ∑ j ∈ Finset.range (n + 1),
          (freshLogCoefficients j : K) *
            ι (S.logBaseAnalytic j) := by
  obtain ⟨C, hC⟩ := S.beforeTauPrimitive_exists_coefficients hL
  refine ⟨C.constantCoeff, C.logXCoeff,
    PrimitiveCoefficients.tauCoeffNat S C,
    PrimitiveCoefficients.freshLogCoeffNat S C, ?_, ?_, ?_, ?_⟩
  · exact fun j hj ↦ PrimitiveCoefficients.tauCoeffNat_of_ge S C hj
  · exact fun j hj ↦ PrimitiveCoefficients.freshLogCoeffNat_of_ge S C hj
  · exact fun _j hnot ↦
      PrimitiveCoefficients.freshLogCoeffNat_eq_zero_of_not_fresh S C hnot
  · exact hC.trans (PrimitiveCoefficients.evaluate_eq_range_sums S C)

end GeneratorSequence

end

end Natfunbasis.Wilkie
