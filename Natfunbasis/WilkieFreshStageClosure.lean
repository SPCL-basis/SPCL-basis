import Natfunbasis.WilkieCoefficientInduction
import Natfunbasis.WilkieFreshStagePrimeDerivation
import Natfunbasis.WilkieBeforeTauPolynomialCoordinates
import Natfunbasis.WilkieRealDescent
import Natfunbasis.WilkieNonTangency

/-!
# Closing fresh-stage integral-slope rigidity

This file discharges `FreshStageIntegralSlopeRigidity`, the last premise of
Wilkie's finite-stage induction, and hence proves
`CanonicalWilkieIndependence`.

* **Denominators.**  With `Wⱼ = x·∏_{i<j} uᵢ`, every stage generator has a
  derivative in `ℝ[Gⱼ][Wⱼ⁻¹]` (`stageCleared`), and before `τⱼ` the generators
  and the logarithmic derivative of `τⱼ` lie in `ℝ[Bⱼ][W_{j+1}⁻¹]`.
* **Non-tangency.**  At a fresh stage the real coordinate base `U` is
  squarefree, coprime to `W`, and does not divide its polynomial derivative:
  the exponential Darboux argument is applied at the top variable of `U`.
* **Rigidity.**  The repository's residue reduction then gives integral
  slopes.  Rigidity at stage `n` uses only the induction data below `n`, so the
  finite-stage induction closes with no premise.
-/

open MvPolynomial
open scoped Differential

namespace Natfunbasis.Wilkie

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "Kₐ" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A Kₐ)

/-! ## Cleared subalgebras -/

namespace Cleared

/-- Elements `z` with `w ^ k * z ∈ ℝ[s]` for some `k`. -/
def sub (s : Set Kₐ) (w : Kₐ) (hw : w ∈ Algebra.adjoin ℝ s) :
    Subalgebra ℝ Kₐ where
  carrier := {z | ∃ k : ℕ, w ^ k * z ∈ Algebra.adjoin ℝ s}
  mul_mem' := by
    rintro a b ⟨k₁, h₁⟩ ⟨k₂, h₂⟩
    refine ⟨k₁ + k₂, ?_⟩
    have := mul_mem h₁ h₂
    convert this using 1
    ring
  add_mem' := by
    rintro a b ⟨k₁, h₁⟩ ⟨k₂, h₂⟩
    refine ⟨k₁ + k₂, ?_⟩
    have := add_mem (mul_mem (pow_mem hw k₂) h₁) (mul_mem (pow_mem hw k₁) h₂)
    convert this using 1
    ring
  algebraMap_mem' := by
    intro r
    exact ⟨0, by simp⟩

theorem mem_sub {s : Set Kₐ} {w : Kₐ} {hw : w ∈ Algebra.adjoin ℝ s} {z : Kₐ} :
    z ∈ sub s w hw ↔ ∃ k : ℕ, w ^ k * z ∈ Algebra.adjoin ℝ s :=
  Iff.rfl

theorem adjoin_le {s : Set Kₐ} {w : Kₐ} (hw : w ∈ Algebra.adjoin ℝ s) :
    Algebra.adjoin ℝ s ≤ sub s w hw :=
  fun z hz ↦ ⟨0, by simpa using hz⟩

theorem subset {s : Set Kₐ} {w : Kₐ} (hw : w ∈ Algebra.adjoin ℝ s) :
    s ⊆ sub s w hw :=
  fun _ hz ↦ adjoin_le hw (Algebra.subset_adjoin hz)

theorem inv_mem {s : Set Kₐ} {w : Kₐ} (hw : w ∈ Algebra.adjoin ℝ s)
    (hw0 : w ≠ 0) : w⁻¹ ∈ sub s w hw :=
  ⟨1, by rw [pow_one, mul_inv_cancel₀ hw0]; exact one_mem _⟩

theorem mono {s s' : Set Kₐ} {w w' v : Kₐ} {hw : w ∈ Algebra.adjoin ℝ s}
    (hw' : w' ∈ Algebra.adjoin ℝ s') (hss : s ⊆ s')
    (hv : v ∈ Algebra.adjoin ℝ s') (hwv : w' = w * v) {z : Kₐ}
    (hz : z ∈ sub s w hw) : z ∈ sub s' w' hw' := by
  obtain ⟨k, hk⟩ := hz
  refine ⟨k, ?_⟩
  have := mul_mem (pow_mem hv k) (Algebra.adjoin_mono hss hk)
  rw [hwv]
  convert this using 1
  ring

/-- Finitely many cleared elements share one clearing exponent. -/
theorem exists_uniform {s : Set Kₐ} {w : Kₐ} {hw : w ∈ Algebra.adjoin ℝ s}
    (t : Set Kₐ) (ht : t.Finite) (f : Kₐ → Kₐ)
    (h : ∀ g ∈ t, f g ∈ sub s w hw) :
    ∃ K : ℕ, ∀ g ∈ t, w ^ K * f g ∈ Algebra.adjoin ℝ s := by
  induction t, ht using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a t _ _ ih =>
      obtain ⟨K₁, hK₁⟩ := ih fun g hg ↦ h g (Set.mem_insert_of_mem a hg)
      obtain ⟨k, hk⟩ := h a (Set.mem_insert a t)
      refine ⟨K₁ + k, ?_⟩
      intro g hg
      rcases hg with rfl | hg
      · have := mul_mem (pow_mem hw K₁) hk
        convert this using 1
        ring
      · have := mul_mem (pow_mem hw k) (hK₁ g hg)
        convert this using 1
        ring

end Cleared

theorem deriv_algebraMap_real (r : ℝ) : (algebraMap ℝ Kₐ r)′ = 0 :=
  PositiveAnalyticFractionField.derivation_algebraMap_real r

theorem deriv_mul_K (a b : Kₐ) : (a * b)′ = a * b′ + b * a′ := by
  letI : Algebra ℤ Kₐ := Ring.toIntAlgebra Kₐ
  have h := Differential.deriv.leibniz a b
  simpa only [smul_eq_mul] using h

/-- A derivative-closed subalgebra containing the generators contains the
derivatives of the whole generated algebra. -/
theorem deriv_mem_of_mem_adjoin {s : Set Kₐ} {T : Subalgebra ℝ Kₐ}
    (hsT : s ⊆ T) (hd : ∀ g ∈ s, g′ ∈ T) {z : Kₐ}
    (hz : z ∈ Algebra.adjoin ℝ s) : z′ ∈ T := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact hd x hx
  | algebraMap r => rw [deriv_algebraMap_real]; exact zero_mem T
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
      rw [deriv_mul_K]
      exact add_mem (mul_mem (Algebra.adjoin_le hsT hx') hy)
        (mul_mem (Algebra.adjoin_le hsT hy') hx)

theorem exists_aeval_eq_of_mem_adjoin {s : Set Kₐ} {z : Kₐ}
    (hz : z ∈ Algebra.adjoin ℝ s) :
    ∃ p : MvPolynomial s ℝ, aeval ((↑) : s → Kₐ) p = z := by
  have hadj := Algebra.adjoin_range_eq_range_aeval ℝ ((↑) : s → Kₐ)
  rw [Subtype.range_coe] at hadj
  rw [hadj] at hz
  exact hz

/-- A real polynomial derivation prescribed by `c`-scaled derivatives of the
generators realizes `c·(d/dx)`. -/
theorem aeval_mkDerivation {s : Set Kₐ} (c : Kₐ) (num : s → MvPolynomial s ℝ)
    (hnum : ∀ g : s, aeval ((↑) : s → Kₐ) (num g) = c * (g : Kₐ)′)
    (a : MvPolynomial s ℝ) :
    aeval ((↑) : s → Kₐ) (MvPolynomial.mkDerivation ℝ num a) =
      c * (aeval ((↑) : s → Kₐ) a)′ := by
  induction a using MvPolynomial.induction_on with
  | C r =>
      have h0 : MvPolynomial.mkDerivation ℝ num (C r) = 0 :=
        (MvPolynomial.mkDerivation ℝ num).map_algebraMap r
      rw [h0, map_zero, aeval_C, deriv_algebraMap_real, mul_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p g hp =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul,
        map_mul, MvPolynomial.mkDerivation_X, hnum, hp, map_mul, aeval_X,
        deriv_mul_K]
      ring

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-! ## Denominators of generator derivatives -/

/-- Wilkie's common denominator `Wⱼ = x·∏_{i<j} uᵢ`. -/
def denomW (j : ℕ) : Kₐ :=
  OneVariableBaseField.x * ∏ i ∈ Finset.range j, ι (S.baseAnalytic i)

theorem denomW_succ (j : ℕ) :
    S.denomW (j + 1) = S.denomW j * ι (S.baseAnalytic j) := by
  simp [denomW, Finset.prod_range_succ, mul_assoc]

theorem baseAnalytic_ne_zero' (j : ℕ) : ι (S.baseAnalytic j) ≠ 0 := by
  intro h
  apply S.currentBaseElement_ne_zero j
  exact Subtype.ext h

theorem denomW_ne_zero (j : ℕ) : S.denomW j ≠ 0 :=
  mul_ne_zero OneVariableBaseField.x_ne_zero
    (Finset.prod_ne_zero_iff.2 fun i _ ↦ S.baseAnalytic_ne_zero' i)

theorem stagePolynomialEval_mem_adjoin (n : ℕ) (p : StagePolynomial n) :
    S.stagePolynomialEval n p ∈ Algebra.adjoin ℝ (S.stageGenerators n) := by
  rw [← S.aeval_stageCoordinatePolynomial]
  have hadj := Algebra.adjoin_range_eq_range_aeval ℝ
    ((↑) : S.stageGenerators n → Kₐ)
  rw [Subtype.range_coe] at hadj
  rw [hadj]
  exact ⟨_, rfl⟩

theorem baseAnalytic_mem_adjoin {i j : ℕ} (h : i ≤ j) :
    ι (S.baseAnalytic i) ∈ Algebra.adjoin ℝ (S.stageGenerators j) := by
  rw [← S.stagePolynomialEval_basePolynomialAtStage j i h]
  exact S.stagePolynomialEval_mem_adjoin j _

theorem exponentAnalytic_mem_adjoin {i j : ℕ} (h : i ≤ j) :
    ι (S.exponentAnalytic i) ∈ Algebra.adjoin ℝ (S.stageGenerators j) := by
  rw [← S.stagePolynomialEval_exponentPolynomialAtStage j i h]
  exact S.stagePolynomialEval_mem_adjoin j _

theorem x_mem_stageGenerators (j : ℕ) :
    OneVariableBaseField.x ∈ S.stageGenerators j := by
  apply S.stageGenerators_mono (Nat.zero_le j)
  simp [stageGenerators]

theorem denomW_mem_adjoin (j : ℕ) :
    S.denomW j ∈ Algebra.adjoin ℝ (S.stageGenerators j) :=
  mul_mem (Algebra.subset_adjoin (S.x_mem_stageGenerators j))
    (prod_mem fun _ hi ↦
      S.baseAnalytic_mem_adjoin (Finset.mem_range.1 hi).le)

theorem stageGenerators_subset_beforeTau (j : ℕ) :
    S.stageGenerators j ⊆ S.beforeTauGenerators j :=
  S.stageGenerators_subset_beforeTauGenerators j

theorem beforeTau_subset_stageGenerators_succ (j : ℕ) :
    S.beforeTauGenerators j ⊆ S.stageGenerators (j + 1) := by
  rw [stageGenerators_succ]
  exact Set.subset_insert _ _

theorem denomW_succ_mem_adjoin_beforeTau (j : ℕ) :
    S.denomW (j + 1) ∈ Algebra.adjoin ℝ (S.beforeTauGenerators j) := by
  rw [denomW_succ]
  exact Algebra.adjoin_mono (S.stageGenerators_subset_beforeTau j)
    (mul_mem (S.denomW_mem_adjoin j) (S.baseAnalytic_mem_adjoin le_rfl))

theorem logBase_mem_adjoin_beforeTau (j : ℕ) :
    ι (S.logBaseAnalytic j) ∈ Algebra.adjoin ℝ (S.beforeTauGenerators j) := by
  by_cases hc : S.IsConstantBase j
  · obtain ⟨c, hc'⟩ := S.exists_logBaseFraction_eq_real_of_constant hc
    rw [hc']
    exact Subalgebra.algebraMap_mem _ c
  · exact Algebra.subset_adjoin
      (S.logBase_mem_beforeTauGenerators_of_not_constant le_rfl hc)

/-- The logarithmic derivative of `τⱼ`. -/
def tauLog (j : ℕ) : Kₐ :=
  (ι (S.exponentAnalytic j))′ * ι (S.logBaseAnalytic j) +
    ι (S.exponentAnalytic j) * (ι (S.baseAnalytic j))′ / ι (S.baseAnalytic j)

theorem deriv_tau (j : ℕ) :
    (ι (S.realTauAnalyticFunction j))′ =
      ι (S.realTauAnalyticFunction j) * S.tauLog j :=
  PositiveAnalyticFractionField.derivation_realTauAnalyticFunction S j

theorem deriv_logBase (j : ℕ) :
    (ι (S.logBaseAnalytic j))′ =
      (ι (S.baseAnalytic j))′ / ι (S.baseAnalytic j) :=
  PositiveAnalyticFractionField.derivation_logBaseAnalytic S j

/-- Every stage generator has a derivative in `ℝ[Gⱼ][Wⱼ⁻¹]`. -/
def StageCleared (j : ℕ) : Prop :=
  ∀ g ∈ S.stageGenerators j,
    g′ ∈ Cleared.sub (S.stageGenerators j) (S.denomW j) (S.denomW_mem_adjoin j)

/-- Before `τⱼ`, generator derivatives and `τⱼ′/τⱼ` lie in
`ℝ[Bⱼ][W_{j+1}⁻¹]`. -/
def BeforeCleared (j : ℕ) : Prop :=
  (∀ g ∈ S.beforeTauGenerators j,
    g′ ∈ Cleared.sub (S.beforeTauGenerators j) (S.denomW (j + 1))
      (S.denomW_succ_mem_adjoin_beforeTau j)) ∧
  S.tauLog j ∈ Cleared.sub (S.beforeTauGenerators j) (S.denomW (j + 1))
      (S.denomW_succ_mem_adjoin_beforeTau j)

theorem stageCleared_zero : S.StageCleared 0 := by
  intro g hg
  simp only [stageGenerators_zero, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [OneVariableBaseField.deriv_x]
    exact one_mem _
  · rw [OneVariableBaseField.deriv_logX]
    have h := Cleared.inv_mem (S.denomW_mem_adjoin 0) (S.denomW_ne_zero 0)
    simpa [denomW] using h

theorem beforeCleared_of_stageCleared {j : ℕ} (hj : S.StageCleared j) :
    S.BeforeCleared j := by
  set T := Cleared.sub (S.beforeTauGenerators j) (S.denomW (j + 1))
    (S.denomW_succ_mem_adjoin_beforeTau j)
  set T₀ := Cleared.sub (S.stageGenerators j) (S.denomW j)
    (S.denomW_mem_adjoin j)
  have hGB := S.stageGenerators_subset_beforeTau j
  have hu : ι (S.baseAnalytic j) ∈ Algebra.adjoin ℝ (S.beforeTauGenerators j) :=
    Algebra.adjoin_mono hGB (S.baseAnalytic_mem_adjoin le_rfl)
  have hmono : ∀ z, z ∈ T₀ → z ∈ T := fun z hz ↦
    Cleared.mono (S.denomW_succ_mem_adjoin_beforeTau j) hGB hu
      (S.denomW_succ j) hz
  have hderiv : ∀ z ∈ Algebra.adjoin ℝ (S.stageGenerators j), z′ ∈ T := by
    intro z hz
    exact hmono _ (deriv_mem_of_mem_adjoin (Cleared.subset _) hj hz)
  have hadjT : ∀ z ∈ Algebra.adjoin ℝ (S.beforeTauGenerators j), z ∈ T :=
    fun z hz ↦ Cleared.adjoin_le _ hz
  have hinv : (ι (S.baseAnalytic j))⁻¹ ∈ T := by
    refine ⟨1, ?_⟩
    rw [pow_one, denomW_succ, mul_assoc, mul_inv_cancel₀ (S.baseAnalytic_ne_zero' j),
      mul_one]
    exact Algebra.adjoin_mono hGB (S.denomW_mem_adjoin j)
  have hu' := hderiv _ (S.baseAnalytic_mem_adjoin (j := j) le_rfl)
  have hs' := hderiv _ (S.exponentAnalytic_mem_adjoin (j := j) le_rfl)
  have hs := hadjT _ (Algebra.adjoin_mono hGB (S.exponentAnalytic_mem_adjoin le_rfl))
  have hlog := hadjT _ (S.logBase_mem_adjoin_beforeTau j)
  refine ⟨?_, ?_⟩
  · intro g hg
    by_cases hfresh : S.IsFreshBase j
    · rw [S.beforeTauGenerators_eq_of_fresh hfresh] at hg
      rcases hg with rfl | hg
      · rw [deriv_logBase, div_eq_mul_inv]
        exact mul_mem hu' hinv
      · exact hmono _ (hj g hg)
    · rw [S.beforeTauGenerators_eq_of_not_fresh hfresh] at hg
      exact hmono _ (hj g hg)
  · rw [tauLog, mul_div_assoc, div_eq_mul_inv]
    exact add_mem (mul_mem hs' hlog) (mul_mem hs (mul_mem hu' hinv))

theorem stageCleared_succ {j : ℕ} (hb : S.BeforeCleared j) :
    S.StageCleared (j + 1) := by
  have hmono : ∀ z, z ∈ Cleared.sub (S.beforeTauGenerators j) (S.denomW (j + 1))
      (S.denomW_succ_mem_adjoin_beforeTau j) →
      z ∈ Cleared.sub (S.stageGenerators (j + 1)) (S.denomW (j + 1))
        (S.denomW_mem_adjoin (j + 1)) := fun z hz ↦
    Cleared.mono (S.denomW_mem_adjoin (j + 1))
      (S.beforeTau_subset_stageGenerators_succ j) (one_mem _)
      (mul_one _).symm hz
  intro g hg
  rw [stageGenerators_succ] at hg
  rcases hg with rfl | hg
  · rw [deriv_tau]
    exact mul_mem (Cleared.subset _ (S.tau_mem_stageGenerators_succ j))
      (hmono _ hb.2)
  · exact hmono _ (hb.1 g hg)

theorem stageCleared : ∀ j, S.StageCleared j
  | 0 => S.stageCleared_zero
  | j + 1 => S.stageCleared_succ (S.beforeCleared_of_stageCleared (stageCleared j))

theorem beforeCleared (j : ℕ) : S.BeforeCleared j :=
  S.beforeCleared_of_stageCleared (S.stageCleared j)

/-! ## The fresh base at stage `n` -/

/-- The integer denominator polynomial `x·∏_{i<n} pᵢ` at stage `n`. -/
def denomIntPolynomial (n : ℕ) : StagePolynomial n :=
  X 0 * ∏ i : Fin n, S.basePolynomialAtStage n i i.2.le

theorem stagePolynomialEval_denomInt (n : ℕ) :
    S.stagePolynomialEval n (S.denomIntPolynomial n) = S.denomW n := by
  rw [denomIntPolynomial, map_mul, map_prod, stagePolynomialEval_X,
    analyticAssignment_zero]
  simp only [stagePolynomialEval_basePolynomialAtStage]
  rw [denomW, Fin.prod_univ_eq_prod_range (fun i ↦ ι (S.baseAnalytic i)) n]
  rfl

theorem not_dvd_denomInt {n : ℕ} (hfresh : S.IsFreshBase n) :
    ¬ S.currentBasePolynomial n ∣ S.denomIntPolynomial n := by
  have hp := S.currentBasePolynomial_prime n
  intro h
  rw [denomIntPolynomial] at h
  rcases hp.dvd_or_dvd h with h | h
  · exact S.currentBasePolynomial_not_dvd_X hfresh 0 h
  · obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff hp _).1 h
    exact S.currentBasePolynomial_not_dvd_earlierBase hfresh i.2 hi

theorem stageGeneratorCoordinateIndex_injective' {n : ℕ}
    (hpriorTau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j)
        (ι (S.realTauAnalyticFunction j))) :
    Function.Injective (S.stageGeneratorCoordinateIndex n) := by
  intro i j hij
  apply S.finiteFractionCoordinates_injective_of_tauTranscendence hpriorTau
  exact congrArg Subtype.val hij

theorem constants_real (z : Kₐ) (hz : z′ = 0) :
    ∃ r : ℝ, z = algebraMap ℝ Kₐ r := by
  obtain ⟨r, hr⟩ := mem_range_of_deriv_eq_zero Real hz
  exact ⟨r, hr.symm⟩

theorem not_isUnit_X' {σ : Type*} (i : σ) :
    ¬ IsUnit (X i : MvPolynomial σ ℝ) := by
  classical
  intro h
  obtain ⟨r, _, hr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
  have h1 : MvPolynomial.coeff (Finsupp.single i 1) (X i : MvPolynomial σ ℝ) = 1 := by
    rw [MvPolynomial.coeff_X, if_pos rfl]
  have h2 : MvPolynomial.coeff (Finsupp.single i 1) (C r : MvPolynomial σ ℝ) = 0 := by
    rw [MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
  rw [hr, h2] at h1
  exact zero_ne_one h1

set_option maxHeartbeats 1000000 in
/-- **Non-tangency of the fresh base.**  No polynomial derivation realizing
`w·(d/dx)`, with `w` coprime to the base, is tangent to the base. -/
theorem stageCoordinateBase_not_dvd {n : ℕ}
    (hpriorTau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j)
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hfresh : S.IsFreshBase n)
    (Dp : S.StageCoordinateRing n →+ S.StageCoordinateRing n)
    (Wp : S.StageCoordinateRing n)
    (hDp : ∀ p, aeval ((↑) : S.stageGenerators n → Kₐ) (Dp p) =
      aeval ((↑) : S.stageGenerators n → Kₐ) Wp *
        (aeval ((↑) : S.stageGenerators n → Kₐ) p)′)
    (hUW : IsRelPrime (S.stageCoordinateBasePolynomial n) Wp) :
    ¬ S.stageCoordinateBasePolynomial n ∣ Dp (S.stageCoordinateBasePolynomial n) := by
  classical
  set f := S.currentBasePolynomial n with hf
  set idx := S.stageGeneratorCoordinateIndex n with hidxdef
  set U := S.stageCoordinateBasePolynomial n with hUdef
  have hidx : Function.Injective idx :=
    S.stageGeneratorCoordinateIndex_injective' hpriorTau
  have hU : U = RealDescent.realLift idx f := rfl
  have hfirr : Irreducible f := (S.currentBasePolynomial_prime n).irreducible
  have hXU : ∀ i : StageVar n, ¬ X (idx i) ∣ U := by
    intro i h
    have hrel := RealDescent.isRelPrime_realLift hidx hfirr
      (S.currentBasePolynomial_not_dvd_X hfresh i)
    have hXi : RealDescent.realLift idx (X i) = X (idx i) := by
      simp [RealDescent.realLift]
    rw [hXi, ← hU] at hrel
    exact not_isUnit_X' _ (hrel h (dvd_refl _))
  have hvarsU : ∀ v ∈ U.vars, ∃ i ∈ f.vars, idx i = v := by
    intro v hv
    rw [hU] at hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (vars_rename idx _ hv)
    exact ⟨i, MvPolynomial.vars_map (S.currentBasePolynomial n) (Int.castRingHom ℝ) hi,
      rfl⟩
  have hmemU : ∀ i, i ∈ f.vars → idx i ∈ U.vars := by
    intro i hi
    rw [mem_vars_iff_degreeOf_ne_zero] at hi ⊢
    rw [hU, RealDescent.degreeOf_realLift hidx]
    exact hi
  have hcoeIdx : ∀ i, ((idx i : S.stageGenerators n) : Kₐ) =
      S.finiteFractionCoordinates n i := fun _ ↦ rfl
  by_cases hJ : ∃ j : Fin n, j.succ ∈ f.vars
  · -- the top variable is a power generator `τ_m`
    let J : Finset (Fin n) := Finset.univ.filter (fun j ↦ j.succ ∈ f.vars)
    have hJne : J.Nonempty := by
      obtain ⟨j, hj⟩ := hJ
      exact ⟨j, by simp [J, hj]⟩
    set m := J.max' hJne with hmdef
    have hmJ : m.succ ∈ f.vars := (Finset.mem_filter.1 (J.max'_mem hJne)).2
    have hle : ∀ j : Fin n, j.succ ∈ f.vars → j ≤ m :=
      fun j hj ↦ J.le_max' j (by simp [J, hj])
    let t : S.stageGenerators n := idx m.succ
    have ht_val : (t : Kₐ) = ι (S.realTauAnalyticFunction m) := by
      rw [hcoeIdx, S.finiteFractionCoordinates_succ]
    have hmn : m.1 + 1 ≤ n := m.2
    have hgens : S.beforeTauGenerators m ⊆ S.stageGenerators n :=
      (S.beforeTau_subset_stageGenerators_succ m).trans (S.stageGenerators_mono hmn)
    have htg : (t : Kₐ) ∉ S.beforeTauGenerators m := by
      intro h
      rw [ht_val] at h
      have htr : Transcendental (S.finiteStageBeforeTau m).toIntermediateField
          (ι (S.realTauAnalyticFunction m)) := hpriorTau m m.2
      rw [S.finiteStageBeforeTau_toIntermediateField_eq_adjoin m] at htr
      have htr' := (IntermediateField.transcendental_adjoin_iff
        (F := Real) (s := S.beforeTauGenerators m)
        (x := ι (S.realTauAnalyticFunction m))).mp htr
      exact htr' (isAlgebraic_algebraMap
        (⟨_, Algebra.subset_adjoin h⟩ : Algebra.adjoin ℝ (S.beforeTauGenerators m)))
    have hvars : ∀ v ∈ U.vars, (v : Kₐ) ∈ S.beforeTauGenerators m ∨ v = t := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := hvarsU v hv
      cases i using Fin.cases with
      | zero =>
          left
          rw [hcoeIdx, S.finiteFractionCoordinates_zero]
          exact S.stageGenerators_subset_beforeTau m (S.x_mem_stageGenerators m)
      | succ j =>
          rcases (hle j hi).lt_or_eq with hlt | heq
          · left
            rw [hcoeIdx, S.finiteFractionCoordinates_succ]
            apply S.stageGenerators_subset_beforeTau m
            exact S.stageGenerators_mono (Nat.succ_le_of_lt hlt)
              (S.tau_mem_stageGenerators_succ j)
          · right
            rw [heq]
    -- Darboux data from the pre-`τ_m` denominators
    have hb := S.beforeCleared m
    have hBfin : (S.beforeTauGenerators m).Finite :=
      (S.stageGenerators_finite (m + 1)).subset (S.beforeTau_subset_stageGenerators_succ m)
    obtain ⟨k₁, hk₁⟩ := Cleared.exists_uniform (S.beforeTauGenerators m) hBfin
      (fun g ↦ g′) hb.1
    obtain ⟨k₂, hk₂⟩ := hb.2
    obtain ⟨c, hc_def⟩ : ∃ c : Kₐ, c = S.denomW (m + 1) ^ (k₁ + k₂) := ⟨_, rfl⟩
    have hWB := S.denomW_succ_mem_adjoin_beforeTau m
    have hnum : ∀ g : S.beforeTauGenerators m,
        c * (g : Kₐ)′ ∈ Algebra.adjoin ℝ (S.beforeTauGenerators m) := by
      intro g
      have := mul_mem (pow_mem hWB k₂) (hk₁ g g.2)
      convert this using 1
      rw [hc_def]
      ring
    choose num hnumEq using fun g ↦ exists_aeval_eq_of_mem_adjoin (hnum g)
    obtain ⟨N, hNEq⟩ := exists_aeval_eq_of_mem_adjoin (s := S.beforeTauGenerators m)
      (z := c * S.tauLog m) (by
        have := mul_mem (pow_mem hWB k₁) hk₂
        convert this using 1
        rw [hc_def]
        ring)
    have hc0 : c ≠ 0 := hc_def ▸ pow_ne_zero _ (S.denomW_ne_zero _)
    have hcG : c ∈ Algebra.adjoin ℝ (S.stageGenerators n) :=
      hc_def ▸ pow_mem (Algebra.adjoin_mono (S.stageGenerators_mono hmn)
        (S.denomW_mem_adjoin (m + 1))) _
    let D₀ : MvPolynomial (S.beforeTauGenerators m) ℝ →+
        MvPolynomial (S.beforeTauGenerators m) ℝ :=
      (MvPolynomial.mkDerivation ℝ num).toLinearMap.toAddMonoidHom
    have hD₀ : ∀ a, aeval ((↑) : S.beforeTauGenerators m → Kₐ) (D₀ a) =
        c * (aeval ((↑) : S.beforeTauGenerators m → Kₐ) a)′ := by
      intro a
      exact aeval_mkDerivation c num hnumEq a
    have hN : aeval ((↑) : S.beforeTauGenerators m → Kₐ) N * t = c * (t : Kₐ)′ := by
      rw [hNEq, ht_val, deriv_tau]
      ring
    exact NonTangency.not_dvd_of_darbouxData hstage constants_real Dp Wp hDp U hUW
      t (hXU _) (hmemU _ hmJ) (S.beforeTauGenerators m) hgens htg hvars
      D₀ N c hc0 hcG hD₀ hN
  · -- no power generator occurs: the top variable is `x`
    push Not at hJ
    let t : S.stageGenerators n := idx 0
    have ht_val : (t : Kₐ) = OneVariableBaseField.x := by
      rw [hcoeIdx, S.finiteFractionCoordinates_zero]
    have h0f : (0 : StageVar n) ∈ f.vars := by
      by_contra h0
      have hempty : f.vars = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i hi
        cases i using Fin.cases with
        | zero => exact h0 hi
        | succ j => exact hJ j hi
      rw [vars_eq_empty_iff_eq_C] at hempty
      exact S.currentBasePolynomial_ne_C hfresh _ hempty
    have hvars : ∀ v ∈ U.vars, (v : Kₐ) ∈ (∅ : Set Kₐ) ∨ v = t := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := hvarsU v hv
      cases i using Fin.cases with
      | zero => right; rfl
      | succ j => exact absurd hi (hJ j)
    have hD₀ : ∀ a : MvPolynomial (∅ : Set Kₐ) ℝ,
        aeval ((↑) : (∅ : Set Kₐ) → Kₐ) ((0 : MvPolynomial _ ℝ →+ MvPolynomial _ ℝ) a) =
          OneVariableBaseField.x * (aeval ((↑) : (∅ : Set Kₐ) → Kₐ) a)′ := by
      intro a
      have hconst : (aeval ((↑) : (∅ : Set Kₐ) → Kₐ) a)′ = 0 := by
        induction a using MvPolynomial.induction_on with
        | C r => rw [aeval_C, deriv_algebraMap_real]
        | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
        | mul_X p g _ => exact absurd g.2 (Set.notMem_empty _)
      rw [hconst, mul_zero, AddMonoidHom.zero_apply, map_zero]
    have hN : aeval ((↑) : (∅ : Set Kₐ) → Kₐ) (1 : MvPolynomial _ ℝ) * t =
        OneVariableBaseField.x * (t : Kₐ)′ := by
      rw [ht_val, OneVariableBaseField.deriv_x, map_one]
      ring
    exact NonTangency.not_dvd_of_darbouxData hstage constants_real Dp Wp hDp U hUW
      t (hXU _) (hmemU _ h0f) ∅ (Set.empty_subset _) (Set.notMem_empty _) hvars
      0 1 OneVariableBaseField.x OneVariableBaseField.x_ne_zero
      (Algebra.subset_adjoin (by rw [← ht_val]; exact t.2)) hD₀ hN

/-- A compatible polynomial derivation whose scale is coprime to the fresh
base, and to which the fresh base is not tangent. -/
theorem exists_goodDerivation {n : ℕ}
    (hpriorTau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j)
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hfresh : S.IsFreshBase n) :
    ∃ (Dpoly : Derivation Int (S.StageCoordinateRing n)
          (S.StageCoordinateRing n))
        (scale : S.StageCoordinateRing n),
      (∀ z : S.StageCoordinateField n,
        S.stageCoordinateEquiv hstage
            (FractionDerivation.extend Dpoly z) =
          S.stageCoordinateEquiv hstage
              (algebraMap (S.StageCoordinateRing n)
                (S.StageCoordinateField n) scale) *
            Differential.deriv (S.stageCoordinateEquiv hstage z)) ∧
      ¬ S.stageCoordinateBasePolynomial n ∣
        Dpoly (S.stageCoordinateBasePolynomial n) := by
  classical
  have hfin := S.stageGenerators_finite n
  haveI : Finite (S.stageGenerators n) := hfin.to_subtype
  obtain ⟨K, hK⟩ := Cleared.exists_uniform (S.stageGenerators n) hfin
    (fun g ↦ g′) (S.stageCleared n)
  choose num hnum using fun g : S.stageGenerators n ↦
    exists_aeval_eq_of_mem_adjoin (hK g g.2)
  set Wp := S.stageCoordinatePolynomial n (S.denomIntPolynomial n) with hWpdef
  have hWp : aeval ((↑) : S.stageGenerators n → Kₐ) Wp = S.denomW n := by
    rw [hWpdef, aeval_stageCoordinatePolynomial, stagePolynomialEval_denomInt]
  set scale := Wp ^ K with hscale
  let Dpoly := FreshStagePrimeDerivation.CommonDenominator.polynomialDerivation num
  have hDpoly : ∀ p, aeval ((↑) : S.stageGenerators n → Kₐ) (Dpoly p) =
      aeval ((↑) : S.stageGenerators n → Kₐ) scale *
        (aeval ((↑) : S.stageGenerators n → Kₐ) p)′ := by
    intro p
    rw [hscale, map_pow, hWp]
    exact aeval_mkDerivation _ num (fun g ↦ hnum g) p
  refine ⟨Dpoly, scale, ?_, ?_⟩
  · have hgen : ∀ i,
        algebraMap (S.StageCoordinateRing n) (S.StageCoordinateField n) (num i) =
          algebraMap (S.StageCoordinateRing n) (S.StageCoordinateField n) scale *
            S.stageCoordinateDerivation hstage
              (algebraMap (S.StageCoordinateRing n) (S.StageCoordinateField n)
                (MvPolynomial.X i)) := by
      intro i
      apply (S.stageCoordinateEquiv hstage).injective
      apply Subtype.ext
      rw [map_mul, MulMemClass.coe_mul, S.stageCoordinateDerivation_compatibility,
        DifferentialIntermediateField.coe_deriv,
        S.stageCoordinateEquiv_algebraMap_apply, S.stageCoordinateEquiv_algebraMap_apply,
        S.stageCoordinateEquiv_algebraMap_apply, hnum, aeval_X, hscale, map_pow, hWp]
    intro z
    rw [FreshStagePrimeDerivation.CommonDenominator.extend_polynomialDerivation_eq_of_generatorValues
      (S.stageCoordinateDerivation hstage) scale num hgen z, map_mul,
      S.stageCoordinateDerivation_compatibility]
  · have hidx := S.stageGeneratorCoordinateIndex_injective' hpriorTau
    have hUW : IsRelPrime (S.stageCoordinateBasePolynomial n) scale := by
      rw [hscale]
      apply IsRelPrime.pow_right
      exact RealDescent.isRelPrime_realLift hidx
        (S.currentBasePolynomial_prime n).irreducible (S.not_dvd_denomInt hfresh)
    exact S.stageCoordinateBase_not_dvd hpriorTau hstage hfresh
      (Dpoly : S.StageCoordinateRing n →ₗ[ℤ] S.StageCoordinateRing n).toAddMonoidHom
      scale hDpoly hUW

/-- **Stage-local integral-slope rigidity.** -/
theorem currentBase_integralSlopeRigidity_of_stage {n : ℕ}
    (hpriorTau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j)
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hfresh : S.IsFreshBase n) :
    Proposition31II.IntegralSlopeRigidity (S.currentBaseElement n) := by
  classical
  obtain ⟨Dpoly, scale, hcompat, hnot⟩ :=
    S.exists_goodDerivation hpriorTau hstage hfresh
  have hsq : Squarefree (S.stageCoordinateBasePolynomial n) :=
    RealDescent.squarefree_realLift (S.stageGeneratorCoordinateIndex_injective' hpriorTau)
      (S.currentBasePolynomial_prime n).irreducible
  exact S.currentBase_integralSlopeRigidity_of_primeDerivation hstage
    (S.freshStagePrimeDerivationInput_of_squarefree_of_not_dvd hstage hsq
      Dpoly scale hcompat hnot)

/-- Wilkie's finite-stage induction, with rigidity supplied stage by stage. -/
theorem finiteStageInduction_closed : ∀ n, S.FiniteStageInductionResult n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hstage :
          AlgebraicIndepOn Real id (S.stageGenerators n) ∧
            S.StageLogDerivClassification n := by
        cases n with
        | zero =>
            exact ⟨S.algebraicIndepOn_stageGenerators_zero,
              S.stageLogDerivClassification_zero⟩
        | succ k =>
            have hk := ih k (Nat.lt_succ_self k)
            exact ⟨hk.successorStageAlgebraicIndependent,
              hk.successorStageLogDerivClassification⟩
      have hpriorTau : ∀ j < n,
          Transcendental (S.finiteStageBeforeTau j)
            (ι (S.realTauAnalyticFunction j)) := by
        intro j hj
        exact (ih j hj).tauTranscendental
      have hrigid : S.IsFreshBase n →
          Proposition31II.IntegralSlopeRigidity
            (⟨ι (S.baseAnalytic n), S.baseAnalytic_mem_finiteStageField n⟩ :
              S.finiteStageField n) :=
        fun hfresh ↦ S.currentBase_integralSlopeRigidity_of_stage hpriorTau hstage.1 hfresh
      have hcurrentLog : S.IsFreshBase n →
          Transcendental (S.finiteStageField n)
            (ι (S.logBaseAnalytic n)) := by
        intro hfresh
        exact S.freshLog_transcendental_of_stage_induction
          hfresh hpriorTau hstage.1 hstage.2
      have hlogs : ∀ r ≤ n, S.IsFreshBase r →
          Transcendental (S.finiteStageField r)
            (ι (S.logBaseAnalytic r)) := by
        intro r hrn hrfresh
        rcases hrn.eq_or_lt with rfl | hrn
        · exact hcurrentLog hrfresh
        · exact (ih r hrn).freshLogTranscendental hrfresh
      have hbeforeAI :
          AlgebraicIndepOn Real id (S.beforeTauGenerators n) :=
        S.algebraicIndepOn_beforeTauGenerators hstage.1 hcurrentLog
      have hbeforeII : S.BeforeTauLogDerivClassification n := by
        by_cases hfresh : S.IsFreshBase n
        · exact S.beforeTauLogDerivClassification_of_fresh
            hfresh (hcurrentLog hfresh) (hrigid hfresh) hstage.2
        · exact S.beforeTauLogDerivClassification_of_not_fresh
            hfresh hstage.2
      have htau : Transcendental (S.finiteStageBeforeTau n)
          (ι (S.realTauAnalyticFunction n)) :=
        S.tau_transcendental_of_primitiveRelationExclusion hbeforeII
          (S.localTauPrimitiveRelationExclusion n hpriorTau hlogs hstage.1
            hbeforeAI)
      exact S.finiteStageInductionStep hpriorTau hrigid htau
        hstage.1 hstage.2

/-- **Fresh-stage integral-slope rigidity**, with no premise. -/
theorem freshStageIntegralSlopeRigidity : S.FreshStageIntegralSlopeRigidity := by
  intro n hfresh
  have R := S.finiteStageInduction_closed
  exact S.currentBase_integralSlopeRigidity_of_stage
    (fun j _ ↦ (R j).tauTranscendental) (R n).stageAlgebraicIndependent hfresh

end GeneratorSequence

/-- **Wilkie's Theorem 4.4 for the canonical generators**: the canonical real
coordinates are algebraically independent. -/
theorem canonicalWilkieIndependence : CanonicalWilkieIndependence :=
  canonicalWilkieIndependence_of_freshStageIntegralSlopeRigidity
    canonicalGeneratorSequence.freshStageIntegralSlopeRigidity

end

end Natfunbasis.Wilkie
