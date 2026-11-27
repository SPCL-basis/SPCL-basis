import Natfunbasis.WilkieStageClassification
import Natfunbasis.WilkieStageTranscendenceReductions

/-!
# Additive primitives of finite-stage Laurent monomials

The logarithmic derivative of an integral Laurent monomial has a canonical
additive primitive.  Recording those primitives turns the relation supplied
by Proposition 3.2(i) into the linear polynomial identity used in Wilkie's
coefficient-comparison argument, without introducing a logarithm operation
on the ambient fraction field.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- Additive logarithmic primitives of the integral monomials present after
`n` completed power adjunctions.  An arbitrary real constant is included,
because primitives are unique only modulo constants. -/
def StagePrimitive (S : GeneratorSequence D) : (n : Nat) → K → Prop
  | 0, L => ∃ c : Real, ∃ m : Int,
      L = algebraMap Real K c + (m : K) * OneVariableBaseField.logX
  | n + 1, L => ∃ k : Int, ∃ W : K,
      ((S.IsFreshBase n ∧
          ∃ m : Int, ∃ U : K, S.StagePrimitive n U ∧
            W = (m : K) * ι (S.logBaseAnalytic n) + U) ∨
        (¬ S.IsFreshBase n ∧ S.StagePrimitive n W)) ∧
      L = W + (k : K) * S.tauPrimitive n

/-- Additive primitives immediately before adjoining `tau_n`. -/
def BeforeTauPrimitive (S : GeneratorSequence D) (n : Nat) (L : K) : Prop :=
  (S.IsFreshBase n ∧
      ∃ m : Int, ∃ U : K, S.StagePrimitive n U ∧
        L = (m : K) * ι (S.logBaseAnalytic n) + U) ∨
    (¬ S.IsFreshBase n ∧ S.StagePrimitive n L)

@[simp]
theorem stagePrimitive_zero_iff {L : K} :
    S.StagePrimitive 0 L ↔
      ∃ c : Real, ∃ m : Int,
        L = algebraMap Real K c +
          (m : K) * OneVariableBaseField.logX :=
  Iff.rfl

@[simp]
theorem stagePrimitive_succ_iff {n : Nat} {L : K} :
    S.StagePrimitive (n + 1) L ↔
      ∃ k : Int, ∃ W : K, S.BeforeTauPrimitive n W ∧
        L = W + (k : K) * S.tauPrimitive n :=
  Iff.rfl

theorem beforeTauPrimitive_iff_of_fresh {n : Nat}
    (hfresh : S.IsFreshBase n) {L : K} :
    S.BeforeTauPrimitive n L ↔
      ∃ m : Int, ∃ U : K, S.StagePrimitive n U ∧
        L = (m : K) * ι (S.logBaseAnalytic n) + U := by
  constructor
  · rintro (⟨_, h⟩ | ⟨hnot, _⟩)
    · exact h
    · exact False.elim (hnot hfresh)
  · intro h
    exact Or.inl ⟨hfresh, h⟩

theorem beforeTauPrimitive_iff_of_not_fresh {n : Nat}
    (hfresh : ¬ S.IsFreshBase n) {L : K} :
    S.BeforeTauPrimitive n L ↔ S.StagePrimitive n L := by
  constructor
  · rintro (⟨hf, _⟩ | ⟨_, h⟩)
    · exact False.elim (hfresh hf)
    · exact h
  · intro h
    exact Or.inr ⟨hfresh, h⟩

private theorem baseAnalytic_ne_zero (n : Nat) :
    ι (S.baseAnalytic n) ≠ 0 := by
  have hbaseA : S.baseAnalytic n ≠ 0 := by
    intro hzero
    have hpos := S.baseAnalytic_pos n ⟨1, zero_lt_one⟩
    rw [hzero] at hpos
    simp at hpos
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hbaseA)

private theorem tau_ne_zero (n : Nat) :
    ι (S.realTauAnalyticFunction n) ≠ 0 := by
  have htauA : S.realTauAnalyticFunction n ≠ 0 := by
    intro hzero
    have hpos : 0 < (S.realTauAnalyticFunction n).1
        ⟨1, zero_lt_one⟩ :=
      S.canonicalRealization.tau_pos n ⟨1, zero_lt_one⟩
    rw [hzero] at hpos
    simp at hpos
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr htauA)

private theorem deriv_zpow_eq_primitive {z L : K} (hz0 : z ≠ 0)
    (hz : z′ = L′ * z) (m : Int) :
    (z ^ m)′ = (((m : K) * L))′ * z ^ m := by
  change PositiveAnalyticFractionField.derivation z =
    PositiveAnalyticFractionField.derivation L * z at hz
  change PositiveAnalyticFractionField.derivation (z ^ m) =
    PositiveAnalyticFractionField.derivation ((m : K) * L) * z ^ m
  rw [PositiveAnalyticFractionField.derivation_zpow, hz,
    PositiveAnalyticFractionField.derivation_mul,
    PositiveAnalyticFractionField.derivation_intCast]
  simp only [mul_zero, add_zero]
  have hpow : z ^ (m - 1) * z = z ^ m := by
    rw [← zpow_add_one₀ hz0]
    congr 1
    omega
  calc
    (m : K) * z ^ (m - 1) * (L′ * z) =
        (m : K) * L′ * (z ^ (m - 1) * z) := by ring
    _ = (m : K) * L′ * z ^ m := by rw [hpow]

private theorem deriv_mul_eq_add_primitive {X Z L M : K}
    (hX : X′ = L′ * X) (hZ : Z′ = M′ * Z) :
    (X * Z)′ = (L + M)′ * (X * Z) := by
  change PositiveAnalyticFractionField.derivation X =
    PositiveAnalyticFractionField.derivation L * X at hX
  change PositiveAnalyticFractionField.derivation Z =
    PositiveAnalyticFractionField.derivation M * Z at hZ
  change PositiveAnalyticFractionField.derivation (X * Z) =
    PositiveAnalyticFractionField.derivation (L + M) * (X * Z)
  rw [PositiveAnalyticFractionField.derivation_mul, hX, hZ,
    PositiveAnalyticFractionField.derivation_add]
  ring

private theorem deriv_const_mul_eq_primitive (c : Real) {X L : K}
    (hX : X′ = L′ * X) :
    (algebraMap Real K c * X)′ = L′ * (algebraMap Real K c * X) := by
  change PositiveAnalyticFractionField.derivation X =
    PositiveAnalyticFractionField.derivation L * X at hX
  change PositiveAnalyticFractionField.derivation
      (algebraMap Real K c * X) =
    PositiveAnalyticFractionField.derivation L *
      (algebraMap Real K c * X)
  rw [PositiveAnalyticFractionField.derivation_mul,
    PositiveAnalyticFractionField.derivation_algebraMap_real, hX]
  ring

private theorem deriv_x_eq_logX_deriv_mul :
    OneVariableBaseField.x′ =
      OneVariableBaseField.logX′ * OneVariableBaseField.x := by
  rw [OneVariableBaseField.deriv_logX, OneVariableBaseField.deriv_x]
  exact (inv_mul_cancel₀ OneVariableBaseField.x_ne_zero).symm

private theorem deriv_base_eq_logBase_deriv_mul (n : Nat) :
    (ι (S.baseAnalytic n))′ =
      (ι (S.logBaseAnalytic n))′ * ι (S.baseAnalytic n) := by
  change PositiveAnalyticFractionField.derivation
      (ι (S.baseAnalytic n)) =
    PositiveAnalyticFractionField.derivation
        (ι (S.logBaseAnalytic n)) * ι (S.baseAnalytic n)
  rw [PositiveAnalyticFractionField.derivation_logBaseAnalytic]
  exact (div_mul_cancel₀ _ (S.baseAnalytic_ne_zero n)).symm

/-- Every multiplicative stage monomial admits a structured additive
primitive of its logarithmic derivative; likewise at the pre-`tau` half
stage. -/
theorem stageMonomial_hasPrimitive_and_beforeTauMonomial_hasPrimitive :
    ∀ n : Nat,
      (∀ {X : K}, S.StageMonomial n X →
        ∃ L : K, S.StagePrimitive n L ∧ X′ = L′ * X) ∧
      (∀ {X : K}, S.BeforeTauMonomial n X →
        ∃ L : K, S.BeforeTauPrimitive n L ∧ X′ = L′ * X) := by
  intro n
  induction n with
  | zero =>
      have hstage : ∀ {X : K}, S.StageMonomial 0 X →
          ∃ L : K, S.StagePrimitive 0 L ∧ X′ = L′ * X := by
        intro X hX
        obtain ⟨c, _hc, m, rfl⟩ := hX
        refine ⟨(m : K) * OneVariableBaseField.logX, ?_, ?_⟩
        · exact ⟨0, m, by simp⟩
        · apply deriv_const_mul_eq_primitive
          exact deriv_zpow_eq_primitive OneVariableBaseField.x_ne_zero
            deriv_x_eq_logX_deriv_mul m
      refine ⟨hstage, ?_⟩
      intro X hX
      classical
      by_cases hfresh : S.IsFreshBase 0
      · rw [S.beforeTauMonomial_iff_of_fresh hfresh] at hX
        obtain ⟨m, u, hu, rfl⟩ := hX
        obtain ⟨U, hUprim, hUderiv⟩ := hstage hu
        refine ⟨(m : K) * ι (S.logBaseAnalytic 0) + U, ?_, ?_⟩
        · rw [S.beforeTauPrimitive_iff_of_fresh hfresh]
          exact ⟨m, U, hUprim, rfl⟩
        · apply deriv_mul_eq_add_primitive
          · exact deriv_zpow_eq_primitive (S.baseAnalytic_ne_zero 0)
              (S.deriv_base_eq_logBase_deriv_mul 0) m
          · exact hUderiv
      · rw [S.beforeTauMonomial_iff_of_not_fresh hfresh] at hX
        obtain ⟨L, hL, hderiv⟩ := hstage hX
        exact ⟨L,
          (S.beforeTauPrimitive_iff_of_not_fresh hfresh).2 hL,
          hderiv⟩
  | succ n ih =>
      have hstage : ∀ {X : K}, S.StageMonomial (n + 1) X →
          ∃ L : K, S.StagePrimitive (n + 1) L ∧ X′ = L′ * X := by
        intro X hX
        rw [stageMonomial_succ_iff] at hX
        obtain ⟨m, w, hw, rfl⟩ := hX
        obtain ⟨W, hWprim, hWderiv⟩ := ih.2 hw
        refine ⟨W + (m : K) * S.tauPrimitive n, ?_, ?_⟩
        · rw [stagePrimitive_succ_iff]
          exact ⟨m, W, hWprim, rfl⟩
        · apply deriv_mul_eq_add_primitive hWderiv
          exact deriv_zpow_eq_primitive (S.tau_ne_zero n)
            (S.deriv_tau_eq_tauPrimitive_deriv_mul n) m
      refine ⟨hstage, ?_⟩
      intro X hX
      classical
      by_cases hfresh : S.IsFreshBase (n + 1)
      · rw [S.beforeTauMonomial_iff_of_fresh hfresh] at hX
        obtain ⟨m, u, hu, rfl⟩ := hX
        obtain ⟨U, hUprim, hUderiv⟩ := hstage hu
        refine ⟨(m : K) * ι (S.logBaseAnalytic (n + 1)) + U,
          ?_, ?_⟩
        · rw [S.beforeTauPrimitive_iff_of_fresh hfresh]
          exact ⟨m, U, hUprim, rfl⟩
        · apply deriv_mul_eq_add_primitive
          · exact deriv_zpow_eq_primitive
              (S.baseAnalytic_ne_zero (n + 1))
              (S.deriv_base_eq_logBase_deriv_mul (n + 1)) m
          · exact hUderiv
      · rw [S.beforeTauMonomial_iff_of_not_fresh hfresh] at hX
        obtain ⟨L, hL, hderiv⟩ := hstage hX
        exact ⟨L,
          (S.beforeTauPrimitive_iff_of_not_fresh hfresh).2 hL,
          hderiv⟩

theorem stageMonomial_hasPrimitive {n : Nat} {X : K}
    (hX : S.StageMonomial n X) :
    ∃ L : K, S.StagePrimitive n L ∧ X′ = L′ * X :=
  (S.stageMonomial_hasPrimitive_and_beforeTauMonomial_hasPrimitive n).1 hX

theorem beforeTauMonomial_hasPrimitive {n : Nat} {X : K}
    (hX : S.BeforeTauMonomial n X) :
    ∃ L : K, S.BeforeTauPrimitive n L ∧ X′ = L′ * X :=
  (S.stageMonomial_hasPrimitive_and_beforeTauMonomial_hasPrimitive n).2 hX

/-- If `X' = Y'X` and `L` is the structured primitive attached to the same
nonzero monomial, then `Y-L` is a real constant. -/
theorem eq_real_add_primitive_of_logDeriv
    {X Y L : K} (hX0 : X ≠ 0)
    (hXY : X′ = Y′ * X) (hXL : X′ = L′ * X) :
    ∃ c : Real, Y = algebraMap Real K c + L := by
  have hderiv : (Y - L)′ = 0 := by
    rw [map_sub]
    have hcancel : Y′ = L′ := by
      apply mul_right_cancel₀ hX0
      rw [← hXY, ← hXL]
    rw [hcancel, sub_self]
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero Real hderiv
  refine ⟨c, ?_⟩
  calc
    Y = (Y - L) + L := by ring
    _ = algebraMap Real K c + L := by rw [← hc]

/-- If the current power generator were algebraic, Proposition 3.2(i) and
the pre-`tau` logarithmic-derivative classification would force a nonzero
integer multiple of its primitive to equal one of the structured old-stage
primitives, modulo a real constant.  This is the exact linear identity to be
ruled out by finite-coordinate coefficient comparison and W1.3. -/
theorem tau_algebraic_implies_primitive_relation {n : Nat}
    (hbefore : S.BeforeTauLogDerivClassification n)
    (halgebraic : IsAlgebraic (S.finiteStageBeforeTau n)
      (ι (S.realTauAnalyticFunction n))) :
    ∃ m : Int, m ≠ 0 ∧ ∃ L : K, S.BeforeTauPrimitive n L ∧
      ∃ c : Real,
        (m : K) * (S.tauPrimitive n : K) =
          algebraMap Real K c + L := by
  obtain ⟨m, hm0, u, v, htau, hmv, huv⟩ :=
    S.tau_powerRelation_of_isAlgebraic halgebraic
  have hu0 : (u : K) ≠ 0 := by
    intro hu
    have htau0 :
        (ι (S.realTauAnalyticFunction n)) ^ m = 0 := by
      rw [htau]
      change (u : K) = 0
      exact hu
    exact (zpow_ne_zero m (S.tau_ne_zero n)) htau0
  have huvK : ((u : K))′ = ((v : K))′ * (u : K) := by
    have h := congrArg
      (fun z : S.finiteStageBeforeTau n ↦ (z : K)) huv
    simpa using h
  have hmono : S.BeforeTauMonomial n (u : K) :=
    hbefore u v hu0 huvK
  obtain ⟨L, hL, huL⟩ := S.beforeTauMonomial_hasPrimitive hmono
  obtain ⟨c, hvc⟩ :=
    eq_real_add_primitive_of_logDeriv hu0 huvK huL
  refine ⟨m, hm0, L, hL, c, ?_⟩
  have hmvK := congrArg
    (fun z : S.finiteStageBeforeTau n ↦ (z : K)) hmv
  calc
    (m : K) * (S.tauPrimitive n : K) = (v : K) := by
      simpa using hmvK
    _ = algebraMap Real K c + L := hvc

end GeneratorSequence

end

end Natfunbasis.Wilkie
