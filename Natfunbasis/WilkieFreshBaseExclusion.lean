import Natfunbasis.WilkieStageClassificationSteps
import Natfunbasis.WilkieFiniteCoordinateIndependence
import Natfunbasis.PowerBranchEvaluation
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Excluding a fresh polynomial base from the old Laurent monomials

This file supplies the polynomial-factor argument in the logarithmic part of
Wilkie's simultaneous induction.  Algebraic independence reflects an
analytic equality to a polynomial equality.  Unique factorization over the
integers then says that a fresh irreducible base cannot be a Laurent product
of the original variable, earlier auxiliary variables, and earlier bases.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial
open scoped Differential

noncomputable section

local notation "A" => PositiveAnalyticFunction
local notation "K" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A K)

/-! ## A coefficient-clearing lemma -/

/-- If two integer polynomials become proportional by a nonzero real scalar,
then every nonconstant prime divisor of the left polynomial divides the
integer polynomial on the right.  The coefficient argument is what prevents
an unrecorded real scalar from weakening integer unique factorization. -/
theorem prime_dvd_of_map_mul_eq_C_mul_map
    {J : Type*} {p r q : MvPolynomial J Int} {c : Real}
    (hp : Prime p)
    (hpnonconstant : ∀ a : Int, p ≠ C a)
    (hq0 : q ≠ 0) (hc0 : c ≠ 0)
    (heq : map (Int.castRingHom Real) (p * r) =
      C c * map (Int.castRingHom Real) q) :
    p ∣ q := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hq0
  let a : Int := coeff d (p * r)
  let b : Int := coeff d q
  have hb0 : b ≠ 0 := hd
  have hdcoeff := congrArg (coeff d) heq
  have hab : (a : Real) = c * (b : Real) := by
    simpa only [a, b, MvPolynomial.coeff_map, Int.coe_castRingHom,
      MvPolynomial.coeff_C_mul] using hdcoeff
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, Int.cast_zero] at hab
    exact (mul_ne_zero hc0 (Int.cast_ne_zero.mpr hb0)) hab.symm
  have hcross : C b * (p * r) = C a * q := by
    ext e
    have hecoeff := congrArg (coeff e) heq
    have hecoeff' : ((coeff e (p * r) : Int) : Real) =
        c * ((coeff e q : Int) : Real) := by
      simpa only [MvPolynomial.coeff_map, Int.coe_castRingHom,
        MvPolynomial.coeff_C_mul] using hecoeff
    simp only [MvPolynomial.coeff_C_mul]
    apply Int.cast_injective (α := Real)
    push_cast
    calc
      (b : Real) * (coeff e (p * r) : Int) =
          (b : Real) * (c * (coeff e q : Int)) := by rw [hecoeff']
      _ = ((a : Real) * (coeff e q : Int)) := by rw [hab]; ring
  have hp_dvd_right : p ∣ C a * q := by
    rw [← hcross]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (dvd_refl p) r) (C b)
  rcases hp.dvd_or_dvd hp_dvd_right with hpa | hpq
  · obtain ⟨z, _hz, hpz⟩ := (MvPolynomial.dvd_C_iff_exists ha0).mp hpa
    exact False.elim (hpnonconstant z hpz)
  · exact hpq

/-- Two associated integer polynomials which are both positive at the
all-ones real point are literally equal. -/
theorem eq_of_associated_of_evalOne_pos
    {J : Type*} {p q : MvPolynomial J Int}
    (hassoc : Associated p q)
    (hp : 0 < MvPolynomial.eval₂ (Int.castRingHom Real) (fun _ ↦ 1) p)
    (hq : 0 < MvPolynomial.eval₂ (Int.castRingHom Real) (fun _ ↦ 1) q) :
    p = q := by
  obtain ⟨u, hu⟩ := hassoc
  have huUnit : IsUnit (u : MvPolynomial J Int) := u.isUnit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at huUnit
  obtain ⟨r, hr, hur⟩ := huUnit
  rw [hur] at hu
  obtain ⟨v, rfl⟩ := hr
  rcases Int.units_eq_one_or v with hv | hv
  · subst v
    simpa using hu
  · subst v
    have heval := congrArg
      (MvPolynomial.eval₂ (Int.castRingHom Real) (fun _ ↦ 1)) hu
    norm_num [Int.coe_castRingHom] at heval
    linarith

private theorem prime_rename_of_injective
    {J L : Type*} (f : J → L) (hf : Function.Injective f)
    {p : MvPolynomial J Int} (hp : Prime p) :
    Prime (rename f p) := by
  let e : J ≃ Set.range f := Equiv.ofInjective f hf
  have he : Prime (rename e p) := by
    exact (MulEquiv.prime_iff (renameEquiv Int e)).2 hp
  have hrange : Prime (rename ((↑) : Set.range f → L) (rename e p)) :=
    (MvPolynomial.prime_rename_iff (Set.range f)).2 he
  rw [MvPolynomial.rename_rename] at hrange
  convert hrange using 1
  apply congrArg (fun g ↦ rename g p)
  funext i
  rfl

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

private theorem stageVarEmbedding_injective (k : Nat) :
    Function.Injective (stageVarEmbedding k) := by
  intro i j hij
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · cases hij
  · cases hij
  · apply Fin.ext
    simpa [stageVarEmbedding] using hij

/-! ## Finite-stage polynomial coordinates -/

/-- Evaluation of an integer stage polynomial in the corresponding analytic
fraction-field coordinates. -/
def stagePolynomialEval (n : Nat) : StagePolynomial n →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K)
    (fun i ↦ ι (S.analyticAssignment n i))

@[simp]
theorem stagePolynomialEval_X (n : Nat) (i : StageVar n) :
    S.stagePolynomialEval n (X i) = ι (S.analyticAssignment n i) := by
  simp [stagePolynomialEval]

@[simp]
theorem stagePolynomialEval_C (n : Nat) (a : Int) :
    S.stagePolynomialEval n (C a) = (a : K) := by
  simp [stagePolynomialEval]

/-- Transport an integer polynomial to a later finite coordinate stage. -/
def liftStagePolynomial {k n : Nat} (p : StagePolynomial k) (h : k ≤ n) :
    StagePolynomial n :=
  rename (stageInclusion h) p

theorem liftStagePolynomial_toGlobal {k n : Nat}
    (p : StagePolynomial k) (h : k ≤ n) :
    (liftStagePolynomial p h).toGlobal = p.toGlobal := by
  simp only [liftStagePolynomial, StagePolynomial.toGlobal,
    MvPolynomial.rename_rename]
  apply congrArg (fun f ↦ MvPolynomial.rename f p)
  funext i
  exact stageVarEmbedding_stageInclusion h i

theorem analyticAssignment_stageInclusion {k n : Nat} (h : k ≤ n)
    (i : StageVar k) :
    S.analyticAssignment n (stageInclusion h i) =
      S.analyticAssignment k i := by
  cases i using Fin.cases <;> rfl

theorem stagePolynomialEval_lift {k n : Nat}
    (p : StagePolynomial k) (h : k ≤ n) :
    S.stagePolynomialEval n (liftStagePolynomial p h) =
      S.stagePolynomialEval k p := by
  change MvPolynomial.eval₂ (Int.castRingHom K)
      (fun i ↦ ι (S.analyticAssignment n i))
        (rename (stageInclusion h) p) =
    MvPolynomial.eval₂ (Int.castRingHom K)
      (fun i ↦ ι (S.analyticAssignment k i)) p
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext i
  exact congrArg ι (S.analyticAssignment_stageInclusion h i)

theorem stagePolynomialEval_eq_map_evalAnalytic {n : Nat}
    (p : StagePolynomial n) :
    S.stagePolynomialEval n p =
      ι (p.evalAnalytic (S.analyticAssignment n)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [stagePolynomialEval_C]
      rw [StagePolynomial.evalAnalytic, MvPolynomial.eval₂_C]
      exact (map_intCast (algebraMap A K) a).symm
  | add p q hp hq =>
      simp only [map_add, hp, hq, StagePolynomial.evalAnalytic,
        MvPolynomial.eval₂_add]
  | mul_X p i hp =>
      simp only [map_mul, hp, stagePolynomialEval_X,
        StagePolynomial.evalAnalytic, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X]

/-- The presentation of the base at index `j`, transported to stage `n`. -/
def basePolynomialAtStage (n j : Nat) (hj : j ≤ n) : StagePolynomial n :=
  liftStagePolynomial (S.pair j).base.polynomial
    ((S.pair j).baseStage_le.trans hj)

/-- The current base polynomial in the full current coordinate type. -/
def currentBasePolynomial (n : Nat) : StagePolynomial n :=
  S.basePolynomialAtStage n n le_rfl

theorem basePolynomialAtStage_toGlobal (n j : Nat) (hj : j ≤ n) :
    (S.basePolynomialAtStage n j hj).toGlobal = S.baseGlobal j := by
  exact liftStagePolynomial_toGlobal _ _

theorem currentBasePolynomial_toGlobal (n : Nat) :
    (S.currentBasePolynomial n).toGlobal = S.baseGlobal n := by
  exact S.basePolynomialAtStage_toGlobal n n le_rfl

theorem stagePolynomialEval_basePolynomialAtStage (n j : Nat)
    (hj : j ≤ n) :
    S.stagePolynomialEval n (S.basePolynomialAtStage n j hj) =
      ι (S.baseAnalytic j) := by
  rw [basePolynomialAtStage, stagePolynomialEval_lift,
    stagePolynomialEval_eq_map_evalAnalytic]
  rfl

theorem stagePolynomialEval_currentBasePolynomial (n : Nat) :
    S.stagePolynomialEval n (S.currentBasePolynomial n) =
      ι (S.baseAnalytic n) := by
  exact S.stagePolynomialEval_basePolynomialAtStage n n le_rfl

/-! ## Prime and nonassociation facts for W1 bases -/

/-- Every W1 base stays prime after embedding its finite presentation in the
common global integer polynomial ring. -/
theorem baseGlobal_prime (j : Nat) : Prime (S.baseGlobal j) := by
  unfold baseGlobal Base.toGlobal
  cases hbase : (S.pair j).base with
  | original =>
      simpa [Base.polynomial, StagePolynomial.toGlobal] using
        (MvPolynomial.X_prime (R := Int)
          (i := (.original : GlobalVar)))
  | irreducible p hp =>
      change Prime (rename (stageVarEmbedding (S.pair j).baseStage) p)
      exact prime_rename_of_injective _
        (stageVarEmbedding_injective (S.pair j).baseStage)
        hp.irreducible.prime

/-- A global base polynomial is positive at every strictly positive real
assignment. -/
theorem baseGlobal_eval_pos (j : Nat) (a : GlobalVar → Real)
    (ha : ∀ i, 0 < a i) :
    0 < MvPolynomial.eval₂ (Int.castRingHom Real) a (S.baseGlobal j) := by
  unfold baseGlobal Base.toGlobal StagePolynomial.toGlobal
  rw [MvPolynomial.eval₂_rename]
  exact (S.pair j).base.positiveOnOrthant
    (fun i ↦ a (stageVarEmbedding (S.pair j).baseStage i))
    (fun i ↦ ha _)

/-- Associated global W1 bases have identical polynomial presentations; the
positivity convention removes the possible factor `-1`. -/
theorem baseGlobal_eq_of_associated {i j : Nat}
    (hassoc : Associated (S.baseGlobal i) (S.baseGlobal j)) :
    S.baseGlobal i = S.baseGlobal j := by
  apply eq_of_associated_of_evalOne_pos hassoc
  · exact S.baseGlobal_eval_pos i (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
  · exact S.baseGlobal_eval_pos j (fun _ ↦ 1) (fun _ ↦ zero_lt_one)

/-- No encoded W1 base is a single auxiliary variable. -/
theorem baseGlobal_ne_X_auxiliary (j k : Nat) :
    S.baseGlobal j ≠ X (.auxiliary k) := by
  unfold baseGlobal Base.toGlobal
  cases hbase : (S.pair j).base with
  | original =>
      simp [Base.polynomial, StagePolynomial.toGlobal]
  | irreducible p hp =>
      intro heq
      let f := stageVarEmbedding (S.pair j).baseStage
      change rename f p = X (.auxiliary k) at heq
      have hkvars : (.auxiliary k : GlobalVar) ∈ (rename f p).vars := by
        rw [heq, MvPolynomial.vars_X]
        simp
      obtain ⟨i, _hi, hfi⟩ := MvPolynomial.mem_vars_rename f p hkvars
      apply hp.ne_variable i
      apply MvPolynomial.rename_injective f
      · exact stageVarEmbedding_injective _
      · calc
          rename f p = X (.auxiliary k) := heq
          _ = X (f i) := congrArg X hfi.symm
          _ = rename f (X i) := (MvPolynomial.rename_X f i).symm

/-- Freshness rules out a coordinate variable as a divisor of the current
base polynomial. -/
theorem currentBasePolynomial_not_dvd_X {n : Nat}
    (hfresh : S.IsFreshBase n) (i : StageVar n) :
    ¬ S.currentBasePolynomial n ∣ X i := by
  intro hdvd
  have hdvdGlobal : S.baseGlobal n ∣ X (stageVarEmbedding n i) := by
    rw [← S.currentBasePolynomial_toGlobal n]
    unfold StagePolynomial.toGlobal
    simpa only [MvPolynomial.rename_X] using
      map_dvd (rename (stageVarEmbedding n)) hdvd
  have hassoc : Associated (S.baseGlobal n) (X (stageVarEmbedding n i)) :=
    (S.baseGlobal_prime n).irreducible.associated_of_dvd
      (MvPolynomial.X_prime (R := Int)
        (i := stageVarEmbedding n i)).irreducible hdvdGlobal
  have heq : S.baseGlobal n = X (stageVarEmbedding n i) := by
    apply eq_of_associated_of_evalOne_pos hassoc
    · exact S.baseGlobal_eval_pos n (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
    · simp
  cases i using Fin.cases with
  | zero =>
      exact hfresh.2.1 (by simpa [IsOriginalBase, originalPolynomial] using heq)
  | succ j =>
      exact S.baseGlobal_ne_X_auxiliary n j.1 (by simpa using heq)

/-- Freshness also rules out every earlier W1 base as a divisor of the
current base polynomial. -/
theorem currentBasePolynomial_not_dvd_earlierBase {n j : Nat}
    (hfresh : S.IsFreshBase n) (hj : j < n) :
    ¬ S.currentBasePolynomial n ∣
      S.basePolynomialAtStage n j hj.le := by
  intro hdvd
  have hdvdGlobal : S.baseGlobal n ∣ S.baseGlobal j := by
    rw [← S.currentBasePolynomial_toGlobal n,
      ← S.basePolynomialAtStage_toGlobal n j hj.le]
    exact map_dvd (rename (stageVarEmbedding n)) hdvd
  have hassoc : Associated (S.baseGlobal n) (S.baseGlobal j) :=
    (S.baseGlobal_prime n).irreducible.associated_of_dvd
      (S.baseGlobal_prime j).irreducible hdvdGlobal
  exact hfresh.2.2 j hj (S.baseGlobal_eq_of_associated hassoc).symm

/-- A fresh current base is not a constant polynomial in the current stage. -/
theorem currentBasePolynomial_ne_C {n : Nat}
    (hfresh : S.IsFreshBase n) (a : Int) :
    S.currentBasePolynomial n ≠ C a := by
  intro heq
  apply hfresh.1
  refine ⟨a, ?_⟩
  rw [← S.currentBasePolynomial_toGlobal n, heq]
  simp [StagePolynomial.toGlobal]

theorem currentBasePolynomial_prime (n : Nat) :
    Prime (S.currentBasePolynomial n) := by
  unfold currentBasePolynomial basePolynomialAtStage liftStagePolynomial
  cases hbase : (S.pair n).base with
  | original =>
      simpa [Base.polynomial] using
        (MvPolynomial.X_prime (R := Int)
          (i := stageInclusion (S.pair n).baseStage_le (0 : StageVar _)))
  | irreducible p hp =>
      exact prime_rename_of_injective _
        (stageInclusion_injective (S.pair n).baseStage_le)
        hp.irreducible.prime

/-! ## Laurent presentations avoiding the current prime -/

/-- A cleared Laurent presentation whose numerator and denominator are both
coprime to the current base prime. -/
def FreshLaurentPresentation (n : Nat) (Z : K) : Prop :=
  ∃ c : Real, c ≠ 0 ∧ ∃ numerator denominator : StagePolynomial n,
    (¬ S.currentBasePolynomial n ∣ numerator) ∧
    (¬ S.currentBasePolynomial n ∣ denominator) ∧
    Z * S.stagePolynomialEval n denominator =
      algebraMap Real K c * S.stagePolynomialEval n numerator

theorem stagePolynomialEval_injective_of_algebraicIndependent {n : Nat}
    (hcoord : AlgebraicIndependent Real
      (fun i : StageVar n ↦ ι (S.analyticAssignment n i))) :
    Function.Injective (S.stagePolynomialEval n) := by
  have hfun : S.finiteFractionCoordinates n =
      fun i : StageVar n ↦ ι (S.analyticAssignment n i) := by
    funext i
    exact S.finiteFractionCoordinates_eq_analyticAssignment n i
  have hcoord' : AlgebraicIndependent Real
      (S.finiteFractionCoordinates n) := by
    rw [hfun]
    exact hcoord
  have h := S.stagePolynomial_eval₂_injective_of_algebraicIndependent
    (n := n) hcoord'
  rw [hfun] at h
  exact h

private theorem FreshLaurentPresentation.scalar_only {n : Nat}
    (_hfresh : S.IsFreshBase n) {c : Real} (hc : c ≠ 0) :
    S.FreshLaurentPresentation n (algebraMap Real K c) := by
  refine ⟨c, hc, 1, 1, ?_, ?_, ?_⟩
  · exact (S.currentBasePolynomial_prime n).not_dvd_one
  · exact (S.currentBasePolynomial_prime n).not_dvd_one
  · simp

/-- Multiplication by an integral power of one allowed atom preserves a
cleared Laurent presentation avoiding the current prime. -/
private theorem FreshLaurentPresentation.mul_zpow {n : Nat}
    (_hfresh : S.IsFreshBase n)
    (heval : Function.Injective (S.stagePolynomialEval n))
    {Z : K} (hZ : S.FreshLaurentPresentation n Z)
    (q : StagePolynomial n)
    (hq : ¬ S.currentBasePolynomial n ∣ q) (m : Int) :
    S.FreshLaurentPresentation n
      (Z * S.stagePolynomialEval n q ^ m) := by
  rcases hZ with ⟨c, hc, numerator, denominator,
    hnumerator, hdenominator, hclearing⟩
  have hp := S.currentBasePolynomial_prime n
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hq
    rw [hzero]
    exact dvd_zero _
  have hqeval0 : S.stagePolynomialEval n q ≠ 0 := by
    intro hzero
    apply hq0
    apply heval
    simpa using hzero
  cases m with
  | ofNat k =>
      have hqpow : ¬ S.currentBasePolynomial n ∣ q ^ k := by
        intro hdvd
        exact hq (hp.dvd_of_dvd_pow hdvd)
      refine
        ⟨c, hc, numerator * q ^ k,
          denominator, hp.not_dvd_mul hnumerator hqpow,
          hdenominator, ?_⟩
      simp only [map_mul, map_pow]
      calc
        (Z * S.stagePolynomialEval n q ^ k) *
              S.stagePolynomialEval n denominator =
            (Z * S.stagePolynomialEval n denominator) *
              S.stagePolynomialEval n q ^ k := by ring
        _ = (algebraMap Real K c *
              S.stagePolynomialEval n numerator) *
              S.stagePolynomialEval n q ^ k := by rw [hclearing]
        _ = algebraMap Real K c *
              (S.stagePolynomialEval n numerator *
                S.stagePolynomialEval n q ^ k) := by ring
  | negSucc k =>
      have hqpow : ¬ S.currentBasePolynomial n ∣ q ^ (k + 1) := by
        intro hdvd
        exact hq (hp.dvd_of_dvd_pow hdvd)
      refine
        ⟨c, hc, numerator,
          denominator * q ^ (k + 1), hnumerator,
          hp.not_dvd_mul hdenominator hqpow, ?_⟩
      simp only [zpow_negSucc, map_mul, map_pow]
      calc
        (Z * (S.stagePolynomialEval n q ^ (k + 1))⁻¹) *
              (S.stagePolynomialEval n denominator *
                S.stagePolynomialEval n q ^ (k + 1)) =
            Z * S.stagePolynomialEval n denominator := by
              field_simp
        _ = algebraMap Real K c *
              S.stagePolynomialEval n numerator := hclearing

/-- Every old-stage monomial has a Laurent presentation whose numerator and
denominator avoid a fresh current base. -/
theorem freshLaurentPresentation_of_stageMonomial {n : Nat}
    (hfresh : S.IsFreshBase n)
    (hcoord : AlgebraicIndependent Real
      (fun i : StageVar n ↦ ι (S.analyticAssignment n i))) :
    ∀ {k : Nat}, k ≤ n → ∀ {Z : K}, S.StageMonomial k Z →
      S.FreshLaurentPresentation n Z := by
  have heval : Function.Injective (S.stagePolynomialEval n) :=
    S.stagePolynomialEval_injective_of_algebraicIndependent hcoord
  intro k hk
  induction k with
  | zero =>
      intro Z hZ
      obtain ⟨c, hc, m, rfl⟩ := hZ
      have hscalar :=
        FreshLaurentPresentation.scalar_only S hfresh hc
      have hmul := FreshLaurentPresentation.mul_zpow S hfresh heval hscalar
        (X (0 : StageVar n))
        (S.currentBasePolynomial_not_dvd_X hfresh 0) m
      simpa [stagePolynomialEval_X, OneVariableBaseField.x,
        mul_comm] using hmul
  | succ k ih =>
      intro Z hZ
      rw [stageMonomial_succ_iff] at hZ
      obtain ⟨m, w, hw, rfl⟩ := hZ
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hkle : k ≤ n := hklt.le
      have hwPresentation : S.FreshLaurentPresentation n w := by
        rcases hw with hwfresh | hwnot
        · obtain ⟨_hfreshk, a, u, hu, rfl⟩ := hwfresh
          have huPresentation := ih hkle hu
          let q := S.basePolynomialAtStage n k hkle
          have hqeval : S.stagePolynomialEval n q =
              ι (S.baseAnalytic k) :=
            S.stagePolynomialEval_basePolynomialAtStage n k hkle
          have hmul := FreshLaurentPresentation.mul_zpow S hfresh heval
            huPresentation q
            (S.currentBasePolynomial_not_dvd_earlierBase hfresh hklt) a
          simpa [q, hqeval, mul_comm] using hmul
        · exact ih hkle hwnot.2
      let j : Fin n := ⟨k, hklt⟩
      have htauEval : S.stagePolynomialEval n (X j.succ) =
          ι (S.realTauAnalyticFunction k) := by
        rw [S.stagePolynomialEval_X, S.analyticAssignment_succ]
      have hmul := FreshLaurentPresentation.mul_zpow S hfresh heval
        hwPresentation (X j.succ)
        (S.currentBasePolynomial_not_dvd_X hfresh j.succ) m
      simpa [htauEval] using hmul

/-! ## Fresh-base exclusion and logarithmic nonmembership -/

/-- A fresh current base cannot be one of the Laurent monomials classified
at the preceding stage.  This is the coefficient-comparison step in
Wilkie's proof of Theorem 4.4. -/
theorem freshBase_not_stageMonomial_of_algebraicIndependent {n : Nat}
    (hfresh : S.IsFreshBase n)
    (hcoord : AlgebraicIndependent Real
      (fun i : StageVar n ↦ ι (S.analyticAssignment n i))) :
    ¬ S.StageMonomial n (ι (S.baseAnalytic n)) := by
  intro hmonomial
  obtain ⟨c, hc, numerator, denominator,
      hnumerator, _hdenominator, hclearing⟩ :=
    S.freshLaurentPresentation_of_stageMonomial
      hfresh hcoord le_rfl hmonomial
  have hclearing' :
      S.stagePolynomialEval n (S.currentBasePolynomial n) *
          S.stagePolynomialEval n denominator =
        algebraMap Real K c * S.stagePolynomialEval n numerator := by
    rw [S.stagePolynomialEval_currentBasePolynomial]
    exact hclearing
  have hcast :
      (algebraMap Real K).comp (Int.castRingHom Real) =
        Int.castRingHom K := by
    ext z
    simp
  have hpoly :
      map (Int.castRingHom Real)
          (S.currentBasePolynomial n * denominator) =
        C c * map (Int.castRingHom Real) numerator := by
    apply (algebraicIndependent_iff_injective_aeval.mp hcoord)
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hcast,
      stagePolynomialEval, MvPolynomial.coe_eval₂Hom] using hclearing'
  have hnum0 : numerator ≠ 0 := by
    intro hzero
    apply hnumerator
    rw [hzero]
    exact dvd_zero _
  apply hnumerator
  exact prime_dvd_of_map_mul_eq_C_mul_map
    (S.currentBasePolynomial_prime n)
    (S.currentBasePolynomial_ne_C hfresh)
    hnum0 hc hpoly

/-- The previous stage-set independence together with the already proved
earlier `tau` transcendences supplies the labeled coefficient independence
used by `freshBase_not_stageMonomial_of_algebraicIndependent`. -/
theorem freshBase_not_stageMonomial {n : Nat}
    (hfresh : S.IsFreshBase n)
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    ¬ S.StageMonomial n (ι (S.baseAnalytic n)) := by
  have hfinite := S.algebraicIndependent_finiteFractionCoordinates
    htau hstage
  have hfun : S.finiteFractionCoordinates n =
      fun i : StageVar n ↦ ι (S.analyticAssignment n i) := by
    funext i
    exact S.finiteFractionCoordinates_eq_analyticAssignment n i
  rw [hfun] at hfinite
  exact S.freshBase_not_stageMonomial_of_algebraicIndependent
    hfresh hfinite

/-- Clause `(II)_n` turns hypothetical membership of `log u_n` in the old
field into the forbidden monomial description of the fresh base `u_n`.
Hence a fresh logarithm is not already in the completed old stage. -/
theorem freshLog_not_mem_of_stage_induction {n : Nat}
    (hfresh : S.IsFreshBase n)
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstageAI : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hstageII : S.StageLogDerivClassification n) :
    ι (S.logBaseAnalytic n) ∉ S.finiteStageField n := by
  intro hlogmem
  have hbaseA : S.baseAnalytic n ≠ 0 := by
    intro hzero
    have hpos := S.baseAnalytic_pos n ⟨1, zero_lt_one⟩
    rw [hzero] at hpos
    simp at hpos
  have hbase0 : ι (S.baseAnalytic n) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hbaseA)
  let base : S.finiteStageField n :=
    ⟨ι (S.baseAnalytic n), S.baseAnalytic_mem_finiteStageField n⟩
  let logBase : S.finiteStageField n :=
    ⟨ι (S.logBaseAnalytic n), hlogmem⟩
  have heq : ((base : K))′ = ((logBase : K))′ * (base : K) := by
    change PositiveAnalyticFractionField.derivation
        (ι (S.baseAnalytic n)) =
      PositiveAnalyticFractionField.derivation
          (ι (S.logBaseAnalytic n)) *
        ι (S.baseAnalytic n)
    rw [PositiveAnalyticFractionField.derivation_logBaseAnalytic]
    field_simp
  have hmonomial : S.StageMonomial n (ι (S.baseAnalytic n)) :=
    hstageII base logBase hbase0 heq
  exact (S.freshBase_not_stageMonomial hfresh htau hstageAI) hmonomial

/-- The resulting fresh-logarithm transcendence, with the sole use of
Wilkie Proposition 3.2(ii) delegated to the existing reduction lemma. -/
theorem freshLog_transcendental_of_stage_induction {n : Nat}
    (hfresh : S.IsFreshBase n)
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstageAI : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hstageII : S.StageLogDerivClassification n) :
    Transcendental (S.finiteStageField n)
      (ι (S.logBaseAnalytic n)) :=
  S.freshLog_transcendental_of_not_mem
    (S.freshLog_not_mem_of_stage_induction
      hfresh htau hstageAI hstageII)

end GeneratorSequence

end

end Natfunbasis.Wilkie
