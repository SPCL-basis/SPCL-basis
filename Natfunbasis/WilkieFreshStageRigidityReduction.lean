import Natfunbasis.WilkieStageLogRigidity
import Natfunbasis.WilkieFreshBaseExclusion
import Natfunbasis.WilkieFiniteStageInduction
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.NumDen

/-!
# Reduction of fresh-stage integral-slope rigidity to a prime residue

For a completed finite stage, algebraic independence identifies its field
exactly with the fraction field of a multivariate polynomial ring on the
actual stage generators.  The current W1 base is represented there by its
literal integer polynomial after scalar extension to `Real`.

This file proves the logarithmic-residue calculation over an arbitrary UFD,
including the case where the W1 base splits after scalar extension: it is
enough to choose a multiplicity-one non-invariant irreducible factor.  It
then transports that result through the canonical multivariate coordinate
equivalence and proves the exact `FreshStageIntegralSlopeRigidity` adapter.

Consequently the remaining stage-specific input is narrowly algebraic:
construct a common-denominator polynomial derivation, prove the scalar-
extended W1 base squarefree, and find a factor not dividing its derivative.
It is not another copy of the desired integral-slope conclusion.
-/

open scoped Differential

namespace Natfunbasis.Wilkie.FreshStageRigidityReduction

noncomputable section

/-! ## Ring-generic prime orders

The univariate API in `WilkieStageLogRigidity` is sufficient once a stage
has been exhibited as a simple extension.  A completed Wilkie stage is more
naturally a multivariate fraction field, however.  The following small API
records the part of the prime-order argument which does not depend on a
choice of polynomial coordinate.
-/

namespace GenericPrimeResidue

variable {F R : Type*} [Field F] [CharZero F]
  [CommRing R] [IsDomain R] [CharZero R] [Algebra F R]
  [UniqueFactorizationMonoid R]

/-- `HasExactOrder h n f` means that `h^n` is the exact power of the prime
`h` occurring in `f`. -/
def HasExactOrder (h : R) (n : Nat) (f : R) : Prop :=
  ∃ u, f = h ^ n * u ∧ ¬ h ∣ u

namespace HasExactOrder

variable {h : R} {m n : Nat} {f g : R}

theorem ne_zero (hh : h ≠ 0) (hf : HasExactOrder h n f) : f ≠ 0 := by
  obtain ⟨u, rfl, hu⟩ := hf
  exact mul_ne_zero (pow_ne_zero _ hh)
    fun hu0 ↦ hu (hu0 ▸ dvd_zero h)

theorem dvd (hf : HasExactOrder h n f) : h ^ n ∣ f := by
  obtain ⟨u, rfl, -⟩ := hf
  exact dvd_mul_right _ _

theorem not_dvd_succ (hh : h ≠ 0) (hf : HasExactOrder h n f) :
    ¬ h ^ (n + 1) ∣ f := by
  obtain ⟨u, hfu, hu⟩ := hf
  rintro ⟨v, hv⟩
  have heq : u = h * v := by
    apply mul_left_cancel₀ (pow_ne_zero n hh)
    calc
      h ^ n * u = f := hfu.symm
      _ = h ^ (n + 1) * v := hv
      _ = h ^ n * (h * v) := by rw [pow_succ, mul_assoc]
  exact hu ⟨v, heq⟩

theorem mul (hh : Prime h) (hf : HasExactOrder h m f)
    (hg : HasExactOrder h n g) : HasExactOrder h (m + n) (f * g) := by
  obtain ⟨u, rfl, hu⟩ := hf
  obtain ⟨v, rfl, hv⟩ := hg
  refine ⟨u * v, ?_, ?_⟩
  · rw [pow_add]
    ring
  · exact fun hd ↦ (hh.dvd_mul.mp hd).elim hu hv

theorem sub_of_dvd_succ (hf : HasExactOrder h n f)
    (hg : h ^ (n + 1) ∣ g) : HasExactOrder h n (f - g) := by
  obtain ⟨u, hfu, hu⟩ := hf
  obtain ⟨v, hgv⟩ := hg
  refine ⟨u - h * v, ?_, ?_⟩
  · rw [hfu, hgv, pow_succ']
    ring
  · intro hd
    apply hu
    have hhv : h ∣ h * v := dvd_mul_right _ _
    simpa only [sub_add_cancel] using dvd_add hd hhv

theorem neg (hf : HasExactOrder h n f) : HasExactOrder h n (-f) := by
  obtain ⟨u, rfl, hu⟩ := hf
  refine ⟨-u, by ring, ?_⟩
  simpa only [dvd_neg] using hu

theorem sub_of_dvd_succ_right (hg : HasExactOrder h n g)
    (hf : h ^ (n + 1) ∣ f) : HasExactOrder h n (f - g) := by
  have h := sub_of_dvd_succ (f := g) (g := f) hg hf
  simpa only [neg_sub] using h.neg

theorem pos_of_dvd (hf : HasExactOrder h n f) (hdiv : h ∣ f) : 0 < n := by
  obtain ⟨u, hfu, hu⟩ := hf
  cases n with
  | zero =>
      simp only [pow_zero, one_mul] at hfu
      exact False.elim (hu (hfu ▸ hdiv))
  | succ n => exact Nat.succ_pos n

theorem dvd_base_of_pos (hf : HasExactOrder h n f) (hn : 0 < n) : h ∣ f := by
  have hpow : h ^ 1 ∣ h ^ n := pow_dvd_pow h hn
  simpa only [pow_one] using hpow.trans hf.dvd

end HasExactOrder

/-- Every nonzero element of a UFD has an exact order at an irreducible. -/
theorem exists_hasExactOrder (h : R) (hh : Irreducible h)
    {f : R} (hf : f ≠ 0) : ∃ n, HasExactOrder h n f := by
  obtain ⟨n, u, hu, hfu⟩ := WfDvdMonoid.max_power_factor hf hh
  exact ⟨n, u, hfu, hu⟩

/-- An irreducible divisor of a nonzero squarefree element occurs with exact
order one.  This is the scalar-extension shape needed when a W1 base splits
over `Real`. -/
theorem hasExactOrder_one_of_irreducible_dvd_squarefree
    {h base : R} (hh : Irreducible h) (hdiv : h ∣ base)
    (hbase0 : base ≠ 0) (hsquarefree : Squarefree base) :
    HasExactOrder h 1 base := by
  obtain ⟨e, he⟩ := exists_hasExactOrder h hh hbase0
  have hepos : 0 < e := he.pos_of_dvd hdiv
  have hsquarefreePow : Squarefree (h ^ e) :=
    hsquarefree.squarefree_of_dvd he.dvd
  rcases hsquarefreePow.eq_zero_or_one_of_pow_of_not_isUnit
      hh.not_isUnit with hezero | heone
  · omega
  · simpa [heone] using he

/-- Leibniz expansion after extracting a positive prime power. -/
theorem deriv_pow_mul_factor (D : Derivation Int R R)
    (h u : R) {n : Nat} (hn : 0 < n) :
    D (h ^ n * u) = h ^ (n - 1) *
      ((n : R) * D h * u + h * D u) := by
  rw [D.leibniz, D.leibniz_pow]
  simp only [nsmul_eq_mul]
  rw [show h ^ n = h ^ (n - 1) * h by
    nth_rewrite 1 [show n = (n - 1) + 1 by omega]
    rw [pow_succ]]
  ring

include F
/-- At a non-invariant prime, differentiation lowers a positive exact order
by one. -/
theorem HasExactOrder.deriv (D : Derivation Int R R)
    {h f : R} {n : Nat} (hh : Prime h) (hDh : ¬ h ∣ D h)
    (hf : HasExactOrder h n f) (hn : 0 < n) :
    HasExactOrder h (n - 1) (D f) := by
  obtain ⟨u, hfu, hu⟩ := hf
  rw [hfu, deriv_pow_mul_factor D h u hn]
  refine ⟨(n : R) * D h * u + h * D u, rfl, ?_⟩
  intro hd
  have hfirst : h ∣ (n : R) * D h * u := by
    have hsecond : h ∣ h * D u := dvd_mul_right _ _
    simpa only [add_sub_cancel_right] using dvd_sub hd hsecond
  rcases hh.dvd_mul.mp hfirst with hleft | hu'
  · rcases hh.dvd_mul.mp hleft with hncast | hDh'
    · have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hnunitF : IsUnit (n : F) :=
        isUnit_iff_ne_zero.mpr hnF
      have hnunitR : IsUnit (n : R) := by
        have := hnunitF.map (algebraMap F R)
        simpa using this
      exact hh.not_unit (isUnit_of_dvd_unit hncast hnunitR)
    · exact hDh hDh'
  · exact hu hu'

/-- Multiplying a logarithmic cross numerator by the chosen prime exposes
the difference of the two prime orders. -/
theorem prime_mul_logCross_factor
    (D : Derivation Int R R) {h p q : R} {i j : Nat}
    (hp : HasExactOrder h i p) (hq : HasExactOrder h j q) :
    ∃ P Q : R,
      p = h ^ i * P ∧ q = h ^ j * Q ∧
      ¬ h ∣ P ∧ ¬ h ∣ Q ∧
      h * (D p * q - p * D q) =
        h ^ (i + j) *
          (((i : F) - (j : F) : F) • (D h * P * Q) +
            h * (D P * Q - P * D Q)) := by
  obtain ⟨P, hp, hP⟩ := hp
  obtain ⟨Q, hq, hQ⟩ := hq
  refine ⟨P, Q, hp, hq, hP, hQ, ?_⟩
  rw [hp, hq]
  calc
    h * (D (h ^ i * P) * (h ^ j * Q) -
        h ^ i * P * D (h ^ j * Q)) =
        (h * D (h ^ i * P)) * (h ^ j * Q) -
          (h ^ i * P) * (h * D (h ^ j * Q)) := by ring
    _ = _ := by
      rw [show h * D (h ^ i * P) =
          h ^ i * ((i : R) * D h * P + h * D P) by
        cases i with
        | zero => simp
        | succ i =>
            rw [deriv_pow_mul_factor D h P (Nat.succ_pos i), pow_succ]
            simp only [Nat.succ_sub_one]
            ring,
        show h * D (h ^ j * Q) =
          h ^ j * ((j : R) * D h * Q + h * D Q) by
        cases j with
        | zero => simp
        | succ j =>
            rw [deriv_pow_mul_factor D h Q (Nat.succ_pos j), pow_succ]
            simp only [Nat.succ_sub_one]
            ring,
        pow_add]
      simp only [Algebra.smul_def, map_sub, map_natCast]
      ring

/-- The prime-order part of the logarithmic-residue calculation is valid in
any UFD carrying a derivation. -/
theorem prime_pow_add_dvd_prime_mul_logCross
    (D : Derivation Int R R) {h p q : R} {i j : Nat}
    (hp : HasExactOrder h i p) (hq : HasExactOrder h j q) :
    h ^ (i + j) ∣ h * (D p * q - p * D q) := by
  obtain ⟨P, Q, -, -, -, -, hfactor⟩ :=
    prime_mul_logCross_factor (F := F) D hp hq
  rw [hfactor]
  exact dvd_mul_right _ _

/-- If a reduced denominator has positive order at a non-invariant prime,
its derivative cross numerator has exact order one less. -/
theorem hasExactOrder_derivCross_of_denominator
    (D : Derivation Int R R) {h r s : R} {e : Nat}
    (hh : Prime h) (hDh : ¬ h ∣ D h) (he : 0 < e)
    (hr : HasExactOrder h 0 r) (hs : HasExactOrder h e s) :
    HasExactOrder h (e - 1) (D r * s - r * D s) := by
  have hDs := hs.deriv (F := F) D hh hDh he
  have hsecond : HasExactOrder h (e - 1) (r * D s) := by
    simpa [Nat.zero_add] using hr.mul hh hDs
  apply hsecond.sub_of_dvd_succ_right
  have hse : h ^ e ∣ s := hs.dvd
  have htarget : h ^ e ∣ D r * s := dvd_mul_of_dvd_right hse _
  simpa [show e - 1 + 1 = e by omega] using htarget

/-- Replacing the chosen prime itself by any element having exact order one
does not alter the leading logarithmic-residue term. -/
theorem base_mul_logCross_factor
    (D : Derivation Int R R) {h base p q : R} {i j : Nat}
    (hbase : HasExactOrder h 1 base)
    (hp : HasExactOrder h i p) (hq : HasExactOrder h j q) :
    ∃ T P Q : R,
      base = h * T ∧ p = h ^ i * P ∧ q = h ^ j * Q ∧
      ¬ h ∣ T ∧ ¬ h ∣ P ∧ ¬ h ∣ Q ∧
      base * (D p * q - p * D q) =
        h ^ (i + j) *
          (T * (((i : F) - (j : F) : F) • (D h * P * Q) +
            h * (D P * Q - P * D Q))) ∧
      D base = D h * T + h * D T := by
  obtain ⟨T, hbase, hT⟩ := hbase
  simp only [pow_one] at hbase
  obtain ⟨P, Q, hp, hq, hP, hQ, hcross⟩ :=
    prime_mul_logCross_factor (F := F) D hp hq
  refine ⟨T, P, Q, hbase, hp, hq, hT, hP, hQ, ?_, ?_⟩
  · calc
      base * (D p * q - p * D q) =
          T * (h * (D p * q - p * D q)) := by rw [hbase]; ring
      _ = _ := by rw [hcross]; ring
  · rw [hbase, D.leibniz]
    ring

/-- A reduced rational primitive cannot have a pole at a simple,
non-invariant factor of the base in a logarithmic identity. -/
theorem denominator_not_dvd_prime_of_base_logarithmic_identity
    (D : Derivation Int R R)
    {h base : R} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (hbase : HasExactOrder h 1 base)
    (a : F) {p q r s : R}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrs : IsRelPrime r s)
    (heq :
      base * (D p * q - p * D q) * s ^ 2 =
        (algebraMap F R a * D base * s ^ 2 +
          base * (D r * s - r * D s)) * p * q) :
    ¬ h ∣ s := by
  intro hhs
  obtain ⟨i, hi⟩ := exists_hasExactOrder h hh hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder h hh hq0
  obtain ⟨l, hl⟩ := exists_hasExactOrder h hh hr0
  obtain ⟨e, hs⟩ := exists_hasExactOrder h hh hs0
  have hepos : 0 < e := hs.pos_of_dvd hhs
  have hlzero : l = 0 := by
    by_contra hl0
    exact hh.not_isUnit <| hrs
      (hl.dvd_base_of_pos (Nat.pos_of_ne_zero hl0)) hhs
  have hr : HasExactOrder h 0 r := by simpa [hlzero] using hl
  have hprimitive : HasExactOrder h (e - 1)
      (D r * s - r * D s) :=
    hasExactOrder_derivCross_of_denominator
      (F := F) D hh.prime hDh hepos hr hs
  have hbasePrimitive : HasExactOrder h e
      (base * (D r * s - r * D s)) := by
    have := hbase.mul hh.prime hprimitive
    simpa [show 1 + (e - 1) = e by omega] using this
  have hs2 : HasExactOrder h (e + e) (s ^ 2) := by
    simpa [pow_two] using hs.mul hh.prime hs
  have hcoefficient : h ^ (e + 1) ∣
      algebraMap F R a * D base * s ^ 2 := by
    have hpow : h ^ (e + 1) ∣ h ^ (e + e) :=
      pow_dvd_pow h (by omega)
    exact dvd_mul_of_dvd_right (hpow.trans hs2.dvd)
      (algebraMap F R a * D base)
  have hsum : HasExactOrder h e
      (algebraMap F R a * D base * s ^ 2 +
        base * (D r * s - r * D s)) := by
    have hneg := hbasePrimitive.neg
    have h := hneg.sub_of_dvd_succ_right hcoefficient
    simpa only [sub_neg_eq_add] using h
  have hright : HasExactOrder h ((e + i) + j)
      ((algebraMap F R a * D base * s ^ 2 +
          base * (D r * s - r * D s)) * p * q) :=
    (hsum.mul hh.prime hi).mul hh.prime hj
  have hbaseCross : h ^ (i + j) ∣
      base * (D p * q - p * D q) := by
    obtain ⟨T, P, Q, -, -, -, -, -, -, hfactor, -⟩ :=
      base_mul_logCross_factor (F := F) D hbase hi hj
    rw [hfactor]
    exact dvd_mul_right _ _
  have hleftBig : h ^ ((i + j) + (e + e)) ∣
      base * (D p * q - p * D q) * s ^ 2 := by
    rw [pow_add]
    exact mul_dvd_mul hbaseCross hs2.dvd
  have hnext : h ^ (((e + i) + j) + 1) ∣
      base * (D p * q - p * D q) * s ^ 2 :=
    (pow_dvd_pow h (by omega)).trans hleftBig
  apply hright.not_dvd_succ hh.ne_zero
  rw [← heq]
  exact hnext

/-- Prime-residue comparison at a regular primitive.  The selected factor
need only occur once in `base`; `base` itself need not remain irreducible
after extending the coefficient field. -/
theorem integer_slope_of_base_logarithmic_identity_of_regular_primitive
    (D : Derivation Int R R)
    {h base : R} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (hbase : HasExactOrder h 1 base)
    (a : F) {p q r s : R}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hhs : ¬ h ∣ s)
    (heq :
      base * (D p * q - p * D q) * s ^ 2 =
        (algebraMap F R a * D base * s ^ 2 +
          base * (D r * s - r * D s)) * p * q) :
    ∃ m : Int, a = (m : F) := by
  obtain ⟨i, hi⟩ := exists_hasExactOrder h hh hp0
  obtain ⟨j, hj⟩ := exists_hasExactOrder h hh hq0
  obtain ⟨T, P, Q, hbaseEq, hp, hq, hT, hP, hQ,
      hcross, hDbase⟩ :=
    base_mul_logCross_factor (F := F) D hbase hi hj
  let E : R := D P * Q - P * D Q
  let B : R := D r * s - r * D s
  have hcancel :
      T * (((i : F) - (j : F) : F) • (D h * P * Q) + h * E) * s ^ 2 =
        (algebraMap F R a * D base * s ^ 2 + base * B) * P * Q := by
    apply mul_left_cancel₀ (pow_ne_zero (i + j) hh.ne_zero)
    calc
      h ^ (i + j) *
          (T * (((i : F) - (j : F) : F) • (D h * P * Q) +
            h * E) * s ^ 2) =
          base * (D p * q - p * D q) * s ^ 2 := by
            rw [hcross]
            dsimp [E]
            ring
      _ = (algebraMap F R a * D base * s ^ 2 +
          base * (D r * s - r * D s)) * p * q := heq
      _ = h ^ (i + j) *
          ((algebraMap F R a * D base * s ^ 2 + base * B) * P * Q) := by
            rw [hp, hq, pow_add]
            dsimp [B]
            ring
  have hdiv : h ∣
      algebraMap F R (((i : F) - (j : F)) - a) *
        (D h * T * P * Q * s ^ 2) := by
    refine ⟨algebraMap F R a * D T * s ^ 2 * P * Q +
        T * B * P * Q - T * E * s ^ 2, ?_⟩
    have hcancel' := hcancel
    rw [hDbase, hbaseEq] at hcancel'
    dsimp [E, B] at hcancel' ⊢
    simp only [Algebra.smul_def, map_sub] at hcancel' ⊢
    linear_combination hcancel'
  have hrest : ¬ h ∣ D h * T * P * Q * s ^ 2 := by
    apply hh.prime.not_dvd_mul
    · apply hh.prime.not_dvd_mul
      · apply hh.prime.not_dvd_mul
        · exact hh.prime.not_dvd_mul hDh hT
        · exact hP
      · exact hQ
    · intro hs2
      exact hhs (hh.prime.dvd_of_dvd_pow hs2)
  have hscalar : h ∣
      algebraMap F R (((i : F) - (j : F)) - a) :=
    (hh.prime.dvd_mul.mp hdiv).resolve_right hrest
  have ha : (i : F) - (j : F) = a := by
    by_contra hne
    have hunitF : IsUnit (((i : F) - (j : F)) - a) :=
      isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)
    have hunitR : IsUnit
        (algebraMap F R (((i : F) - (j : F)) - a)) :=
      hunitF.map (algebraMap F R)
    exact hh.not_isUnit (isUnit_of_dvd_unit hscalar hunitR)
  refine ⟨(i : Int) - (j : Int), ?_⟩
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  exact ha.symm

/-- Fully reduced UFD prime-residue theorem for a base having a simple
non-invariant factor. -/
theorem integer_slope_of_base_logarithmic_identity
    (D : Derivation Int R R)
    {h base : R} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (hbase : HasExactOrder h 1 base)
    (a : F) {p q r s : R}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hrs : IsRelPrime r s)
    (heq :
      base * (D p * q - p * D q) * s ^ 2 =
        (algebraMap F R a * D base * s ^ 2 +
          base * (D r * s - r * D s)) * p * q) :
    ∃ m : Int, a = (m : F) := by
  by_cases hr0 : r = 0
  · have hbaseEq :
        base * (D p * q - p * D q) =
          algebraMap F R a * D base * p * q := by
      apply mul_right_cancel₀ (pow_ne_zero 2 hs0)
      calc
        base * (D p * q - p * D q) * s ^ 2 =
            (algebraMap F R a * D base * s ^ 2 +
              base * (D r * s - r * D s)) * p * q := heq
        _ = (algebraMap F R a * D base * p * q) * s ^ 2 := by
          rw [hr0, map_zero]
          ring
    apply integer_slope_of_base_logarithmic_identity_of_regular_primitive
      (F := F) D hh hDh hbase (r := 0) (s := 1) a hp0 hq0
      hh.prime.not_dvd_one
    simpa using hbaseEq
  · apply integer_slope_of_base_logarithmic_identity_of_regular_primitive
      (F := F) D hh hDh hbase a hp0 hq0
    · exact denominator_not_dvd_prime_of_base_logarithmic_identity
        (F := F) D hh hDh hbase a hp0 hq0 hr0 hs0 hrs heq
    · exact heq

/-! ### Passage to a fraction field -/

/-- Clearing denominators for the canonical extension of a derivation from
a UFD to its fraction field. -/
theorem cleared_base_logarithmic_identity_of_fractions
    (D : Derivation Int R R) {base : R} (hbase0 : base ≠ 0)
    (a : F) {p q r s : R} (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (heq :
      FractionDerivation.extend D
          (algebraMap R (FractionRing R) p /
            algebraMap R (FractionRing R) q) =
        (algebraMap F (FractionRing R) a *
              (FractionDerivation.extend D
                  (algebraMap R (FractionRing R) base) /
                algebraMap R (FractionRing R) base) +
            FractionDerivation.extend D
              (algebraMap R (FractionRing R) r /
                algebraMap R (FractionRing R) s)) *
          (algebraMap R (FractionRing R) p /
            algebraMap R (FractionRing R) q)) :
    base * (D p * q - p * D q) * s ^ 2 =
      (algebraMap F R a * D base * s ^ 2 +
        base * (D r * s - r * D s)) * p * q := by
  apply IsFractionRing.injective R (FractionRing R)
  rw [FractionDerivation.extend_div_algebraMap,
    FractionDerivation.extend_div_algebraMap,
    FractionDerivation.extend_algebraMap] at heq
  simp only [map_mul, map_add, map_sub, map_pow]
  have hbaseMap : algebraMap R (FractionRing R) base ≠ 0 :=
    by simpa using
      (IsFractionRing.injective R (FractionRing R)).ne hbase0
  have hqMap : algebraMap R (FractionRing R) q ≠ 0 :=
    by simpa using
      (IsFractionRing.injective R (FractionRing R)).ne hq0
  have hsMap : algebraMap R (FractionRing R) s ≠ 0 :=
    by simpa using
      (IsFractionRing.injective R (FractionRing R)).ne hs0
  rw [IsScalarTower.algebraMap_apply F R (FractionRing R)] at heq
  field_simp [hbaseMap, hqMap, hsMap] at heq ⊢
  linear_combination heq

/-- Fraction-field form of the generic prime-residue theorem.  This is the
direct multivariate replacement for choosing one simple-extension
coordinate. -/
theorem fractionRing_integer_slope_of_base_logarithmic_identity
    (D : Derivation Int R R)
    {h base : R} (hh : Irreducible h) (hDh : ¬ h ∣ D h)
    (hbase : HasExactOrder h 1 base)
    (a : F) (u v : FractionRing R) (hu0 : u ≠ 0)
    (heq : FractionDerivation.extend D u =
      (algebraMap F (FractionRing R) a *
          (FractionDerivation.extend D
              (algebraMap R (FractionRing R) base) /
            algebraMap R (FractionRing R) base) +
        FractionDerivation.extend D v) * u) :
    ∃ m : Int, a = (m : F) := by
  let p : R := IsFractionRing.num R u
  let q : R := IsFractionRing.den R u
  let r : R := IsFractionRing.num R v
  let s : R := IsFractionRing.den R v
  have hp0 : p ≠ 0 := by
    simpa [p] using
      (IsFractionRing.num_eq_zero (A := R) u).not.mpr hu0
  have hq0 : q ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den R u).property
  have hs0 : s ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp
      (IsFractionRing.den R v).property
  have hrs : IsRelPrime r s := by
    simpa [r, s] using IsFractionRing.num_den_reduced R v
  have hu : algebraMap R (FractionRing R) p /
      algebraMap R (FractionRing R) q = u := by
    simp [p, q]
  have hv : algebraMap R (FractionRing R) r /
      algebraMap R (FractionRing R) s = v := by
    simp [r, s]
  have hbase0 : base ≠ 0 := hbase.ne_zero hh.ne_zero
  apply integer_slope_of_base_logarithmic_identity
    (F := F) D hh hDh hbase a hp0 hq0 hs0 hrs
  apply cleared_base_logarithmic_identity_of_fractions
    (F := F) D hbase0 a hq0 hs0
  simpa only [hu, hv] using heq

end GenericPrimeResidue

/-! ## Abstract logarithmic-residue criterion -/

variable {C K κ : Type*} [Field C] [Field K] [Field κ]
  [Algebra C K] [Algebra C κ] [Differential K]

/-- The exact local data supplied by a simple prime divisor of `beta`.

For the usual prime-adic construction, `κ` is the residue field of the
prime divisor and `residue` extracts the coefficient of its logarithmic
differential. -/
structure LogResidueCertificate (beta : K) where
  residue : K →ₗ[C] κ
  residue_deriv : ∀ v : K, residue v′ = 0
  residue_logDeriv_integral : ∀ u : K, u ≠ 0 →
    ∃ m : Int, residue (u′ / u) = (m : κ)
  residue_base_logDeriv : residue (beta′ / beta) = 1

/-- A logarithmic-residue certificate forces every constant slope to be an
integer.  This is the abstract form of the final one-line residue comparison
in Wilkie Proposition 3.1(ii). -/
theorem integralSlopeRigidity_of_logResidueCertificate
    [Differential.ContainConstants C K]
    {beta : K} (cert : LogResidueCertificate (C := C) (K := K) (κ := κ) beta) :
    Proposition31II.IntegralSlopeRigidity beta := by
  intro a u v ha hu0 hu
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero C ha
  obtain ⟨m, hm⟩ := cert.residue_logDeriv_integral u hu0
  have hlog : u′ / u = a * (beta′ / beta) + v′ := by
    exact (div_eq_iff hu0).2 hu
  have hres := congrArg cert.residue hlog
  have hcm : algebraMap C κ c = (m : κ) := by
    rw [← hm]
    rw [hres, map_add, cert.residue_deriv]
    rw [← hc]
    rw [← Algebra.smul_def c (beta′ / beta)]
    rw [map_smul, cert.residue_base_logDeriv]
    simp [Algebra.smul_def]
  have hcInt : c = (m : C) := by
    apply (algebraMap C κ).injective
    rw [hcm]
    exact (map_intCast (algebraMap C κ) m).symm
  refine ⟨m, ?_⟩
  rw [← hc, hcInt]
  exact map_intCast (algebraMap C K) m

/-! ## Canonical multivariate coordinates for a completed stage -/

end

end Natfunbasis.Wilkie.FreshStageRigidityReduction

namespace Natfunbasis.Wilkie.GeneratorSequence

noncomputable section

open FreshStageRigidityReduction

open Set MvPolynomial

local notation "A" => PositiveAnalyticFunction
local notation "Kₐ" => PositiveAnalyticFractionField
local notation "ι" => (algebraMap A Kₐ)

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- The polynomial coordinate ring on the actual completed-stage generator
set. -/
abbrev StageCoordinateRing (n : Nat) :=
  MvPolynomial (S.stageGenerators n) Real

/-- Its fraction field. -/
abbrev StageCoordinateField (n : Nat) :=
  FractionRing (S.StageCoordinateRing n)

/-- A labeled algebraic coordinate, regarded as an index in the actual
completed-stage generator set. -/
def stageGeneratorCoordinateIndex (n : Nat) (i : StageVar n) :
    S.stageGenerators n :=
  ⟨S.finiteFractionCoordinates n i,
    S.finiteFractionCoordinate_mem_stageGenerators n i⟩

@[simp]
theorem coe_stageGeneratorCoordinateIndex (n : Nat) (i : StageVar n) :
    ((S.stageGeneratorCoordinateIndex n i : S.stageGenerators n) : Kₐ) =
      S.finiteFractionCoordinates n i :=
  rfl

/-- Transport an integer stage polynomial to the real polynomial ring on
the actual completed-stage generator set. -/
def stageCoordinatePolynomial (n : Nat) (p : StagePolynomial n) :
    S.StageCoordinateRing n :=
  rename (S.stageGeneratorCoordinateIndex n)
    (map (Int.castRingHom Real) p)

/-- Evaluation of the transported polynomial recovers the existing staged
polynomial evaluation. -/
theorem aeval_stageCoordinatePolynomial (n : Nat)
    (p : StagePolynomial n) :
    MvPolynomial.aeval ((↑) : S.stageGenerators n → Kₐ)
        (S.stageCoordinatePolynomial n p) =
      S.stagePolynomialEval n p := by
  rw [stageCoordinatePolynomial, MvPolynomial.aeval_rename]
  change MvPolynomial.eval₂ (algebraMap Real Kₐ)
      (((↑) : S.stageGenerators n → Kₐ) ∘
        S.stageGeneratorCoordinateIndex n)
      (map (Int.castRingHom Real) p) = S.stagePolynomialEval n p
  rw [MvPolynomial.eval₂_map]
  rw [show (algebraMap Real Kₐ).comp (Int.castRingHom Real) =
      Int.castRingHom Kₐ by
    ext z
    simp]
  change MvPolynomial.eval₂ (Int.castRingHom Kₐ)
      (((↑) : S.stageGenerators n → Kₐ) ∘
        S.stageGeneratorCoordinateIndex n) p =
    MvPolynomial.eval₂ (Int.castRingHom Kₐ)
      (fun i ↦ ι (S.analyticAssignment n i)) p
  apply congrArg (fun assignment : StageVar n → Kₐ ↦
    MvPolynomial.eval₂ (Int.castRingHom Kₐ) assignment p)
  funext i
  exact S.finiteFractionCoordinates_eq_analyticAssignment n i

/-- Algebraic independence gives the exact rational-coordinate
identification of the completed finite-stage field. -/
def stageCoordinateEquiv {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    S.StageCoordinateField n ≃ₐ[Real] S.finiteStageField n := by
  let e₀ := hstage.aevalEquivField
  have hrange :
      Set.range ((↑) : S.stageGenerators n → Kₐ) =
        S.stageGenerators n := by
    ext x
    simp
  have hfield :
      IntermediateField.adjoin Real
          (Set.range ((↑) : S.stageGenerators n → Kₐ)) =
        (S.finiteStageField n).toIntermediateField := by
    rw [hrange, ← S.finiteStageField_toIntermediateField_eq_adjoin n]
  exact e₀.trans (IntermediateField.equivOfEq hfield)

/-- The coordinate equivalence sends an embedded coordinate polynomial to
its analytic evaluation. -/
theorem stageCoordinateEquiv_algebraMap_apply {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (p : S.StageCoordinateRing n) :
    ((S.stageCoordinateEquiv hstage
      (algebraMap (S.StageCoordinateRing n)
        (S.StageCoordinateField n) p) : S.finiteStageField n) : Kₐ) =
      MvPolynomial.aeval ((↑) : S.stageGenerators n → Kₐ) p := by
  change (((hstage.aevalEquivField
      (algebraMap (S.StageCoordinateRing n)
        (S.StageCoordinateField n) p) :
          IntermediateField.adjoin Real
            (Set.range ((↑) : S.stageGenerators n → Kₐ))) : Kₐ)) = _
  exact hstage.aevalEquivField_algebraMap_apply_coe p

/-- The real multivariate polynomial representing the current W1 base. -/
def stageCoordinateBasePolynomial (n : Nat) : S.StageCoordinateRing n :=
  S.stageCoordinatePolynomial n (S.currentBasePolynomial n)

/-- Under the canonical field equivalence, the current base polynomial is
exactly the current analytic base element. -/
theorem stageCoordinateEquiv_currentBase {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    S.stageCoordinateEquiv hstage
        (algebraMap (S.StageCoordinateRing n)
          (S.StageCoordinateField n)
          (S.stageCoordinateBasePolynomial n)) =
      S.currentBaseElement n := by
  apply Subtype.ext
  rw [stageCoordinateEquiv_algebraMap_apply]
  rw [stageCoordinateBasePolynomial, aeval_stageCoordinatePolynomial,
    S.stagePolynomialEval_currentBasePolynomial]
  rfl

/-- The coordinate representative of a fresh base is nonzero. -/
theorem stageCoordinateBasePolynomial_ne_zero {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    S.stageCoordinateBasePolynomial n ≠ 0 := by
  intro hzero
  have hmapzero :
      algebraMap (S.StageCoordinateRing n) (S.StageCoordinateField n)
          (S.stageCoordinateBasePolynomial n) = 0 := by
    rw [hzero, map_zero]
  have hbasezero : S.currentBaseElement n = 0 := by
    rw [← S.stageCoordinateEquiv_currentBase hstage, hmapzero, map_zero]
  exact S.currentBaseElement_ne_zero n hbasezero

/-- Freshness and the earlier power-coordinate transcendences ensure that
the real coordinate representative of the current W1 base is not a unit.
This is the nonconstant input needed to choose an irreducible factor after
scalar extension. -/
theorem stageCoordinateBasePolynomial_not_isUnit {n : Nat}
    (hfresh : S.IsFreshBase n)
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j))) :
    ¬ IsUnit (S.stageCoordinateBasePolynomial n) := by
  intro hunit
  obtain ⟨c, _hcunit, hconstant⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit
  have hindex : Function.Injective (S.stageGeneratorCoordinateIndex n) := by
    intro i j hij
    apply S.finiteFractionCoordinates_injective_of_tauTranscendence htau
    exact congrArg Subtype.val hij
  have hmapConstant :
      map (Int.castRingHom Real) (S.currentBasePolynomial n) = C c := by
    apply MvPolynomial.rename_injective
      (S.stageGeneratorCoordinateIndex n) hindex
    simpa [stageCoordinateBasePolynomial, stageCoordinatePolynomial] using
      hconstant
  let z : Int := (S.currentBasePolynomial n).coeff 0
  have hcz : c = (z : Real) := by
    have hcoeff := congrArg (MvPolynomial.coeff (0 : StageVar n →₀ Nat))
      hmapConstant
    rw [MvPolynomial.coeff_map] at hcoeff
    simpa [z] using hcoeff.symm
  apply S.currentBasePolynomial_ne_C hfresh z
  apply MvPolynomial.map_injective (Int.castRingHom Real)
    Int.cast_injective
  rw [hmapConstant, MvPolynomial.map_C, hcz]
  simp

/-- A fresh real-coordinate W1 base has an irreducible factor. -/
theorem exists_irreducible_factor_stageCoordinateBase {n : Nat}
    (hfresh : S.IsFreshBase n)
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) :
    ∃ h : S.StageCoordinateRing n,
      Irreducible h ∧ h ∣ S.stageCoordinateBasePolynomial n := by
  exact WfDvdMonoid.exists_irreducible_factor
    (S.stageCoordinateBasePolynomial_not_isUnit hfresh htau)
    (S.stageCoordinateBasePolynomial_ne_zero hstage)

/-- If scalar extension of the W1 base is squarefree, one of its real
irreducible factors has exact order one.  This proves the factor-theoretic
part of the fresh-stage residue input. -/
theorem exists_irreducible_orderOne_stageCoordinateBase {n : Nat}
    (hfresh : S.IsFreshBase n)
    (htau : ∀ j < n,
      Transcendental (S.finiteStageBeforeTau j).toIntermediateField
        (ι (S.realTauAnalyticFunction j)))
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hsquarefree : Squarefree (S.stageCoordinateBasePolynomial n)) :
    ∃ h : S.StageCoordinateRing n,
      Irreducible h ∧
        GenericPrimeResidue.HasExactOrder h 1
          (S.stageCoordinateBasePolynomial n) := by
  obtain ⟨h, hh, hdiv⟩ :=
    S.exists_irreducible_factor_stageCoordinateBase hfresh htau hstage
  refine ⟨h, hh, ?_⟩
  exact GenericPrimeResidue.hasExactOrder_one_of_irreducible_dvd_squarefree
    hh hdiv (S.stageCoordinateBasePolynomial_ne_zero hstage) hsquarefree

/-! ## Direct prime-derivation reduction -/

/-- The exact local algebra data still needed at a completed fresh stage.

`polynomialDerivation` is a common-denominator multiple of the transported
analytic derivation which preserves the multivariate polynomial coordinate
ring.  The common denominator must avoid `primeFactor`; this is encoded by
the compatibility equation and `primeFactor_nonInvariant`.  The factor is
required to occur exactly once in the real scalar extension of the W1 base,
not to equal the whole base polynomial.  Thus this interface remains valid
when an integer-irreducible W1 polynomial splits over `Real`. -/
structure FreshStagePrimeDerivationInput {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n)) where
  polynomialDerivation :
    Derivation Int (S.StageCoordinateRing n) (S.StageCoordinateRing n)
  primeFactor : S.StageCoordinateRing n
  primeFactor_irreducible : Irreducible primeFactor
  currentBase_order_one :
    GenericPrimeResidue.HasExactOrder primeFactor 1
      (S.stageCoordinateBasePolynomial n)
  primeFactor_nonInvariant :
    ¬ primeFactor ∣ polynomialDerivation primeFactor
  derivationScale : S.StageCoordinateRing n
  derivation_compatibility : ∀ z : S.StageCoordinateField n,
    S.stageCoordinateEquiv hstage
        (FractionDerivation.extend polynomialDerivation z) =
      S.stageCoordinateEquiv hstage
          (algebraMap (S.StageCoordinateRing n)
            (S.StageCoordinateField n) derivationScale) *
        (S.stageCoordinateEquiv hstage z)′

/-- Build the direct stage input from squarefreeness, a chosen irreducible
divisor, and a common-denominator polynomial derivation. -/
def FreshStagePrimeDerivationInput.ofSquarefreeFactor {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (hsquarefree : Squarefree (S.stageCoordinateBasePolynomial n))
    (polynomialDerivation :
      Derivation Int (S.StageCoordinateRing n) (S.StageCoordinateRing n))
    (derivationScale : S.StageCoordinateRing n)
    (hcompat : ∀ z : S.StageCoordinateField n,
      S.stageCoordinateEquiv hstage
          (FractionDerivation.extend polynomialDerivation z) =
        S.stageCoordinateEquiv hstage
            (algebraMap (S.StageCoordinateRing n)
              (S.StageCoordinateField n) derivationScale) *
          (S.stageCoordinateEquiv hstage z)′)
    (primeFactor : S.StageCoordinateRing n)
    (hirreducible : Irreducible primeFactor)
    (hdiv : primeFactor ∣ S.stageCoordinateBasePolynomial n)
    (hnoninvariant :
      ¬ primeFactor ∣ polynomialDerivation primeFactor) :
    S.FreshStagePrimeDerivationInput hstage where
  polynomialDerivation := polynomialDerivation
  primeFactor := primeFactor
  primeFactor_irreducible := hirreducible
  currentBase_order_one :=
    GenericPrimeResidue.hasExactOrder_one_of_irreducible_dvd_squarefree
      hirreducible hdiv
        (S.stageCoordinateBasePolynomial_ne_zero hstage) hsquarefree
  primeFactor_nonInvariant := hnoninvariant
  derivationScale := derivationScale
  derivation_compatibility := hcompat

/-- A simple non-invariant factor in polynomial coordinates proves the
integral-slope rigidity required at that stage. -/
theorem currentBase_integralSlopeRigidity_of_primeDerivation {n : Nat}
    (hstage : AlgebraicIndepOn Real id (S.stageGenerators n))
    (input : S.FreshStagePrimeDerivationInput hstage) :
    Proposition31II.IntegralSlopeRigidity (S.currentBaseElement n) := by
  intro a u v ha hu0 hu
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero Real ha
  let e := S.stageCoordinateEquiv hstage
  let U : S.StageCoordinateField n := e.symm u
  let V : S.StageCoordinateField n := e.symm v
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hu0
    have hzero' := congrArg e hzero
    simpa [U, e] using hzero'
  have hbase : e
      (algebraMap (S.StageCoordinateRing n) (S.StageCoordinateField n)
        (S.stageCoordinateBasePolynomial n)) =
      S.currentBaseElement n :=
    S.stageCoordinateEquiv_currentBase hstage
  have hcoordEq :
      FractionDerivation.extend input.polynomialDerivation U =
        (algebraMap Real (S.StageCoordinateField n) c *
            (FractionDerivation.extend input.polynomialDerivation
                (algebraMap (S.StageCoordinateRing n)
                  (S.StageCoordinateField n)
                  (S.stageCoordinateBasePolynomial n)) /
              algebraMap (S.StageCoordinateRing n)
                (S.StageCoordinateField n)
                (S.stageCoordinateBasePolynomial n)) +
          FractionDerivation.extend input.polynomialDerivation V) * U := by
    apply e.injective
    rw [input.derivation_compatibility]
    simp only [map_mul, map_add, map_div₀, AlgEquiv.commutes]
    rw [input.derivation_compatibility,
      input.derivation_compatibility, hbase]
    simp only [U, V, e, AlgEquiv.apply_symm_apply]
    rw [hc, hu]
    simp only [div_eq_mul_inv]
    ring
  obtain ⟨m, hm⟩ :=
    GenericPrimeResidue.fractionRing_integer_slope_of_base_logarithmic_identity
      input.polynomialDerivation input.primeFactor_irreducible
      input.primeFactor_nonInvariant input.currentBase_order_one
      c U V hU0 hcoordEq
  refine ⟨m, ?_⟩
  rw [← hc, hm]
  exact map_intCast (algebraMap Real (S.finiteStageField n)) m

/-- Stagewise algebraic independence plus the explicit local
prime-derivation construction discharges the global fresh-stage rigidity
input used by `WilkieFiniteStageInduction`. -/
theorem freshStageIntegralSlopeRigidity_of_primeDerivations
    (hstage : ∀ n, AlgebraicIndepOn Real id (S.stageGenerators n))
    (hprime : ∀ n, S.IsFreshBase n →
      S.FreshStagePrimeDerivationInput (hstage n)) :
    S.FreshStageIntegralSlopeRigidity := by
  intro n hfresh
  exact S.currentBase_integralSlopeRigidity_of_primeDerivation
    (hstage n) (hprime n hfresh)

/-! ## Stage-facing residue adapter -/

variable {κₛ : Type*} [Field κₛ] [Algebra Real κₛ]

/-- A residue certificate at the current coordinate polynomial is the sole
local input needed for fresh-stage integral-slope rigidity. -/
theorem currentBase_integralSlopeRigidity_of_logResidue {n : Nat}
    (cert : LogResidueCertificate
      (C := Real) (K := S.finiteStageField n) (κ := κₛ)
      (S.currentBaseElement n)) :
    Proposition31II.IntegralSlopeRigidity (S.currentBaseElement n) :=
  integralSlopeRigidity_of_logResidueCertificate cert

/-- Exact algebraic construction problem left at a fresh stage.  In the
canonical multivariate rational coordinates above, it is supplied by any
multiplicity-one irreducible factor of `stageCoordinateBasePolynomial` which
is non-invariant under the transported derivation. -/
def FreshStageLogResidueInput (n : Nat) : Prop :=
  ∃ (κₛ : Type) (_ : Field κₛ) (_ : Algebra Real κₛ),
    Nonempty (LogResidueCertificate
      (C := Real) (K := S.finiteStageField n) (κ := κₛ)
      (S.currentBaseElement n))

/-- Discharging the explicit residue construction problem at every fresh
stage proves exactly the induction input `FreshStageIntegralSlopeRigidity`. -/
theorem freshStageIntegralSlopeRigidity_of_logResidues
    (hresidue : ∀ n, S.IsFreshBase n → S.FreshStageLogResidueInput n) :
    S.FreshStageIntegralSlopeRigidity := by
  intro n hfresh
  obtain ⟨κₛ, fieldκ, algebraκ, ⟨cert⟩⟩ := hresidue n hfresh
  letI : Field κₛ := fieldκ
  letI : Algebra Real κₛ := algebraκ
  exact S.currentBase_integralSlopeRigidity_of_logResidue cert

end

end Natfunbasis.Wilkie.GeneratorSequence
