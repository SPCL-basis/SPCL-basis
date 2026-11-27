import Natfunbasis.AlgebraicIndependence
import Natfunbasis.Expressions
import Natfunbasis.WilkieGeneratorExistence
import Natfunbasis.WilkieIntegerEvaluation
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Direct integer separation by rapidly growing coordinates

This file isolates a purely discrete alternative to an integer-to-real
identity theorem.  The coordinate family

`n, n^n, n^(n^2), ...`

is algebraically independent as a family of integer-valued functions on the
positive integers.  The proof evaluates a putative polynomial relation at a
sufficiently large prime.  Distinct multivariate monomials then have distinct
prime-adic orders; the coefficient at the least order cannot cancel.

The argument uses neither real evaluation nor an eventual-zero theorem for
the original expression language.
-/

namespace Natfunbasis

namespace DirectIntegerRapidSeparation

open scoped BigOperators
open Filter MvPolynomial

noncomputable section

/-- The polynomial whose coefficients are the entries of a monomial exponent
vector.  Evaluation at `n` is the exponent obtained after substituting
`X_i = n^(n^i)`. -/
def exponentPolynomial (m : Nat →₀ Nat) : Polynomial Int :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff
      (m.mapRange (fun e : Nat ↦ (e : Int)) (by simp)))

theorem exponentPolynomial_injective :
    Function.Injective exponentPolynomial := by
  intro m l h
  apply Finsupp.mapRange_injective (fun e : Nat ↦ (e : Int)) (by simp)
      Nat.cast_injective
  exact congrArg AddMonoidAlgebra.coeff
    (congrArg Polynomial.toFinsupp h)

/-- The natural exponent encoded by a monomial at the integer `n`. -/
def exponentCode (n : Nat) (m : Nat →₀ Nat) : Nat :=
  m.sum fun i e ↦ e * n ^ i

theorem eval_exponentPolynomial (n : Nat) (m : Nat →₀ Nat) :
    Polynomial.eval (n : Int) (exponentPolynomial m) =
      (exponentCode n m : Int) := by
  classical
  simp only [exponentPolynomial, Polynomial.eval_eq_sum, Polynomial.sum,
    Polynomial.coeff_ofFinsupp, Polynomial.support_ofFinsupp,
    Finsupp.mapRange_apply, exponentCode, Finsupp.sum]
  rw [Finsupp.support_mapRange_of_injective rfl m Nat.cast_injective]
  push_cast
  rfl

/-- The rapidly growing integer coordinate `n^(n^i)`. -/
def rapidCoordinate (i : Nat) (n : PosNat) : Int :=
  (n.1 : Int) ^ (n.1 ^ i)

theorem monomial_rapidCoordinate (n : PosNat) (m : Nat →₀ Nat) :
    m.prod (fun i e ↦ rapidCoordinate i n ^ e) =
      (n.1 : Int) ^ exponentCode n.1 m := by
  classical
  simp only [rapidCoordinate, ← pow_mul, Finsupp.prod, exponentCode]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact Nat.mul_comm _ _

/-! ## The elementary least-order argument -/

/-- A finite sum of powers cannot vanish when one term has a unique least
exponent and its coefficient is not divisible by the base. -/
theorem sum_mul_pow_ne_zero_of_unique_min
    {A : Type*} (s : Finset A)
    (c : A → Int) (e : A → Nat) (a : A) (p : Nat)
    (ha : a ∈ s)
    (hp : p ≠ 0)
    (hmin : ∀ b ∈ s, b ≠ a → e a < e b)
    (hcoeff : ¬ (p : Int) ∣ c a) :
    ∑ b ∈ s, c b * (p : Int) ^ e b ≠ 0 := by
  classical
  intro hsum
  have hrest_dvd : (p : Int) ^ (e a + 1) ∣
      ∑ b ∈ s.erase a, c b * (p : Int) ^ e b := by
    apply Finset.dvd_sum
    intro b hb
    have hbmem : b ∈ s := Finset.mem_of_mem_erase hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    exact ((pow_dvd_pow (p : Int) (hmin b hbmem hba)).mul_left (c b))
  have hsplit : c a * (p : Int) ^ e a +
      ∑ b ∈ s.erase a, c b * (p : Int) ^ e b = 0 := by
    calc
      c a * (p : Int) ^ e a +
          ∑ b ∈ s.erase a, c b * (p : Int) ^ e b =
          ∑ b ∈ s, c b * (p : Int) ^ e b :=
        Finset.add_sum_erase s (fun b ↦ c b * (p : Int) ^ e b) ha
      _ = 0 := hsum
  have hselected_dvd : (p : Int) ^ (e a + 1) ∣
      c a * (p : Int) ^ e a := by
    rw [eq_neg_of_add_eq_zero_left hsplit]
    exact dvd_neg.mpr hrest_dvd
  obtain ⟨z, hz⟩ := hselected_dvd
  apply hcoeff
  refine ⟨z, ?_⟩
  have hpow : (p : Int) ^ e a ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr hp)
  apply mul_left_cancel₀ hpow
  calc
    (p : Int) ^ e a * c a = c a * (p : Int) ^ e a := mul_comm _ _
    _ = (p : Int) ^ (e a + 1) * z := hz
    _ = (p : Int) ^ e a * ((p : Int) * z) := by rw [pow_succ, mul_assoc]

/-! ## Strategic primes separate all monomials in a fixed polynomial -/

/-- For a fixed nonzero multivariate polynomial, all exponent codes occurring
in its support are distinct at every sufficiently large natural input. -/
theorem eventually_exponentCode_injective_on_support
    (P : MvPolynomial Nat Int) :
    ∀ᶠ n : Nat in atTop,
      Set.InjOn (exponentCode n) P.support := by
  rw [show (∀ᶠ n : Nat in atTop, Set.InjOn (exponentCode n) P.support) ↔
      (∀ᶠ n : Nat in atTop, ∀ m ∈ P.support, ∀ l ∈ P.support,
        exponentCode n m = exponentCode n l → m = l) by rfl]
  apply P.support.eventually_all.mpr
  intro m hm
  apply P.support.eventually_all.mpr
  intro l hl
  by_cases hml : m = l
  · exact Filter.Eventually.of_forall fun _ _ ↦ hml
  · have hpoly : exponentPolynomial m - exponentPolynomial l ≠ 0 := by
      intro hzero
      apply hml
      apply exponentPolynomial_injective
      exact sub_eq_zero.mp hzero
    let q : Polynomial Rat :=
      (exponentPolynomial m - exponentPolynomial l).map
        (Int.castRingHom Rat)
    have hq : q ≠ 0 := by
      intro hqzero
      apply hpoly
      apply Polynomial.map_injective (f := Int.castRingHom Rat)
        Int.cast_injective
      simpa only [Polynomial.map_zero] using hqzero
    have hroot :=
      (Polynomial.eventually_atTop_not_isRoot q hq).natCast_atTop
    filter_upwards [hroot] with n hn hcode
    exfalso
    apply hn
    rw [Polynomial.IsRoot.def]
    dsimp only [q]
    change Polynomial.eval ((Int.castRingHom Rat) (n : Int))
      ((exponentPolynomial m - exponentPolynomial l).map
        (Int.castRingHom Rat)) = 0
    have hcodeInt : (exponentCode n m : Int) =
        (exponentCode n l : Int) := congrArg Int.ofNat hcode
    rw [Polynomial.eval_map_apply,
      Polynomial.eval_sub, eval_exponentPolynomial,
      eval_exponentPolynomial, hcodeInt, sub_self, map_zero]

/-- A large prime simultaneously separates all monomials in the support and
divides none of their nonzero coefficients. -/
theorem exists_separating_prime {P : MvPolynomial Nat Int} (_hP : P ≠ 0) :
    ∃ p : Nat, p.Prime ∧
      Set.InjOn (exponentCode p) P.support ∧
      ∀ m ∈ P.support, ¬ (p : Int) ∣ P.coeff m := by
  have hevent := eventually_exponentCode_injective_on_support P
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let coefficientBound : Nat := P.support.sup fun m ↦ (P.coeff m).natAbs
  obtain ⟨p, hpBound, hpPrime⟩ :=
    Nat.exists_infinite_primes (max N coefficientBound + 1)
  refine ⟨p, hpPrime, hN p ?_, ?_⟩
  · omega
  · intro m hm hdiv
    have hcoeff_ne : P.coeff m ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    have hp_le_abs : p ≤ (P.coeff m).natAbs :=
      Int.natAbs_le_of_dvd_ne_zero hdiv hcoeff_ne
    have habs_le : (P.coeff m).natAbs ≤ coefficientBound :=
      Finset.le_sup (f := fun m ↦ (P.coeff m).natAbs) hm
    omega

/-- Every nonzero integer-coefficient polynomial in the rapid coordinates is
detected at one positive prime input. -/
theorem exists_rapid_eval_ne_zero {P : MvPolynomial Nat Int} (hP : P ≠ 0) :
    ∃ n : PosNat, MvPolynomial.eval (fun i ↦ rapidCoordinate i n) P ≠ 0 := by
  classical
  obtain ⟨p, hpPrime, hcode, hcoeff⟩ := exists_separating_prime hP
  let n : PosNat := ⟨p, hpPrime.pos⟩
  refine ⟨n, ?_⟩
  rw [MvPolynomial.eval_eq]
  have hmonomial (d : Nat →₀ Nat) :
      ∏ i ∈ d.support, rapidCoordinate i n ^ d i =
        (p : Int) ^ exponentCode p d := by
    simpa only [Finsupp.prod] using monomial_rapidCoordinate n d
  simp_rw [hmonomial]
  obtain ⟨a, ha, hamin⟩ :=
    P.support.exists_min_image (exponentCode p)
      (MvPolynomial.support_nonempty.mpr hP)
  apply sum_mul_pow_ne_zero_of_unique_min P.support P.coeff
      (exponentCode p) a p ha hpPrime.ne_zero
  · intro b hb hba
    exact (hamin b hb).lt_of_ne
      (fun heq ↦ hba (hcode ha hb heq).symm)
  · exact hcoeff a ha

/-- Evaluation in the ring of integer-valued functions at the rapid family is
injective. -/
theorem rapid_aeval_injective :
    Function.Injective
      (MvPolynomial.aeval rapidCoordinate :
        MvPolynomial Nat Int → (PosNat → Int)) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  by_contra hsub
  obtain ⟨n, hn⟩ := exists_rapid_eval_ne_zero hsub
  apply hn
  have hpoint :
      MvPolynomial.eval (fun i ↦ rapidCoordinate i n) P =
        MvPolynomial.eval (fun i ↦ rapidCoordinate i n) Q := by
    simpa [MvPolynomial.aeval_def, MvPolynomial.eval_eq,
      MvPolynomial.eval₂_eq] using congrFun hPQ n
  rw [MvPolynomial.eval_sub, hpoint, sub_self]

/-- The family `n ↦ n^(n^i)` is algebraically independent over the integers
as a family of functions on positive natural inputs. -/
theorem rapidCoordinate_algebraicIndependent :
    AlgebraicIndependent Int rapidCoordinate :=
  algebraicIndependent_iff_injective_aeval.mpr rapid_aeval_injective

/-! ## The rapid family inside the canonical Wilkie enumeration -/

/-- The common integer assignment to global Wilkie variables. -/
def integerGlobalAssignment {D : Wilkie.PolynomialDerivability}
    (S : Wilkie.GeneratorSequence D) (n : PosNat) :
    Wilkie.GlobalVar → Int
  | .original => n.1
  | .auxiliary j => S.integerTau j n

/-- Embedding a finite-stage polynomial into global variables preserves its
integer evaluation at the recursive coordinate assignment. -/
theorem evalInt_toGlobal {D : Wilkie.PolynomialDerivability}
    (S : Wilkie.GeneratorSequence D) (n : PosNat) {k : Nat}
    (P : Wilkie.StagePolynomial k) :
    MvPolynomial.eval (integerGlobalAssignment S n) P.toGlobal =
      P.evalInt (S.integerAssignment k n) := by
  rw [Wilkie.StagePolynomial.toGlobal, MvPolynomial.eval_rename]
  apply congrArg (fun assignment : Wilkie.StageVar k → Int ↦
    MvPolynomial.eval assignment P)
  funext i
  cases i using Fin.cases <;> rfl

/-- Equal global presentations, even from different finite stages, have the
same recursive integer evaluation. -/
theorem evalInt_eq_of_toGlobal_eq {D : Wilkie.PolynomialDerivability}
    (S : Wilkie.GeneratorSequence D) (n : PosNat) {k l : Nat}
    {P : Wilkie.StagePolynomial k} {Q : Wilkie.StagePolynomial l}
    (h : P.toGlobal = Q.toGlobal) :
    P.evalInt (S.integerAssignment k n) =
      Q.evalInt (S.integerAssignment l n) := by
  rw [← evalInt_toGlobal S n P, ← evalInt_toGlobal S n Q, h]

/-- Coordinate zero is followed, at the canonical free indices, by the
stage-zero filler coordinates. -/
def canonicalRapidIndex : Nat → Nat
  | 0 => 0
  | m + 1 => (Wilkie.freeIndexEquivNat.symm m).1 + 1

/-- The auxiliary coordinate assigned to filler code `m` is exactly
`n^(n^(m+1))`. -/
theorem canonical_filler_integerTau (m : Nat) (n : PosNat) :
    Wilkie.canonicalGeneratorSequence.integerTau
        (Wilkie.freeIndexEquivNat.symm m).1 n =
      rapidCoordinate (m + 1) n := by
  let k := (Wilkie.freeIndexEquivNat.symm m).1
  have htarget := Wilkie.enumeratedEntry_target_filler m
  have hbaseGlobal :
      (Wilkie.canonicalGeneratorSequence.pair k).base.toGlobal =
        (Wilkie.Base.original : Wilkie.Base 0).toGlobal := by
    change (Wilkie.enumeratedEntry k).base.toGlobal = _
    simpa [Wilkie.GeneratorEntry.target, Wilkie.fillerTarget] using
      congrArg (fun target : Wilkie.GeneratorTarget ↦ target.1.1) htarget
  have hexponentGlobal :
      (Wilkie.canonicalGeneratorSequence.pair k).exponent.toGlobal =
        (Wilkie.fillerExponent m).toGlobal := by
    change (Wilkie.enumeratedEntry k).exponent.toGlobal = _
    simpa [Wilkie.GeneratorEntry.target, Wilkie.fillerTarget] using
      congrArg (fun target : Wilkie.GeneratorTarget ↦ target.2.1) htarget
  have hbaseEval := evalInt_eq_of_toGlobal_eq
    Wilkie.canonicalGeneratorSequence n hbaseGlobal
  have hexponentEval := evalInt_eq_of_toGlobal_eq
    Wilkie.canonicalGeneratorSequence n hexponentGlobal
  have hbase :
      Wilkie.canonicalGeneratorSequence.integerBase k n = (n.1 : Int) := by
    simpa [Wilkie.GeneratorSequence.integerBase,
      Wilkie.StagePolynomial.evalInt, Wilkie.Base.polynomial,
      Wilkie.GeneratorSequence.integerAssignment] using hbaseEval
  have hfillerEval :
      (Wilkie.fillerExponent m).polynomial.evalInt
          (Wilkie.canonicalGeneratorSequence.integerAssignment 0 n) =
        (n.1 : Int) ^ (m + 1) := by
    rw [Wilkie.NonconstantMonomial.polynomial,
      Wilkie.StagePolynomial.evalInt, MvPolynomial.eval_monomial]
    change 1 * (Finsupp.single (0 : Wilkie.StageVar 0) (m + 1)).prod
      (fun i e ↦
        Wilkie.canonicalGeneratorSequence.integerAssignment 0 n i ^ e) = _
    rw [one_mul, Finsupp.prod_single_index (by simp)]
    rfl
  have hexponent :
      Wilkie.canonicalGeneratorSequence.integerExponent k n =
        (n.1 : Int) ^ (m + 1) := by
    change
      (Wilkie.canonicalGeneratorSequence.pair k).exponent.polynomial.evalInt
          (Wilkie.canonicalGeneratorSequence.integerAssignment
            (Wilkie.canonicalGeneratorSequence.pair k).exponentStage n) = _
    exact hexponentEval.trans hfillerEval
  have htoNat : ((n.1 : Int) ^ (m + 1)).toNat = n.1 ^ (m + 1) := by
    rw [← Int.natCast_pow, Int.toNat_natCast]
  rw [Wilkie.GeneratorSequence.integerTau_eq, hbase, hexponent]
  change (n.1 : Int) ^ ((n.1 : Int) ^ (m + 1)).toNat =
    (n.1 : Int) ^ (n.1 ^ (m + 1))
  rw [htoNat]

/-- The canonical integer coordinate family contains the entire rapid family
as the explicitly reindexed subfamily `canonicalRapidIndex`. -/
theorem canonicalIntegerCoordinates_canonicalRapidIndex
    (i : Nat) (n : PosNat) :
    Wilkie.canonicalGeneratorSequence.integerCoordinates
        (canonicalRapidIndex i) n = rapidCoordinate i n := by
  cases i with
  | zero =>
      simp [canonicalRapidIndex, rapidCoordinate]
  | succ m =>
      simpa [canonicalRapidIndex] using canonical_filler_integerTau m n

/-- Hence the explicitly selected subfamily of the canonical integer
coordinates is algebraically independent, without any real-function bridge. -/
theorem canonicalRapidSubfamily_algebraicIndependent :
    AlgebraicIndependent Int
      (fun i ↦ Wilkie.canonicalGeneratorSequence.integerCoordinates
        (canonicalRapidIndex i)) := by
  have hfamily :
      (fun i ↦ Wilkie.canonicalGeneratorSequence.integerCoordinates
        (canonicalRapidIndex i)) = rapidCoordinate := by
    funext i n
    exact canonicalIntegerCoordinates_canonicalRapidIndex i n
  rw [hfamily]
  exact rapidCoordinate_algebraicIndependent

/-- Consequently, formal polynomials using only the original coordinate and
the stage-zero filler coordinates are separated directly on positive
integers.  This is the precise fragment of the canonical family covered by
the strategic-prime argument. -/
theorem canonicalRapidRename_aeval_injective :
    Function.Injective
      (fun P : MvPolynomial Nat Int ↦
        MvPolynomial.aeval
          Wilkie.canonicalGeneratorSequence.integerCoordinates
          (MvPolynomial.rename canonicalRapidIndex P)) := by
  intro P Q hPQ
  apply AlgebraicIndependence.aeval_injective
    (fun i ↦ Wilkie.canonicalGeneratorSequence.integerCoordinates
      (canonicalRapidIndex i))
    canonicalRapidSubfamily_algebraicIndependent
  change MvPolynomial.aeval
      Wilkie.canonicalGeneratorSequence.integerCoordinates
      (MvPolynomial.rename canonicalRapidIndex P) =
    MvPolynomial.aeval
      Wilkie.canonicalGeneratorSequence.integerCoordinates
      (MvPolynomial.rename canonicalRapidIndex Q) at hPQ
  rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename] at hPQ
  change MvPolynomial.aeval
      (fun i ↦ Wilkie.canonicalGeneratorSequence.integerCoordinates
        (canonicalRapidIndex i)) P =
    MvPolynomial.aeval
      (fun i ↦ Wilkie.canonicalGeneratorSequence.integerCoordinates
        (canonicalRapidIndex i)) Q at hPQ
  exact hPQ

/-- Natural-coefficient form of `canonicalRapidRename_aeval_injective`, in
the exact evaluation type used by fixed-family precertificates. -/
theorem canonicalRapidRename_natAeval_injective :
    Function.Injective
      (fun P : MvPolynomial Nat Nat ↦
        AlgebraicIndependence.natAeval (K := Int)
          Wilkie.canonicalGeneratorSequence.integerCoordinates
          (MvPolynomial.rename canonicalRapidIndex P)) := by
  intro P Q hPQ
  apply MvPolynomial.map_injective (f := Nat.castRingHom Int)
    Nat.cast_injective
  apply canonicalRapidRename_aeval_injective
  change AlgebraicIndependence.natAeval (K := Int)
      Wilkie.canonicalGeneratorSequence.integerCoordinates
      (MvPolynomial.rename canonicalRapidIndex P) =
    AlgebraicIndependence.natAeval (K := Int)
      Wilkie.canonicalGeneratorSequence.integerCoordinates
      (MvPolynomial.rename canonicalRapidIndex Q) at hPQ
  change MvPolynomial.aeval
      Wilkie.canonicalGeneratorSequence.integerCoordinates
      (MvPolynomial.map (Nat.castRingHom Int)
        (MvPolynomial.rename canonicalRapidIndex P)) =
    MvPolynomial.aeval
      Wilkie.canonicalGeneratorSequence.integerCoordinates
      (MvPolynomial.map (Nat.castRingHom Int)
        (MvPolynomial.rename canonicalRapidIndex Q)) at hPQ
  rw [MvPolynomial.map_rename, MvPolynomial.map_rename] at hPQ
  exact hPQ

end

end DirectIntegerRapidSeparation

end Natfunbasis
