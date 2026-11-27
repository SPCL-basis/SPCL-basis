import Natfunbasis.WilkieFreshBaseExclusion
import Natfunbasis.WilkieGeneratorFieldRelations
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Constant W1 bases and logarithms of primes

The admissibility conditions on a Wilkie W1 base allow a constant base, but
only when that constant is prime in `Int`.  The positivity convention on W1
bases removes the negative associate.  Thus every constant W1 base is
literally the constant polynomial attached to a unique natural prime.

The second part records the elementary unique-factorization consequence used
when constant-base logarithms occur in a primitive relation: logarithms of a
finite injective family of natural primes are linearly independent over the
integers.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- A constant W1 base is literally a positive natural prime constant.  The
prime is unique, not merely determined up to the two units of `Int`. -/
theorem exists_unique_prime_of_isConstantBase {k : Nat}
    (hconstant : S.IsConstantBase k) :
    ∃! p : Nat, p.Prime ∧ S.baseGlobal k = C (p : Int) := by
  obtain ⟨c, hc⟩ := hconstant
  have hCprime : Prime (C c : GlobalPolynomial) := by
    rw [← hc]
    exact S.baseGlobal_prime k
  have hcprime : Prime c :=
    comap_prime MvPolynomial.C MvPolynomial.constantCoeff
      (MvPolynomial.constantCoeff_C _) hCprime
  have hcposReal : 0 < (c : Real) := by
    have hpos := S.baseGlobal_eval_pos k (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
    rw [hc, MvPolynomial.eval₂_C] at hpos
    exact hpos
  have hcpos : 0 < c := by exact_mod_cast hcposReal
  let p := c.natAbs
  have hp : p.Prime := Int.prime_iff_natAbs_prime.mp hcprime
  have hcp : c = (p : Int) := by
    simpa [p] using (Int.natAbs_of_nonneg hcpos.le).symm
  refine ⟨p, ⟨hp, hc.trans (by rw [hcp])⟩, ?_⟩
  intro q hq
  have hC : C (p : Int) = (C (q : Int) : GlobalPolynomial) :=
    (hc.trans (by rw [hcp])).symm.trans hq.2
  have hInt : (p : Int) = (q : Int) :=
    MvPolynomial.C_injective GlobalVar Int hC
  exact_mod_cast hInt.symm

/-- The natural prime represented by a constant W1 base. -/
def constantBasePrime {k : Nat} (hconstant : S.IsConstantBase k) : Nat :=
  (S.exists_unique_prime_of_isConstantBase hconstant).choose

theorem constantBasePrime_prime {k : Nat} (hconstant : S.IsConstantBase k) :
    (S.constantBasePrime hconstant).Prime :=
  (S.exists_unique_prime_of_isConstantBase hconstant).choose_spec.1.1

theorem baseGlobal_eq_C_constantBasePrime {k : Nat}
    (hconstant : S.IsConstantBase k) :
    S.baseGlobal k = C (S.constantBasePrime hconstant : Int) :=
  (S.exists_unique_prime_of_isConstantBase hconstant).choose_spec.1.2

/-- The chosen analytic logarithm of a constant base is exactly the real
logarithm of its positive natural prime. -/
theorem logBaseAnalytic_eq_constantBasePrime {k : Nat}
    (hconstant : S.IsConstantBase k) :
    S.logBaseAnalytic k =
      algebraMap Real PositiveAnalyticFunction
        (Real.log (S.constantBasePrime hconstant : Real)) := by
  apply Subtype.ext
  funext y
  rw [S.logBaseAnalytic_apply,
    S.baseAnalytic_eq_const (S.baseGlobal_eq_C_constantBasePrime hconstant)]
  rfl

end GeneratorSequence

/-! ## Integer independence of logarithms of distinct natural primes -/

section PrimeLogs

variable {I : Type*} [Fintype I]

private theorem log_natPrimePower_product (p : I → Nat)
    (hp : ∀ i, (p i).Prime) (a : I → Nat) :
    Real.log ((∏ i, p i ^ a i : Nat) : Real) =
      ∑ i, (a i : Real) * Real.log (p i : Real) := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_pow, Real.log_pow]
  · intro i _
    norm_cast
    exact pow_ne_zero _ (hp i).ne_zero

/-- Natural exponents of pairwise distinct primes are determined by the
corresponding real logarithmic sum. -/
theorem nat_prime_log_combination_injective
    (p : I → Nat) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {a b : I → Nat}
    (hlog : (∑ i, (a i : Real) * Real.log (p i : Real)) =
      ∑ i, (b i : Real) * Real.log (p i : Real)) :
    a = b := by
  classical
  let A : Nat := ∏ i, p i ^ a i
  let B : Nat := ∏ i, p i ^ b i
  have hApos : 0 < A := by
    dsimp [A]
    exact Finset.prod_pos fun i _ ↦ pow_pos (hp i).pos _
  have hBpos : 0 < B := by
    dsimp [B]
    exact Finset.prod_pos fun i _ ↦ pow_pos (hp i).pos _
  have hlogAB : Real.log (A : Real) = Real.log (B : Real) := by
    rw [log_natPrimePower_product p hp a,
      log_natPrimePower_product p hp b]
    exact hlog
  have hcast : (A : Real) = (B : Real) := by
    have hAposReal : 0 < (A : Real) := by exact_mod_cast hApos
    have hBposReal : 0 < (B : Real) := by exact_mod_cast hBpos
    have hexp := congrArg Real.exp hlogAB
    rw [Real.exp_log hAposReal, Real.exp_log hBposReal] at hexp
    exact hexp
  have hAB : A = B := by exact_mod_cast hcast
  funext i
  have hfactor := congrArg (fun n : Nat ↦ n.factorization (p i)) hAB
  dsimp [A, B] at hfactor
  rw [Nat.factorization_prod_apply, Nat.factorization_prod_apply] at hfactor
  · simpa [Nat.factorization_pow, (hp _).factorization,
      Finsupp.single_apply, hinj.eq_iff] using hfactor
  · intro j _
    exact pow_ne_zero _ (hp j).ne_zero
  · intro j _
    exact pow_ne_zero _ (hp j).ne_zero

/-- A finite injective family of natural-prime logarithms is linearly
independent over `Int`, stated in the coefficient form needed downstream. -/
theorem int_prime_log_combination_eq_zero
    (p : I → Nat) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (z : I → Int)
    (hlog : ∑ i, (z i : Real) * Real.log (p i : Real) = 0) :
    ∀ i, z i = 0 := by
  classical
  let a : I → Nat := fun i ↦ (z i).toNat
  let b : I → Nat := fun i ↦ (-z i).toNat
  have hsplit (i : I) :
      (z i : Real) = (a i : Real) - (b i : Real) := by
    exact_mod_cast (z i).toNat_sub_toNat_neg.symm
  have habLog :
      (∑ i, (a i : Real) * Real.log (p i : Real)) =
        ∑ i, (b i : Real) * Real.log (p i : Real) := by
    rw [← sub_eq_zero]
    rw [← Finset.sum_sub_distrib]
    convert hlog using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hsplit]
    ring
  have hab : a = b :=
    nat_prime_log_combination_injective p hp hinj habLog
  intro i
  rw [← (z i).toNat_sub_toNat_neg, show (z i).toNat = (-z i).toNat by
    exact congrFun hab i]
  simp

end PrimeLogs

namespace GeneratorSequence

variable {D : PolynomialDerivability} (S : GeneratorSequence D)

/-- For constant W1 bases, equality of the associated natural primes is
equivalent to literal equality of the global base polynomials. -/
theorem constantBasePrime_eq_iff_baseGlobal_eq {i j : Nat}
    (hi : S.IsConstantBase i) (hj : S.IsConstantBase j) :
    S.constantBasePrime hi = S.constantBasePrime hj ↔
      S.baseGlobal i = S.baseGlobal j := by
  constructor
  · intro hp
    rw [S.baseGlobal_eq_C_constantBasePrime hi,
      S.baseGlobal_eq_C_constantBasePrime hj, hp]
  · intro hbase
    have hC :
        C (S.constantBasePrime hi : Int) =
          (C (S.constantBasePrime hj : Int) : GlobalPolynomial) := by
      rw [← S.baseGlobal_eq_C_constantBasePrime hi,
        ← S.baseGlobal_eq_C_constantBasePrime hj]
      exact hbase
    have hInt :
        (S.constantBasePrime hi : Int) =
          (S.constantBasePrime hj : Int) :=
      MvPolynomial.C_injective GlobalVar Int hC
    exact_mod_cast hInt

/-- W1-indexed form of integer independence of logarithms of distinct
constant bases.  Distinctness is required only for their literal global
polynomial presentations; the classification theorem turns it into
distinctness of the represented natural primes. -/
theorem int_constantBase_log_combination_eq_zero
    {I : Type*} [Fintype I] (k : I → Nat)
    (hconstant : ∀ i, S.IsConstantBase (k i))
    (hdistinct : Function.Injective (fun i ↦ S.baseGlobal (k i)))
    (z : I → Int)
    (hlog : ∑ i, (z i : Real) *
      Real.log (S.constantBasePrime (hconstant i) : Real) = 0) :
    ∀ i, z i = 0 := by
  apply int_prime_log_combination_eq_zero
    (fun i ↦ S.constantBasePrime (hconstant i))
    (fun i ↦ S.constantBasePrime_prime (hconstant i))
  · intro i j hij
    apply hdistinct
    exact (S.constantBasePrime_eq_iff_baseGlobal_eq
      (hconstant i) (hconstant j)).mp hij
  · exact hlog

end GeneratorSequence

end

end Natfunbasis.Wilkie
