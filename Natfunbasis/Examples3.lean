import Natfunbasis.MainTheorems

/-!
# Wilkie's identity at `y = 1`

Take Wilkie's polynomials `A = n+1`, `B = n^2+n+1`, `C = n^3+1`, `D = n^4+n^2+1` and
put `x = n`, `y = 1` in his identity:

  `(A^n + B^n)·(C+D)^n = (A+B)^n·(C^n + D^n)`.                                (*)

All of `A, B, C, D, A+B, C+D` are `≠ 1`, so every `n`-th power below is a tower, and
distributing gives two expansions into elements of `𝓑`:

  `LHS = a1 + a2`, `a1 = A^n (C+D)^n`, `a2 = B^n (C+D)^n`,
  `RHS = a3 + a4`, `a3 = (A+B)^n C^n`, `a4 = (A+B)^n D^n`.

By uniqueness of the decomposition into atoms, `{a1, a2} = {a3, a4}`; since
`a1(1) = 10 ≠ 15 = a4(1)`, this forces `a1 = a3` and `a2 = a4`.  Taking `n`-th roots
pointwise gives `A(C+D) = (A+B)C` and `B(C+D) = (A+B)D`, and these amount to the
positive-coefficient identity `AD = BC = n^5+n^4+n^3+n^2+n+1`.

The atom `a1 = a3` has two factorizations into two towers whose four bases are
pairwise distinct and irreducible in `ℕ[n]`; the common refinement exists only
over `ℤ`, through Wilkie's factor `Q = n^2-n+1`: `C = A·Q`, `C+D = (A+B)·Q`,
`D = B·Q` (checked pointwise over `ℤ` below).
-/

namespace Natfunbasis.Examples3

open NaturalFunction

/-- The variable `n`. -/
abbrev N : NaturalFunction := input

/-- Wilkie's `A = n+1`. -/
def A : NaturalFunction := N + 1
/-- Wilkie's `B = n^2+n+1`. -/
def B : NaturalFunction := N * N + N + 1
/-- Wilkie's `C = n^3+1`. -/
def C : NaturalFunction := N * N * N + 1
/-- Wilkie's `D = n^4+n^2+1`. -/
def D : NaturalFunction := N * N * N * N + N * N + 1

/-- The four atoms. -/
def a1 : NaturalFunction := A ^ N * (C + D) ^ N
def a2 : NaturalFunction := B ^ N * (C + D) ^ N
def a3 : NaturalFunction := (A + B) ^ N * C ^ N
def a4 : NaturalFunction := (A + B) ^ N * D ^ N

/-- The left-hand side `(A^n + B^n)(C+D)^n` of Wilkie's identity at `y = 1`. -/
def lhs : NaturalFunction := (A ^ N + B ^ N) * (C + D) ^ N
/-- The right-hand side `(A+B)^n (C^n + D^n)` of Wilkie's identity at `y = 1`. -/
def rhs : NaturalFunction := (A + B) ^ N * (C ^ N + D ^ N)

/-- **Wilkie's identity at `y = 1`**: `(A^n + B^n)(C+D)^n = (A+B)^n (C^n + D^n)`. -/
theorem wilkie_y1 : lhs = rhs := by
  ext m
  simp only [lhs, rhs, A, B, C, D, pow_apply, mul_apply, add_apply, one_apply, input_apply]
  rw [add_mul, mul_add, ← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
  congr 2 <;> ring

/-! ### The bases are `≠ 1` -/

theorem ne_one_of_apply_one (F : NaturalFunction) (k : ℕ) (hk : F ⟨1, by norm_num⟩ = k)
    (hk2 : k ≠ 1) : F ≠ 1 := by
  intro H
  rw [H] at hk
  simp at hk
  omega

theorem A_ne_one : A ≠ 1 := ne_one_of_apply_one A 2 (by rfl) (by norm_num)
theorem B_ne_one : B ≠ 1 := ne_one_of_apply_one B 3 (by rfl) (by norm_num)
theorem C_ne_one : C ≠ 1 := ne_one_of_apply_one C 2 (by rfl) (by norm_num)
theorem D_ne_one : D ≠ 1 := ne_one_of_apply_one D 3 (by rfl) (by norm_num)
theorem A_add_B_ne_one : A + B ≠ 1 := ne_one_of_apply_one (A + B) 5 (by rfl) (by norm_num)
theorem C_add_D_ne_one : C + D ≠ 1 := ne_one_of_apply_one (C + D) 5 (by rfl) (by norm_num)

/-! ### The four atoms are products of two towers -/

theorem isBasis_pow_N {U : NaturalFunction} (hU : U ≠ 1) : IsBasis (U ^ N) :=
  IsBasis.of_tower (IsTower.pow hU IsTower.input)

theorem isBasis_a1 : IsBasis a1 := (isBasis_pow_N A_ne_one).mul (isBasis_pow_N C_add_D_ne_one)
theorem isBasis_a2 : IsBasis a2 := (isBasis_pow_N B_ne_one).mul (isBasis_pow_N C_add_D_ne_one)
theorem isBasis_a3 : IsBasis a3 := (isBasis_pow_N A_add_B_ne_one).mul (isBasis_pow_N C_ne_one)
theorem isBasis_a4 : IsBasis a4 := (isBasis_pow_N A_add_B_ne_one).mul (isBasis_pow_N D_ne_one)

/-- Each `aᵢ` is `+`-atomic (Theorem A(1)). -/
theorem a1_addAtomic : a1.AddAtomic := (Main.addAtomic_iff_isBasis _).2 isBasis_a1
theorem a2_addAtomic : a2.AddAtomic := (Main.addAtomic_iff_isBasis _).2 isBasis_a2
theorem a3_addAtomic : a3.AddAtomic := (Main.addAtomic_iff_isBasis _).2 isBasis_a3
theorem a4_addAtomic : a4.AddAtomic := (Main.addAtomic_iff_isBasis _).2 isBasis_a4

/-! ### The two expansions -/

/-- The expansion `a1 + a2` of the left-hand side. -/
def sL : BasisSum := .cons a1 (.single a2)
/-- The expansion `a3 + a4` of the right-hand side. -/
def sR : BasisSum := .cons a3 (.single a4)

theorem sL_valid : sL.Valid := by
  simp only [sL, BasisSum.valid_cons_iff, BasisSum.valid_single_iff]
  exact ⟨isBasis_a1, isBasis_a2⟩

theorem sR_valid : sR.Valid := by
  simp only [sR, BasisSum.valid_cons_iff, BasisSum.valid_single_iff]
  exact ⟨isBasis_a3, isBasis_a4⟩

theorem sL_value : sL.value = lhs := by
  ext m
  simp only [sL, lhs, a1, a2, BasisSum.value_cons, BasisSum.value_single, add_apply,
    mul_apply, pow_apply]
  ring

theorem sR_value : sR.value = rhs := by
  ext m
  simp only [sR, rhs, a3, a4, BasisSum.value_cons, BasisSum.value_single, add_apply,
    mul_apply, pow_apply]
  ring

/-- `lhs = a1 + a2` and `rhs = a3 + a4`. -/
theorem lhs_eq : lhs = a1 + a2 := by rw [← sL_value]; rfl
theorem rhs_eq : rhs = a3 + a4 := by rw [← sR_value]; rfl

/-- **Uniqueness**: every `𝓑`-expansion of `rhs` (equivalently of `lhs`) is a
permutation of `a3, a4`. -/
theorem decomposition_unique (t : BasisSum) (ht : t.Valid) (htf : t.value = rhs) :
    t.terms.Perm sR.terms := by
  obtain ⟨s, _, _, hs⟩ := Main.exists_basisSum_unique rhs
  exact (hs t ht htf).symm.trans (hs sR sR_valid sR_value)

/-- By Theorem A(2), the two expansions are permutations of each other. -/
theorem sL_perm_sR : sL.terms.Perm sR.terms :=
  decomposition_unique sL sL_valid (sL_value.trans wilkie_y1)

/-- Neither side of `(*)` is `+`-atomic. -/
theorem rhs_not_addAtomic : ¬ rhs.AddAtomic := fun h ↦ h ⟨a3, a4, rhs_eq⟩
theorem lhs_not_addAtomic : ¬ lhs.AddAtomic := fun h ↦ h ⟨a1, a2, lhs_eq⟩

/-! ### Matching the atoms -/

theorem a1_apply_one : a1 ⟨1, by norm_num⟩ = 10 := by rfl
theorem a2_apply_one : a2 ⟨1, by norm_num⟩ = 15 := by rfl
theorem a3_apply_one : a3 ⟨1, by norm_num⟩ = 10 := by rfl
theorem a4_apply_one : a4 ⟨1, by norm_num⟩ = 15 := by rfl

/-- `a1 = a3`, derived from uniqueness of the decomposition into atoms alone. -/
theorem a1_eq_a3 : a1 = a3 := by
  have hmem : a1 ∈ sR.terms := sL_perm_sR.subset (by simp [sL, BasisSum.terms_cons])
  simp only [sR, BasisSum.terms_cons, BasisSum.terms_single, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · exact h
  · have := congrArg (fun F : NaturalFunction ↦ F ⟨1, by norm_num⟩) h
    simp only [a1_apply_one, a4_apply_one] at this
    omega

/-- `a2 = a4`, derived from uniqueness of the decomposition into atoms alone. -/
theorem a2_eq_a4 : a2 = a4 := by
  have hmem : a2 ∈ sR.terms := sL_perm_sR.subset (by simp [sL, BasisSum.terms_cons])
  simp only [sR, BasisSum.terms_cons, BasisSum.terms_single, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · have := congrArg (fun F : NaturalFunction ↦ F ⟨1, by norm_num⟩) h
    simp only [a2_apply_one, a3_apply_one] at this
    omega
  · exact h

/-- Cross-check: `a1 = a3` directly, by `A(C+D) = (A+B)C`. -/
theorem a1_eq_a3_direct : a1 = a3 := by
  ext m
  simp only [a1, a3, A, B, C, D, pow_apply, mul_apply, add_apply, one_apply, input_apply]
  rw [← mul_pow, ← mul_pow]
  congr 1
  ring

/-! ### Taking `n`-th roots -/

theorem eq_of_pow_input_eq {F G : NaturalFunction} (h : F ^ N = G ^ N) : F = G := by
  ext m
  have := congrArg (fun H : NaturalFunction ↦ H m) h
  simp only [pow_apply, input_apply] at this
  exact Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp m.2) this

/-- From `a1 = a3`: `A(C+D) = (A+B)C`. -/
theorem root1 : A * (C + D) = (A + B) * C := by
  apply eq_of_pow_input_eq
  have h := a1_eq_a3
  ext m
  have := congrArg (fun H : NaturalFunction ↦ H m) h
  simp only [a1, a3, pow_apply, mul_apply] at this ⊢
  rw [mul_pow, mul_pow]
  exact this

/-- From `a2 = a4`: `B(C+D) = (A+B)D`. -/
theorem root2 : B * (C + D) = (A + B) * D := by
  apply eq_of_pow_input_eq
  have h := a2_eq_a4
  ext m
  have := congrArg (fun H : NaturalFunction ↦ H m) h
  simp only [a2, a4, pow_apply, mul_apply] at this ⊢
  rw [mul_pow, mul_pow]
  exact this

/-- Both reduce to the positive-coefficient identity `AD = BC`. -/
theorem A_mul_D_eq_B_mul_C : A * D = B * C := by
  ext m
  simp only [A, B, C, D, mul_apply, add_apply, one_apply, input_apply]
  ring

/-- `AD = n^5+n^4+n^3+n^2+n+1`. -/
theorem A_mul_D_apply (m : PosNat) :
    (A * D) m = m.1 ^ 5 + m.1 ^ 4 + m.1 ^ 3 + m.1 ^ 2 + m.1 + 1 := by
  simp only [A, D, mul_apply, add_apply, one_apply, input_apply]
  ring

/-- `A(C+D) = (A+B)C = n^5+2n^4+2n^3+n^2+2n+2`. -/
theorem root1_apply (m : PosNat) :
    (A * (C + D)) m = m.1 ^ 5 + 2 * m.1 ^ 4 + 2 * m.1 ^ 3 + m.1 ^ 2 + 2 * m.1 + 2 := by
  simp only [A, C, D, mul_apply, add_apply, one_apply, input_apply]
  ring

/-- `B(C+D) = (A+B)D = n^6+2n^5+3n^4+2n^3+3n^2+2n+2`. -/
theorem root2_apply (m : PosNat) :
    (B * (C + D)) m =
      m.1 ^ 6 + 2 * m.1 ^ 5 + 3 * m.1 ^ 4 + 2 * m.1 ^ 3 + 3 * m.1 ^ 2 + 2 * m.1 + 2 := by
  simp only [B, C, D, mul_apply, add_apply, one_apply, input_apply]
  ring

/-! ### The common refinement over `ℤ`, through `Q = n^2 - n + 1` -/

/-- `C = A·Q`, `C + D = (A+B)·Q`, `D = B·Q` over `ℤ`, with `Q = n^2-n+1`. -/
theorem factor_over_int (m : PosNat) :
    ((C m : ℕ) : ℤ) = ((A m : ℕ) : ℤ) * ((m.1 : ℤ) ^ 2 - m.1 + 1) ∧
    (((C + D) m : ℕ) : ℤ) = (((A + B) m : ℕ) : ℤ) * ((m.1 : ℤ) ^ 2 - m.1 + 1) ∧
    ((D m : ℕ) : ℤ) = ((B m : ℕ) : ℤ) * ((m.1 : ℤ) ^ 2 - m.1 + 1) := by
  simp only [A, B, C, D, mul_apply, add_apply, one_apply, input_apply]
  push_cast
  refine ⟨by ring, by ring, by ring⟩

/-- `a1 = a3 = (A·Q·(A+B))^n` and `a2 = a4 = (B·Q·(A+B))^n` over `ℤ`. -/
theorem atoms_over_int (m : PosNat) :
    ((a1 m : ℕ) : ℤ) = (((A m : ℕ) : ℤ) * ((m.1 : ℤ) ^ 2 - m.1 + 1) *
      (((A + B) m : ℕ) : ℤ)) ^ m.1 ∧
    ((a2 m : ℕ) : ℤ) = (((B m : ℕ) : ℤ) * ((m.1 : ℤ) ^ 2 - m.1 + 1) *
      (((A + B) m : ℕ) : ℤ)) ^ m.1 := by
  obtain ⟨-, hCD, -⟩ := factor_over_int m
  simp only [a1, a2, mul_apply, pow_apply, input_apply]
  push_cast
  rw [← mul_pow, ← mul_pow]
  rw [hCD]
  constructor <;> ring

end Natfunbasis.Examples3
