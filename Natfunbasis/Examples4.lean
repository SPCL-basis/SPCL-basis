import Natfunbasis.MainTheorems

/-!
# Merging multiplicities: the decomposition of `(1 + 2^n + 4^n)^(n+2)`

Let `X = 2^n = (1+1)^n` and `Y = 4^n = (1+1+1+1)^n` (towers with constant bases),
`h = 1 + X + Y`, `T = h^n` (a tower, since `h ≠ 1`) and `f = h^(n+2)`, the
exponent written `n + 1 + 1`.  Then `f = T·h·h`, and distributing gives nine
products `T·u·v` with `u, v ∈ {1, X, Y}`.  In independent letters these would be
six distinct products with multiplicities `1, 2, 2, 1, 2, 1`.  But `X·X = Y` as
functions, so `T·X·X` and `T·Y` are the same atom, and the decomposition of `f` is

  `f = T + TX + TX + TY + TY + TY + TXY + TXY + TYY`:

nine atoms, five of them distinct (values `7, 14, 28, 56, 112` at `n = 1`), with
multiplicities `1, 2, 3, 2, 1`, the coefficients of `(1 + t + t²)²`.
By the additive basis theorem this decomposition is unique up to order.
-/

namespace Natfunbasis.Examples4

open NaturalFunction

/-- The variable `n`. -/
abbrev N : NaturalFunction := input

/-- `X = 2^n`, written `(1+1)^n`. -/
def X : NaturalFunction := (1 + 1) ^ N

/-- `Y = 4^n`, written `(1+1+1+1)^n`. -/
def Y : NaturalFunction := (1 + 1 + 1 + 1) ^ N

/-- `h = 1 + 2^n + 4^n`. -/
def h : NaturalFunction := 1 + X + Y

/-- The tower `T = h^n`. -/
def T : NaturalFunction := h ^ N

/-- `f = h^(n+2)`, the exponent written `n + 1 + 1`. -/
def f : NaturalFunction := h ^ (N + 1 + 1)

/-- The one point `1 ∈ ℤ_{>0}`. -/
def one' : PosNat := ⟨1, by norm_num⟩

/-! ### Towers and nontriviality -/

theorem two_ne_one : (1 + 1 : NaturalFunction) ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨2, by norm_num⟩) H
  change (2 : ℕ) = 1 at this
  omega

theorem four_ne_one : (1 + 1 + 1 + 1 : NaturalFunction) ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨4, by norm_num⟩) H
  change (4 : ℕ) = 1 at this
  omega

theorem h_ne_one : h ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F one') H
  change (7 : ℕ) = 1 at this
  omega

theorem isTower_X : IsTower X := IsTower.pow two_ne_one IsTower.input

theorem isTower_Y : IsTower Y := IsTower.pow four_ne_one IsTower.input

theorem isTower_T : IsTower T := IsTower.pow h_ne_one IsTower.input

theorem isBasis_T : IsBasis T := IsBasis.of_tower isTower_T

theorem isBasis_TX : IsBasis (T * X) := isBasis_T.mul (IsBasis.of_tower isTower_X)

theorem isBasis_TY : IsBasis (T * Y) := isBasis_T.mul (IsBasis.of_tower isTower_Y)

theorem isBasis_TXY : IsBasis (T * X * Y) := isBasis_TX.mul (IsBasis.of_tower isTower_Y)

theorem isBasis_TYY : IsBasis (T * Y * Y) := isBasis_TY.mul (IsBasis.of_tower isTower_Y)

/-! ### The merge `X·X = Y` -/

/-- `2^n · 2^n = 4^n` as natural functions. -/
theorem X_mul_X : X * X = Y := by
  ext m
  simp only [X, Y, NaturalFunction.mul_apply, NaturalFunction.pow_apply,
    NaturalFunction.add_apply, NaturalFunction.one_apply, NaturalFunction.input_apply]
  rw [← mul_pow]; norm_num

/-- Hence the two products `T·X·X` and `T·Y`, listed separately by distribution,
are one and the same atom. -/
theorem merge : T * X * X = T * Y := by
  rw [mul_assoc, X_mul_X]

/-- `2^n · 4^n = 8^n`. -/
theorem X_mul_Y : X * Y = (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) ^ N := by
  ext m
  simp only [X, Y, NaturalFunction.mul_apply, NaturalFunction.pow_apply,
    NaturalFunction.add_apply, NaturalFunction.one_apply, NaturalFunction.input_apply]
  rw [← mul_pow]; norm_num

/-- `4^n · 4^n = 16^n`. -/
theorem Y_mul_Y :
    Y * Y = (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) ^ N := by
  ext m
  simp only [Y, NaturalFunction.mul_apply, NaturalFunction.pow_apply,
    NaturalFunction.add_apply, NaturalFunction.one_apply, NaturalFunction.input_apply]
  rw [← mul_pow]; norm_num

/-! ### The decomposition -/

/-- The decomposition `T + TX + TX + TY + TY + TY + TXY + TXY + TYY`. -/
def decomposition : BasisSum :=
  .cons T (.cons (T * X) (.cons (T * X) (.cons (T * Y) (.cons (T * Y)
    (.cons (T * Y) (.cons (T * X * Y) (.cons (T * X * Y) (.single (T * Y * Y)))))))))

theorem decomposition_valid : decomposition.Valid := by
  simp only [decomposition, BasisSum.valid_cons_iff, BasisSum.valid_single_iff]
  exact ⟨isBasis_T, isBasis_TX, isBasis_TX, isBasis_TY, isBasis_TY, isBasis_TY,
    isBasis_TXY, isBasis_TXY, isBasis_TYY⟩

/-- `4^m = 2^m · 2^m` in `ℕ`. -/
theorem four_pow (m : ℕ) : (1 + 1 + 1 + 1 : ℕ) ^ m = (1 + 1) ^ m * (1 + 1) ^ m := by
  rw [← mul_pow]; norm_num

/-- `f = T + TX + TX + TY + TY + TY + TXY + TXY + TYY`. -/
theorem decomposition_value : decomposition.value = f := by
  ext m
  simp only [decomposition, f, T, X, Y, h, BasisSum.value_cons, BasisSum.value_single,
    NaturalFunction.mul_apply, NaturalFunction.pow_apply, NaturalFunction.add_apply,
    NaturalFunction.one_apply, NaturalFunction.input_apply, four_pow]
  rw [pow_succ, pow_succ]
  ring

/-- Pointwise: `h(m)^(m+2) = h(m)^m · (1 + 2x + 3x² + 2x³ + x⁴)` with `x = 2^m`. -/
theorem f_apply (m : PosNat) :
    f m = T m * (1 + 2 * X m + 3 * X m ^ 2 + 2 * X m ^ 3 + X m ^ 4) := by
  have hY : Y m = X m * X m := by rw [← X_mul_X]; rfl
  have hf : f m = h m ^ (m.1 + 1 + 1) := rfl
  have hT : T m = h m ^ m.1 := rfl
  have hh : h m = 1 + X m + Y m := rfl
  rw [hf, hT, hh, hY, pow_succ, pow_succ]
  ring

/-- **The decomposition of `f` into atoms is unique**: every expansion of `f` as a
sum of elements of `𝓑` is a permutation of the nine summands above. -/
theorem decomposition_unique (t : BasisSum) (ht : t.Valid) (htf : t.value = f) :
    t.terms.Perm decomposition.terms := by
  obtain ⟨s, _, _, hs⟩ := Main.exists_basisSum_unique f
  exact (hs t ht htf).symm.trans (hs decomposition decomposition_valid decomposition_value)

/-- The nine atomic summands of `f`, with multiplicities `1, 2, 3, 2, 1`. -/
theorem decomposition_terms :
    decomposition.terms =
      [T, T * X, T * X, T * Y, T * Y, T * Y, T * X * Y, T * X * Y, T * Y * Y] :=
  rfl

theorem decomposition_length : decomposition.terms.length = 9 := rfl

/-- The five atoms `T, T·2^n, T·4^n, T·8^n, T·16^n` take the values
`7, 14, 28, 56, 112` at `n = 1`. -/
theorem atom_values :
    [T, T * X, T * Y, T * X * Y, T * Y * Y].map (fun F : NaturalFunction ↦ F one') =
      [7, 14, 28, 56, 112] :=
  rfl

/-- The five atoms are pairwise distinct. -/
theorem atoms_nodup : [T, T * X, T * Y, T * X * Y, T * Y * Y].Nodup := by
  apply List.Nodup.of_map (fun F : NaturalFunction ↦ F one')
  rw [atom_values]
  decide

/-- Every decomposition of `f` into atoms has, at `n = 1`, the values
`7, 14, 14, 28, 28, 28, 56, 56, 112` up to order: the multiplicities `1, 2, 3, 2, 1`
are forced. -/
theorem multiplicities_unique (t : BasisSum) (ht : t.Valid) (htf : t.value = f) :
    (t.terms.map (fun F : NaturalFunction ↦ F one')).Perm
      [7, 14, 14, 28, 28, 28, 56, 56, 112] :=
  (decomposition_unique t ht htf).map _

/-! ### The naive expansion -/

/-- The nine products `T·u·v`, `u, v ∈ {1, X, Y}`, listed by distributing
`T·h·h` syntactically (with `T·X·X` in place of one `T·Y`). -/
def naive : BasisSum :=
  .cons (T * 1 * 1) (.cons (T * 1 * X) (.cons (T * 1 * Y) (.cons (T * X * 1)
    (.cons (T * X * X) (.cons (T * X * Y) (.cons (T * Y * 1) (.cons (T * Y * X)
      (.single (T * Y * Y)))))))))

theorem naive_valid : naive.Valid := by
  have b1 := IsBasis.of_tower isTower_T
  have bX := IsBasis.of_tower isTower_X
  have bY := IsBasis.of_tower isTower_Y
  simp only [naive, BasisSum.valid_cons_iff, BasisSum.valid_single_iff]
  exact ⟨(b1.mul IsBasis.one).mul IsBasis.one, (b1.mul IsBasis.one).mul bX,
    (b1.mul IsBasis.one).mul bY, (b1.mul bX).mul IsBasis.one, (b1.mul bX).mul bX,
    (b1.mul bX).mul bY, (b1.mul bY).mul IsBasis.one, (b1.mul bY).mul bX,
    (b1.mul bY).mul bY⟩

/-- `T·h·h = Σ_{u,v ∈ {1,X,Y}} T·u·v`, which is `f` by `h^(n+1+1) = h^n·h·h`. -/
theorem naive_value : naive.value = f := by
  ext m
  simp only [naive, f, T, X, Y, h, BasisSum.value_cons, BasisSum.value_single,
    NaturalFunction.mul_apply, NaturalFunction.pow_apply, NaturalFunction.add_apply,
    NaturalFunction.one_apply, NaturalFunction.input_apply]
  rw [pow_succ, pow_succ]
  ring

/-- The naive expansion is a permutation of the decomposition, after the merge
`T·X·X = T·Y`. -/
theorem naive_perm : naive.terms.Perm decomposition.terms :=
  decomposition_unique naive naive_valid naive_value

/-- The naive list, simplified, is the decomposition with one `T·Y` written
`T·X·X`. -/
theorem naive_terms :
    naive.terms =
      [T, T * X, T * Y, T * X, T * X * X, T * X * Y, T * Y, T * X * Y, T * Y * Y] := by
  simp only [naive, BasisSum.terms_cons, BasisSum.terms_single, mul_one]
  have hYX : T * Y * X = T * X * Y := by rw [mul_assoc, mul_comm Y X, ← mul_assoc]
  rw [hYX]

/-! ### Atomicity -/

/-- `f` is not `+`-atomic. -/
theorem f_not_addAtomic : ¬ f.AddAtomic := by
  intro hf
  apply hf
  refine ⟨T, T * X + (T * X + (T * Y + (T * Y + (T * Y + (T * X * Y +
    (T * X * Y + T * Y * Y)))))), ?_⟩
  rw [← decomposition_value]
  rfl

/-- The tower `T = h^n` is `+`-atomic. -/
theorem T_addAtomic : T.AddAtomic := Main.pow_input_addAtomic h

/-- Each of the five distinct atoms is `+`-atomic. -/
theorem atoms_addAtomic :
    ∀ b ∈ [T, T * X, T * Y, T * X * Y, T * Y * Y], b.AddAtomic := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact (Main.addAtomic_iff_isBasis _).2 isBasis_T
  · exact (Main.addAtomic_iff_isBasis _).2 isBasis_TX
  · exact (Main.addAtomic_iff_isBasis _).2 isBasis_TY
  · exact (Main.addAtomic_iff_isBasis _).2 isBasis_TXY
  · exact (Main.addAtomic_iff_isBasis _).2 isBasis_TYY

end Natfunbasis.Examples4
