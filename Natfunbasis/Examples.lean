import Natfunbasis.MainTheorems

/-!
# A worked example of the additive basis theorem

Let `h = (n+1)^n + n^(n^n) + 8` and `f = h^(n^2+2n+1)`, with the exponent written
as `n·n + n + n + 1`.  With the towers `T₁ = h^n` and `T₂ = (h^n)^n`, and
`c = T₂·T₁·T₁`,

  `f = c·(n+1)^n + c·n^(n^n) + c + c + c + c + c + c + c + c`,

a sum of ten elements of the basis `𝓑` (finite products of towers).  By the
additive basis theorem this is the unique decomposition of `f` into atoms, up
to order: `f` is not `+`-atomic, although `h^((n+1)^n)` is (it is a tower).

This is Example 4.5 of the accompanying paper.
-/

namespace Natfunbasis.Examples

open NaturalFunction

/-- The variable `n`. -/
abbrev N : NaturalFunction := input

/-- The constant `8 = 1 + ⋯ + 1`. -/
def eight : NaturalFunction := 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1

/-- `h = (n+1)^n + n^(n^n) + 8`. -/
def h : NaturalFunction := (N + 1) ^ N + N ^ (N ^ N) + eight

/-- `f = h^(n^2 + 2n + 1)`, the exponent written as `n·n + n + n + 1`. -/
def f : NaturalFunction := h ^ (N * N + N + N + 1)

/-- The towers `T₁ = h^n` and `T₂ = (h^n)^n`. -/
def T₁ : NaturalFunction := h ^ N
def T₂ : NaturalFunction := (h ^ N) ^ N

/-- The three atoms occurring in `f`. -/
def c : NaturalFunction := T₂ * T₁ * T₁
def b₁ : NaturalFunction := c * (N + 1) ^ N
def b₂ : NaturalFunction := c * N ^ (N ^ N)

/-- The decomposition `b₁ + b₂ + c + ⋯ + c` (eight copies of `c`). -/
def decomposition : BasisSum :=
  .cons b₁ (.cons b₂ (.cons c (.cons c (.cons c (.cons c
    (.cons c (.cons c (.cons c (.single c)))))))))

theorem N_ne_one : N ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨2, by norm_num⟩) H
  change (2 : ℕ) = 1 at this
  omega

theorem N_add_one_ne_one : N + 1 ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨1, by norm_num⟩) H
  simp at this

theorem h_ne_one : h ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨1, by norm_num⟩) H
  simp [h, eight] at this

theorem isTower_N_add_one_pow : IsTower ((N + 1) ^ N) :=
  IsTower.pow N_add_one_ne_one IsTower.input

theorem isTower_N_pow_N_pow : IsTower (N ^ (N ^ N)) :=
  IsTower.pow N_ne_one (IsTower.pow N_ne_one IsTower.input)

theorem isTower_T₁ : IsTower T₁ := IsTower.pow h_ne_one IsTower.input

theorem isTower_T₂ : IsTower T₂ :=
  IsTower.pow (pow_ne_one h_ne_one) IsTower.input

theorem isBasis_c : IsBasis c :=
  ((IsBasis.of_tower isTower_T₂).mul (IsBasis.of_tower isTower_T₁)).mul
    (IsBasis.of_tower isTower_T₁)

theorem isBasis_b₁ : IsBasis b₁ :=
  isBasis_c.mul (IsBasis.of_tower isTower_N_add_one_pow)

theorem isBasis_b₂ : IsBasis b₂ :=
  isBasis_c.mul (IsBasis.of_tower isTower_N_pow_N_pow)

theorem decomposition_valid : decomposition.Valid := by
  simp only [decomposition, BasisSum.valid_cons_iff, BasisSum.valid_single_iff]
  exact ⟨isBasis_b₁, isBasis_b₂, isBasis_c, isBasis_c, isBasis_c, isBasis_c,
    isBasis_c, isBasis_c, isBasis_c, isBasis_c⟩

/-- `f = b₁ + b₂ + c + ⋯ + c`. -/
theorem decomposition_value : decomposition.value = f := by
  apply NaturalFunction.ext
  intro m
  have key : ∀ H k : ℕ, H ^ (k * k + k + k + 1) = (H ^ k) ^ k * H ^ k * H ^ k * H := by
    intro H k
    rw [pow_succ, pow_add, pow_add, pow_mul]
  simp only [decomposition, BasisSum.value_cons, BasisSum.value_single, f, b₁, b₂, c,
    T₁, T₂, add_apply, mul_apply, pow_apply, one_apply, key]
  simp only [h, eight, add_apply, pow_apply, one_apply]
  ring

/-- **The decomposition of `f` into atoms is unique**: every expansion of `f`
as a sum of elements of `𝓑` is a permutation of `b₁, b₂, c, …, c`. -/
theorem decomposition_unique (t : BasisSum) (ht : t.Valid) (htf : t.value = f) :
    t.terms.Perm decomposition.terms := by
  obtain ⟨s, _, _, hs⟩ := Main.exists_basisSum_unique f
  exact (hs t ht htf).symm.trans (hs decomposition decomposition_valid decomposition_value)

/-- `f` has exactly ten atomic summands: `b₁` and `b₂` once each, `c` eight times. -/
theorem decomposition_terms :
    decomposition.terms = [b₁, b₂, c, c, c, c, c, c, c, c] :=
  rfl

/-- `f` is not `+`-atomic (its exponent `(n+1)^2` is not `+`-atomic). -/
theorem f_not_addAtomic : ¬ f.AddAtomic := by
  intro hf
  apply hf
  refine ⟨b₁, b₂ + (c + (c + (c + (c + (c + (c + (c + c))))))), ?_⟩
  rw [← decomposition_value]
  rfl

/-- By contrast, `h^((n+1)^n)` is a tower, hence `+`-atomic. -/
theorem h_pow_addAtomic : (h ^ ((N + 1) ^ N)).AddAtomic :=
  (Main.addAtomic_iff_isBasis _).2
    (IsBasis.of_tower (IsTower.pow h_ne_one isTower_N_add_one_pow))

/-- The atoms `b₁`, `b₂`, `c` are pairwise distinct (compare their values at
`n = 2`; at `n = 1` one has `b₂ = c`). -/
theorem atoms_nodup : [b₁, b₂, c].Nodup := by
  have hc : 0 < c ⟨2, by norm_num⟩ := apply_pos c _
  have h₁ : b₁ ⟨2, by norm_num⟩ = c ⟨2, by norm_num⟩ * 9 := by
    show c ⟨2, _⟩ * (2 + 1) ^ 2 = c ⟨2, _⟩ * 9
    rfl
  have h₂ : b₂ ⟨2, by norm_num⟩ = c ⟨2, by norm_num⟩ * 16 := by
    show c ⟨2, _⟩ * 2 ^ 2 ^ 2 = c ⟨2, _⟩ * 16
    rfl
  have hne : ∀ F G : NaturalFunction, F ⟨2, by norm_num⟩ ≠ G ⟨2, by norm_num⟩ → F ≠ G :=
    fun F G h H => h (H ▸ rfl)
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2
    ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩
  · intro hm
    rcases List.mem_cons.1 hm with h | h
    · exact hne _ _ (by omega) h
    · rcases List.mem_cons.1 h with h | h
      · exact hne _ _ (by omega) h
      · exact List.not_mem_nil h
  · intro hm
    rcases List.mem_cons.1 hm with h | h
    · exact hne _ _ (by omega) h
    · exact List.not_mem_nil h

end Natfunbasis.Examples
