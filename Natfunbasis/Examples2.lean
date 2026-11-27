import Natfunbasis.MainTheorems

/-!
# Atomic powers: an exact criterion

For natural functions `f, g`, the power `f^g` is `+`-atomic if and only if
`f` is `+`-atomic, or `g ≠ 1` and `g` is not of the form `1 + g'`
(`pow_addAtomic_iff`).  Theorem B is the special case where `g` is nonconstant
and atomic (`thmB_from_criterion`).

Instances:
* (a) `(n+1)^(n^n+n) = (n+1)^(n^n)·(n+1)^n` is an atom, although neither the
  base `n+1` nor the nonconstant exponent `n^n+n` is.
* (b) `(n+1)^(n^n+1) = n(n+1)^(n^n) + (n+1)^(n^n)`, its unique decomposition
  into two (distinct) atoms.
* (c) `2^((n+1)^(n+1)) = (2^((n+1)^n))^n · 2^((n+1)^n)` is an atom, although
  neither `2` nor `(n+1)^(n+1)` is; hence `(n+1)^(n+1)` is not of the form
  `1 + g'`, i.e. `n ↦ (n+1)^(n+1) - 1` is not a natural function.
* (d) `n^(n+1)` is an atom, `2^(n+1)` is not; `FG` is an atom iff `F` and `G` are.
-/

namespace Natfunbasis.Examples2

open NaturalFunction

/-- The variable `n`. -/
abbrev N : NaturalFunction := input

/-- The constant `2 = 1 + 1`. -/
def two : NaturalFunction := 1 + 1

theorem N_ne_one : N ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨2, by norm_num⟩) H
  change (2 : ℕ) = 1 at this
  omega

theorem N_add_one_ne_one : N + 1 ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨1, by norm_num⟩) H
  simp at this

theorem two_ne_one : two ≠ 1 := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨1, by norm_num⟩) H
  simp [two] at this

theorem two_not_addAtomic : ¬ two.AddAtomic := fun h => h ⟨1, 1, rfl⟩

theorem isTower_N_add_one_pow : IsTower ((N + 1) ^ N) :=
  IsTower.pow N_add_one_ne_one IsTower.input

theorem isTower_N_add_one_pow_N_pow : IsTower ((N + 1) ^ (N ^ N)) :=
  IsTower.pow N_add_one_ne_one (IsTower.pow N_ne_one IsTower.input)

/-! ## The criterion -/

/-- If `b` is a summand of a `𝓑`-expansion, the expanded function is `b` or `b + r`. -/
theorem exists_eq_add_of_mem (s : BasisSum) {b : NaturalFunction} (hb : b ∈ s.terms) :
    s.value = b ∨ ∃ r, s.value = b + r := by
  induction s with
  | single c =>
      simp [BasisSum.terms] at hb
      subst hb; left; rfl
  | cons c rest ih =>
      simp only [BasisSum.terms_cons, List.mem_cons] at hb
      rcases hb with rfl | hb
      · right; exact ⟨rest.value, rfl⟩
      · rcases ih hb with h | ⟨r, h⟩
        · right; refine ⟨c, ?_⟩
          simp only [BasisSum.value_cons, h]; exact add_comm _ _
        · right; refine ⟨c + r, ?_⟩
          simp only [BasisSum.value_cons, h]; exact add_left_comm _ _ _

/-- `f^(b₁+⋯+b_r) = ∏ f^(b_i) ∈ 𝓑` when `f ≠ 1` and either `f ∈ 𝓑` or no `b_i` is `1`. -/
theorem isBasis_pow_aux {f : NaturalFunction} (hf1 : f ≠ 1) (s : BasisSum) (hs : s.Valid)
    (h : IsBasis f ∨ ∀ b ∈ s.terms, b ≠ 1) : IsBasis (f ^ s.value) := by
  have term : ∀ b ∈ s.terms, IsBasis (f ^ b) := by
    intro b hb
    have hbB : IsBasis b := (BasisSum.valid_iff_forall_mem s).1 hs b hb
    obtain ⟨ts, hts, rfl⟩ := hbB
    cases ts with
    | nil =>
        rcases h with h | h
        · simpa [pow_one_function] using h
        · exact absurd (by simp) (h _ hb)
    | cons t ts =>
        exact IsBasis.of_tower
          (BasisSum.tower_pow_of_nonempty_basis_product hf1 (hts t (by simp)) rfl)
  clear h
  induction s with
  | single b => exact term b (by simp)
  | cons b rest ih =>
      rw [BasisSum.value_cons, pow_add_function]
      exact (term b (by simp)).mul (ih hs.2 (fun c hc => term c (by simp [hc])))

/-- **Criterion.** `f^g` is `+`-atomic iff `f` is, or `g ≠ 1` and `g ≠ 1 + g'` for all `g'`. -/
theorem pow_addAtomic_iff (f g : NaturalFunction) :
    (f ^ g).AddAtomic ↔ f.AddAtomic ∨ (g ≠ 1 ∧ ∀ g', g ≠ 1 + g') := by
  constructor
  · intro hfg
    by_contra hcon
    have hf : ¬ f.AddAtomic := fun h => hcon (Or.inl h)
    have hf' : ∃ a b : NaturalFunction, f = a + b := by
      simpa [AddAtomic] using hf
    obtain ⟨a, b, rfl⟩ := hf'
    apply hfg
    by_cases hg1 : g = 1
    · subst hg1
      exact ⟨a, b, by rw [pow_one_function]⟩
    · have hg : ∃ g', g = 1 + g' := by
        by_contra hne
        exact hcon (Or.inr ⟨hg1, fun g' h => hne ⟨g', h⟩⟩)
      obtain ⟨g', rfl⟩ := hg
      refine ⟨a * (a + b) ^ g', b * (a + b) ^ g', ?_⟩
      ext m
      simp only [pow_apply, add_apply, mul_apply, one_apply]
      rw [pow_add, pow_one, add_mul]
  · intro h
    by_cases hf1 : f = 1
    · subst hf1; rw [one_pow_function]; exact one_addAtomic
    obtain ⟨s, hs, rfl⟩ := exists_basisSum g
    apply (Main.addAtomic_iff_isBasis _).2
    apply isBasis_pow_aux hf1 s hs
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl ((Main.addAtomic_iff_isBasis _).1 h)
    · right
      intro b hb hb1
      subst hb1
      rcases exists_eq_add_of_mem s hb with h | ⟨r, h⟩
      · exact h1 h
      · exact h2 r h

/-- Theorem B re-derived from the criterion. -/
theorem thmB_from_criterion (f g : NaturalFunction) (hnc : g.Nonconstant)
    (ha : g.AddAtomic) : (f ^ g).AddAtomic :=
  (pow_addAtomic_iff f g).2 (Or.inr ⟨fun h => by
      subst h; obtain ⟨m, m', h⟩ := hnc; exact h rfl,
    fun g' h => ha ⟨1, g', h⟩⟩)

/-- `FG` is `+`-atomic iff `F` and `G` both are. -/
theorem mul_addAtomic_iff (F G : NaturalFunction) :
    (F * G).AddAtomic ↔ F.AddAtomic ∧ G.AddAtomic := by
  constructor
  · intro h
    refine ⟨fun ⟨a, b, hab⟩ => h ⟨a * G, b * G, ?_⟩,
      fun ⟨a, b, hab⟩ => h ⟨F * a, F * b, ?_⟩⟩
    · subst hab; ext m; simp only [mul_apply, add_apply]; rw [add_mul]
    · subst hab; ext m; simp only [mul_apply, add_apply]; rw [mul_add]
  · rintro ⟨hF, hG⟩
    exact (Main.addAtomic_iff_isBasis _).2
      (((Main.addAtomic_iff_isBasis _).1 hF).mul ((Main.addAtomic_iff_isBasis _).1 hG))

/-! ## (a) `(n+1)^(n^n+n)` is an atom -/

theorem ex_a_eq : (N + 1) ^ (N ^ N + N) = (N + 1) ^ (N ^ N) * (N + 1) ^ N :=
  pow_add_function _ _ _

theorem ex_a_addAtomic : ((N + 1) ^ (N ^ N + N)).AddAtomic := by
  rw [ex_a_eq]
  exact (Main.addAtomic_iff_isBasis _).2
    ((IsBasis.of_tower isTower_N_add_one_pow_N_pow).mul
      (IsBasis.of_tower isTower_N_add_one_pow))

theorem base_not_addAtomic : ¬ (N + 1).AddAtomic := fun h => h ⟨N, 1, rfl⟩

theorem ex_a_exp_not_addAtomic : ¬ (N ^ N + N).AddAtomic := fun h => h ⟨N ^ N, N, rfl⟩

theorem ex_a_exp_nonconstant : (N ^ N + N).Nonconstant :=
  ⟨⟨1, by norm_num⟩, ⟨2, by norm_num⟩, by decide⟩

/-! ## (b) `(n+1)^(n^n+1)` has exactly two atoms -/

/-- The atoms `n(n+1)^(n^n)` and `(n+1)^(n^n)`. -/
def ex_b_sum : BasisSum := .cons (N * (N + 1) ^ (N ^ N)) (.single ((N + 1) ^ (N ^ N)))

theorem ex_b_valid : ex_b_sum.Valid := by
  simp only [ex_b_sum, BasisSum.valid_cons_iff, BasisSum.valid_single_iff]
  exact ⟨(IsBasis.of_tower IsTower.input).mul (IsBasis.of_tower isTower_N_add_one_pow_N_pow),
    IsBasis.of_tower isTower_N_add_one_pow_N_pow⟩

theorem ex_b_value : ex_b_sum.value = (N + 1) ^ (N ^ N + 1) := by
  ext m
  simp only [ex_b_sum, BasisSum.value_cons, BasisSum.value_single, add_apply, mul_apply,
    pow_apply, one_apply, input_apply]
  rw [pow_succ]
  ring

/-- Every `𝓑`-expansion of `(n+1)^(n^n+1)` is a permutation of the two atoms above. -/
theorem ex_b_unique (t : BasisSum) (ht : t.Valid) (htf : t.value = (N + 1) ^ (N ^ N + 1)) :
    t.terms.Perm ex_b_sum.terms := by
  obtain ⟨s, _, _, hs⟩ := Main.exists_basisSum_unique ((N + 1) ^ (N ^ N + 1))
  exact (hs t ht htf).symm.trans (hs ex_b_sum ex_b_valid ex_b_value)

theorem ex_b_terms : ex_b_sum.terms = [N * (N + 1) ^ (N ^ N), (N + 1) ^ (N ^ N)] := rfl

/-- The two atoms are distinct: values `162` and `81` at `n = 2`. -/
theorem ex_b_atoms_at_two :
    (N * (N + 1) ^ (N ^ N)) ⟨2, by norm_num⟩ = 162 ∧
    ((N + 1) ^ (N ^ N)) ⟨2, by norm_num⟩ = 81 := ⟨rfl, rfl⟩

theorem ex_b_atoms_ne : N * (N + 1) ^ (N ^ N) ≠ (N + 1) ^ (N ^ N) := by
  intro H
  have := congrArg (fun F : NaturalFunction ↦ F ⟨2, by norm_num⟩) H
  simp only [ex_b_atoms_at_two] at this
  omega

theorem ex_b_not_addAtomic : ¬ ((N + 1) ^ (N ^ N + 1)).AddAtomic := by
  intro h; apply h
  exact ⟨_, _, ex_b_value.symm⟩

theorem ex_b_exp_not_addAtomic : ¬ (N ^ N + 1).AddAtomic := fun h => h ⟨N ^ N, 1, rfl⟩

theorem ex_b_exp_nonconstant : (N ^ N + 1).Nonconstant :=
  ⟨⟨1, by norm_num⟩, ⟨2, by norm_num⟩, by decide⟩

/-! ## (c) `2^((n+1)^(n+1))` is an atom -/

theorem ex_c_eq : two ^ ((N + 1) ^ (N + 1)) =
    (two ^ ((N + 1) ^ N)) ^ N * two ^ ((N + 1) ^ N) := by
  ext m
  simp only [two, pow_apply, mul_apply, add_apply, one_apply, input_apply]
  rw [← pow_mul, ← pow_add]
  congr 1

theorem ex_c_addAtomic : (two ^ ((N + 1) ^ (N + 1))).AddAtomic := by
  rw [ex_c_eq]
  exact (Main.addAtomic_iff_isBasis _).2
    ((IsBasis.of_tower (IsTower.pow (pow_ne_one two_ne_one) IsTower.input)).mul
      (IsBasis.of_tower (IsTower.pow two_ne_one isTower_N_add_one_pow)))

/-- `(n+1)^(n+1) = n(n+1)^n + (n+1)^n`. -/
theorem ex_c_exp_eq : (N + 1) ^ (N + 1) = N * (N + 1) ^ N + (N + 1) ^ N := by
  ext m
  simp only [pow_apply, mul_apply, add_apply, one_apply, input_apply]
  rw [pow_succ]; ring

theorem ex_c_exp_not_addAtomic : ¬ ((N + 1) ^ (N + 1)).AddAtomic := fun h =>
  h ⟨_, _, ex_c_exp_eq⟩

/-- `(n+1)^(n+1)` is not of the form `1 + g'`: `n ↦ (n+1)^(n+1) - 1` is not a
natural function. -/
theorem N_add_one_pow_ne_one_add : ¬ ∃ g', (N + 1) ^ (N + 1) = 1 + g' := by
  rintro ⟨g', h⟩
  rcases (pow_addAtomic_iff two _).1 ex_c_addAtomic with h2 | ⟨_, h3⟩
  · exact two_not_addAtomic h2
  · exact h3 g' h

/-! ## (d) exponent `n+1` -/

theorem ex_d_eq : N ^ (N + 1) = N ^ N * N := by
  rw [pow_add_function, pow_one_function]

theorem ex_d_addAtomic : (N ^ (N + 1)).AddAtomic :=
  (pow_addAtomic_iff N _).2 (Or.inl input_addAtomic)

theorem ex_d_two_not_addAtomic : ¬ (two ^ (N + 1)).AddAtomic := by
  intro h
  rcases (pow_addAtomic_iff two _).1 h with h2 | ⟨_, h3⟩
  · exact two_not_addAtomic h2
  · exact h3 N (add_comm _ _)

end Natfunbasis.Examples2
