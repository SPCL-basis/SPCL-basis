import Natfunbasis.NaturalFunctions

/-!
# Towers and elementary additive generation

This module defines the candidate additive basis extensionally.  Its main
result is the elementary half of the basis theorem: every natural function is
a nonempty finite sum of finite products of nondegenerate towers.  No normal
form or uniqueness theorem is used here.
-/

namespace Natfunbasis

open NaturalFunction

/-- Nondegenerate towers.  The input function is the height-zero tower, and a
natural function different from one may be placed below an existing tower. -/
inductive IsTower : NaturalFunction → Prop where
  | input : IsTower NaturalFunction.input
  | pow {u t : NaturalFunction} : u ≠ 1 → IsTower t → IsTower (u ^ t)

/-- The candidate basis consists of finite products of towers.  The empty
product is the constant-one function. -/
def IsBasis (b : NaturalFunction) : Prop :=
  ∃ towers : List NaturalFunction,
    (∀ t ∈ towers, IsTower t) ∧ b = towers.prod

namespace IsBasis

theorem one : IsBasis (1 : NaturalFunction) := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · simp

theorem of_tower {t : NaturalFunction} (ht : IsTower t) : IsBasis t := by
  refine ⟨[t], ?_, ?_⟩
  · simpa
  · simp

theorem mul {a b : NaturalFunction} (ha : IsBasis a) (hb : IsBasis b) :
    IsBasis (a * b) := by
  obtain ⟨as, has, rfl⟩ := ha
  obtain ⟨bs, hbs, rfl⟩ := hb
  refine ⟨as ++ bs, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact has t ht
    · exact hbs t ht
  · exact List.prod_append.symm

end IsBasis

namespace NaturalFunction

theorem pow_one_function (f : NaturalFunction) :
    f ^ (1 : NaturalFunction) = f := by
  ext n
  simp

theorem one_pow_function (f : NaturalFunction) :
    (1 : NaturalFunction) ^ f = 1 := by
  ext n
  simp

theorem pow_add_function (f g h : NaturalFunction) :
    f ^ (g + h) = f ^ g * f ^ h := by
  ext n
  exact Nat.pow_add _ _ _

theorem pow_mul_function (f g h : NaturalFunction) :
    f ^ (g * h) = (f ^ g) ^ h := by
  ext n
  exact Nat.pow_mul _ _ _

/-- Raising a non-one natural function to a positive-valued natural function
cannot produce the constant-one function. -/
theorem pow_ne_one {f g : NaturalFunction} (hf : f ≠ 1) : f ^ g ≠ 1 := by
  intro hpow
  apply hf
  ext n
  have hn : f n ^ g n = 1 := by
    have happly := congrArg (fun h : NaturalFunction ↦ h n) hpow
    simpa using happly
  exact (Nat.pow_eq_one.mp hn).resolve_right (Nat.ne_of_gt (apply_pos g n))

end NaturalFunction

/-- A nonempty list of candidate basis summands. -/
inductive BasisSum where
  | single (b : NaturalFunction)
  | cons (b : NaturalFunction) (rest : BasisSum)

namespace BasisSum

/-- The nonempty list of summands. -/
def terms : BasisSum → List NaturalFunction
  | .single b => [b]
  | .cons b rest => b :: rest.terms

/-- The natural function represented by the sum. -/
def value : BasisSum → NaturalFunction
  | .single b => b
  | .cons b rest => b + rest.value

/-- Every summand is a member of the candidate basis. -/
def Valid : BasisSum → Prop
  | .single b => IsBasis b
  | .cons b rest => IsBasis b ∧ rest.Valid

@[simp]
theorem terms_single (b : NaturalFunction) : terms (.single b) = [b] :=
  rfl

@[simp]
theorem terms_cons (b : NaturalFunction) (rest : BasisSum) :
    terms (.cons b rest) = b :: rest.terms :=
  rfl

theorem terms_ne_nil (s : BasisSum) : s.terms ≠ [] := by
  cases s <;> simp [terms]

@[simp]
theorem value_single (b : NaturalFunction) : value (.single b) = b :=
  rfl

@[simp]
theorem value_cons (b : NaturalFunction) (rest : BasisSum) :
    value (.cons b rest) = b + rest.value :=
  rfl

@[simp]
theorem valid_single_iff (b : NaturalFunction) :
    Valid (.single b) ↔ IsBasis b :=
  Iff.rfl

@[simp]
theorem valid_cons_iff (b : NaturalFunction) (rest : BasisSum) :
    Valid (.cons b rest) ↔ IsBasis b ∧ rest.Valid :=
  Iff.rfl

theorem valid_iff_forall_mem (s : BasisSum) :
    s.Valid ↔ ∀ b ∈ s.terms, IsBasis b := by
  induction s with
  | single b => simp [Valid, terms]
  | cons b rest ih => simp [Valid, terms, ih]

/-- Concatenate two nonempty sums. -/
def append : BasisSum → BasisSum → BasisSum
  | .single b, t => .cons b t
  | .cons b rest, t => .cons b (append rest t)

@[simp]
theorem terms_append (s t : BasisSum) :
    (s.append t).terms = s.terms ++ t.terms := by
  induction s with
  | single b => rfl
  | cons b rest ih => simp [append, terms, ih]

@[simp]
theorem value_append (s t : BasisSum) :
    (s.append t).value = s.value + t.value := by
  induction s with
  | single b => rfl
  | cons b rest ih =>
      simp only [append, value_cons, ih]
      exact (add_assoc _ _ _).symm

theorem valid_append {s t : BasisSum} (hs : s.Valid) (ht : t.Valid) :
    (s.append t).Valid := by
  induction s with
  | single b => exact ⟨hs, ht⟩
  | cons b rest ih =>
      exact ⟨hs.1, ih hs.2⟩

/-- Multiply every summand in a basis sum on the left by one basis element. -/
def leftMul (a : NaturalFunction) : BasisSum → BasisSum
  | .single b => .single (a * b)
  | .cons b rest => .cons (a * b) (leftMul a rest)

@[simp]
theorem terms_leftMul (a : NaturalFunction) (s : BasisSum) :
    (s.leftMul a).terms = s.terms.map (a * ·) := by
  induction s with
  | single b => rfl
  | cons b rest ih => simp [leftMul, terms, ih]

@[simp]
theorem value_leftMul (a : NaturalFunction) (s : BasisSum) :
    (s.leftMul a).value = a * s.value := by
  induction s with
  | single b => rfl
  | cons b rest ih =>
      simp only [leftMul, value_cons, ih]
      ext n
      exact (Nat.mul_add _ _ _).symm

theorem valid_leftMul {a : NaturalFunction} (ha : IsBasis a)
    {s : BasisSum} (hs : s.Valid) : (s.leftMul a).Valid := by
  induction s with
  | single b => exact IsBasis.mul ha hs
  | cons b rest ih =>
      exact ⟨IsBasis.mul ha hs.1, ih hs.2⟩

/-- Distribute the product of two nonempty basis sums. -/
def mul : BasisSum → BasisSum → BasisSum
  | .single a, t => t.leftMul a
  | .cons a rest, t => (t.leftMul a).append (mul rest t)

@[simp]
theorem value_mul (s t : BasisSum) :
    (s.mul t).value = s.value * t.value := by
  induction s with
  | single a => simp [mul]
  | cons a rest ih =>
      simp only [mul, value_append, value_leftMul, ih, value_cons]
      ext n
      exact (Nat.add_mul _ _ _).symm

theorem valid_mul {s t : BasisSum} (hs : s.Valid) (ht : t.Valid) :
    (s.mul t).Valid := by
  induction s with
  | single a => exact valid_leftMul hs ht
  | cons a rest ih =>
      exact valid_append (valid_leftMul hs.1 ht) (ih hs.2)

/-- A single basis element is a valid nonempty basis sum. -/
theorem valid_single_of_basis {b : NaturalFunction} (hb : IsBasis b) :
    (single b).Valid :=
  hb

/-- A nonempty product of towers can be used as an exponent to make a new
tower over any non-one base. -/
theorem tower_pow_of_nonempty_basis_product {u b t : NaturalFunction}
    {ts : List NaturalFunction} (hu : u ≠ 1) (ht : IsTower t)
    (hb : b = (t :: ts).prod) : IsTower (u ^ b) := by
  have hbase : u ^ ts.prod ≠ (1 : NaturalFunction) :=
    NaturalFunction.pow_ne_one hu
  have htower : IsTower ((u ^ ts.prod) ^ t) :=
    IsTower.pow hbase ht
  rw [hb, List.prod_cons, mul_comm t ts.prod,
    NaturalFunction.pow_mul_function]
  exact htower

/-- A nonconstant basis exponent turns every non-one base into one tower, and
hence into a basis element. -/
theorem basis_pow_of_nonconstant {u b : NaturalFunction}
    (hu : u ≠ 1) (hb : IsBasis b)
    (hb_nonconstant : NaturalFunction.Nonconstant b) : IsBasis (u ^ b) := by
  obtain ⟨towers, htowers, hb_product⟩ := hb
  cases towers with
  | nil =>
      exfalso
      obtain ⟨m, n, hmn⟩ := hb_nonconstant
      apply hmn
      rw [hb_product]
      simp
  | cons t towers =>
      apply IsBasis.of_tower
      exact BasisSum.tower_pow_of_nonempty_basis_product hu
        (htowers t (by simp)) hb_product

/-- Raising a function with a valid expansion to one basis summand again has
a valid expansion.  The empty tower product (the basis element one) returns
the original expansion; a nonempty tower product produces one new tower. -/
theorem exists_pow_basis_term (base : BasisSum) (hbase : base.Valid)
    {u b : NaturalFunction} (hvalue : base.value = u) (hu : u ≠ 1)
    (hb : IsBasis b) :
    ∃ result : BasisSum,
      result.Valid ∧ result.value = u ^ b := by
  obtain ⟨towers, htowers, rfl⟩ := hb
  cases towers with
  | nil =>
      refine ⟨base, hbase, ?_⟩
      simpa [hvalue] using (NaturalFunction.pow_one_function u).symm
  | cons t ts =>
      have ht : IsTower t := htowers t (by simp)
      have hnew : IsTower (u ^ (t :: ts).prod) :=
        tower_pow_of_nonempty_basis_product hu ht rfl
      exact ⟨.single (u ^ (t :: ts).prod), IsBasis.of_tower hnew, rfl⟩

/-- Exponentiating the value of one valid basis sum by the value of another
valid basis sum produces a valid basis-sum expansion. -/
theorem exists_pow (base exponent : BasisSum) (hbase : base.Valid)
    (hexponent : exponent.Valid) :
    ∃ result : BasisSum,
      result.Valid ∧ result.value = base.value ^ exponent.value := by
  by_cases hbase_one : base.value = (1 : NaturalFunction)
  · refine ⟨.single 1, IsBasis.one, ?_⟩
    rw [hbase_one, NaturalFunction.one_pow_function]
    rfl
  · induction exponent with
    | single b =>
        exact exists_pow_basis_term base hbase rfl hbase_one hexponent
    | cons b rest ih =>
        obtain ⟨first, hfirst_valid, hfirst_value⟩ :=
          exists_pow_basis_term base hbase rfl hbase_one hexponent.1
        obtain ⟨later, hlater_valid, hlater_value⟩ := ih hexponent.2
        refine ⟨first.mul later, valid_mul hfirst_valid hlater_valid, ?_⟩
        rw [value_mul, hfirst_value, hlater_value,
          ← NaturalFunction.pow_add_function]
        rfl

end BasisSum

/-- Every expression has a nonempty basis-sum expansion. -/
theorem exists_basisSum_ofExpr (e : UnaryExpr) :
    ∃ expansion : BasisSum,
      expansion.Valid ∧ expansion.value = NaturalFunction.ofExpr e := by
  induction e with
  | one =>
      exact ⟨.single 1, IsBasis.one, NaturalFunction.ofExpr_one.symm⟩
  | var x =>
      cases x
      exact ⟨.single NaturalFunction.input,
        IsBasis.of_tower IsTower.input, rfl⟩
  | add e d he hd =>
      obtain ⟨se, hse_valid, hse_value⟩ := he
      obtain ⟨sd, hsd_valid, hsd_value⟩ := hd
      refine ⟨se.append sd, BasisSum.valid_append hse_valid hsd_valid, ?_⟩
      rw [BasisSum.value_append, hse_value, hsd_value,
        NaturalFunction.ofExpr_add]
  | mul e d he hd =>
      obtain ⟨se, hse_valid, hse_value⟩ := he
      obtain ⟨sd, hsd_valid, hsd_value⟩ := hd
      refine ⟨se.mul sd, BasisSum.valid_mul hse_valid hsd_valid, ?_⟩
      rw [BasisSum.value_mul, hse_value, hsd_value,
        NaturalFunction.ofExpr_mul]
  | pow e d he hd =>
      obtain ⟨se, hse_valid, hse_value⟩ := he
      obtain ⟨sd, hsd_valid, hsd_value⟩ := hd
      obtain ⟨result, hresult_valid, hresult_value⟩ :=
        BasisSum.exists_pow se sd hse_valid hsd_valid
      refine ⟨result, hresult_valid, ?_⟩
      rw [hresult_value, hse_value, hsd_value,
        NaturalFunction.ofExpr_pow]

/-- Every natural function is a nonempty finite sum of finite products of
nondegenerate towers. -/
theorem exists_basisSum (f : NaturalFunction) :
    ∃ expansion : BasisSum,
      expansion.Valid ∧ expansion.value = f := by
  obtain ⟨e, he⟩ := f.exists_expr
  obtain ⟨expansion, hvalid, hvalue⟩ := exists_basisSum_ofExpr e
  refine ⟨expansion, hvalid, hvalue.trans ?_⟩
  apply NaturalFunction.ext
  intro n
  exact (he n).symm

/-- The elementary direction of the atomicity characterization: additive
atomicity forces the generated expansion to consist of a single basis term.
No normal-form uniqueness or independence theorem is used. -/
theorem isBasis_of_addAtomic {f : NaturalFunction}
    (hf : NaturalFunction.AddAtomic f) : IsBasis f := by
  obtain ⟨expansion, hvalid, hvalue⟩ := exists_basisSum f
  cases expansion with
  | single b =>
      rw [← hvalue]
      exact hvalid
  | cons b rest =>
      exfalso
      apply hf
      exact ⟨b, rest.value, by simpa [BasisSum.value] using hvalue.symm⟩

end Natfunbasis
