import Mathlib

/-!
# Natural expressions and positive semantics

The foundational syntax requested by `lean_wilkie_prompt.md`.  Expressions use
only `1`, variables, addition, multiplication, and binary exponentiation.
Their intended assignments are strictly positive natural numbers.
-/

namespace Natfunbasis

/-- A natural expression in variables of type `Var`. -/
inductive Expr (Var : Type*) where
  | one : Expr Var
  | var : Var → Expr Var
  | add : Expr Var → Expr Var → Expr Var
  | mul : Expr Var → Expr Var → Expr Var
  | pow : Expr Var → Expr Var → Expr Var
  deriving DecidableEq, Repr

namespace Expr

variable {Var W : Type*}

/-- The positive constant `n + 1`, represented using only `1` and addition. -/
def posConst : Nat → Expr Var
  | 0 => .one
  | n + 1 => .add (posConst n) .one

/-- Evaluate a natural expression in `Nat`. Positivity is imposed separately. -/
@[simp]
def eval (assignment : Var → Nat) : Expr Var → Nat
  | .one => 1
  | .var x => assignment x
  | .add s t => eval assignment s + eval assignment t
  | .mul s t => eval assignment s * eval assignment t
  | .pow s t => eval assignment s ^ eval assignment t

@[simp]
theorem eval_posConst (assignment : Var → Nat) (n : Nat) :
    eval assignment (posConst n) = n + 1 := by
  induction n with
  | zero => simp [posConst]
  | succ n ih => simp [posConst, ih, Nat.add_assoc]

/-- An assignment of strictly positive natural numbers to all variables. -/
def PositiveAssignment (assignment : Var → Nat) : Prop :=
  ∀ x, 0 < assignment x

/-- Every natural expression evaluates positively on a positive assignment. -/
theorem eval_pos (assignment : Var → Nat) (hassignment : PositiveAssignment assignment) :
    ∀ e : Expr Var, 0 < eval assignment e := by
  intro e
  induction e with
  | one => simp
  | var x => exact hassignment x
  | add s t hs ht => exact Nat.add_pos_left hs _
  | mul s t hs ht => exact Nat.mul_pos hs ht
  | pow s t hs ht => exact Nat.pow_pos hs

/-- Semantic equality on all strictly positive assignments. -/
def SemEq (s t : Expr Var) : Prop :=
  ∀ assignment, PositiveAssignment assignment → eval assignment s = eval assignment t

namespace SemEq

theorem refl (s : Expr Var) : SemEq s s := by
  intro assignment hassignment
  rfl

theorem symm {s t : Expr Var} (h : SemEq s t) : SemEq t s := by
  intro assignment hassignment
  exact (h assignment hassignment).symm

theorem trans {s t u : Expr Var} (hst : SemEq s t) (htu : SemEq t u) : SemEq s u := by
  intro assignment hassignment
  exact (hst assignment hassignment).trans (htu assignment hassignment)

end SemEq

/-- Substitute an expression for every variable. -/
def subst (substitution : Var → Expr W) : Expr Var → Expr W
  | .one => .one
  | .var x => substitution x
  | .add s t => .add (subst substitution s) (subst substitution t)
  | .mul s t => .mul (subst substitution s) (subst substitution t)
  | .pow s t => .pow (subst substitution s) (subst substitution t)

@[simp]
theorem eval_subst (assignment : W → Nat) (substitution : Var → Expr W)
    (e : Expr Var) :
    eval assignment (subst substitution e) =
      eval (fun x ↦ eval assignment (substitution x)) e := by
  induction e <;> simp_all [subst]

end Expr

/-- A strictly positive natural number. -/
abbrev PosNat := {n : Nat // 0 < n}

/-- Unary natural expressions. -/
abbrev UnaryExpr := Expr Unit

namespace UnaryExpr

/-- Evaluate a unary expression at a positive natural number. -/
def eval (e : UnaryExpr) (n : PosNat) : Nat :=
  Expr.eval (fun _ => n.1) e

/-- Equality of the functions represented on the positive natural numbers. -/
def SemEq (s t : UnaryExpr) : Prop :=
  ∀ n : PosNat, eval s n = eval t n

/-- A unary expression whose represented function is not a sum of two represented functions. -/
def AddAtomic (t : UnaryExpr) : Prop :=
  ¬ ∃ a b : UnaryExpr, SemEq t (.add a b)

/-- A unary expression representing a nonconstant function on positive naturals. -/
def Nonconstant (t : UnaryExpr) : Prop :=
  ∃ m n : PosNat, eval t m ≠ eval t n

theorem semEq_refl (t : UnaryExpr) : SemEq t t := by
  intro n
  rfl

theorem semEq_symm {s t : UnaryExpr} (h : SemEq s t) : SemEq t s := by
  intro n
  exact (h n).symm

theorem semEq_trans {s t u : UnaryExpr} (hst : SemEq s t) (htu : SemEq t u) : SemEq s u := by
  intro n
  exact (hst n).trans (htu n)

theorem eval_pos (e : UnaryExpr) (n : PosNat) : 0 < eval e n := by
  exact Expr.eval_pos (fun _ => n.1) (fun _ => n.2) e

/-- Every unary natural expression is nondecreasing on the positive naturals. -/
theorem eval_monotone (e : UnaryExpr) : Monotone (eval e) := by
  intro m n hmn
  induction e with
  | one => rfl
  | var x => simpa [eval] using hmn
  | add a b ha hb =>
      simpa [eval] using Nat.add_le_add ha hb
  | mul a b ha hb =>
      simpa [eval] using Nat.mul_le_mul ha hb
  | pow a b ha hb =>
      simp only [eval, Expr.eval]
      exact (Nat.pow_le_pow_left ha _).trans
        (Nat.pow_le_pow_right (eval_pos a n) hb)

/-- Evaluation at `2` detects exactly the expressions representing constant one. -/
theorem eval_two_eq_one_iff_semEq_one (e : UnaryExpr) :
    eval e ⟨2, by decide⟩ = 1 ↔ SemEq e .one := by
  constructor
  · intro he
    induction e with
    | one => exact semEq_refl _
    | var x => simp [eval] at he
    | add a b ha hb =>
        change eval a ⟨2, by decide⟩ + eval b ⟨2, by decide⟩ = 1 at he
        have hpa := eval_pos a ⟨2, by decide⟩
        have hpb := eval_pos b ⟨2, by decide⟩
        omega
    | mul a b ha hb =>
        change eval a ⟨2, by decide⟩ * eval b ⟨2, by decide⟩ = 1 at he
        have hab : eval a ⟨2, by decide⟩ = 1 ∧ eval b ⟨2, by decide⟩ = 1 := by
          have hpa := eval_pos a ⟨2, by decide⟩
          have hpb := eval_pos b ⟨2, by decide⟩
          constructor <;> nlinarith
        have haone := ha hab.1
        have hbone := hb hab.2
        intro n
        change eval a n * eval b n = 1
        rw [haone n, hbone n]
        rfl
    | pow a b ha hb =>
        change eval a ⟨2, by decide⟩ ^ eval b ⟨2, by decide⟩ = 1 at he
        have hbase : eval a ⟨2, by decide⟩ = 1 := by
          rcases Nat.pow_eq_one.mp he with h | h
          · exact h
          · have hp := eval_pos b ⟨2, by decide⟩
            omega
        have haone := ha hbase
        intro n
        change eval a n ^ eval b n = 1
        rw [haone n]
        exact Nat.one_pow _
  · intro he
    simpa [eval] using he ⟨2, by decide⟩

/-- A unary natural expression is not constant one exactly when its value at `2`
is strictly larger than one. -/
theorem not_semEq_one_iff_one_lt_eval_two (e : UnaryExpr) :
    ¬ SemEq e .one ↔ 1 < eval e ⟨2, by decide⟩ := by
  rw [← not_congr (eval_two_eq_one_iff_semEq_one e)]
  have hp := eval_pos e ⟨2, by decide⟩
  omega

/-- In particular, every nonconstant unary natural expression has value greater
than one at `2`. -/
theorem one_lt_eval_two_of_nonconstant {e : UnaryExpr} (he : Nonconstant e) :
    1 < eval e ⟨2, by decide⟩ := by
  rw [← not_semEq_one_iff_one_lt_eval_two]
  rintro hone
  rcases he with ⟨m, n, hmn⟩
  exact hmn ((hone m).trans (hone n).symm)

/-- Additive atomicity depends only on the represented function. -/
theorem addAtomic_congr {s t : UnaryExpr} (h : SemEq s t) : AddAtomic s ↔ AddAtomic t := by
  constructor
  · intro hs ht
    rcases ht with ⟨a, b, htab⟩
    exact hs ⟨a, b, semEq_trans h htab⟩
  · intro ht hs
    rcases hs with ⟨a, b, hsab⟩
    exact ht ⟨a, b, semEq_trans (semEq_symm h) hsab⟩

/-- Nonconstancy depends only on the represented function. -/
theorem nonconstant_congr {s t : UnaryExpr} (h : SemEq s t) :
    Nonconstant s ↔ Nonconstant t := by
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    intro htn
    apply hmn
    exact (h m).trans (htn.trans (h n).symm)
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    intro hsn
    apply hmn
    exact (h m).symm.trans (hsn.trans (h n))

/-- Being nonconstant is equivalent to not representing a positive constant. -/
theorem nonconstant_iff_not_semEq_posConst (t : UnaryExpr) :
    Nonconstant t ↔ ¬ ∃ k : Nat, SemEq t (Expr.posConst k) := by
  constructor
  · rintro ⟨m, n, hmn⟩ ⟨k, hk⟩
    apply hmn
    calc
      eval t m = eval (Expr.posConst k) m := hk m
      _ = k + 1 := by simp [UnaryExpr.eval]
      _ = eval (Expr.posConst k) n := by simp [UnaryExpr.eval]
      _ = eval t n := (hk n).symm
  · intro h
    by_contra hconstant
    have hall : ∀ m n : PosNat, eval t m = eval t n := by
      intro m n
      by_contra hne
      exact hconstant ⟨m, n, hne⟩
    let one : PosNat := ⟨1, by decide⟩
    have hpositive := eval_pos t one
    apply h
    refine ⟨eval t one - 1, ?_⟩
    intro n
    calc
      eval t n = eval t one := hall n one
      _ = (eval t one - 1) + 1 := by omega
      _ = eval (Expr.posConst (eval t one - 1)) n := by
        simp [UnaryExpr.eval]

/-- The constant-one function is additively atomic. -/
theorem one_addAtomic : AddAtomic (.one : UnaryExpr) := by
  rintro ⟨a, b, h⟩
  let n : PosNat := ⟨1, by decide⟩
  have heq : 1 = eval a n + eval b n := by
    simpa [n, UnaryExpr.eval] using h n
  have ha := eval_pos a n
  have hb := eval_pos b n
  omega

/-- The identity function is nonconstant. -/
theorem variable_nonconstant : Nonconstant (.var () : UnaryExpr) := by
  refine ⟨⟨1, by decide⟩, ⟨2, by decide⟩, ?_⟩
  norm_num [eval, Expr.eval]

/-- The identity function is additively atomic. -/
theorem variable_addAtomic : AddAtomic (.var () : UnaryExpr) := by
  rintro ⟨a, b, h⟩
  let n : PosNat := ⟨1, by decide⟩
  have heq : 1 = eval a n + eval b n := by
    simpa [n, UnaryExpr.eval] using h n
  have ha := eval_pos a n
  have hb := eval_pos b n
  omega

/-- Atomicity of a product implies atomicity of its left factor. -/
theorem addAtomic_of_mul_left {a b : UnaryExpr} (h : AddAtomic (.mul a b)) :
    AddAtomic a := by
  rintro ⟨s, t, hst⟩
  apply h
  refine ⟨.mul s b, .mul t b, ?_⟩
  intro n
  have hst' : Expr.eval (fun _ ↦ n.1) a =
      Expr.eval (fun _ ↦ n.1) s + Expr.eval (fun _ ↦ n.1) t := by
    simpa [UnaryExpr.eval] using hst n
  simp only [UnaryExpr.eval, Expr.eval]
  rw [hst', Nat.add_mul]

/-- Atomicity of a product implies atomicity of its right factor. -/
theorem addAtomic_of_mul_right {a b : UnaryExpr} (h : AddAtomic (.mul a b)) :
    AddAtomic b := by
  rintro ⟨s, t, hst⟩
  apply h
  refine ⟨.mul a s, .mul a t, ?_⟩
  intro n
  have hst' : Expr.eval (fun _ ↦ n.1) b =
      Expr.eval (fun _ ↦ n.1) s + Expr.eval (fun _ ↦ n.1) t := by
    simpa [UnaryExpr.eval] using hst n
  simp only [UnaryExpr.eval, Expr.eval]
  rw [hst', Nat.mul_add]

/-- Atomicity of a product implies atomicity of both factors. -/
theorem addAtomic_factors {a b : UnaryExpr} (h : AddAtomic (.mul a b)) :
    AddAtomic a ∧ AddAtomic b :=
  ⟨addAtomic_of_mul_left h, addAtomic_of_mul_right h⟩

/-- If a positive constant power is atomic, then its base is atomic. -/
theorem addAtomic_of_pow_posConst {a : UnaryExpr} (k : Nat)
    (h : AddAtomic (.pow a (Expr.posConst k))) : AddAtomic a := by
  rintro ⟨s, t, hst⟩
  cases k with
  | zero =>
      apply h
      refine ⟨s, t, ?_⟩
      intro n
      simpa [UnaryExpr.eval] using hst n
  | succ k =>
      apply h
      refine ⟨.mul s (.pow a (Expr.posConst k)),
        .mul t (.pow a (Expr.posConst k)), ?_⟩
      intro n
      have hst' : Expr.eval (fun _ ↦ n.1) a =
          Expr.eval (fun _ ↦ n.1) s + Expr.eval (fun _ ↦ n.1) t := by
        simpa [UnaryExpr.eval] using hst n
      simp only [UnaryExpr.eval, Expr.eval, Expr.eval_posConst]
      calc
        Expr.eval (fun _ ↦ n.1) a ^ ((k + 1) + 1) =
            Expr.eval (fun _ ↦ n.1) a ^ (k + 1) *
              Expr.eval (fun _ ↦ n.1) a := by rw [pow_succ]
        _ = Expr.eval (fun _ ↦ n.1) a ^ (k + 1) *
              (Expr.eval (fun _ ↦ n.1) s + Expr.eval (fun _ ↦ n.1) t) := by
              rw [hst']
        _ = Expr.eval (fun _ ↦ n.1) s * Expr.eval (fun _ ↦ n.1) a ^ (k + 1) +
              Expr.eval (fun _ ↦ n.1) t * Expr.eval (fun _ ↦ n.1) a ^ (k + 1) := by
              ring

/-- The function `n ↦ n + 1` is not additively atomic. -/
theorem variable_add_one_not_atomic :
    ¬ AddAtomic (.add (.var ()) .one : UnaryExpr) := by
  intro h
  exact h ⟨.var (), .one, semEq_refl _⟩

/-- The expression `(n + 1)^1` witnesses why exponent nonconstancy is needed. -/
theorem variable_add_one_pow_one_not_atomic :
    ¬ AddAtomic (.pow (.add (.var ()) .one) .one : UnaryExpr) := by
  intro h
  apply h
  refine ⟨.var (), .one, ?_⟩
  intro n
  simp [UnaryExpr.eval]

/-- The base `1` is permitted: every represented power of it is atomic. -/
theorem one_pow_addAtomic (g : UnaryExpr) : AddAtomic (.pow .one g) := by
  apply (addAtomic_congr (t := (.one : UnaryExpr)) ?_).2 one_addAtomic
  intro n
  simp [UnaryExpr.eval]

end UnaryExpr

end Natfunbasis
