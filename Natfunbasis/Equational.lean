import Natfunbasis.Expressions

/-!
# Equational syntax for the eleven high-school identities

This module encodes exactly the original language `{1, +, *, ^}`, the eleven
HSI axiom schemes, and ordinary equational derivations.  The soundness theorem
is model-generic: every derivation is valid in every algebra satisfying HSI.
-/

namespace Natfunbasis

/-- An interpretation of the four operation symbols in the original language. -/
structure ExprAlgebra (A : Type*) where
  one : A
  add : A → A → A
  mul : A → A → A
  pow : A → A → A

namespace Expr

variable {Var W A : Type*}

/-- Evaluate an expression in an arbitrary algebra for the original signature. -/
@[simp]
def evalIn (M : ExprAlgebra A) (assignment : Var → A) : Expr Var → A
  | .one => M.one
  | .var x => assignment x
  | .add s t => M.add (evalIn M assignment s) (evalIn M assignment t)
  | .mul s t => M.mul (evalIn M assignment s) (evalIn M assignment t)
  | .pow s t => M.pow (evalIn M assignment s) (evalIn M assignment t)

@[simp]
theorem evalIn_subst (M : ExprAlgebra A) (assignment : W → A)
    (substitution : Var → Expr W) (e : Expr Var) :
    evalIn M assignment (Expr.subst substitution e) =
      evalIn M (fun x ↦ evalIn M assignment (substitution x)) e := by
  induction e <;> simp_all [Expr.subst]

end Expr

/-- An algebra satisfying exactly the eleven high-school identities. -/
structure HSIModel (A : Type*) extends ExprAlgebra A where
  add_comm_axiom : ∀ x y, add x y = add y x
  add_assoc_axiom : ∀ x y z, add x (add y z) = add (add x y) z
  mul_comm_axiom : ∀ x y, mul x y = mul y x
  mul_assoc_axiom : ∀ x y z, mul x (mul y z) = mul (mul x y) z
  left_distrib_axiom : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_one_axiom : ∀ x, mul x one = x
  pow_add_axiom : ∀ x y z, pow x (add y z) = mul (pow x y) (pow x z)
  mul_pow_axiom : ∀ x y z, pow (mul x y) z = mul (pow x z) (pow y z)
  pow_pow_axiom : ∀ x y z, pow (pow x y) z = pow x (mul y z)
  one_pow_axiom : ∀ x, pow one x = one
  pow_one_axiom : ∀ x, pow x one = x

/-- The eleven HSI axiom schemes, already closed under term instantiation. -/
inductive HSIAxiom {Var : Type*} : Expr Var → Expr Var → Prop where
  | add_comm (x y) : HSIAxiom (.add x y) (.add y x)
  | add_assoc (x y z) : HSIAxiom (.add x (.add y z)) (.add (.add x y) z)
  | mul_comm (x y) : HSIAxiom (.mul x y) (.mul y x)
  | mul_assoc (x y z) : HSIAxiom (.mul x (.mul y z)) (.mul (.mul x y) z)
  | left_distrib (x y z) :
      HSIAxiom (.mul x (.add y z)) (.add (.mul x y) (.mul x z))
  | mul_one (x) : HSIAxiom (.mul x .one) x
  | pow_add (x y z) : HSIAxiom (.pow x (.add y z)) (.mul (.pow x y) (.pow x z))
  | mul_pow (x y z) : HSIAxiom (.pow (.mul x y) z) (.mul (.pow x z) (.pow y z))
  | pow_pow (x y z) : HSIAxiom (.pow (.pow x y) z) (.pow x (.mul y z))
  | one_pow (x) : HSIAxiom (.pow .one x) .one
  | pow_one (x) : HSIAxiom (.pow x .one) x

universe u

/-- Standard equational derivability: axioms, equivalence rules, substitution,
and congruence for every operation symbol. -/
inductive Derives (rules : ∀ {Var : Type u}, Expr Var → Expr Var → Prop) :
    {Var : Type u} → Expr Var → Expr Var → Prop where
  | of_rule {Var} {s t : Expr Var} : rules s t → Derives rules s t
  | refl {Var} (s : Expr Var) : Derives rules s s
  | symm {Var} {s t : Expr Var} : Derives rules s t → Derives rules t s
  | trans {Var} {s t u : Expr Var} :
      Derives rules s t → Derives rules t u → Derives rules s u
  | subst {Var W} {s t : Expr Var} :
      Derives rules s t → (substitution : Var → Expr W) →
      Derives rules (Expr.subst substitution s) (Expr.subst substitution t)
  | add_congr {Var} {s₁ s₂ t₁ t₂ : Expr Var} :
      Derives rules s₁ t₁ → Derives rules s₂ t₂ →
      Derives rules (.add s₁ s₂) (.add t₁ t₂)
  | mul_congr {Var} {s₁ s₂ t₁ t₂ : Expr Var} :
      Derives rules s₁ t₁ → Derives rules s₂ t₂ →
      Derives rules (.mul s₁ s₂) (.mul t₁ t₂)
  | pow_congr {Var} {s₁ s₂ t₁ t₂ : Expr Var} :
      Derives rules s₁ t₁ → Derives rules s₂ t₂ →
      Derives rules (.pow s₁ s₂) (.pow t₁ t₂)

/-- The universe-polymorphic family of HSI axiom instances. -/
def HSIRules {Var : Type u} (s t : Expr Var) : Prop := HSIAxiom s t

/-- Derivability from the eleven HSI schemes. -/
abbrev HSIDerives {Var : Type u} (s t : Expr Var) : Prop :=
  Derives HSIRules s t

namespace HSIAxiom

variable {Var A : Type*} {s t : Expr Var}

/-- Each HSI axiom instance is valid in every HSI model. -/
theorem sound (M : HSIModel A) (assignment : Var → A) (h : HSIAxiom s t) :
    Expr.evalIn M.toExprAlgebra assignment s = Expr.evalIn M.toExprAlgebra assignment t := by
  cases h with
  | add_comm => exact M.add_comm_axiom _ _
  | add_assoc => exact M.add_assoc_axiom _ _ _
  | mul_comm => exact M.mul_comm_axiom _ _
  | mul_assoc => exact M.mul_assoc_axiom _ _ _
  | left_distrib => exact M.left_distrib_axiom _ _ _
  | mul_one => exact M.mul_one_axiom _
  | pow_add => exact M.pow_add_axiom _ _ _
  | mul_pow => exact M.mul_pow_axiom _ _ _
  | pow_pow => exact M.pow_pow_axiom _ _ _
  | one_pow => exact M.one_pow_axiom _
  | pow_one => exact M.pow_one_axiom _

end HSIAxiom

namespace HSIDerives

variable {Var A : Type*} {s t : Expr Var}

/-- Model-generic soundness of ordinary equational derivations from HSI. -/
theorem sound (h : HSIDerives s t) (M : HSIModel A) (assignment : Var → A) :
    Expr.evalIn M.toExprAlgebra assignment s = Expr.evalIn M.toExprAlgebra assignment t := by
  induction h with
  | of_rule hax => exact hax.sound M assignment
  | refl => rfl
  | symm h ih => exact (ih assignment).symm
  | trans hst htu ihst ihtU => exact (ihst assignment).trans (ihtU assignment)
  | subst h substitution ih =>
      rw [Expr.evalIn_subst, Expr.evalIn_subst]
      exact ih (fun x ↦ Expr.evalIn M.toExprAlgebra assignment (substitution x))
  | add_congr h₁ h₂ ih₁ ih₂ =>
      exact congrArg₂ M.add (ih₁ assignment) (ih₂ assignment)
  | mul_congr h₁ h₂ ih₁ ih₂ =>
      exact congrArg₂ M.mul (ih₁ assignment) (ih₂ assignment)
  | pow_congr h₁ h₂ ih₁ ih₂ =>
      exact congrArg₂ M.pow (ih₁ assignment) (ih₂ assignment)

end HSIDerives

/-- The usual natural-number operations form an HSI model. -/
def natHSIModel : HSIModel Nat where
  one := 1
  add := Nat.add
  mul := Nat.mul
  pow := Nat.pow
  add_comm_axiom := Nat.add_comm
  add_assoc_axiom := fun x y z ↦ (Nat.add_assoc x y z).symm
  mul_comm_axiom := Nat.mul_comm
  mul_assoc_axiom := fun x y z ↦ (Nat.mul_assoc x y z).symm
  left_distrib_axiom := Nat.mul_add
  mul_one_axiom := Nat.mul_one
  pow_add_axiom := Nat.pow_add
  mul_pow_axiom := Nat.mul_pow
  pow_pow_axiom := fun x y z ↦ (pow_mul x y z).symm
  one_pow_axiom := one_pow
  pow_one_axiom := pow_one

@[simp]
theorem evalIn_natHSIModel {Var : Type u} (assignment : Var → Nat) (e : Expr Var) :
    Expr.evalIn natHSIModel.toExprAlgebra assignment e = Expr.eval assignment e := by
  induction e <;> simp_all [natHSIModel]

/-- In particular, every HSI derivation is sound on positive natural assignments. -/
theorem hsiDerives_semEq {Var : Type u} {s t : Expr Var} (h : HSIDerives s t) :
    Expr.SemEq s t := by
  intro assignment hpositive
  simpa using h.sound natHSIModel assignment

end Natfunbasis
