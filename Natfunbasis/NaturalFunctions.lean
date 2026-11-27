import Natfunbasis.Expressions

/-!
# Extensional natural functions

A `NaturalFunction` is a function on the strictly positive natural numbers
which is represented by a unary expression.  Equality is ordinary function
equality, so different expressions representing the same function determine
the same element of this type.
-/

namespace Natfunbasis

/-- An extensionally represented unary natural function. -/
def NaturalFunction :=
  {f : PosNat → Nat // ∃ e : UnaryExpr, ∀ n, f n = UnaryExpr.eval e n}

namespace NaturalFunction

/-- Regard a unary expression as the natural function that it represents. -/
def ofExpr (e : UnaryExpr) : NaturalFunction :=
  ⟨UnaryExpr.eval e, e, fun _ ↦ rfl⟩

instance : CoeFun NaturalFunction (fun _ ↦ PosNat → Nat) :=
  ⟨fun f ↦ f.1⟩

@[simp]
theorem ofExpr_apply (e : UnaryExpr) (n : PosNat) :
    ofExpr e n = UnaryExpr.eval e n :=
  rfl

/-- Every natural function has an expression representative. -/
theorem exists_expr (f : NaturalFunction) :
    ∃ e : UnaryExpr, ∀ n, f n = UnaryExpr.eval e n :=
  f.2

/-- Equality of natural functions is pointwise equality. -/
@[ext]
theorem ext {f g : NaturalFunction} (h : ∀ n, f n = g n) : f = g := by
  apply Subtype.ext
  exact funext h

/-- Equality of represented functions is precisely semantic equality. -/
theorem ofExpr_eq_iff {e d : UnaryExpr} :
    ofExpr e = ofExpr d ↔ UnaryExpr.SemEq e d := by
  constructor
  · intro h n
    have := congrArg (fun f : NaturalFunction ↦ f n) h
    simpa using this
  · intro h
    exact ext h

/-- Every value of a natural function is strictly positive. -/
theorem apply_pos (f : NaturalFunction) (n : PosNat) : 0 < f n := by
  obtain ⟨e, he⟩ := f.2
  rw [he n]
  exact UnaryExpr.eval_pos e n

/-- The constant-one natural function. -/
protected def one : NaturalFunction :=
  ofExpr .one

/-- Pointwise addition of natural functions. -/
protected def add (f g : NaturalFunction) : NaturalFunction :=
  ⟨fun n ↦ f n + g n, by
    obtain ⟨e, he⟩ := f.2
    obtain ⟨d, hd⟩ := g.2
    refine ⟨.add e d, fun n ↦ ?_⟩
    simp [he n, hd n, UnaryExpr.eval]⟩

/-- Pointwise multiplication of natural functions. -/
protected def mul (f g : NaturalFunction) : NaturalFunction :=
  ⟨fun n ↦ f n * g n, by
    obtain ⟨e, he⟩ := f.2
    obtain ⟨d, hd⟩ := g.2
    refine ⟨.mul e d, fun n ↦ ?_⟩
    simp [he n, hd n, UnaryExpr.eval]⟩

/-- Pointwise exponentiation of natural functions. -/
protected def pow (f g : NaturalFunction) : NaturalFunction :=
  ⟨fun n ↦ f n ^ g n, by
    obtain ⟨e, he⟩ := f.2
    obtain ⟨d, hd⟩ := g.2
    refine ⟨.pow e d, fun n ↦ ?_⟩
    simp [he n, hd n, UnaryExpr.eval]⟩

instance : AddCommSemigroup NaturalFunction where
  add := NaturalFunction.add
  add_assoc f g h := by
    ext n
    exact Nat.add_assoc _ _ _
  add_comm f g := by
    ext n
    exact Nat.add_comm _ _

instance : CommMonoid NaturalFunction where
  one := NaturalFunction.one
  mul := NaturalFunction.mul
  one_mul f := by
    ext n
    exact Nat.one_mul _
  mul_one f := by
    ext n
    exact Nat.mul_one _
  mul_assoc f g h := by
    ext n
    exact Nat.mul_assoc _ _ _
  mul_comm f g := by
    ext n
    exact Nat.mul_comm _ _

instance : HPow NaturalFunction NaturalFunction NaturalFunction where
  hPow := NaturalFunction.pow

@[simp]
theorem one_apply (n : PosNat) : (1 : NaturalFunction) n = 1 :=
  rfl

@[simp]
theorem add_apply (f g : NaturalFunction) (n : PosNat) :
    (f + g) n = f n + g n :=
  rfl

@[simp]
theorem mul_apply (f g : NaturalFunction) (n : PosNat) :
    (f * g) n = f n * g n :=
  rfl

@[simp]
theorem pow_apply (f g : NaturalFunction) (n : PosNat) :
    (f ^ g) n = f n ^ g n :=
  rfl

/-- The input natural function `n ↦ n`. -/
def input : NaturalFunction :=
  ofExpr (.var ())

@[simp]
theorem input_apply (n : PosNat) : input n = n.1 :=
  rfl

@[simp]
theorem ofExpr_one : ofExpr .one = 1 :=
  rfl

@[simp]
theorem ofExpr_add (e d : UnaryExpr) :
    ofExpr (.add e d) = ofExpr e + ofExpr d :=
  rfl

@[simp]
theorem ofExpr_mul (e d : UnaryExpr) :
    ofExpr (.mul e d) = ofExpr e * ofExpr d :=
  rfl

@[simp]
theorem ofExpr_pow (e d : UnaryExpr) :
    ofExpr (.pow e d) = ofExpr e ^ ofExpr d :=
  rfl

/-- A natural function is additively atomic if it is not a sum of two natural
functions. -/
def AddAtomic (f : NaturalFunction) : Prop :=
  ¬ ∃ a b : NaturalFunction, f = a + b

/-- A natural function is nonconstant if it takes two different values. -/
def Nonconstant (f : NaturalFunction) : Prop :=
  ∃ m n : PosNat, f m ≠ f n

/-- The function represented by an expression is additively atomic exactly
when the expression is additively atomic under semantic equality. -/
@[simp]
theorem ofExpr_addAtomic_iff (e : UnaryExpr) :
    AddAtomic (ofExpr e) ↔ UnaryExpr.AddAtomic e := by
  constructor
  · intro hf
    rintro ⟨a, b, hab⟩
    apply hf
    refine ⟨ofExpr a, ofExpr b, ?_⟩
    calc
      ofExpr e = ofExpr (.add a b) := ofExpr_eq_iff.mpr hab
      _ = ofExpr a + ofExpr b := ofExpr_add a b
  · intro he
    rintro ⟨f, g, hfg⟩
    obtain ⟨a, ha⟩ := exists_expr f
    obtain ⟨b, hb⟩ := exists_expr g
    have hfa : f = ofExpr a := ext ha
    have hgb : g = ofExpr b := ext hb
    apply he
    refine ⟨a, b, ofExpr_eq_iff.mp ?_⟩
    calc
      ofExpr e = f + g := hfg
      _ = ofExpr a + ofExpr b := by rw [hfa, hgb]
      _ = ofExpr (.add a b) := (ofExpr_add a b).symm

/-- The function represented by an expression is nonconstant exactly when the
expression is nonconstant under the unary semantics. -/
@[simp]
theorem ofExpr_nonconstant_iff (e : UnaryExpr) :
    Nonconstant (ofExpr e) ↔ UnaryExpr.Nonconstant e :=
  Iff.rfl

/-- The constant-one natural function is additively atomic. -/
theorem one_addAtomic : AddAtomic (1 : NaturalFunction) := by
  rw [← ofExpr_one, ofExpr_addAtomic_iff]
  exact UnaryExpr.one_addAtomic

/-- The input natural function is additively atomic. -/
theorem input_addAtomic : AddAtomic input := by
  exact (ofExpr_addAtomic_iff (.var ())).mpr UnaryExpr.variable_addAtomic

/-- The input natural function is nonconstant. -/
theorem input_nonconstant : Nonconstant input := by
  exact (ofExpr_nonconstant_iff (.var ())).mpr UnaryExpr.variable_nonconstant

end NaturalFunction

end Natfunbasis
