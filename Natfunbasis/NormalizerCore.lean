import Natfunbasis.Equational

/-!
# The unconditional core of one-variable normalization

This module formalizes the part of the polynomial normalizer that does not use
Wilkie's generator existence or independence theorem.  It has two layers.

* `rawPolynomial` regards every syntactic power as a fresh variable.  It is
  exactly compatible with arbitrary expression substitution, via
  `MvPolynomial.bind₁`.
* `normalize` recursively performs the `1`, variable, addition,
  multiplication, and constant-exponent cases.  A power with a genuinely
  nonconstant normalized exponent is deliberately left as an `Atom.power`.

The unresolved power branch is precisely where the fixed (W1)--(W3) generator
system is needed in AJK Lemma 2.6: its base must be factored, auxiliary-variable
bases must be flattened, and each resulting base/exponent pair must be found
in the common enumeration.  Giving each unresolved syntactic power its own
variable is sound for evaluation, but is *not* a faithful common Wilkie normal
form and therefore cannot be used to instantiate `NormalFormPackage`.

The final section proves, in the actual HSI derivation system, the finite
exponent-splitting, product-distribution, constant-positive-power, and
flattening identities used by that missing branch.  No theorem in this file
uses a project-specific unproved axiom, opaque declaration, admitted proof
placeholder, or normal-form theorem parameter. Noncomputable choices use Lean's ordinary
`Classical.choice`.
-/

namespace Natfunbasis

open MvPolynomial

namespace NormalizerCore

noncomputable section

universe u v

/-- Variables of the elementary polynomialization.  Original variables remain
distinguished; an unresolved power records its complete syntactic base and
exponent so that its intended evaluation is unambiguous. -/
inductive Atom (Var : Type u) where
  | original : Var → Atom Var
  | power : Expr Var → Expr Var → Atom Var
  deriving DecidableEq, Repr

namespace Atom

variable {Var : Type u}

/-- The evaluation of a raw atom induced by an assignment of the original
variables. -/
@[simp]
def interpret (assignment : Var → Nat) : Atom Var → Nat
  | .original x => assignment x
  | .power base exponent =>
      Expr.eval assignment base ^ Expr.eval assignment exponent

end Atom

variable {Var : Type u} {W : Type v}

/-- Polynomialize the semiring structure of an expression, regarding each
whole power subterm as an opaque variable. -/
@[simp]
def rawPolynomial : Expr Var → MvPolynomial (Atom Var) Nat
  | .one => 1
  | .var x => X (.original x)
  | .add s t => rawPolynomial s + rawPolynomial t
  | .mul s t => rawPolynomial s * rawPolynomial t
  | .pow s t => X (.power s t)

/-- Raw polynomialization is exactly correct under the intended evaluation of
its original-variable and power atoms. -/
theorem eval_rawPolynomial (assignment : Var → Nat) (e : Expr Var) :
    MvPolynomial.eval (Atom.interpret assignment) (rawPolynomial e) =
      Expr.eval assignment e := by
  induction e <;> simp_all [Atom.interpret]

/-- Consequently the raw polynomial of an expression is never zero. -/
theorem rawPolynomial_ne_zero (e : Expr Var) : rawPolynomial e ≠ 0 := by
  intro hzero
  let assignment : Var → Nat := fun _ ↦ 1
  have hpositive : Expr.PositiveAssignment assignment := by
    intro x
    simp [assignment]
  have heval : Expr.eval assignment e = 0 := by
    calc
      Expr.eval assignment e =
          MvPolynomial.eval (Atom.interpret assignment) (rawPolynomial e) :=
        (eval_rawPolynomial assignment e).symm
      _ = MvPolynomial.eval (Atom.interpret assignment) 0 := by rw [hzero]
      _ = 0 := by simp
  exact (Nat.ne_of_gt (Expr.eval_pos assignment hpositive e)) heval

/-- The polynomial substituted for a raw atom when an expression substitution
is performed.  Original variables receive their substituted polynomial;
power atoms remain atoms, with the substitution recursively applied to their
recorded base and exponent. -/
def atomSubstitution (substitution : Var → Expr W) :
    Atom Var → MvPolynomial (Atom W) Nat
  | .original x => rawPolynomial (substitution x)
  | .power base exponent =>
      X (.power (Expr.subst substitution base)
        (Expr.subst substitution exponent))

/-- Raw polynomialization commutes exactly with arbitrary expression
substitution.  `bind₁` is polynomial substitution in the variable type. -/
theorem rawPolynomial_subst (substitution : Var → Expr W) (e : Expr Var) :
    rawPolynomial (Expr.subst substitution e) =
      MvPolynomial.bind₁ (atomSubstitution substitution) (rawPolynomial e) := by
  induction e <;>
    simp_all [Expr.subst, rawPolynomial, atomSubstitution]

/-- In particular, an unresolved raw power is a coefficient-one,
nonconstant monomial. -/
theorem rawPolynomial_pow_is_monomial (base exponent : Expr Var) :
    ∃ m : Atom Var →₀ Nat, m ≠ 0 ∧
      rawPolynomial (.pow base exponent) = monomial m 1 := by
  refine ⟨Finsupp.single (.power base exponent) 1, ?_, ?_⟩
  · exact Finsupp.single_ne_zero.mpr one_ne_zero
  · rfl

/-- A polynomial is constant when it equals the embedding of its own constant
coefficient.  This formulation makes the value canonical. -/
def IsConstant {A : Type*} (p : MvPolynomial A Nat) : Prop :=
  p = C (constantCoeff p)

/-- A classical conditional used to keep the normalizer independent of a
decidable-equality assumption on its variable type. -/
private noncomputable def ifProp {A : Type*} (p : Prop) (yes no : A) : A :=
  @ite A p (Classical.propDecidable p) yes no

/-- The unconditional recursive normalizer.  Its only unresolved case is a
power whose recursively normalized exponent is nonconstant. -/
def normalize : Expr Var → MvPolynomial (Atom Var) Nat
  | .one => 1
  | .var x => X (.original x)
  | .add s t => normalize s + normalize t
  | .mul s t => normalize s * normalize t
  | .pow base exponent =>
      ifProp (IsConstant (normalize exponent))
        (normalize base ^ constantCoeff (normalize exponent))
        (X (.power base exponent))

@[simp]
theorem normalize_one : normalize (.one : Expr Var) = 1 := rfl

@[simp]
theorem normalize_var (x : Var) : normalize (.var x) = X (.original x) := rfl

@[simp]
theorem normalize_add (s t : Expr Var) :
    normalize (.add s t) = normalize s + normalize t := rfl

@[simp]
theorem normalize_mul (s t : Expr Var) :
    normalize (.mul s t) = normalize s * normalize t := rfl

/-- The completed constant-exponent branch of the normalizer. -/
theorem normalize_pow_of_constant (base exponent : Expr Var)
    (hexponent : IsConstant (normalize exponent)) :
    normalize (.pow base exponent) =
      normalize base ^ constantCoeff (normalize exponent) := by
  simp [normalize, ifProp, hexponent]

/-- The exact residual branch: no assertion is made that this syntactic atom
is a member of one common admissible Wilkie enumeration. -/
theorem normalize_pow_of_unresolved (base exponent : Expr Var)
    (hexponent : ¬ IsConstant (normalize exponent)) :
    normalize (.pow base exponent) = X (.power base exponent) := by
  simp [normalize, ifProp, hexponent]

/-- The recursive normalizer is correct for ordinary natural-number
evaluation, including both branches of exponentiation. -/
theorem eval_normalize (assignment : Var → Nat) (e : Expr Var) :
    MvPolynomial.eval (Atom.interpret assignment) (normalize e) =
      Expr.eval assignment e := by
  induction e with
  | one => simp
  | var x => simp [Atom.interpret]
  | add s t hs ht => simp [hs, ht]
  | mul s t hs ht => simp [hs, ht]
  | pow base exponent hbase hexponent =>
      by_cases hconstant : IsConstant (normalize exponent)
      · rw [normalize_pow_of_constant base exponent hconstant]
        have hexponentValue :
            Expr.eval assignment exponent = constantCoeff (normalize exponent) := by
          rw [← hexponent, hconstant]
          simp
        simp [hbase, hexponentValue]
      · rw [normalize_pow_of_unresolved base exponent hconstant]
        simp [Atom.interpret]

/-- The recursively normalized polynomial is always nonzero. -/
theorem normalize_ne_zero (e : Expr Var) : normalize e ≠ 0 := by
  intro hzero
  let assignment : Var → Nat := fun _ ↦ 1
  have hpositive : Expr.PositiveAssignment assignment := by
    intro x
    simp [assignment]
  have heval : Expr.eval assignment e = 0 := by
    calc
      Expr.eval assignment e =
          MvPolynomial.eval (Atom.interpret assignment) (normalize e) :=
        (eval_normalize assignment e).symm
      _ = MvPolynomial.eval (Atom.interpret assignment) 0 := by rw [hzero]
      _ = 0 := by simp
  exact (Nat.ne_of_gt (Expr.eval_pos assignment hpositive e)) heval

/-- Equality of core normal forms is a sound criterion for semantic equality.
The converse is exactly what fails without the common Wilkie generators and
their independence theorem. -/
theorem semEq_of_normalize_eq {s t : Expr Var} (h : normalize s = normalize t) :
    Expr.SemEq s t := by
  intro assignment hpositive
  rw [← eval_normalize assignment s, ← eval_normalize assignment t, h]

/-- If a normalized expression is constant, every evaluation has that
constant value. -/
theorem eval_eq_constant_of_normalize_constant (assignment : Var → Nat)
    (e : Expr Var) (h : IsConstant (normalize e)) :
    Expr.eval assignment e = constantCoeff (normalize e) := by
  rw [← eval_normalize assignment e, h]
  simp

/-- A genuinely nonconstant unary expression cannot enter the completed
constant-exponent branch. -/
theorem not_normalize_constant_of_nonconstant {e : UnaryExpr}
    (he : UnaryExpr.Nonconstant e) : ¬ IsConstant (normalize e) := by
  intro hconstant
  rcases he with ⟨m, n, hmn⟩
  apply hmn
  calc
    UnaryExpr.eval e m = constantCoeff (normalize e) := by
      simpa [UnaryExpr.eval] using
        eval_eq_constant_of_normalize_constant (fun _ ↦ m.1) e hconstant
    _ = UnaryExpr.eval e n := by
      symm
      simpa [UnaryExpr.eval] using
        eval_eq_constant_of_normalize_constant (fun _ ↦ n.1) e hconstant

/-- Thus the remaining power case for a nonconstant unary exponent is exactly
a nonconstant coefficient-one monomial in the temporary raw atom. -/
theorem normalize_pow_nonconstant_exponent_is_monomial
    (base exponent : UnaryExpr) (hexponent : UnaryExpr.Nonconstant exponent) :
    ∃ m : Atom Unit →₀ Nat, m ≠ 0 ∧
      normalize (.pow base exponent) = monomial m 1 := by
  have hunresolved := not_normalize_constant_of_nonconstant hexponent
  rw [normalize_pow_of_unresolved base exponent hunresolved]
  refine ⟨Finsupp.single (.power base exponent) 1, ?_, ?_⟩
  · exact Finsupp.single_ne_zero.mpr one_ne_zero
  · rfl

/-- Positive constants normalize to their natural-number coefficients. -/
@[simp]
theorem normalize_posConst (n : Nat) :
    normalize (Expr.posConst n : Expr Var) = C (n + 1) := by
  induction n with
  | zero => simp [Expr.posConst]
  | succ n ih =>
      simp [Expr.posConst, ih]

/-- The normalizer completely handles every literal positive constant
exponent. -/
theorem normalize_pow_posConst (base : Expr Var) (n : Nat) :
    normalize (.pow base (Expr.posConst n)) = normalize base ^ (n + 1) := by
  have hconstant :
      IsConstant (normalize (Expr.posConst n : Expr Var)) := by
    simp [IsConstant]
  rw [normalize_pow_of_constant base (Expr.posConst n) hconstant]
  simp

/-! ## The unconditional algebraic factorization step

AJK's nonconstant power case asserts a factorization of the nonzero
natural-coefficient base polynomial into its class of positive irreducibles.
Mathlib's UFD theorem first gives ordinary irreducibles over `Int`.  To justify
the additional positivity built into AJK's assertion, each factor must be
replaced by an associate positive throughout the positive real orthant before
W2 applies.

Ordinary irreducibles here include single variables.  This makes explicit a
minor compression in AJK: the factorization line places every factor in its
nonvariable class `Irr`, although the immediately following subcases separately
handle original- and auxiliary-variable factors.  The W1 variable/nonvariable
split is therefore postponed rather than silently discarded.
-/

/-- A natural-coefficient polynomial other than `1` does not become a unit
after its coefficients are embedded into `Int`. -/
theorem not_isUnit_map_int_of_ne_one {A : Type*}
    (p : MvPolynomial A Nat) (hp : p ≠ 1) :
    ¬ IsUnit (MvPolynomial.map (Nat.castRingHom Int) p) := by
  intro hunit
  obtain ⟨r, hr, heq⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit)
  have hconstantCoeff : ((constantCoeff p : Nat) : Int) = r := by
    have := congrArg constantCoeff heq
    simpa using this
  rcases Int.isUnit_eq_one_or hr with hrOne | hrNegOne
  · apply hp
    apply MvPolynomial.map_injective (f := Nat.castRingHom Int)
      Int.ofNat_injective
    simpa [hrOne] using heq
  · have hnonnegative : (0 : Int) ≤ ((constantCoeff p : Nat) : Int) := by omega
    rw [hconstantCoeff, hrNegOne] at hnonnegative
    omega

/-- A nonzero natural-coefficient polynomial other than `1` has an exact,
nonempty factorization over `Int` into irreducibles.  The unit has already
been absorbed into one factor by mathlib's factorization theorem. -/
theorem exists_nonempty_irreducible_factorization {A : Type*}
    (p : MvPolynomial A Nat) (hpZero : p ≠ 0) (hpOne : p ≠ 1) :
    ∃ factors : Multiset (MvPolynomial A Int),
      (∀ q ∈ factors, Irreducible q) ∧
      factors.prod = MvPolynomial.map (Nat.castRingHom Int) p ∧
      factors ≠ 0 := by
  apply (WfDvdMonoid.not_unit_iff_exists_factors_eq
    (MvPolynomial.map (Nat.castRingHom Int) p) ?_).mp
  · exact not_isUnit_map_int_of_ne_one p hpOne
  · intro hzero
    apply hpZero
    apply MvPolynomial.map_injective (f := Nat.castRingHom Int)
      Int.ofNat_injective
    simpa using hzero

/-! ## Positivity of signed irreducible factors

This section supplies the topological sign argument implicit in AJK's choice
of positive irreducible factors; the paper does not spell this argument out.
It is stated for arbitrary variable types: the positive orthant is convex even
for an infinite product, while each polynomial depends on only finitely many
coordinates.
-/

/-- The strictly positive real orthant in the assignment space. -/
def positiveRealOrthant (A : Type*) : Set (A → Real) :=
  {assignment | ∀ i, 0 < assignment i}

@[simp]
theorem mem_positiveRealOrthant {A : Type*} {assignment : A → Real} :
    assignment ∈ positiveRealOrthant A ↔ ∀ i, 0 < assignment i :=
  Iff.rfl

/-- The positive real orthant is convex. -/
theorem convex_positiveRealOrthant (A : Type*) :
    Convex Real (positiveRealOrthant A) := by
  have hset : positiveRealOrthant A =
      Set.univ.pi (fun _ : A ↦ Set.Ioi (0 : Real)) := by
    ext assignment
    simp [positiveRealOrthant]
  rw [hset]
  exact convex_pi fun _ _ ↦ convex_Ioi 0

/-- The positive real orthant is nonempty. -/
theorem positiveRealOrthant_nonempty (A : Type*) :
    (positiveRealOrthant A).Nonempty := by
  refine ⟨fun _ ↦ 1, ?_⟩
  simp [positiveRealOrthant]

/-- Evaluate an integer-coefficient multivariate polynomial over `Real`. -/
def evalReal {A : Type*} (p : MvPolynomial A Int)
    (assignment : A → Real) : Real :=
  MvPolynomial.eval₂ (Int.castRingHom Real) assignment p

/-- Real evaluation of an integer polynomial is continuous in all its
variables. -/
theorem continuous_evalReal {A : Type*} (p : MvPolynomial A Int) :
    Continuous (evalReal p) := by
  change Continuous
    (fun assignment ↦ MvPolynomial.eval₂
      (Int.castRingHom Real) assignment p)
  have hfun :
      (fun assignment ↦ MvPolynomial.eval₂
        (Int.castRingHom Real) assignment p) =
      (fun assignment ↦ MvPolynomial.eval assignment
        (MvPolynomial.map (Int.castRingHom Real) p)) := by
    funext assignment
    exact MvPolynomial.eval₂_eq_eval_map
      (Int.castRingHom Real) assignment p
  rw [hfun]
  exact MvPolynomial.continuous_eval
    (MvPolynomial.map (Int.castRingHom Real) p)

/-- Positivity of an integer polynomial throughout the strictly positive real
orthant. -/
def PositiveOnRealOrthant {A : Type*} (p : MvPolynomial A Int) : Prop :=
  ∀ assignment, assignment ∈ positiveRealOrthant A →
    0 < evalReal p assignment

/-- Evaluate a natural-coefficient polynomial directly over `Real`. -/
def evalNatReal {A : Type*} (p : MvPolynomial A Nat)
    (assignment : A → Real) : Real :=
  MvPolynomial.eval₂ (Nat.castRingHom Real) assignment p

/-- A natural-coefficient polynomial has nonnegative value on every
nonnegative assignment. -/
theorem evalNatReal_nonnegative {A : Type*} (p : MvPolynomial A Nat)
    (assignment : A → Real) (hassignment : ∀ i, 0 ≤ assignment i) :
    0 ≤ evalNatReal p assignment := by
  induction p using MvPolynomial.induction_on with
  | C coefficient => simp [evalNatReal]
  | add p q hp hq =>
      simpa [evalNatReal] using add_nonneg hp hq
  | mul_X p i hp =>
      simpa [evalNatReal] using mul_nonneg hp (hassignment i)

/-- Evaluation at a strictly positive real assignment reflects zero for
polynomials with natural coefficients. -/
theorem eq_zero_of_evalNatReal_eq_zero {A : Type*}
    (assignment : A → Real) (hassignment : ∀ i, 0 < assignment i) :
    ∀ p : MvPolynomial A Nat, evalNatReal p assignment = 0 → p = 0 := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C coefficient =>
      intro hzero
      have : coefficient = 0 := by
        have hcast : (coefficient : Real) = 0 := by
          simpa [evalNatReal] using hzero
        exact_mod_cast hcast
      simp [this]
  | add p q hp hq =>
      intro hzero
      have hpNonnegative := evalNatReal_nonnegative p assignment
        (fun i ↦ (hassignment i).le)
      have hqNonnegative := evalNatReal_nonnegative q assignment
        (fun i ↦ (hassignment i).le)
      have hpZero : evalNatReal p assignment = 0 := by
        have : evalNatReal p assignment + evalNatReal q assignment = 0 := by
          simpa [evalNatReal] using hzero
        linarith
      have hqZero : evalNatReal q assignment = 0 := by
        have : evalNatReal p assignment + evalNatReal q assignment = 0 := by
          simpa [evalNatReal] using hzero
        linarith
      rw [hp hpZero, hq hqZero, zero_add]
  | mul_X p i hp =>
      intro hzero
      have hproduct : evalNatReal p assignment * assignment i = 0 := by
        simpa [evalNatReal] using hzero
      have hpZero : evalNatReal p assignment = 0 :=
        (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt (hassignment i))
      rw [hp hpZero, zero_mul]

/-- A nonzero natural-coefficient polynomial is strictly positive on every
strictly positive real assignment. -/
theorem evalNatReal_positive {A : Type*} (p : MvPolynomial A Nat)
    (hp : p ≠ 0) (assignment : A → Real)
    (hassignment : ∀ i, 0 < assignment i) :
    0 < evalNatReal p assignment := by
  have hnonnegative := evalNatReal_nonnegative p assignment
    (fun i ↦ (hassignment i).le)
  have hne : evalNatReal p assignment ≠ 0 := by
    intro hzero
    exact hp (eq_zero_of_evalNatReal_eq_zero assignment hassignment p hzero)
  exact lt_of_le_of_ne hnonnegative (Ne.symm hne)

/-- After embedding coefficients through `Nat → Int`, every nonzero
natural-coefficient polynomial is positive on the positive real orthant. -/
theorem map_nat_int_positiveOnRealOrthant {A : Type*}
    (p : MvPolynomial A Nat) (hp : p ≠ 0) :
    PositiveOnRealOrthant (MvPolynomial.map (Nat.castRingHom Int) p) := by
  intro assignment hassignment
  have hpositive := evalNatReal_positive p hp assignment hassignment
  change 0 < MvPolynomial.eval₂ (Int.castRingHom Real) assignment
    (MvPolynomial.map (Nat.castRingHom Int) p)
  rw [MvPolynomial.eval₂_map]
  have hcast :
      (Int.castRingHom Real).comp (Nat.castRingHom Int) =
        Nat.castRingHom Real := by
    ext n
    simp
  rw [hcast]
  exact hpositive

/-- A continuous nonvanishing real-valued function has one strict sign on the
connected positive orthant. -/
theorem continuous_strict_sign_on_positiveRealOrthant {A : Type*}
    {f : (A → Real) → Real} (hf : Continuous f)
    (hnonzero : ∀ assignment, assignment ∈ positiveRealOrthant A →
      f assignment ≠ 0) :
    (∀ assignment, assignment ∈ positiveRealOrthant A →
      0 < f assignment) ∨
    (∀ assignment, assignment ∈ positiveRealOrthant A →
      f assignment < 0) := by
  let origin : A → Real := fun _ ↦ 1
  have horigin : origin ∈ positiveRealOrthant A := by
    simp [origin, positiveRealOrthant]
  have hpreconnected : IsPreconnected (positiveRealOrthant A) :=
    (convex_positiveRealOrthant A).isPreconnected
  rcases lt_or_gt_of_ne (hnonzero origin horigin) with horiginNeg | horiginPos
  · right
    intro assignment hassignment
    exact hpreconnected.gt_of_ne hf.continuousOn hnonzero
      ⟨origin, horigin, horiginNeg⟩ hassignment
  · left
    intro assignment hassignment
    exact hpreconnected.lt_of_ne hf.continuousOn hnonzero
      ⟨origin, horigin, horiginPos⟩ hassignment

/-- Every factor of a polynomial positive on the positive orthant is nowhere
zero there.  Irreducibility is not needed for this step. -/
theorem factor_ne_zero_on_positiveRealOrthant {A : Type*}
    {factors : Multiset (MvPolynomial A Int)}
    (hpositive : PositiveOnRealOrthant factors.prod)
    {q : MvPolynomial A Int} (hq : q ∈ factors) :
    ∀ assignment, assignment ∈ positiveRealOrthant A →
      evalReal q assignment ≠ 0 := by
  intro assignment hassignment hqZero
  obtain ⟨rest, hfactor⟩ := Multiset.dvd_prod hq
  have hproductZero : evalReal factors.prod assignment = 0 := by
    rw [hfactor]
    change MvPolynomial.eval₂ (Int.castRingHom Real) assignment (q * rest) = 0
    change MvPolynomial.eval₂ (Int.castRingHom Real) assignment q = 0 at hqZero
    rw [MvPolynomial.eval₂_mul, hqZero, zero_mul]
  exact (ne_of_gt (hpositive assignment hassignment)) hproductZero

/-- Each factor of a positive product can be multiplied by `+1` or `-1` so
that it is positive throughout the positive real orthant.  Applied to the
irreducible factors above, this is exactly the sign-choice step required
before invoking W2. -/
theorem exists_sign_mul_factor_positive {A : Type*}
    {factors : Multiset (MvPolynomial A Int)}
    (hpositive : PositiveOnRealOrthant factors.prod)
    {q : MvPolynomial A Int} (hq : q ∈ factors) :
    ∃ sign : Int, (sign = 1 ∨ sign = -1) ∧
      PositiveOnRealOrthant (C sign * q) := by
  have hnonzero := factor_ne_zero_on_positiveRealOrthant hpositive hq
  rcases continuous_strict_sign_on_positiveRealOrthant
      (continuous_evalReal q) hnonzero with hqPositive | hqNegative
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro assignment hassignment
    simpa [evalReal] using hqPositive assignment hassignment
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro assignment hassignment
    have hnegative := hqNegative assignment hassignment
    have hnegPositive : 0 < -evalReal q assignment := neg_pos.mpr hnegative
    simpa [evalReal] using hnegPositive

/-- A finite product of polynomials positive on the positive real orthant is
again positive there. -/
theorem positiveOnRealOrthant_multiset_prod {A : Type*}
    (polynomials : Multiset (MvPolynomial A Int))
    (hpositive : ∀ p ∈ polynomials, PositiveOnRealOrthant p) :
    PositiveOnRealOrthant polynomials.prod := by
  induction polynomials using Multiset.induction_on with
  | empty =>
      intro assignment hassignment
      simp [evalReal]
  | @cons p polynomials ih =>
      have hp : PositiveOnRealOrthant p := hpositive p (by simp)
      have hrest : PositiveOnRealOrthant polynomials.prod :=
        ih (fun q hq ↦ hpositive q (by simp [hq]))
      intro assignment hassignment
      rw [Multiset.prod_cons]
      change 0 < MvPolynomial.eval₂ (Int.castRingHom Real) assignment
        (p * polynomials.prod)
      rw [MvPolynomial.eval₂_mul]
      exact mul_pos (hp assignment hassignment) (hrest assignment hassignment)

/-- Simultaneously choose signs for every occurrence in a factor multiset.
The mapped multiset preserves all multiplicities, every signed factor is
positive, and its product is *exactly* the original product.  This proves the
implicit `+1` unit forced by AJK's exact displayed factorization. -/
theorem exists_exact_positive_signing {A : Type*}
    (factors : Multiset (MvPolynomial A Int))
    (hpositive : PositiveOnRealOrthant factors.prod) :
    ∃ sign : MvPolynomial A Int → Int,
      (∀ q ∈ factors,
        (sign q = 1 ∨ sign q = -1) ∧
        PositiveOnRealOrthant (C (sign q) * q)) ∧
      (factors.map fun q ↦ C (sign q) * q).prod = factors.prod := by
  classical
  have hexists : ∀ q : MvPolynomial A Int, ∃ chosenSign : Int,
      q ∈ factors →
        (chosenSign = 1 ∨ chosenSign = -1) ∧
        PositiveOnRealOrthant (C chosenSign * q) := by
    intro q
    by_cases hq : q ∈ factors
    · obtain ⟨chosenSign, hsign, hqPositive⟩ :=
        exists_sign_mul_factor_positive hpositive hq
      exact ⟨chosenSign, fun _ ↦ ⟨hsign, hqPositive⟩⟩
    · exact ⟨1, fun h ↦ (hq h).elim⟩
  choose sign hsign using hexists
  have hproductFormula :
      (factors.map fun q ↦ C (sign q) * q).prod =
        C (factors.map sign).prod * factors.prod := by
    clear hpositive hsign
    induction factors using Multiset.induction_on with
    | empty => simp
    | @cons q factors ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        rw [ih]
        simp only [map_mul]
        ring
  have hsignedPositive :
      PositiveOnRealOrthant
        (factors.map fun q ↦ C (sign q) * q).prod := by
    apply positiveOnRealOrthant_multiset_prod
    intro signedFactor hsignedFactor
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hsignedFactor
    exact (hsign q hq).2
  have hsignsUnit : IsUnit (factors.map sign).prod := by
    refine Multiset.prod_induction (fun value : Int ↦ IsUnit value)
      (factors.map sign) ?_ ?_ ?_
    · intro left right hleft hright
      exact hleft.mul hright
    · simp
    · intro chosenSign hchosenSign
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hchosenSign
      rcases (hsign q hq).1 with hOne | hNegOne
      · simp [hOne]
      · simp [hNegOne]
  have hsignProduct : (factors.map sign).prod = 1 := by
    rcases Int.isUnit_eq_one_or hsignsUnit with hOne | hNegOne
    · exact hOne
    · exfalso
      let allOnes : A → Real := fun _ ↦ 1
      have hallOnes : allOnes ∈ positiveRealOrthant A := by
        simp [allOnes, positiveRealOrthant]
      have horiginalPositive := hpositive allOnes hallOnes
      have hsignedPositiveAt := hsignedPositive allOnes hallOnes
      have hevaluation := congrArg
        (fun p : MvPolynomial A Int ↦ evalReal p allOnes)
        hproductFormula
      have hevaluationNeg :
          evalReal (factors.map fun q ↦ C (sign q) * q).prod allOnes =
            -evalReal factors.prod allOnes := by
        simpa [hNegOne, evalReal] using hevaluation
      rw [hevaluationNeg] at hsignedPositiveAt
      linarith
  refine ⟨sign, ?_, ?_⟩
  · intro q hq
    exact hsign q hq
  · rw [hproductFormula, hsignProduct]
    simp

/-- The complete unconditional factorization-and-sign fragment of the AJK
power case.  What remains after this theorem is to classify each signed
irreducible as an admissible W1 base (with the special variable case split)
and use the joint W2 enumeration. -/
theorem exists_signed_irreducible_factorization {A : Type*}
    (p : MvPolynomial A Nat) (hpZero : p ≠ 0) (hpOne : p ≠ 1) :
    ∃ factors : Multiset (MvPolynomial A Int),
      (∀ q ∈ factors, Irreducible q) ∧
      factors.prod = MvPolynomial.map (Nat.castRingHom Int) p ∧
      factors ≠ 0 ∧
      ∀ q ∈ factors, ∃ sign : Int, (sign = 1 ∨ sign = -1) ∧
        PositiveOnRealOrthant (C sign * q) := by
  obtain ⟨factors, hirreducible, hproduct, hnonempty⟩ :=
    exists_nonempty_irreducible_factorization p hpZero hpOne
  refine ⟨factors, hirreducible, hproduct, hnonempty, ?_⟩
  have hpositive : PositiveOnRealOrthant factors.prod := by
    rw [hproduct]
    exact map_nat_int_positiveOnRealOrthant p hpZero
  intro q hq
  exact exists_sign_mul_factor_positive hpositive hq

/-- A source-compatible completion of the simultaneous sign step.  The raw
irreducible multiset and a sign function are returned explicitly; mapping each
occurrence through that sign preserves multiplicity and yields positive
irreducibles whose product is exactly the original integer embedding.

This is a noncomputable existence theorem for arbitrary variable types, not
AJK's finite-stage algorithm, and it does not yet separate individual
variables from the admissible nonvariable W1 bases. -/
theorem exists_exact_positive_irreducible_factorization {A : Type*}
    (p : MvPolynomial A Nat) (hpZero : p ≠ 0) (hpOne : p ≠ 1) :
    ∃ (factors : Multiset (MvPolynomial A Int))
      (sign : MvPolynomial A Int → Int),
      factors ≠ 0 ∧
      (∀ q ∈ factors, sign q = 1 ∨ sign q = -1) ∧
      (factors.map fun q ↦ C (sign q) * q).prod =
        MvPolynomial.map (Nat.castRingHom Int) p ∧
      ∀ q ∈ factors,
        Irreducible (C (sign q) * q) ∧
        PositiveOnRealOrthant (C (sign q) * q) := by
  obtain ⟨factors, hirreducible, hproduct, hnonempty⟩ :=
    exists_nonempty_irreducible_factorization p hpZero hpOne
  have hpositive : PositiveOnRealOrthant factors.prod := by
    rw [hproduct]
    exact map_nat_int_positiveOnRealOrthant p hpZero
  obtain ⟨sign, hsign, hsignedProduct⟩ :=
    exists_exact_positive_signing factors hpositive
  refine ⟨factors, sign, hnonempty, ?_, ?_, ?_⟩
  · intro q hq
    exact (hsign q hq).1
  · rw [hsignedProduct, hproduct]
  · intro q hq
    refine ⟨?_, (hsign q hq).2⟩
    have hsignUnit : IsUnit (sign q) := by
      rcases (hsign q hq).1 with hOne | hNegOne
      · simp [hOne]
      · simp [hNegOne]
    have hconstantUnit : IsUnit (C (sign q) : MvPolynomial A Int) :=
      hsignUnit.map C
    exact (irreducible_isUnit_mul hconstantUnit).mpr (hirreducible q hq)

/-! ## Exact HSI derivations used in the power branch -/

namespace PowerDerivations

/-- A right-associated sum with at least one term.  Avoiding an empty sum is
important because the original language has no zero constant. -/
def nonemptySum (head : Expr Var) : List (Expr Var) → Expr Var
  | [] => head
  | term :: terms => .add head (nonemptySum term terms)

/-- A right-associated product with at least one factor. -/
def nonemptyProduct (head : Expr Var) : List (Expr Var) → Expr Var
  | [] => head
  | factor :: factors => .mul head (nonemptyProduct factor factors)

/-- The product of the positive powers of all bases by one exponent. -/
def poweredProduct (base : Expr Var) (bases : List (Expr Var))
    (exponent : Expr Var) : Expr Var :=
  nonemptyProduct (.pow base exponent)
    (bases.map fun nextBase ↦ .pow nextBase exponent)

/-- The rectangular product obtained after splitting a nonempty exponent sum
and distributing each resulting power over a nonempty base product. -/
def powerGrid (base : Expr Var) (bases : List (Expr Var))
    (exponent : Expr Var) : List (Expr Var) → Expr Var
  | [] => poweredProduct base bases exponent
  | nextExponent :: exponents =>
      .mul (poweredProduct base bases exponent)
        (powerGrid base bases nextExponent exponents)

/-- Repeated multiplication of a base a positive number of times.  The index
`n` represents the positive exponent `n + 1`. -/
def positivePower (base : Expr Var) : Nat → Expr Var
  | 0 => base
  | n + 1 => .mul (positivePower base n) base

@[simp]
theorem eval_nonemptySum (assignment : Var → Nat) (head : Expr Var)
    (terms : List (Expr Var)) :
    Expr.eval assignment (nonemptySum head terms) =
      Expr.eval assignment head + (terms.map (Expr.eval assignment)).sum := by
  induction terms generalizing head with
  | nil => simp [nonemptySum]
  | cons term terms ih =>
      simp [nonemptySum, ih]

@[simp]
theorem eval_nonemptyProduct (assignment : Var → Nat) (head : Expr Var)
    (factors : List (Expr Var)) :
    Expr.eval assignment (nonemptyProduct head factors) =
      Expr.eval assignment head * (factors.map (Expr.eval assignment)).prod := by
  induction factors generalizing head with
  | nil => simp [nonemptyProduct]
  | cons factor factors ih =>
      simp [nonemptyProduct, ih]

/-- HSI splits a power over any nonempty finite sum of exponents. -/
theorem hsi_pow_nonemptySum (base head : Expr Var) (terms : List (Expr Var)) :
    HSIDerives (.pow base (nonemptySum head terms))
      (nonemptyProduct (.pow base head)
        (terms.map fun exponent ↦ .pow base exponent)) := by
  induction terms generalizing head with
  | nil => exact Derives.refl _
  | cons term terms ih =>
      exact Derives.trans
        (Derives.of_rule (HSIAxiom.pow_add base head (nonemptySum term terms)))
        (Derives.mul_congr (Derives.refl _) (ih term))

/-- HSI distributes a power over any nonempty finite product of bases. -/
theorem hsi_nonemptyProduct_pow (head : Expr Var) (factors : List (Expr Var))
    (exponent : Expr Var) :
    HSIDerives (.pow (nonemptyProduct head factors) exponent)
      (poweredProduct head factors exponent) := by
  induction factors generalizing head with
  | nil => exact Derives.refl _
  | cons factor factors ih =>
      exact Derives.trans
        (Derives.of_rule
          (HSIAxiom.mul_pow head (nonemptyProduct factor factors) exponent))
        (Derives.mul_congr (Derives.refl _) (ih factor))

/-- The combined finite grid expansion used after splitting an exponent and
factoring a base. -/
theorem hsi_nonemptyProduct_pow_nonemptySum
    (base : Expr Var) (bases : List (Expr Var))
    (exponent : Expr Var) (exponents : List (Expr Var)) :
    HSIDerives
      (.pow (nonemptyProduct base bases) (nonemptySum exponent exponents))
      (powerGrid base bases exponent exponents) := by
  induction exponents generalizing exponent with
  | nil => exact hsi_nonemptyProduct_pow base bases exponent
  | cons nextExponent exponents ih =>
      exact Derives.trans
        (Derives.of_rule
          (HSIAxiom.pow_add (nonemptyProduct base bases) exponent
            (nonemptySum nextExponent exponents)))
        (Derives.mul_congr
          (hsi_nonemptyProduct_pow base bases exponent)
          (ih nextExponent))

/-- The auxiliary-variable flattening identity is one of the original eleven
HSI schemes. -/
theorem hsi_flatten (base exponent outerExponent : Expr Var) :
    HSIDerives (.pow (.pow base exponent) outerExponent)
      (.pow base (.mul exponent outerExponent)) :=
  Derives.of_rule (HSIAxiom.pow_pow base exponent outerExponent)

/-- HSI reduces a literal positive constant exponent to repeated
multiplication, without ever introducing a zero exponent or an empty product. -/
theorem hsi_pow_posConst (base : Expr Var) (n : Nat) :
    HSIDerives (.pow base (Expr.posConst n)) (positivePower base n) := by
  induction n with
  | zero => exact Derives.of_rule (HSIAxiom.pow_one base)
  | succ n ih =>
      exact Derives.trans
        (Derives.of_rule
          (HSIAxiom.pow_add base (Expr.posConst n) (.one : Expr Var)))
        (Derives.mul_congr ih
          (Derives.of_rule (HSIAxiom.pow_one base)))

/-- Polynomialization of the repeated product agrees with ordinary natural
polynomial exponentiation. -/
theorem normalize_positivePower (base : Expr Var) (n : Nat) :
    normalize (positivePower base n) = normalize base ^ (n + 1) := by
  induction n with
  | zero => simp [positivePower]
  | succ n ih =>
      simp [positivePower, ih, pow_succ, Nat.add_assoc]

end PowerDerivations

end

end NormalizerCore

end Natfunbasis
