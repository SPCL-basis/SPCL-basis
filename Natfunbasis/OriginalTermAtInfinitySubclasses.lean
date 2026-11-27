import Natfunbasis.OriginalTermIntegerToRealBridge
import Mathlib.Algebra.Polynomial.Roots

/-!
# Unconditional at-infinity uniqueness for polynomial original terms

This file proves the integer-to-real and at-infinity uniqueness bridge for a
genuine subclass of the original expression language.  A term is called
`PolynomialRepresentable` when its positive-real interpretation is the
restriction of an ordinary real polynomial.  This class contains every
power-free term and is closed under powers by syntactically constant natural
exponents.

The final section records reusable closure lemmas for the pairwise
at-infinity uniqueness property.  Common addition and multiplication
contexts preserve it.  A common exponent preserves it unconditionally, and a
common base preserves it once that base is either identically one or
eventually different from one.  Polynomial-representable bases satisfy this
dichotomy.  Thus the remaining power obstruction is precisely the case in
which both base and exponent vary, together with comparisons between general
sums of such power terms.
-/

namespace Natfunbasis.Wilkie

open Filter Set

noncomputable section

namespace RealExpression

/-- Positive constants have the expected value under arbitrary real
assignments. -/
@[simp]
theorem eval_posConst {Var : Type*} (assignment : Var → Real) (n : Nat) :
    eval assignment (Expr.posConst n) = (n + 1 : Nat) := by
  induction n with
  | zero => simp [Expr.posConst]
  | succ n ih =>
      simp [Expr.posConst, ih, Nat.cast_add]

end RealExpression

namespace UnaryExpr

/-- An original unary term whose positive-real interpretation is the
restriction of an ordinary real polynomial. -/
def PolynomialRepresentable (e : UnaryExpr) : Prop :=
  ∃ p : Polynomial Real, ∀ y : PositiveReal, evalReal e y = p.eval y.1

theorem polynomialRepresentable_one :
    PolynomialRepresentable (.one : UnaryExpr) := by
  refine ⟨1, ?_⟩
  intro y
  change 1 = (1 : Polynomial Real).eval y.1
  simp

theorem polynomialRepresentable_var :
    PolynomialRepresentable (.var () : UnaryExpr) := by
  refine ⟨Polynomial.X, ?_⟩
  intro y
  change y.1 = Polynomial.X.eval y.1
  simp

theorem PolynomialRepresentable.add {s t : UnaryExpr}
    (hs : PolynomialRepresentable s) (ht : PolynomialRepresentable t) :
    PolynomialRepresentable (.add s t) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  refine ⟨p + q, ?_⟩
  intro y
  change evalReal s y + evalReal t y = (p + q).eval y.1
  rw [hp y, hq y, Polynomial.eval_add]

theorem PolynomialRepresentable.mul {s t : UnaryExpr}
    (hs : PolynomialRepresentable s) (ht : PolynomialRepresentable t) :
    PolynomialRepresentable (.mul s t) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  refine ⟨p * q, ?_⟩
  intro y
  change evalReal s y * evalReal t y = (p * q).eval y.1
  rw [hp y, hq y, Polynomial.eval_mul]

/-- A polynomial term raised to an expression which is constantly a natural
number is still polynomial-representable. -/
theorem PolynomialRepresentable.pow_natConstant {s t : UnaryExpr}
    (hs : PolynomialRepresentable s) (n : Nat)
    (ht : ∀ y : PositiveReal, evalReal t y = (n : Real)) :
    PolynomialRepresentable (.pow s t) := by
  obtain ⟨p, hp⟩ := hs
  refine ⟨p ^ n, ?_⟩
  intro y
  change Real.rpow (evalReal s y) (evalReal t y) = (p ^ n).eval y.1
  rw [ht y]
  calc
    Real.rpow (evalReal s y) (n : Real) = (evalReal s y) ^ n :=
      Real.rpow_natCast _ n
    _ = (p ^ n).eval y.1 := by rw [Polynomial.eval_pow, hp y]

/-- In particular, the syntax `s ^ (n + 1)` remains polynomial. -/
theorem PolynomialRepresentable.pow_posConst {s : UnaryExpr}
    (hs : PolynomialRepresentable s) (n : Nat) :
    PolynomialRepresentable (.pow s (Expr.posConst n)) := by
  apply hs.pow_natConstant (n + 1)
  intro y
  simp [evalReal]

/-- Syntactic power-freeness for the original unary language. -/
inductive IsPowerFree : UnaryExpr → Prop where
  | one : IsPowerFree .one
  | var : IsPowerFree (.var ())
  | add {s t} : IsPowerFree s → IsPowerFree t → IsPowerFree (.add s t)
  | mul {s t} : IsPowerFree s → IsPowerFree t → IsPowerFree (.mul s t)

/-- Every power-free original unary term is an ordinary polynomial. -/
theorem IsPowerFree.polynomialRepresentable {e : UnaryExpr}
    (he : IsPowerFree e) : PolynomialRepresentable e := by
  induction he with
  | one => exact polynomialRepresentable_one
  | var => exact polynomialRepresentable_var
  | add hs ht ihs iht => exact ihs.add iht
  | mul hs ht ihs iht => exact ihs.mul iht

/-! ## Elementary eventual behavior of every positive original term -/

/-- Every original term has value at least one once its positive input is at
least one. -/
theorem evalReal_one_le_of_one_le_input (e : UnaryExpr) (y : PositiveReal)
    (hy : 1 ≤ y.1) : 1 ≤ evalReal e y := by
  induction e with
  | one => simp [evalReal, RealExpression.eval]
  | var x =>
      cases x
      simpa [evalReal, RealExpression.eval] using hy
  | add s t hs ht =>
      change 1 ≤ evalReal s y + evalReal t y
      linarith
  | mul s t hs ht =>
      change 1 ≤ evalReal s y * evalReal t y
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ evalReal s y * evalReal t y :=
          mul_le_mul hs ht (by norm_num) (zero_le_one.trans hs)
  | pow s t hs _ =>
      change 1 ≤ Real.rpow (evalReal s y) (evalReal t y)
      exact Real.one_le_rpow hs (evalReal_pos t y).le

/-- Every original term is either identically one or is strictly larger than
one at every input larger than one.  This uses only positivity and the
syntax: a power with positive exponent is one exactly in the syntactic branch
where its base is identically one. -/
theorem evalReal_eq_one_or_gt_one_of_one_lt_input (e : UnaryExpr) :
    evalReal e = (fun _ ↦ 1) ∨
      ∀ y : PositiveReal, 1 < y.1 → 1 < evalReal e y := by
  induction e with
  | one =>
      left
      funext y
      rfl
  | var x =>
      cases x
      right
      intro y hy
      exact hy
  | add s t hs ht =>
      right
      intro y hy
      change 1 < evalReal s y + evalReal t y
      have hsOne := evalReal_one_le_of_one_le_input s y hy.le
      have htOne := evalReal_one_le_of_one_le_input t y hy.le
      linarith
  | mul s t hs ht =>
      rcases hs with hsOne | hsLarge
      · rcases ht with htOne | htLarge
        · left
          funext y
          change evalReal s y * evalReal t y = 1
          rw [congrFun hsOne y, congrFun htOne y, one_mul]
        · right
          intro y hy
          change 1 < evalReal s y * evalReal t y
          rw [congrFun hsOne y, one_mul]
          exact htLarge y hy
      · rcases ht with htOne | htLarge
        · right
          intro y hy
          change 1 < evalReal s y * evalReal t y
          rw [congrFun htOne y, mul_one]
          exact hsLarge y hy
        · right
          intro y hy
          change 1 < evalReal s y * evalReal t y
          exact one_lt_mul_of_lt_of_le
            (hsLarge y hy) (htLarge y hy).le
  | pow s t hs _ =>
      rcases hs with hsOne | hsLarge
      · left
        funext y
        change Real.rpow (evalReal s y) (evalReal t y) = 1
        rw [congrFun hsOne y]
        simp
      · right
        intro y hy
        change 1 < Real.rpow (evalReal s y) (evalReal t y)
        exact Real.one_lt_rpow (hsLarge y hy) (evalReal_pos t y)

/-- Filter-style consequence of
`evalReal_eq_one_or_gt_one_of_one_lt_input`. -/
theorem evalReal_eq_one_or_eventually_gt_one (e : UnaryExpr) :
    evalReal e = (fun _ ↦ 1) ∨
      ∃ B : Real, ∀ y : PositiveReal, B < y.1 → 1 < evalReal e y := by
  rcases evalReal_eq_one_or_gt_one_of_one_lt_input e with hOne | hLarge
  · exact Or.inl hOne
  · exact Or.inr ⟨1, hLarge⟩

/-! ## Polynomial identity at infinity -/

/-- Polynomial-representable original terms which agree at infinitely many
positive-real points agree everywhere on the positive axis. -/
theorem PolynomialRepresentable.eq_of_infinite_eqSet {e d : UnaryExpr}
    (he : PolynomialRepresentable e) (hd : PolynomialRepresentable d)
    (hinfinite :
      {y : PositiveReal | evalReal e y = evalReal d y}.Infinite) :
    evalReal e = evalReal d := by
  obtain ⟨p, hp⟩ := he
  obtain ⟨q, hq⟩ := hd
  have hImageInfinite :
      ((fun y : PositiveReal ↦ y.1) ''
        {y : PositiveReal | evalReal e y = evalReal d y}).Infinite :=
    hinfinite.image Subtype.val_injective.injOn
  have hEvalInfinite : {x : Real | p.eval x = q.eval x}.Infinite := by
    apply hImageInfinite.mono
    rintro x ⟨y, hy, rfl⟩
    change p.eval y.1 = q.eval y.1
    rw [← hp y, ← hq y]
    exact hy
  have hpq : p = q := p.eq_of_infinite_eval_eq q hEvalInfinite
  funext y
  rw [hp y, hq y, hpq]

/-- Equality points arbitrarily far to the right are necessarily infinite. -/
theorem infinite_eqSet_of_unbounded {e d : UnaryExpr}
    (hunbounded : ∀ B : Real, ∃ y : PositiveReal,
      B < y.1 ∧ evalReal e y = evalReal d y) :
    {y : PositiveReal | evalReal e y = evalReal d y}.Infinite := by
  let Z : Set PositiveReal :=
    {y | evalReal e y = evalReal d y}
  have hNotBdd : ¬ BddAbove ((fun y : PositiveReal ↦ y.1) '' Z) := by
    intro hBdd
    obtain ⟨B, hB⟩ := hBdd
    obtain ⟨y, hyB, hyEq⟩ := hunbounded B
    have hyLe : y.1 ≤ B := hB ⟨y, hyEq, rfl⟩
    exact (not_lt_of_ge hyLe) hyB
  have hImageInfinite :
      ((fun y : PositiveReal ↦ y.1) '' Z).Infinite :=
    Set.infinite_of_not_bddAbove hNotBdd
  exact (Set.infinite_image_iff Subtype.val_injective.injOn).mp hImageInfinite

/-- At-infinity uniqueness is unconditional for two
polynomial-representable original terms. -/
theorem PolynomialRepresentable.eq_of_unbounded {e d : UnaryExpr}
    (he : PolynomialRepresentable e) (hd : PolynomialRepresentable d)
    (hunbounded : ∀ B : Real, ∃ y : PositiveReal,
      B < y.1 ∧ evalReal e y = evalReal d y) :
    evalReal e = evalReal d :=
  he.eq_of_infinite_eqSet hd (infinite_eqSet_of_unbounded hunbounded)

/-- The exact integer-to-real bridge is unconditional for any pair of
polynomial-representable original terms. -/
theorem PolynomialRepresentable.eq_of_semEq {e d : UnaryExpr}
    (he : PolynomialRepresentable e) (hd : PolynomialRepresentable d)
    (hsem : UnaryExpr.SemEq e d) : evalReal e = evalReal d := by
  apply he.eq_of_infinite_eqSet hd
  apply integerRealInput_range_infinite.mono
  rintro y ⟨n, rfl⟩
  change evalReal e (integerRealInput n) = evalReal d (integerRealInput n)
  simpa only [evalReal_integer] using
    congrArg (fun value : Nat ↦ (value : Real)) (hsem n)

theorem IsPowerFree.evalReal_eq_of_unbounded {e d : UnaryExpr}
    (he : IsPowerFree e) (hd : IsPowerFree d)
    (hunbounded : ∀ B : Real, ∃ y : PositiveReal,
      B < y.1 ∧ evalReal e y = evalReal d y) :
    evalReal e = evalReal d :=
  he.polynomialRepresentable.eq_of_unbounded hd.polynomialRepresentable hunbounded

theorem IsPowerFree.evalReal_eq_of_semEq {e d : UnaryExpr}
    (he : IsPowerFree e) (hd : IsPowerFree d)
    (hsem : UnaryExpr.SemEq e d) :
    evalReal e = evalReal d :=
  he.polynomialRepresentable.eq_of_semEq hd.polynomialRepresentable hsem

/-! ## A pairwise structural API -/

/-- Two terms have equality points arbitrarily far toward `+infinity`. -/
def EqualUnboundedAtInfinity (e d : UnaryExpr) : Prop :=
  ∀ B : Real, ∃ y : PositiveReal,
    B < y.1 ∧ evalReal e y = evalReal d y

/-- Pairwise at-infinity uniqueness, the induction target needed to prove the
global `OriginalTermAtInfinityIdentity` proposition. -/
def AtInfinityUniquePair (e d : UnaryExpr) : Prop :=
  EqualUnboundedAtInfinity e d → evalReal e = evalReal d

/-- Agreement at every positive integer gives equality points unbounded toward
`+infinity`. -/
theorem equalUnboundedAtInfinity_of_semEq {e d : UnaryExpr}
    (hsem : UnaryExpr.SemEq e d) : EqualUnboundedAtInfinity e d := by
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let m : PosNat := ⟨n + 1, by omega⟩
  refine ⟨integerRealInput m, ?_, ?_⟩
  · change B < ((n + 1 : Nat) : Real)
    exact hn.trans_le (by exact_mod_cast Nat.le_succ n)
  · simpa only [evalReal_integer] using
      congrArg (fun value : Nat ↦ (value : Real)) (hsem m)

/-- Any established pairwise at-infinity uniqueness result immediately gives
the corresponding integer-to-real transfer for that pair. -/
theorem AtInfinityUniquePair.eq_of_semEq {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (hsem : UnaryExpr.SemEq e d) :
    evalReal e = evalReal d :=
  h (equalUnboundedAtInfinity_of_semEq hsem)

theorem originalTermAtInfinityIdentity_iff_atInfinityUniquePair :
    OriginalTermAtInfinityIdentity ↔
      ∀ e d : UnaryExpr, AtInfinityUniquePair e d :=
  Iff.rfl

theorem PolynomialRepresentable.atInfinityUniquePair {e d : UnaryExpr}
    (he : PolynomialRepresentable e) (hd : PolynomialRepresentable d) :
    AtInfinityUniquePair e d :=
  he.eq_of_unbounded hd

/-- A base is eventually different from the exceptional value `1`, above an
explicit real threshold. -/
def EventuallyNotOne (b : UnaryExpr) : Prop :=
  ∃ B : Real, ∀ y : PositiveReal, B < y.1 → evalReal b y ≠ 1

/-- Every original base is either identically one or eventually different
from one. -/
theorem evalReal_eq_one_or_eventuallyNotOne (b : UnaryExpr) :
    evalReal b = (fun _ ↦ 1) ∨ EventuallyNotOne b := by
  rcases evalReal_eq_one_or_eventually_gt_one b with hOne | ⟨B, hLarge⟩
  · exact Or.inl hOne
  · exact Or.inr ⟨B, fun y hy ↦ ne_of_gt (hLarge y hy)⟩

theorem AtInfinityUniquePair.add_right {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (c : UnaryExpr) :
    AtInfinityUniquePair (.add e c) (.add d c) := by
  intro hsum
  have hed : evalReal e = evalReal d := h (by
    intro B
    obtain ⟨y, hy, hEq⟩ := hsum B
    refine ⟨y, hy, ?_⟩
    change evalReal e y + evalReal c y =
      evalReal d y + evalReal c y at hEq
    exact add_right_cancel hEq)
  funext y
  change evalReal e y + evalReal c y = evalReal d y + evalReal c y
  rw [congrFun hed y]

theorem AtInfinityUniquePair.add_left {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (c : UnaryExpr) :
    AtInfinityUniquePair (.add c e) (.add c d) := by
  intro hsum
  have hed : evalReal e = evalReal d := h (by
    intro B
    obtain ⟨y, hy, hEq⟩ := hsum B
    refine ⟨y, hy, ?_⟩
    change evalReal c y + evalReal e y =
      evalReal c y + evalReal d y at hEq
    exact add_left_cancel hEq)
  funext y
  change evalReal c y + evalReal e y = evalReal c y + evalReal d y
  rw [congrFun hed y]

theorem AtInfinityUniquePair.mul_right {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (c : UnaryExpr) :
    AtInfinityUniquePair (.mul e c) (.mul d c) := by
  intro hprod
  have hed : evalReal e = evalReal d := h (by
    intro B
    obtain ⟨y, hy, hEq⟩ := hprod B
    refine ⟨y, hy, ?_⟩
    change evalReal e y * evalReal c y =
      evalReal d y * evalReal c y at hEq
    exact mul_right_cancel₀ (ne_of_gt (evalReal_pos c y)) hEq)
  funext y
  change evalReal e y * evalReal c y = evalReal d y * evalReal c y
  rw [congrFun hed y]

theorem AtInfinityUniquePair.mul_left {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (c : UnaryExpr) :
    AtInfinityUniquePair (.mul c e) (.mul c d) := by
  intro hprod
  have hed : evalReal e = evalReal d := h (by
    intro B
    obtain ⟨y, hy, hEq⟩ := hprod B
    refine ⟨y, hy, ?_⟩
    change evalReal c y * evalReal e y =
      evalReal c y * evalReal d y at hEq
    exact mul_left_cancel₀ (ne_of_gt (evalReal_pos c y)) hEq)
  funext y
  change evalReal c y * evalReal e y = evalReal c y * evalReal d y
  rw [congrFun hed y]

/-- With a common positive exponent, equality of powers reduces injectively
to equality of their bases. -/
theorem AtInfinityUniquePair.pow_sameExponent {b c : UnaryExpr}
    (h : AtInfinityUniquePair b c) (exponent : UnaryExpr) :
    AtInfinityUniquePair (.pow b exponent) (.pow c exponent) := by
  intro hpowers
  have hbc : evalReal b = evalReal c := h (by
    intro B
    obtain ⟨y, hy, hEq⟩ := hpowers B
    refine ⟨y, hy, ?_⟩
    change Real.rpow (evalReal b y) (evalReal exponent y) =
      Real.rpow (evalReal c y) (evalReal exponent y) at hEq
    exact (Real.rpow_left_inj
      (evalReal_pos b y).le (evalReal_pos c y).le
      (ne_of_gt (evalReal_pos exponent y))).mp hEq)
  funext y
  change Real.rpow (evalReal b y) (evalReal exponent y) =
    Real.rpow (evalReal c y) (evalReal exponent y)
  rw [congrFun hbc y]

/-- With a common base, equality of powers reduces injectively to equality of
their exponents whenever the base is identically one or eventually avoids
one. -/
theorem AtInfinityUniquePair.pow_sameBase_of_dichotomy {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (base : UnaryExpr)
    (hbase : evalReal base = (fun _ ↦ 1) ∨ EventuallyNotOne base) :
    AtInfinityUniquePair (.pow base e) (.pow base d) := by
  rcases hbase with hOne | hEventually
  · intro _
    funext y
    change Real.rpow (evalReal base y) (evalReal e y) =
      Real.rpow (evalReal base y) (evalReal d y)
    rw [congrFun hOne y]
    simp
  · obtain ⟨B₀, hB₀⟩ := hEventually
    intro hpowers
    have hed : evalReal e = evalReal d := h (by
      intro B
      obtain ⟨y, hy, hEq⟩ := hpowers (max B B₀)
      have hyB : B < y.1 := (le_max_left B B₀).trans_lt hy
      have hyB₀ : B₀ < y.1 := (le_max_right B B₀).trans_lt hy
      refine ⟨y, hyB, ?_⟩
      change Real.rpow (evalReal base y) (evalReal e y) =
        Real.rpow (evalReal base y) (evalReal d y) at hEq
      exact (Real.rpow_right_inj
        (evalReal_pos base y) (hB₀ y hyB₀)).mp hEq)
    funext y
    change Real.rpow (evalReal base y) (evalReal e y) =
      Real.rpow (evalReal base y) (evalReal d y)
    rw [congrFun hed y]

/-- Common-base exponentiation preserves pairwise at-infinity uniqueness for
every original base. -/
theorem AtInfinityUniquePair.pow_sameBase {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) (base : UnaryExpr) :
    AtInfinityUniquePair (.pow base e) (.pow base d) :=
  h.pow_sameBase_of_dichotomy base
    (evalReal_eq_one_or_eventuallyNotOne base)

end UnaryExpr

end

end Natfunbasis.Wilkie
