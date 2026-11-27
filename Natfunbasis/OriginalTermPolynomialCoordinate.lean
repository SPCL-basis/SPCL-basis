import Natfunbasis.OriginalTermAtInfinityMonotonicity
import Mathlib.Analysis.Polynomial.Basic

/-!
# Eventual order for terms polynomial in a common coordinate

This module proves a genuine Hardy-style eventual-order theorem for a broad
semantic subclass of original terms.  If two terms are ordinary real
polynomials in the value of one common increasing-unbounded original term,
then their positive-real interpretations are equal or eventually strictly
ordered.  The representation class contains constants and the coordinate,
and is closed under addition, multiplication, and powers by constant natural
exponents.

The remaining constructor is a power with genuinely varying exponent (and,
more generally, a non-polynomial real exponent): `p(u) ^ q(u)` is not an
ordinary polynomial in `u`.
-/

namespace Natfunbasis.Wilkie

open Filter Set

noncomputable section

namespace UnaryExpr

/-- A term is polynomially representable in a chosen original coordinate. -/
def PolynomialRepresentableOver (coordinate e : UnaryExpr) : Prop :=
  ∃ p : Polynomial Real, ∀ y : PositiveReal,
    evalReal e y = p.eval (evalReal coordinate y)

theorem polynomialRepresentableOver_one (coordinate : UnaryExpr) :
    PolynomialRepresentableOver coordinate (.one : UnaryExpr) := by
  refine ⟨1, ?_⟩
  intro y
  change 1 = (1 : Polynomial Real).eval (evalReal coordinate y)
  simp

theorem polynomialRepresentableOver_self (coordinate : UnaryExpr) :
    PolynomialRepresentableOver coordinate coordinate := by
  refine ⟨Polynomial.X, ?_⟩
  intro y
  simp

/-- Every semantically constant term is a constant polynomial in any
coordinate. -/
theorem ConstantEvaluation.polynomialRepresentableOver
    {e : UnaryExpr} (he : ConstantEvaluation e) (coordinate : UnaryExpr) :
    PolynomialRepresentableOver coordinate e := by
  obtain ⟨c, -, hec⟩ := he
  refine ⟨Polynomial.C c, ?_⟩
  intro y
  rw [congrFun hec y, Polynomial.eval_C]

theorem PolynomialRepresentableOver.add {coordinate s t : UnaryExpr}
    (hs : PolynomialRepresentableOver coordinate s)
    (ht : PolynomialRepresentableOver coordinate t) :
    PolynomialRepresentableOver coordinate (.add s t) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  refine ⟨p + q, ?_⟩
  intro y
  change evalReal s y + evalReal t y =
    (p + q).eval (evalReal coordinate y)
  rw [hp y, hq y, Polynomial.eval_add]

theorem PolynomialRepresentableOver.mul {coordinate s t : UnaryExpr}
    (hs : PolynomialRepresentableOver coordinate s)
    (ht : PolynomialRepresentableOver coordinate t) :
    PolynomialRepresentableOver coordinate (.mul s t) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  refine ⟨p * q, ?_⟩
  intro y
  change evalReal s y * evalReal t y =
    (p * q).eval (evalReal coordinate y)
  rw [hp y, hq y, Polynomial.eval_mul]

/-- Closure under a power whose exponent is semantically a natural number. -/
theorem PolynomialRepresentableOver.pow_natConstant
    {coordinate s t : UnaryExpr}
    (hs : PolynomialRepresentableOver coordinate s) (n : Nat)
    (ht : ∀ y : PositiveReal, evalReal t y = (n : Real)) :
    PolynomialRepresentableOver coordinate (.pow s t) := by
  obtain ⟨p, hp⟩ := hs
  refine ⟨p ^ n, ?_⟩
  intro y
  change Real.rpow (evalReal s y) (evalReal t y) =
    (p ^ n).eval (evalReal coordinate y)
  rw [ht y]
  calc
    Real.rpow (evalReal s y) (n : Real) = (evalReal s y) ^ n :=
      Real.rpow_natCast _ n
    _ = (p ^ n).eval (evalReal coordinate y) := by
      rw [Polynomial.eval_pow, hp y]

theorem PolynomialRepresentableOver.pow_posConst
    {coordinate s : UnaryExpr}
    (hs : PolynomialRepresentableOver coordinate s) (n : Nat) :
    PolynomialRepresentableOver coordinate (.pow s (Expr.posConst n)) := by
  apply hs.pow_natConstant (n + 1)
  intro y
  simp [evalReal]

/-- The exceptional base `1` remains polynomial under an arbitrary original
exponent. -/
theorem polynomialRepresentableOver_pow_of_base_one
    (coordinate exponent : UnaryExpr) {base : UnaryExpr}
    (hbase : evalReal base = fun _ ↦ 1) :
    PolynomialRepresentableOver coordinate (.pow base exponent) := by
  refine ⟨1, ?_⟩
  intro y
  change Real.rpow (evalReal base y) (evalReal exponent y) =
    (1 : Polynomial Real).eval (evalReal coordinate y)
  rw [congrFun hbase y]
  simp

/-! ## Polynomial eventual sign and transfer through a coordinate -/

/-- A nonzero real polynomial has a strict, constant sign sufficiently far
to the right. -/
theorem Polynomial.eventuallyEval_pos_or_neg {p : Polynomial Real}
    (hp : p ≠ 0) :
    (∃ B : Real, ∀ x : Real, B < x → 0 < p.eval x) ∨
      (∃ B : Real, ∀ x : Real, B < x → p.eval x < 0) := by
  by_cases hdegree : p.natDegree = 0
  · have hpC : p = Polynomial.C (p.coeff 0) :=
      p.eq_C_of_natDegree_eq_zero hdegree
    have hcoeff : p.coeff 0 ≠ 0 := by
      intro hzero
      apply hp
      rw [hpC, hzero, Polynomial.C_0]
    rcases lt_trichotomy 0 (p.coeff 0) with hpos | hzero | hneg
    · exact Or.inl ⟨0, fun x _ ↦ by
        rw [hpC, Polynomial.eval_C]
        exact hpos⟩
    · exact False.elim (hcoeff hzero.symm)
    · exact Or.inr ⟨0, fun x _ ↦ by
        rw [hpC, Polynomial.eval_C]
        exact hneg⟩
  · have hdegreePos : 0 < p.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp
        (Nat.pos_of_ne_zero hdegree)
    have hlead : p.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hp
    rcases lt_trichotomy 0 p.leadingCoeff with hpos | hzero | hneg
    · have htend :=
        p.tendsto_atTop_of_leadingCoeff_nonneg hdegreePos hpos.le
      obtain ⟨B, hB⟩ := eventually_atTop.1
        (htend.eventually_gt_atTop 0)
      exact Or.inl ⟨B, fun x hx ↦ hB x hx.le⟩
    · exact False.elim (hlead hzero.symm)
    · have htend :=
        p.tendsto_atBot_of_leadingCoeff_nonpos hdegreePos hneg.le
      obtain ⟨B, hB⟩ := eventually_atTop.1
        (htend.eventually_lt_atBot 0)
      exact Or.inr ⟨B, fun x hx ↦ hB x hx.le⟩

/-- Polynomial eventual sign transfers through any increasing-unbounded
original coordinate. -/
theorem IncreasingUnbounded.eventuallyPolynomialEval_pos_or_neg
    {coordinate : UnaryExpr} (hcoordinate : IncreasingUnbounded coordinate)
    {p : Polynomial Real} (hp : p ≠ 0) :
    (∃ B : Real, ∀ y : PositiveReal, B < y.1 →
      0 < p.eval (evalReal coordinate y)) ∨
    (∃ B : Real, ∀ y : PositiveReal, B < y.1 →
      p.eval (evalReal coordinate y) < 0) := by
  rcases Polynomial.eventuallyEval_pos_or_neg hp with
      ⟨C, hC⟩ | ⟨C, hC⟩
  · obtain ⟨y₀, hy₀, hCy₀⟩ :=
      hcoordinate.unboundedAboveAtInfinity C
    left
    refine ⟨y₀.1, ?_⟩
    intro y hy
    apply hC
    exact hCy₀.trans
      (hcoordinate.strictlyIncreasingAboveOne hy₀.le hy)
  · obtain ⟨y₀, hy₀, hCy₀⟩ :=
      hcoordinate.unboundedAboveAtInfinity C
    right
    refine ⟨y₀.1, ?_⟩
    intro y hy
    apply hC
    exact hCy₀.trans
      (hcoordinate.strictlyIncreasingAboveOne hy₀.le hy)

/-! ## Eventual order and at-infinity uniqueness -/

/-- Two terms polynomial in the same increasing-unbounded coordinate satisfy
the Hardy-style eventual-order trichotomy. -/
theorem PolynomialRepresentableOver.eventualOrderTrichotomyPair
    {coordinate e d : UnaryExpr}
    (hcoordinate : IncreasingUnbounded coordinate)
    (he : PolynomialRepresentableOver coordinate e)
    (hd : PolynomialRepresentableOver coordinate d) :
    EventualOrderTrichotomyPair e d := by
  obtain ⟨p, hp⟩ := he
  obtain ⟨q, hq⟩ := hd
  by_cases hpq : p = q
  · left
    funext y
    rw [hp y, hq y, hpq]
  · have hsub : p - q ≠ 0 := sub_ne_zero.mpr hpq
    rcases hcoordinate.eventuallyPolynomialEval_pos_or_neg hsub with
        ⟨B, hpositive⟩ | ⟨B, hnegative⟩
    · exact Or.inr (Or.inr ⟨B, fun y hy ↦ by
        rw [hp y, hq y]
        have h := hpositive y hy
        rw [Polynomial.eval_sub] at h
        linarith⟩)
    · exact Or.inr (Or.inl ⟨B, fun y hy ↦ by
        rw [hp y, hq y]
        have h := hnegative y hy
        rw [Polynomial.eval_sub] at h
        linarith⟩)

theorem PolynomialRepresentableOver.atInfinityUniquePair
    {coordinate e d : UnaryExpr}
    (hcoordinate : IncreasingUnbounded coordinate)
    (he : PolynomialRepresentableOver coordinate e)
    (hd : PolynomialRepresentableOver coordinate d) :
    AtInfinityUniquePair e d :=
  (he.eventualOrderTrichotomyPair hcoordinate hd).atInfinityUniquePair

/-- Integer agreement transfers to positive-real equality for any two terms
polynomial in one common increasing-unbounded original coordinate. -/
theorem PolynomialRepresentableOver.eq_of_semEq
    {coordinate e d : UnaryExpr}
    (hcoordinate : IncreasingUnbounded coordinate)
    (he : PolynomialRepresentableOver coordinate e)
    (hd : PolynomialRepresentableOver coordinate d)
    (hsem : UnaryExpr.SemEq e d) :
    evalReal e = evalReal d :=
  (he.atInfinityUniquePair hcoordinate hd).eq_of_semEq hsem

/-! ## Constructor-level eventual-order closure -/

/-- Strict eventual inequalities add when their orientations agree. -/
theorem EventuallyStrictlyLess.add
    {a b c d : UnaryExpr}
    (hab : EventuallyStrictlyLess a b)
    (hcd : EventuallyStrictlyLess c d) :
    EventuallyStrictlyLess (.add a c) (.add b d) := by
  obtain ⟨B₁, hB₁⟩ := hab
  obtain ⟨B₂, hB₂⟩ := hcd
  refine ⟨max B₁ B₂, ?_⟩
  intro y hy
  exact add_lt_add
    (hB₁ y ((le_max_left B₁ B₂).trans_lt hy))
    (hB₂ y ((le_max_right B₁ B₂).trans_lt hy))

/-- Strict eventual inequalities multiply when their orientations agree,
because every original-term value is positive. -/
theorem EventuallyStrictlyLess.mul
    {a b c d : UnaryExpr}
    (hab : EventuallyStrictlyLess a b)
    (hcd : EventuallyStrictlyLess c d) :
    EventuallyStrictlyLess (.mul a c) (.mul b d) := by
  obtain ⟨B₁, hB₁⟩ := hab
  obtain ⟨B₂, hB₂⟩ := hcd
  refine ⟨max B₁ B₂, ?_⟩
  intro y hy
  have haby := hB₁ y ((le_max_left B₁ B₂).trans_lt hy)
  have hcdy := hB₂ y ((le_max_right B₁ B₂).trans_lt hy)
  change evalReal a y * evalReal c y < evalReal b y * evalReal d y
  calc
    evalReal a y * evalReal c y < evalReal b y * evalReal c y :=
      mul_lt_mul_of_pos_right haby (evalReal_pos c y)
    _ < evalReal b y * evalReal d y :=
      mul_lt_mul_of_pos_left hcdy (evalReal_pos b y)

/-- Powers preserve two strict eventual inequalities when base and exponent
move in the same direction. -/
theorem EventuallyStrictlyLess.pow
    {a b c d : UnaryExpr}
    (hab : EventuallyStrictlyLess a b)
    (hcd : EventuallyStrictlyLess c d) :
    EventuallyStrictlyLess (.pow a c) (.pow b d) := by
  obtain ⟨B₁, hB₁⟩ := hab
  obtain ⟨B₂, hB₂⟩ := hcd
  refine ⟨max (max B₁ B₂) 1, ?_⟩
  intro y hy
  have hy₁ : 1 < y.1 := (le_max_right (max B₁ B₂) 1).trans_lt hy
  have hy₁₂ : max B₁ B₂ < y.1 :=
    (le_max_left (max B₁ B₂) 1).trans_lt hy
  have haby := hB₁ y ((le_max_left B₁ B₂).trans_lt hy₁₂)
  have hcdy := hB₂ y ((le_max_right B₁ B₂).trans_lt hy₁₂)
  change Real.rpow (evalReal a y) (evalReal c y) <
    Real.rpow (evalReal b y) (evalReal d y)
  calc
    Real.rpow (evalReal a y) (evalReal c y) <
        Real.rpow (evalReal b y) (evalReal c y) :=
      Real.rpow_lt_rpow (evalReal_pos a y).le haby
        (evalReal_pos c y)
    _ < Real.rpow (evalReal b y) (evalReal d y) :=
      Real.rpow_lt_rpow_of_exponent_lt
        ((evalReal_one_le_of_one_le_input a y hy₁.le).trans_lt haby)
        hcdy

theorem EventuallyStrictlyLess.add_right {e d : UnaryExpr}
    (h : EventuallyStrictlyLess e d) (c : UnaryExpr) :
    EventuallyStrictlyLess (.add e c) (.add d c) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, ?_⟩
  intro y hy
  change evalReal e y + evalReal c y < evalReal d y + evalReal c y
  exact add_lt_add_left (hB y hy) _

theorem EventuallyStrictlyLess.add_left {e d : UnaryExpr}
    (h : EventuallyStrictlyLess e d) (c : UnaryExpr) :
    EventuallyStrictlyLess (.add c e) (.add c d) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, ?_⟩
  intro y hy
  change evalReal c y + evalReal e y < evalReal c y + evalReal d y
  exact add_lt_add_right (hB y hy) _

theorem EventuallyStrictlyLess.mul_right {e d : UnaryExpr}
    (h : EventuallyStrictlyLess e d) (c : UnaryExpr) :
    EventuallyStrictlyLess (.mul e c) (.mul d c) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, ?_⟩
  intro y hy
  exact mul_lt_mul_of_pos_right (hB y hy) (evalReal_pos c y)

theorem EventuallyStrictlyLess.mul_left {e d : UnaryExpr}
    (h : EventuallyStrictlyLess e d) (c : UnaryExpr) :
    EventuallyStrictlyLess (.mul c e) (.mul c d) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, ?_⟩
  intro y hy
  exact mul_lt_mul_of_pos_left (hB y hy) (evalReal_pos c y)

theorem EventuallyStrictlyLess.pow_sameExponent {e d : UnaryExpr}
    (h : EventuallyStrictlyLess e d) (exponent : UnaryExpr) :
    EventuallyStrictlyLess (.pow e exponent) (.pow d exponent) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, ?_⟩
  intro y hy
  exact Real.rpow_lt_rpow (evalReal_pos e y).le (hB y hy)
    (evalReal_pos exponent y)

theorem EventualOrderTrichotomyPair.add_right {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) (c : UnaryExpr) :
    EventualOrderTrichotomyPair (.add e c) (.add d c) := by
  rcases h with heq | hlt | hgt
  · left
    funext y
    change evalReal e y + evalReal c y = evalReal d y + evalReal c y
    rw [congrFun heq y]
  · exact Or.inr (Or.inl (hlt.add_right c))
  · exact Or.inr (Or.inr (hgt.add_right c))

theorem EventualOrderTrichotomyPair.add_left {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) (c : UnaryExpr) :
    EventualOrderTrichotomyPair (.add c e) (.add c d) := by
  rcases h with heq | hlt | hgt
  · left
    funext y
    change evalReal c y + evalReal e y = evalReal c y + evalReal d y
    rw [congrFun heq y]
  · exact Or.inr (Or.inl (hlt.add_left c))
  · exact Or.inr (Or.inr (hgt.add_left c))

theorem EventualOrderTrichotomyPair.mul_right {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) (c : UnaryExpr) :
    EventualOrderTrichotomyPair (.mul e c) (.mul d c) := by
  rcases h with heq | hlt | hgt
  · left
    funext y
    change evalReal e y * evalReal c y = evalReal d y * evalReal c y
    rw [congrFun heq y]
  · exact Or.inr (Or.inl (hlt.mul_right c))
  · exact Or.inr (Or.inr (hgt.mul_right c))

theorem EventualOrderTrichotomyPair.mul_left {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) (c : UnaryExpr) :
    EventualOrderTrichotomyPair (.mul c e) (.mul c d) := by
  rcases h with heq | hlt | hgt
  · left
    funext y
    change evalReal c y * evalReal e y = evalReal c y * evalReal d y
    rw [congrFun heq y]
  · exact Or.inr (Or.inl (hlt.mul_left c))
  · exact Or.inr (Or.inr (hgt.mul_left c))

theorem EventualOrderTrichotomyPair.pow_sameExponent {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) (exponent : UnaryExpr) :
    EventualOrderTrichotomyPair (.pow e exponent) (.pow d exponent) := by
  rcases h with heq | hlt | hgt
  · left
    funext y
    change Real.rpow (evalReal e y) (evalReal exponent y) =
      Real.rpow (evalReal d y) (evalReal exponent y)
    rw [congrFun heq y]
  · exact Or.inr (Or.inl (hlt.pow_sameExponent exponent))
  · exact Or.inr (Or.inr (hgt.pow_sameExponent exponent))

/-- A common base preserves eventual order.  The base-`1` branch collapses
both powers to the same function; otherwise the base is eventually greater
than `1`, so exponentiation is strictly increasing in its exponent. -/
theorem EventualOrderTrichotomyPair.pow_sameBase {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) (base : UnaryExpr) :
    EventualOrderTrichotomyPair (.pow base e) (.pow base d) := by
  rcases evalReal_eq_one_or_eventually_gt_one base with hOne | ⟨B₀, hB₀⟩
  · left
    funext y
    change Real.rpow (evalReal base y) (evalReal e y) =
      Real.rpow (evalReal base y) (evalReal d y)
    rw [congrFun hOne y]
    simp
  · rcases h with heq | hlt | hgt
    · left
      funext y
      change Real.rpow (evalReal base y) (evalReal e y) =
        Real.rpow (evalReal base y) (evalReal d y)
      rw [congrFun heq y]
    · obtain ⟨B, hB⟩ := hlt
      exact Or.inr (Or.inl ⟨max B B₀, fun y hy ↦
        Real.rpow_lt_rpow_of_exponent_lt
          (hB₀ y ((le_max_right B B₀).trans_lt hy))
          (hB y ((le_max_left B B₀).trans_lt hy))⟩)
    · obtain ⟨B, hB⟩ := hgt
      exact Or.inr (Or.inr ⟨max B B₀, fun y hy ↦
        Real.rpow_lt_rpow_of_exponent_lt
          (hB₀ y ((le_max_right B B₀).trans_lt hy))
          (hB y ((le_max_left B B₀).trans_lt hy))⟩)

end UnaryExpr

end

end Natfunbasis.Wilkie
