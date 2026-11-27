import Natfunbasis.OriginalTermAtInfinitySubclasses
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Monotonicity reduction for original terms at infinity

Every positive original unary term is either constant or is strictly
increasing above input `1` and unbounded above.  Consequently every
at-infinity comparison involving a constant term is unconditional.  The
full integer-to-real problem is reduced to the genuinely Hardy-field part:
eventual comparison of two increasing, unbounded original terms.
-/

namespace Natfunbasis.Wilkie

open Filter Set

noncomputable section

namespace UnaryExpr

/-- The positive-real interpretation is a constant at least `1`. -/
def ConstantEvaluation (e : UnaryExpr) : Prop :=
  ∃ c : Real, 1 ≤ c ∧ evalReal e = fun _ ↦ c

/-- Strict increase once the input has reached `1`. -/
def StrictlyIncreasingAboveOne (e : UnaryExpr) : Prop :=
  ∀ ⦃x y : PositiveReal⦄, 1 ≤ x.1 → x.1 < y.1 →
    evalReal e x < evalReal e y

/-- Unboundedness along inputs larger than `1`. -/
def UnboundedAboveAtInfinity (e : UnaryExpr) : Prop :=
  ∀ C : Real, ∃ y : PositiveReal,
    1 < y.1 ∧ C < evalReal e y

/-- The nonconstant shape of a positive original term. -/
structure IncreasingUnbounded (e : UnaryExpr) : Prop where
  strictlyIncreasingAboveOne : StrictlyIncreasingAboveOne e
  unboundedAboveAtInfinity : UnboundedAboveAtInfinity e

/-- Either branch of the structural dichotomy is nondecreasing above `1`. -/
theorem nondecreasingAboveOne_of_constant_or_increasingUnbounded
    {e : UnaryExpr}
    (hshape : ConstantEvaluation e ∨ IncreasingUnbounded e) :
    ∀ ⦃x y : PositiveReal⦄, 1 ≤ x.1 → x.1 ≤ y.1 →
      evalReal e x ≤ evalReal e y := by
  intro x y hx hxy
  rcases hshape with ⟨c, -, hc⟩ | hinc
  · rw [congrFun hc x, congrFun hc y]
  · rcases hxy.eq_or_lt with hxy | hxy
    · have hxy' : x = y := Subtype.ext hxy
      subst y
      exact le_rfl
    · exact (hinc.strictlyIncreasingAboveOne hx hxy).le

/-- Every original term is either constant or strictly increasing and
unbounded above.  This is the elementary monotonic part of the Hardy-style
analysis; it uses no external identity theorem. -/
theorem constantEvaluation_or_increasingUnbounded (e : UnaryExpr) :
    ConstantEvaluation e ∨ IncreasingUnbounded e := by
  induction e with
  | one =>
      left
      refine ⟨1, le_rfl, ?_⟩
      funext y
      rfl
  | var x =>
      cases x
      right
      refine ⟨?_, ?_⟩
      · intro a b _ hab
        exact hab
      · intro C
        let y : PositiveReal :=
          ⟨max 2 (C + 1), lt_of_lt_of_le (by norm_num) (le_max_left _ _)⟩
        refine ⟨y, ?_, ?_⟩
        · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
        · change C < max 2 (C + 1)
          exact lt_of_lt_of_le (lt_add_one C) (le_max_right _ _)
  | add s t hs ht =>
      have hsMono :=
        nondecreasingAboveOne_of_constant_or_increasingUnbounded hs
      have htMono :=
        nondecreasingAboveOne_of_constant_or_increasingUnbounded ht
      rcases hs with ⟨a, ha, hsa⟩ | hsInc
      · rcases ht with ⟨b, hb, htb⟩ | htInc
        · left
          refine ⟨a + b, by linarith, ?_⟩
          funext y
          change evalReal s y + evalReal t y = a + b
          rw [congrFun hsa y, congrFun htb y]
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change evalReal s x + evalReal t x <
              evalReal s y + evalReal t y
            rw [congrFun hsa x, congrFun hsa y]
            exact add_lt_add_right
              (htInc.strictlyIncreasingAboveOne hx hxy) a
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              htInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < evalReal s y + evalReal t y
            exact hCy.trans
              (lt_add_of_pos_left _ (evalReal_pos s y))
      · rcases ht with ⟨b, hb, htb⟩ | htInc
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change evalReal s x + evalReal t x <
              evalReal s y + evalReal t y
            rw [congrFun htb x, congrFun htb y]
            exact add_lt_add_left
              (hsInc.strictlyIncreasingAboveOne hx hxy) b
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              hsInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < evalReal s y + evalReal t y
            exact hCy.trans
              (lt_add_of_pos_right _ (evalReal_pos t y))
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            exact add_lt_add
              (hsInc.strictlyIncreasingAboveOne hx hxy)
              (htInc.strictlyIncreasingAboveOne hx hxy)
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              hsInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < evalReal s y + evalReal t y
            exact hCy.trans
              (lt_add_of_pos_right _ (evalReal_pos t y))
  | mul s t hs ht =>
      have hsMono :=
        nondecreasingAboveOne_of_constant_or_increasingUnbounded hs
      have htMono :=
        nondecreasingAboveOne_of_constant_or_increasingUnbounded ht
      rcases hs with ⟨a, ha, hsa⟩ | hsInc
      · rcases ht with ⟨b, hb, htb⟩ | htInc
        · left
          refine ⟨a * b, ?_, ?_⟩
          · calc
              1 = 1 * 1 := by norm_num
              _ ≤ a * b := mul_le_mul ha hb (by norm_num) (by linarith)
          funext y
          change evalReal s y * evalReal t y = a * b
          rw [congrFun hsa y, congrFun htb y]
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change evalReal s x * evalReal t x <
              evalReal s y * evalReal t y
            rw [congrFun hsa x, congrFun hsa y]
            exact mul_lt_mul_of_pos_left
              (htInc.strictlyIncreasingAboveOne hx hxy)
              (zero_lt_one.trans_le ha)
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              htInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < evalReal s y * evalReal t y
            calc
              C < evalReal t y := hCy
              _ ≤ evalReal s y * evalReal t y := by
                rw [congrFun hsa y]
                calc
                  evalReal t y = 1 * evalReal t y := by rw [one_mul]
                  _ ≤ a * evalReal t y :=
                    mul_le_mul_of_nonneg_right ha (evalReal_pos t y).le
      · rcases ht with ⟨b, hb, htb⟩ | htInc
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change evalReal s x * evalReal t x <
              evalReal s y * evalReal t y
            rw [congrFun htb x, congrFun htb y]
            exact mul_lt_mul_of_pos_right
              (hsInc.strictlyIncreasingAboveOne hx hxy)
              (zero_lt_one.trans_le hb)
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              hsInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < evalReal s y * evalReal t y
            calc
              C < evalReal s y := hCy
              _ ≤ evalReal s y * evalReal t y := by
                rw [congrFun htb y]
                calc
                  evalReal s y = evalReal s y * 1 := by rw [mul_one]
                  _ ≤ evalReal s y * b :=
                    mul_le_mul_of_nonneg_left hb (evalReal_pos s y).le
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change evalReal s x * evalReal t x <
              evalReal s y * evalReal t y
            calc
              evalReal s x * evalReal t x <
                  evalReal s y * evalReal t x :=
                mul_lt_mul_of_pos_right
                  (hsInc.strictlyIncreasingAboveOne hx hxy)
                  (evalReal_pos t x)
              _ ≤ evalReal s y * evalReal t y :=
                mul_le_mul_of_nonneg_left
                  (htMono hx hxy.le) (evalReal_pos s y).le
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              hsInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < evalReal s y * evalReal t y
            calc
              C < evalReal s y := hCy
              _ ≤ evalReal s y * evalReal t y :=
                calc
                  evalReal s y = evalReal s y * 1 := by rw [mul_one]
                  _ ≤ evalReal s y * evalReal t y :=
                    mul_le_mul_of_nonneg_left
                      (evalReal_one_le_of_one_le_input t y hy.le)
                      (evalReal_pos s y).le
  | pow s t hs ht =>
      have htMono :=
        nondecreasingAboveOne_of_constant_or_increasingUnbounded ht
      rcases hs with ⟨a, ha, hsa⟩ | hsInc
      · rcases ht with ⟨b, hb, htb⟩ | htInc
        · left
          refine ⟨Real.rpow a b,
            Real.one_le_rpow ha (zero_le_one.trans hb), ?_⟩
          funext y
          change Real.rpow (evalReal s y) (evalReal t y) =
            Real.rpow a b
          rw [congrFun hsa y, congrFun htb y]
        · rcases ha.eq_or_lt with rfl | ha
          · left
            refine ⟨1, le_rfl, ?_⟩
            funext y
            change Real.rpow (evalReal s y) (evalReal t y) = 1
            rw [congrFun hsa y]
            exact Real.one_rpow _
          · right
            refine ⟨?_, ?_⟩
            · intro x y hx hxy
              change Real.rpow (evalReal s x) (evalReal t x) <
                Real.rpow (evalReal s y) (evalReal t y)
              rw [congrFun hsa x, congrFun hsa y]
              exact Real.rpow_lt_rpow_of_exponent_lt ha
                (htInc.strictlyIncreasingAboveOne hx hxy)
            · intro C
              obtain ⟨z, hz⟩ := eventually_atTop.1
                ((tendsto_rpow_atTop_of_base_gt_one a ha).eventually_gt_atTop C)
              obtain ⟨y, hy, hzy⟩ :=
                htInc.unboundedAboveAtInfinity z
              refine ⟨y, hy, ?_⟩
              change C < Real.rpow (evalReal s y) (evalReal t y)
              rw [congrFun hsa y]
              exact hz _ hzy.le
      · rcases ht with ⟨b, hb, htb⟩ | htInc
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change Real.rpow (evalReal s x) (evalReal t x) <
              Real.rpow (evalReal s y) (evalReal t y)
            rw [congrFun htb x, congrFun htb y]
            exact Real.rpow_lt_rpow (evalReal_pos s x).le
              (hsInc.strictlyIncreasingAboveOne hx hxy)
              (zero_lt_one.trans_le hb)
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              hsInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < Real.rpow (evalReal s y) (evalReal t y)
            rw [congrFun htb y]
            exact hCy.trans_le
              (Real.self_le_rpow_of_one_le
                (evalReal_one_le_of_one_le_input s y hy.le) hb)
        · right
          refine ⟨?_, ?_⟩
          · intro x y hx hxy
            change Real.rpow (evalReal s x) (evalReal t x) <
              Real.rpow (evalReal s y) (evalReal t y)
            calc
              Real.rpow (evalReal s x) (evalReal t x) <
                  Real.rpow (evalReal s y) (evalReal t x) :=
                Real.rpow_lt_rpow (evalReal_pos s x).le
                  (hsInc.strictlyIncreasingAboveOne hx hxy)
                  (evalReal_pos t x)
              _ ≤ Real.rpow (evalReal s y) (evalReal t y) :=
                Real.rpow_le_rpow_of_exponent_le
                  (evalReal_one_le_of_one_le_input s y
                    (hx.trans hxy.le))
                  (htMono hx hxy.le)
          · intro C
            obtain ⟨y, hy, hCy⟩ :=
              hsInc.unboundedAboveAtInfinity C
            refine ⟨y, hy, ?_⟩
            change C < Real.rpow (evalReal s y) (evalReal t y)
            exact hCy.trans_le
              (Real.self_le_rpow_of_one_le
                (evalReal_one_le_of_one_le_input s y hy.le)
                (evalReal_one_le_of_one_le_input t y hy.le))

/-- A nonconstant original term has the increasing-unbounded branch. -/
theorem increasingUnbounded_of_not_constantEvaluation {e : UnaryExpr}
    (h : ¬ ConstantEvaluation e) : IncreasingUnbounded e :=
  (constantEvaluation_or_increasingUnbounded e).resolve_left h

/-- Strict eventual dominance in the explicit threshold form used by the
at-infinity property. -/
def EventuallyStrictlyLess (e d : UnaryExpr) : Prop :=
  ∃ B : Real, ∀ y : PositiveReal, B < y.1 → evalReal e y < evalReal d y

/-- A constant term is eventually dominated by every increasing-unbounded
term. -/
theorem ConstantEvaluation.eventuallyStrictlyLess
    {e d : UnaryExpr} (he : ConstantEvaluation e)
    (hd : IncreasingUnbounded d) : EventuallyStrictlyLess e d := by
  obtain ⟨c, -, hec⟩ := he
  obtain ⟨y₀, hy₀, hcy₀⟩ := hd.unboundedAboveAtInfinity c
  refine ⟨y₀.1, ?_⟩
  intro y hy
  rw [congrFun hec y]
  exact hcy₀.trans
    (hd.strictlyIncreasingAboveOne hy₀.le hy)

/-- Eventual strict dominance rules out equality points arbitrarily far to
the right. -/
theorem AtInfinityUniquePair.of_eventuallyStrictlyLess {e d : UnaryExpr}
    (h : EventuallyStrictlyLess e d) : AtInfinityUniquePair e d := by
  obtain ⟨B, hB⟩ := h
  intro hunbounded
  obtain ⟨y, hy, heq⟩ := hunbounded B
  exact False.elim ((ne_of_lt (hB y hy)) heq)

/-- Pairwise at-infinity uniqueness is symmetric. -/
theorem AtInfinityUniquePair.flip {e d : UnaryExpr}
    (h : AtInfinityUniquePair e d) : AtInfinityUniquePair d e := by
  intro hunbounded
  symm
  apply h
  intro B
  obtain ⟨y, hy, heq⟩ := hunbounded B
  exact ⟨y, hy, heq.symm⟩

/-- Every pair involving a constant original term satisfies at-infinity
uniqueness unconditionally. -/
theorem ConstantEvaluation.atInfinityUniquePair_left {e d : UnaryExpr}
    (he : ConstantEvaluation e) : AtInfinityUniquePair e d := by
  rcases constantEvaluation_or_increasingUnbounded d with hd | hd
  · obtain ⟨c, -, hec⟩ := he
    obtain ⟨q, -, hdq⟩ := hd
    intro hunbounded
    obtain ⟨y, -, heq⟩ := hunbounded 0
    rw [congrFun hec y, congrFun hdq y] at heq
    funext z
    rw [congrFun hec z, congrFun hdq z, heq]
  · exact AtInfinityUniquePair.of_eventuallyStrictlyLess
      (he.eventuallyStrictlyLess hd)

theorem ConstantEvaluation.atInfinityUniquePair_right {e d : UnaryExpr}
    (hd : ConstantEvaluation d) : AtInfinityUniquePair e d :=
  hd.atInfinityUniquePair_left.flip

/-! ## Eventual order, the remaining Hardy-field input -/

/-- The usual Hardy-field trichotomy for one pair: the functions are equal,
or one is strictly below the other beyond a threshold. -/
def EventualOrderTrichotomyPair (e d : UnaryExpr) : Prop :=
  evalReal e = evalReal d ∨
    EventuallyStrictlyLess e d ∨ EventuallyStrictlyLess d e

/-- Eventual order trichotomy immediately gives pairwise at-infinity
uniqueness. -/
theorem EventualOrderTrichotomyPair.atInfinityUniquePair
    {e d : UnaryExpr} (h : EventualOrderTrichotomyPair e d) :
    AtInfinityUniquePair e d := by
  rcases h with heq | hlt | hgt
  · intro _
    exact heq
  · exact AtInfinityUniquePair.of_eventuallyStrictlyLess hlt
  · exact (AtInfinityUniquePair.of_eventuallyStrictlyLess hgt).flip

/-- Eventual order trichotomy is symmetric. -/
theorem EventualOrderTrichotomyPair.flip {e d : UnaryExpr}
    (h : EventualOrderTrichotomyPair e d) :
    EventualOrderTrichotomyPair d e := by
  rcases h with heq | hlt | hgt
  · exact Or.inl heq.symm
  · exact Or.inr (Or.inr hlt)
  · exact Or.inr (Or.inl hgt)

/-- Eventual comparison is unconditional when the left term is constant. -/
theorem ConstantEvaluation.eventualOrderTrichotomyPair_left
    {e d : UnaryExpr} (he : ConstantEvaluation e) :
    EventualOrderTrichotomyPair e d := by
  rcases constantEvaluation_or_increasingUnbounded d with hd | hd
  · obtain ⟨c, -, hec⟩ := he
    obtain ⟨q, -, hdq⟩ := hd
    rcases lt_trichotomy c q with hcq | hcq | hcq
    · exact Or.inr (Or.inl ⟨0, fun y _ ↦ by
        rw [congrFun hec y, congrFun hdq y]
        exact hcq⟩)
    · exact Or.inl (by
        funext y
        rw [congrFun hec y, congrFun hdq y, hcq])
    · exact Or.inr (Or.inr ⟨0, fun y _ ↦ by
        rw [congrFun hec y, congrFun hdq y]
        exact hcq⟩)
  · exact Or.inr (Or.inl (he.eventuallyStrictlyLess hd))

theorem ConstantEvaluation.eventualOrderTrichotomyPair_right
    {e d : UnaryExpr} (hd : ConstantEvaluation d) :
    EventualOrderTrichotomyPair e d :=
  hd.eventualOrderTrichotomyPair_left.flip

/-- Global eventual order of original terms.  This is a standard
Hardy-field/no-oscillation formulation of the remaining source theorem. -/
def OriginalTermEventualOrderTrichotomy : Prop :=
  ∀ e d : UnaryExpr, EventualOrderTrichotomyPair e d

/-- All constant cases of global eventual order are automatic; it remains
only to compare two increasing-unbounded original terms. -/
theorem originalTermEventualOrderTrichotomy_iff_increasingUnboundedPairs :
    OriginalTermEventualOrderTrichotomy ↔
      ∀ e d : UnaryExpr, IncreasingUnbounded e → IncreasingUnbounded d →
        EventualOrderTrichotomyPair e d := by
  constructor
  · intro h e d _ _
    exact h e d
  · intro h e d
    rcases constantEvaluation_or_increasingUnbounded e with he | he
    · exact he.eventualOrderTrichotomyPair_left
    · rcases constantEvaluation_or_increasingUnbounded d with hd | hd
      · exact hd.eventualOrderTrichotomyPair_right
      · exact h e d he hd

/-- Eventual Hardy-field order is sufficient for the exact at-infinity
identity property. -/
theorem originalTermAtInfinityIdentity_of_eventualOrderTrichotomy
    (h : OriginalTermEventualOrderTrichotomy) :
    OriginalTermAtInfinityIdentity := by
  intro e d
  exact (h e d).atInfinityUniquePair

/-- Consequently eventual Hardy-field order is also sufficient for the
integer-to-real transfer consumed by the normalizer. -/
theorem originalTermIntegerToReal_of_eventualOrderTrichotomy
    (h : OriginalTermEventualOrderTrichotomy) :
    OriginalTermIntegerToReal :=
  originalTermIntegerToReal_of_atInfinityIdentity
    (originalTermAtInfinityIdentity_of_eventualOrderTrichotomy h)

/-- Exact reduction of the at-infinity identity: all constant cases are now
proved, so only pairs of increasing-unbounded term functions remain. -/
theorem originalTermAtInfinityIdentity_iff_increasingUnboundedPairs :
    OriginalTermAtInfinityIdentity ↔
      ∀ e d : UnaryExpr, IncreasingUnbounded e → IncreasingUnbounded d →
        AtInfinityUniquePair e d := by
  constructor
  · intro h e d _ _
    exact h e d
  · intro h e d hunbounded
    rcases constantEvaluation_or_increasingUnbounded e with he | he
    · exact he.atInfinityUniquePair_left hunbounded
    · rcases constantEvaluation_or_increasingUnbounded d with hd | hd
      · exact hd.atInfinityUniquePair_right hunbounded
      · exact h e d he hd hunbounded

/-- The integer-to-real transfer follows once the remaining
increasing-unbounded pairs have at-infinity uniqueness. -/
theorem originalTermIntegerToReal_of_increasingUnboundedPairs
    (h : ∀ e d : UnaryExpr,
      IncreasingUnbounded e → IncreasingUnbounded d →
        AtInfinityUniquePair e d) :
    OriginalTermIntegerToReal :=
  originalTermIntegerToReal_of_atInfinityIdentity
    (originalTermAtInfinityIdentity_iff_increasingUnboundedPairs.mpr h)

end UnaryExpr

end

end Natfunbasis.Wilkie
