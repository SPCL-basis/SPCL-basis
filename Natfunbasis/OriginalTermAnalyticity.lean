import Natfunbasis.WilkieAnalyticPrerequisites
import Natfunbasis.WilkieTheorem44Target
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analyticity and the unary integer-to-real reduction

This module proves the elementary analytic part of the integer-to-real
handoff for original one-variable terms.  Every such term has a real-analytic
extension on the positive axis.  It then isolates a precise zero-set
dichotomy which is sufficient for the project proposition
`OriginalTermIntegerToReal`.

The zero-set dichotomy itself is not proved here.  For the larger
combinatorial language it is Lemma 3.9 of Alsulami--Jackson,
*Finite models for positive combinatorial and exponential algebra*, and its
proof invokes o-minimality.  Thus this file records a checked reduction, not
a replacement of the missing source input.
-/

namespace Natfunbasis.Wilkie

open Set

noncomputable section

namespace UnaryExpr

/-- Every original unary term, interpreted with real exponentiation, is the
restriction of a real-analytic function on the positive real axis. -/
theorem evalReal_isPositiveAnalytic (e : UnaryExpr) :
    IsPositiveAnalytic (evalReal e) := by
  induction e with
  | one =>
      refine ⟨fun _ ↦ 1, analyticOnNhd_const, ?_⟩
      intro y
      rfl
  | var x =>
      cases x
      refine ⟨id, analyticOnNhd_id, ?_⟩
      intro y
      rfl
  | add s t hs ht =>
      obtain ⟨S, hS, hsRestrict⟩ := hs
      obtain ⟨T, hT, htRestrict⟩ := ht
      refine ⟨S + T, hS.add hT, ?_⟩
      intro y
      simp only [evalReal, RealExpression.eval, Pi.add_apply]
      change evalReal s y + evalReal t y = S y.1 + T y.1
      rw [hsRestrict y, htRestrict y]
  | mul s t hs ht =>
      obtain ⟨S, hS, hsRestrict⟩ := hs
      obtain ⟨T, hT, htRestrict⟩ := ht
      refine ⟨S * T, hS.mul hT, ?_⟩
      intro y
      simp only [evalReal, RealExpression.eval, Pi.mul_apply]
      change evalReal s y * evalReal t y = S y.1 * T y.1
      rw [hsRestrict y, htRestrict y]
  | pow s t hs ht =>
      obtain ⟨S, hS, hsRestrict⟩ := hs
      obtain ⟨T, hT, htRestrict⟩ := ht
      let powerExtension : Real → Real :=
        fun x ↦ Real.exp (Real.log (S x) * T x)
      have hSPositive : ∀ x ∈ positiveAxis, 0 < S x := by
        intro x hx
        let y : PositiveReal := ⟨x, hx⟩
        rw [← hsRestrict y]
        exact evalReal_pos s y
      have hlogS :
          AnalyticOnNhd Real (fun x ↦ Real.log (S x)) positiveAxis := by
        intro x hx
        exact (analyticAt_log (hSPositive x hx)).comp (hS x hx)
      have hpower : AnalyticOnNhd Real powerExtension positiveAxis := by
        exact (hlogS.mul hT).rexp
      refine ⟨powerExtension, hpower, ?_⟩
      intro y
      simp only [evalReal, RealExpression.eval, powerExtension]
      change Real.rpow (evalReal s y) (evalReal t y) =
        Real.exp (Real.log (S y.1) * T y.1)
      change (evalReal s y) ^ (evalReal t y) =
        Real.exp (Real.log (S y.1) * T y.1)
      rw [Real.rpow_def_of_pos (evalReal_pos s y),
        hsRestrict y, htRestrict y]

end UnaryExpr

/-! ## Exact zero-set reduction -/

/-- The unary finite-zero-set alternative needed to pass from agreement on
positive integers to agreement on all positive reals.

The first disjunct is literal equality of the term functions.  The second
says that, when they are not identical, their equality set on the positive
axis is finite. -/
def OriginalTermFiniteOrIdentical : Prop :=
  ∀ e d : UnaryExpr,
    UnaryExpr.evalReal e = UnaryExpr.evalReal d ∨
      {y : PositiveReal | UnaryExpr.evalReal e y =
        UnaryExpr.evalReal d y}.Finite

/-- Positive integers give infinitely many distinct points of the positive
real axis. -/
theorem integerRealInput_injective : Function.Injective integerRealInput := by
  intro m n h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change (m.1 : Real) = (n.1 : Real) at hval
  exact_mod_cast hval

theorem posNat_infinite : Infinite PosNat := by
  apply Infinite.of_injective
    (fun n : Nat ↦ (⟨n + 1, by omega⟩ : PosNat))
  intro m n h
  have hval : m + 1 = n + 1 :=
    congrArg (fun z : PosNat ↦ z.1) h
  omega

theorem integerRealInput_range_infinite :
    (Set.range integerRealInput).Infinite := by
  letI : Infinite PosNat := posNat_infinite
  rw [Set.infinite_range_iff integerRealInput_injective]
  infer_instance

/-- The finite-zero-set alternative implies the exact Macintyre-style
one-variable transfer proposition used by the normal-form construction. -/
theorem originalTermIntegerToReal_of_finiteOrIdentical
    (hfinite : OriginalTermFiniteOrIdentical) :
    OriginalTermIntegerToReal := by
  intro e d hsem
  rcases hfinite e d with heq | hfiniteZeros
  · exact heq
  · exfalso
    apply integerRealInput_range_infinite
    apply hfiniteZeros.subset
    rintro y ⟨n, rfl⟩
    change UnaryExpr.evalReal e (integerRealInput n) =
      UnaryExpr.evalReal d (integerRealInput n)
    simpa only [UnaryExpr.evalReal_integer] using
      congrArg (fun value : Nat ↦ (value : Real)) (hsem n)

end

end Natfunbasis.Wilkie
