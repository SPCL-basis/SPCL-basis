import Natfunbasis.OriginalTermRichardsonRolle
import Natfunbasis.WilkieProposition31
import Natfunbasis.WilkieProposition31II
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Richardson descent through primitive and exponential adjunctions

This file isolates the algebraic part of the Hardy/Richardson finite-zero
argument.  A polynomial in a new primitive has a derivative of smaller degree
after monic normalization.  A polynomial in a nowhere-zero exponential is
handled by Horner descent when its constant coefficient is zero, and otherwise
by normalizing that coefficient and dividing its derivative by `X`.

The real-analysis input is exactly the Rolle closure proved in
`OriginalTermRichardsonRolle`.  Notably, no transcendence or no-new-constants
hypothesis is required for the zero/nonzero dichotomy: if a normalized
polynomial vanishes on a tail, that conclusion transfers algebraically back
to the original polynomial.
-/

open scoped Differential
open Polynomial

namespace Natfunbasis.Wilkie.RichardsonExtension

noncomputable section

variable {K : Type*} [Field K]

/-- Evaluate a polynomial whose coefficients are real-valued functions at a
real-valued generator. -/
def polynomialEval (ι : K →+* (Real → Real)) (theta : Real → Real)
    (p : K[X]) : Real → Real :=
  p.eval₂ ι theta

@[simp]
theorem polynomialEval_zero (ι : K →+* (Real → Real))
    (theta : Real → Real) :
    polynomialEval ι theta (0 : K[X]) = 0 := by
  simp [polynomialEval]

@[simp]
theorem polynomialEval_C (ι : K →+* (Real → Real))
    (theta : Real → Real) (a : K) :
    polynomialEval ι theta (C a) = ι a := by
  simp [polynomialEval]

@[simp]
theorem polynomialEval_X (ι : K →+* (Real → Real))
    (theta : Real → Real) :
    polynomialEval ι theta (X : K[X]) = theta := by
  simp [polynomialEval]

@[simp]
theorem polynomialEval_mul (ι : K →+* (Real → Real))
    (theta : Real → Real) (p q : K[X]) :
    polynomialEval ι theta (p * q) =
      polynomialEval ι theta p * polynomialEval ι theta q := by
  simp [polynomialEval]

/-- A realization of a polynomial derivation by ordinary real
differentiation on the positive axis. -/
def RealizesDerivation (ι : K →+* (Real → Real))
    (theta : Real → Real) (D : K[X] → K[X]) : Prop :=
  ∀ (p : K[X]) (x : Real), 0 < x →
    HasDerivAt (polynomialEval ι theta p)
      (polynomialEval ι theta (D p) x) x

/-- The coefficient embedding intertwines its differential-field derivation
with ordinary real differentiation on the positive axis. -/
def RealizesBaseDerivation [Differential K]
    (ι : K →+* (Real → Real)) : Prop :=
  ∀ (a : K) (x : Real), 0 < x →
    HasDerivAt (ι a) (ι a′ x) x

/-- Polynomial evaluation realizes `implicitDeriv v` as soon as the
coefficient embedding realizes the base derivation and the new generator has
derivative `v(theta)`. -/
theorem realizesDerivation_implicitDeriv [Differential K]
    (ι : K →+* (Real → Real)) (theta : Real → Real) (v : K[X])
    (hι : RealizesBaseDerivation ι)
    (htheta : ∀ x : Real, 0 < x →
      HasDerivAt theta (polynomialEval ι theta v x) x) :
    RealizesDerivation ι theta (Differential.implicitDeriv v) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      intro x hx
      simpa [polynomialEval] using (hp x hx).add (hq x hx)
  | monomial n a =>
      intro x hx
      have ha := hι a x hx
      have hpow := (htheta x hx).pow n
      have hmul := ha.mul hpow
      have hfun : polynomialEval ι theta (monomial n a) =
          ι a * theta ^ n := by
        simp [polynomialEval]
      rw [hfun]
      apply hmul.congr_deriv
      simp [polynomialEval, ← C_mul_X_pow_eq_monomial,
        Differential.implicitDeriv, Derivation.leibniz,
        Derivation.leibniz_pow]
      ring

/-- The finite-zero dichotomy for all polynomials in one generator. -/
def PolynomialTailDichotomy (ι : K →+* (Real → Real))
    (theta : Real → Real) : Prop :=
  ∀ p : K[X],
    EventuallyZero (polynomialEval ι theta p) ∨
      EventuallyNowhereZero (polynomialEval ι theta p)

private theorem eventuallyZero_of_forall_pos_eq
    {f g : Real → Real} (hf : EventuallyZero f)
    (hfg : ∀ x : Real, 0 < x → g x = f x) : EventuallyZero g := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨max B 0, fun x hx ↦ ?_⟩
  rw [hfg x ((le_max_right B 0).trans_lt hx)]
  exact hB x ((le_max_left B 0).trans_lt hx)

private theorem eventuallyNowhereZero_of_forall_pos_eq
    {f g : Real → Real} (hf : EventuallyNowhereZero f)
    (hfg : ∀ x : Real, 0 < x → g x = f x) :
    EventuallyNowhereZero g := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨max B 0, fun x hx ↦ ?_⟩
  rw [hfg x ((le_max_right B 0).trans_lt hx)]
  exact hB x ((le_max_left B 0).trans_lt hx)

private theorem eventuallyZero_mul_right
    {f g : Real → Real} (hf : EventuallyZero f) :
    EventuallyZero (f * g) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, fun x hx ↦ by simp [hB x hx]⟩

private theorem eventuallyNowhereZero_mul_right
    {f g : Real → Real} (hf : EventuallyNowhereZero f)
    (hg : ∀ x : Real, 0 < x → g x ≠ 0) :
    EventuallyNowhereZero (f * g) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨max B 0, fun x hx hzero ↦ ?_⟩
  rcases mul_eq_zero.mp hzero with hfx | hgx
  · exact hB x ((le_max_left B 0).trans_lt hx) hfx
  · exact hg x ((le_max_right B 0).trans_lt hx) hgx

private theorem eventuallyDerivativeDichotomy_of_realizes
    {ι : K →+* (Real → Real)} {theta : Real → Real}
    {D : K[X] → K[X]} (hD : RealizesDerivation ι theta D)
    (p : K[X])
    (hp : EventuallyZero (polynomialEval ι theta (D p)) ∨
      EventuallyNowhereZero (polynomialEval ι theta (D p))) :
    EventuallyZero (deriv (polynomialEval ι theta p)) ∨
      EventuallyNowhereZero (deriv (polynomialEval ι theta p)) := by
  rcases hp with hp | hp
  · left
    exact eventuallyZero_of_forall_pos_eq hp fun x hx ↦
      (hD p x hx).deriv
  · right
    exact eventuallyNowhereZero_of_forall_pos_eq hp fun x hx ↦
      (hD p x hx).deriv

private theorem differentiable_of_realizes
    {ι : K →+* (Real → Real)} {theta : Real → Real}
    {D : K[X] → K[X]} (hD : RealizesDerivation ι theta D)
    (p : K[X]) :
    ∀ x : Real, 0 < x → DifferentiableAt Real
      (polynomialEval ι theta p) x :=
  fun x hx ↦ (hD p x hx).differentiableAt

section Primitive

variable [Differential K]

/-- After monic normalization, a primitive-extension derivative strictly
lowers degree unless it vanishes. -/
theorem natDegree_implicitDeriv_translation_lt_of_monic
    (c : K) {p : K[X]} (hp : p.Monic)
    (hDp : Differential.implicitDeriv (C c) p ≠ 0) :
    (Differential.implicitDeriv (C c) p).natDegree < p.natDegree := by
  have hle :=
    Proposition31II.natDegree_implicitDeriv_translation_le c p
  have htop :
      (Differential.implicitDeriv (C c) p).coeff p.natDegree = 0 := by
    rw [Proposition31II.coeff_implicitDeriv_translation]
    have hnext : p.coeff (p.natDegree + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    rw [show p.coeff p.natDegree = 1 by
      simpa only [Polynomial.leadingCoeff] using hp.leadingCoeff, hnext]
    simp
  by_contra hnot
  have heq :
      (Differential.implicitDeriv (C c) p).natDegree = p.natDegree :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hlead :
      (Differential.implicitDeriv (C c) p).coeff
          (Differential.implicitDeriv (C c) p).natDegree ≠ 0 := by
    simpa only [Polynomial.leadingCoeff] using
      (Polynomial.leadingCoeff_ne_zero.mpr hDp)
  exact hlead (by simpa only [heq] using htop)

/-- A primitive adjunction preserves the finite-zero dichotomy.  The
derivation-realization hypothesis packages `theta' = c`. -/
theorem polynomialTailDichotomy_primitive
    (ι : K →+* (Real → Real)) (theta : Real → Real) (c : K)
    (hD : RealizesDerivation ι theta
      (Differential.implicitDeriv (C c))) :
    PolynomialTailDichotomy ι theta := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp0 : p = 0
      · left
        subst p
        exact ⟨0, by simp⟩
      · let q : K[X] := p * C p.leadingCoeff⁻¹
        have hlc0 : p.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hp0
        have hqmonic : q.Monic := by
          exact Polynomial.monic_mul_leadingCoeff_inv hp0
        let Dq := Differential.implicitDeriv (C c) q
        have hDqDichotomy :
            EventuallyZero (polynomialEval ι theta Dq) ∨
              EventuallyNowhereZero (polynomialEval ι theta Dq) := by
          by_cases hDq0 : Dq = 0
          · left
            rw [hDq0]
            exact ⟨0, by simp⟩
          · have hqdeg : q.natDegree = p.natDegree := by
              dsimp [q]
              exact Polynomial.natDegree_mul_C
                (inv_ne_zero hlc0)
            have hlt : Dq.natDegree < n := by
              rw [← hn, ← hqdeg]
              exact natDegree_implicitDeriv_translation_lt_of_monic
                c hqmonic hDq0
            exact ih Dq.natDegree hlt Dq rfl
        have hderivDichotomy :=
          eventuallyDerivativeDichotomy_of_realizes hD q hDqDichotomy
        have hqDichotomy :
            EventuallyZero (polynomialEval ι theta q) ∨
              EventuallyNowhereZero (polynomialEval ι theta q) :=
          eventuallyZero_or_eventuallyNowhereZero_of_deriv_dichotomy
            (differentiable_of_realizes hD q) hderivDichotomy
        have heval :
            polynomialEval ι theta q =
              polynomialEval ι theta p * ι p.leadingCoeff⁻¹ := by
          simp [q]
        rcases hqDichotomy with hqZero | hqNonzero
        · left
          have hpFromQ : polynomialEval ι theta p =
              polynomialEval ι theta q * ι p.leadingCoeff := by
            apply _root_.funext
            intro x
            have hinv :
                ι p.leadingCoeff⁻¹ x * ι p.leadingCoeff x = 1 := by
              rw [← Pi.mul_apply, ← map_mul]
              simp [hlc0]
            rw [heval, Pi.mul_apply, Pi.mul_apply, mul_assoc, hinv, mul_one]
          rw [hpFromQ]
          exact eventuallyZero_mul_right hqZero
        · right
          obtain ⟨B, hB⟩ := hqNonzero
          refine ⟨B, fun x hx hpx ↦ ?_⟩
          apply hB x hx
          rw [heval]
          simp [hpx]

/-- Primitive closure in terms of the coefficient ODEs and the generator
ODE, without mentioning the induced polynomial derivation explicitly. -/
theorem polynomialTailDichotomy_primitive_of_hasDerivAt
    (ι : K →+* (Real → Real)) (theta : Real → Real) (c : K)
    (hι : RealizesBaseDerivation ι)
    (htheta : ∀ x : Real, 0 < x →
      HasDerivAt theta (ι c x) x) :
    PolynomialTailDichotomy ι theta := by
  apply polynomialTailDichotomy_primitive ι theta c
  apply realizesDerivation_implicitDeriv ι theta (C c) hι
  intro x hx
  simpa using htheta x hx

end Primitive

section Exponential

variable [Differential K]

omit [Differential K] in
/-- If the constant coefficient is zero, dividing by `X` strictly lowers
the degree of a nonzero polynomial. -/
theorem natDegree_divX_lt_of_coeff_zero {p : K[X]} (hp0 : p ≠ 0)
    (hconst : p.coeff 0 = 0) : p.divX.natDegree < p.natDegree := by
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  have hpos : 0 < p.natDegree := by
    exact Nat.pos_of_ne_zero fun hdeg ↦ hp0 <|
      (Polynomial.eq_C_of_natDegree_eq_zero hdeg).trans <| by
        rw [hconst, C_0]
  omega

/-- An Euler derivative has zero constant coefficient after normalizing a
nonzero constant coefficient to `1`. -/
theorem coeff_zero_implicitDeriv_euler_of_coeff_zero_eq_one
    (c : K) {p : K[X]} (hp : p.coeff 0 = 1) :
    (Differential.implicitDeriv (C c * X) p).coeff 0 = 0 := by
  rw [Proposition31.coeff_implicitDeriv_euler, hp]
  simp

/-- A nowhere-zero exponential adjunction preserves the finite-zero
dichotomy.  The proof alternates Horner descent (`p(0)=0`) with Rolle descent
after normalizing a nonzero constant coefficient. -/
theorem polynomialTailDichotomy_exponential
    (ι : K →+* (Real → Real)) (theta : Real → Real) (c : K)
    (htheta : ∀ x : Real, 0 < x → theta x ≠ 0)
    (hD : RealizesDerivation ι theta
      (Differential.implicitDeriv (C c * X))) :
    PolynomialTailDichotomy ι theta := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp0 : p = 0
      · left
        subst p
        exact ⟨0, by simp⟩
      · by_cases hconst : p.coeff 0 = 0
        · let r := p.divX
          have hrlt : r.natDegree < n := by
            rw [← hn]
            exact natDegree_divX_lt_of_coeff_zero hp0 hconst
          have hrDichotomy := ih r.natDegree hrlt r rfl
          have hpEq : p = X * r := by
            have h := Polynomial.X_mul_divX_add p
            rw [hconst, C_0, add_zero] at h
            exact h.symm
          have heval : polynomialEval ι theta p =
              polynomialEval ι theta r * theta := by
            rw [hpEq]
            simp [mul_comm]
          rcases hrDichotomy with hrZero | hrNonzero
          · left
            rw [heval]
            exact eventuallyZero_mul_right hrZero
          · right
            rw [heval]
            exact eventuallyNowhereZero_mul_right hrNonzero htheta
        · let q : K[X] := C (p.coeff 0)⁻¹ * p
          have hqconst : q.coeff 0 = 1 := by
            simp [q, hconst]
          let Dq := Differential.implicitDeriv (C c * X) q
          have hDqconst : Dq.coeff 0 = 0 :=
            coeff_zero_implicitDeriv_euler_of_coeff_zero_eq_one c hqconst
          have hDqDichotomy :
              EventuallyZero (polynomialEval ι theta Dq) ∨
                EventuallyNowhereZero (polynomialEval ι theta Dq) := by
            by_cases hDq0 : Dq = 0
            · left
              rw [hDq0]
              exact ⟨0, by simp⟩
            · let r := Dq.divX
              have hqdeg : q.natDegree = p.natDegree := by
                dsimp [q]
                exact Polynomial.natDegree_C_mul (inv_ne_zero hconst)
              have hDqle : Dq.natDegree ≤ q.natDegree := by
                exact Proposition31.natDegree_implicitDeriv_euler_le c q
              have hrlt : r.natDegree < n := by
                have hrltDq :=
                  natDegree_divX_lt_of_coeff_zero hDq0 hDqconst
                rw [← hn, ← hqdeg]
                exact hrltDq.trans_le hDqle
              have hrDichotomy := ih r.natDegree hrlt r rfl
              have hDqEq : Dq = X * r := by
                have h := Polynomial.X_mul_divX_add Dq
                rw [hDqconst, C_0, add_zero] at h
                exact h.symm
              have heval : polynomialEval ι theta Dq =
                  polynomialEval ι theta r * theta := by
                rw [hDqEq]
                simp [mul_comm]
              rcases hrDichotomy with hrZero | hrNonzero
              · left
                rw [heval]
                exact eventuallyZero_mul_right hrZero
              · right
                rw [heval]
                exact eventuallyNowhereZero_mul_right hrNonzero htheta
          have hderivDichotomy :=
            eventuallyDerivativeDichotomy_of_realizes hD q hDqDichotomy
          have hqDichotomy :
              EventuallyZero (polynomialEval ι theta q) ∨
                EventuallyNowhereZero (polynomialEval ι theta q) :=
            eventuallyZero_or_eventuallyNowhereZero_of_deriv_dichotomy
              (differentiable_of_realizes hD q) hderivDichotomy
          have heval : polynomialEval ι theta q =
              ι (p.coeff 0)⁻¹ * polynomialEval ι theta p := by
            simp [q]
          rcases hqDichotomy with hqZero | hqNonzero
          · left
            have hpFromQ : polynomialEval ι theta p =
                ι (p.coeff 0) * polynomialEval ι theta q := by
              apply _root_.funext
              intro x
              have hinv :
                  ι (p.coeff 0) x * ι (p.coeff 0)⁻¹ x = 1 := by
                rw [← Pi.mul_apply, ← map_mul]
                simp [hconst]
              rw [heval, Pi.mul_apply, Pi.mul_apply, ← mul_assoc, hinv,
                one_mul]
            rw [hpFromQ]
            obtain ⟨B, hB⟩ := hqZero
            exact ⟨B, fun x hx ↦ by simp [hB x hx]⟩
          · right
            obtain ⟨B, hB⟩ := hqNonzero
            refine ⟨B, fun x hx hpx ↦ ?_⟩
            apply hB x hx
            rw [heval]
            simp [hpx]

/-- Exponential closure in terms of the coefficient ODEs and the generator
ODE, without mentioning the induced polynomial derivation explicitly. -/
theorem polynomialTailDichotomy_exponential_of_hasDerivAt
    (ι : K →+* (Real → Real)) (theta : Real → Real) (c : K)
    (htheta0 : ∀ x : Real, 0 < x → theta x ≠ 0)
    (hι : RealizesBaseDerivation ι)
    (htheta : ∀ x : Real, 0 < x →
      HasDerivAt theta (ι c x * theta x) x) :
    PolynomialTailDichotomy ι theta := by
  apply polynomialTailDichotomy_exponential ι theta c htheta0
  apply realizesDerivation_implicitDeriv ι theta (C c * X) hι
  intro x hx
  simpa [polynomialEval] using htheta x hx

end Exponential

end

end Natfunbasis.Wilkie.RichardsonExtension
