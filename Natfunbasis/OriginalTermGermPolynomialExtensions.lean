import Natfunbasis.OriginalTermDifferentialExtensions
import Natfunbasis.OriginalTermTailGerm

/-!
# Polynomial Richardson descent over a field of tail germs

`OriginalTermDifferentialExtensions` gives a convenient pointwise version of
the primitive and exponential closure arguments.  A field of analytic
functions, however, usually maps only to germs at `+∞`: inverses need not be
defined by the field laws at the finitely many zeros of a representative.

This file gives the germ-valued form needed for an iterated Hardy-field
construction.  We use a ring homomorphism from the polynomial ring into
`TailGerm`, choose arbitrary differentiable representatives, and require only
that germ differentiation realizes the relevant formal derivation.  All
algebraic identities are transported to eventual equalities automatically.
-/

open scoped Differential
open Polynomial Filter Set
open Natfunbasis.Wilkie.RichardsonExtension

namespace Natfunbasis.Wilkie.RichardsonGermExtension

noncomputable section

variable {K : Type*} [Field K]

/-- `representative p` represents the germ selected by `Phi p`. -/
def Represents (Phi : K[X] →+* TailGerm)
    (representative : K[X] → Real → Real) : Prop :=
  ∀ p : K[X], (representative p : TailGerm) = Phi p

/-- Every selected representative is differentiable on the positive axis. -/
def PositiveDifferentiable (representative : K[X] → Real → Real) : Prop :=
  ∀ (p : K[X]) (x : Real), 0 < x →
    DifferentiableAt Real (representative p) x

/-- Every selected representative is differentiable on some final tail. -/
def EventuallyDifferentiable
    (representative : K[X] → Real → Real) : Prop :=
  ∀ p : K[X], ∃ B : Real, ∀ x : Real, B < x →
    DifferentiableAt Real (representative p) x

theorem PositiveDifferentiable.eventually
    {representative : K[X] → Real → Real}
    (h : PositiveDifferentiable representative) :
    EventuallyDifferentiable representative := by
  intro p
  exact ⟨0, h p⟩

/-- Germ differentiation realizes a formal polynomial derivation. -/
def GermRealizesDerivation (Phi : K[X] →+* TailGerm)
    (D : K[X] → K[X]) : Prop :=
  ∀ p : K[X], TailGerm.deriv (Phi p) = Phi (D p)

/-- The finite-zero dichotomy for a chosen family of polynomial
representatives. -/
def RepresentativeTailDichotomy
    (representative : K[X] → Real → Real) : Prop :=
  ∀ p : K[X], EventuallyZero (representative p) ∨
    EventuallyNowhereZero (representative p)

private theorem eventuallyZero_congr {f g : Real → Real}
    (hfg : f =ᶠ[atTop] g) : EventuallyZero f ↔ EventuallyZero g := by
  rw [eventuallyZero_iff_tailGerm_eq_zero,
    eventuallyZero_iff_tailGerm_eq_zero]
  rw [Filter.EventuallyEq.germ_eq hfg]

private theorem eventuallyNowhereZero_congr {f g : Real → Real}
    (hfg : f =ᶠ[atTop] g) :
    EventuallyNowhereZero f ↔ EventuallyNowhereZero g := by
  rw [← tailGerm_isUnit_iff_eventuallyNowhereZero,
    ← tailGerm_isUnit_iff_eventuallyNowhereZero]
  rw [Filter.EventuallyEq.germ_eq hfg]

private theorem eventuallyZero_mul_right {f g : Real → Real}
    (hf : EventuallyZero f) : EventuallyZero (f * g) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, fun x hx ↦ by simp [hB x hx]⟩

private theorem eventuallyNowhereZero_mul
    {f g : Real → Real} (hf : EventuallyNowhereZero f)
    (hg : EventuallyNowhereZero g) :
    EventuallyNowhereZero (f * g) := by
  obtain ⟨Bf, hBf⟩ := hf
  obtain ⟨Bg, hBg⟩ := hg
  refine ⟨max Bf Bg, fun x hx hzero ↦ ?_⟩
  rcases mul_eq_zero.mp hzero with hfx | hgx
  · exact hBf x ((le_max_left Bf Bg).trans_lt hx) hfx
  · exact hBg x ((le_max_right Bf Bg).trans_lt hx) hgx

private theorem eventuallyNowhereZero_left_of_mul
    {f g : Real → Real} (hfg : EventuallyNowhereZero (f * g)) :
    EventuallyNowhereZero f := by
  obtain ⟨B, hB⟩ := hfg
  refine ⟨B, fun x hx hfx ↦ ?_⟩
  exact hB x hx (by simp [hfx])

private theorem eventuallyEq_mul
    {Phi : K[X] →+* TailGerm}
    {representative : K[X] → Real → Real}
    (hrep : Represents Phi representative) (p q : K[X]) :
    representative (p * q) =ᶠ[atTop]
      representative p * representative q := by
  apply Filter.Germ.coe_eq.mp
  rw [hrep (p * q), map_mul, ← hrep p, ← hrep q]
  rfl

private theorem eventuallyEq_of_polynomial_eq
    {Phi : K[X] →+* TailGerm}
    {representative : K[X] → Real → Real}
    (hrep : Represents Phi representative) {p q : K[X]} (hpq : p = q) :
    representative p =ᶠ[atTop] representative q := by
  apply Filter.Germ.coe_eq.mp
  rw [hrep p, hrep q, hpq]

private theorem eventuallyZero_zeroRepresentative
    {Phi : K[X] →+* TailGerm}
    {representative : K[X] → Real → Real}
    (hrep : Represents Phi representative) :
    EventuallyZero (representative (0 : K[X])) := by
  rw [eventuallyZero_iff_tailGerm_eq_zero, hrep, map_zero]

/-- Germ realization gives eventual pointwise equality between the ordinary
derivative of a representative and the representative of its formal
derivative. -/
theorem eventuallyEq_deriv_of_germRealizes
    {Phi : K[X] →+* TailGerm}
    {representative : K[X] → Real → Real}
    {D : K[X] → K[X]} (hrep : Represents Phi representative)
    (hD : GermRealizesDerivation Phi D) (p : K[X]) :
    deriv (representative p) =ᶠ[atTop] representative (D p) := by
  apply Filter.Germ.coe_eq.mp
  calc
    (deriv (representative p) : TailGerm) =
        TailGerm.deriv (representative p : TailGerm) := rfl
    _ = TailGerm.deriv (Phi p) := congrArg TailGerm.deriv (hrep p)
    _ = Phi (D p) := hD p
    _ = (representative (D p) : TailGerm) := (hrep (D p)).symm

private theorem derivativeDichotomy_of_germRealizes
    {Phi : K[X] →+* TailGerm}
    {representative : K[X] → Real → Real}
    {D : K[X] → K[X]} (hrep : Represents Phi representative)
    (hD : GermRealizesDerivation Phi D) (p : K[X])
    (hp : EventuallyZero (representative (D p)) ∨
      EventuallyNowhereZero (representative (D p))) :
    EventuallyZero (deriv (representative p)) ∨
      EventuallyNowhereZero (deriv (representative p)) := by
  have heq := eventuallyEq_deriv_of_germRealizes hrep hD p
  rcases hp with hp | hp
  · exact Or.inl ((eventuallyZero_congr heq).2 hp)
  · exact Or.inr ((eventuallyNowhereZero_congr heq).2 hp)

/-- Rolle's dichotomy only needs differentiability on a final tail. -/
private theorem tailDichotomy_of_derivativeDichotomy
    {f : Real → Real}
    (hdiff : ∃ B : Real, ∀ x : Real, B < x →
      DifferentiableAt Real f x)
    (hderiv : EventuallyZero (deriv f) ∨
      EventuallyNowhereZero (deriv f)) :
    EventuallyZero f ∨ EventuallyNowhereZero f := by
  rcases hdiff with ⟨Bd, hdiff⟩
  rcases hderiv with hderivZero | hderivNonzero
  · obtain ⟨Bz, hBz⟩ := hderivZero
    let B := max Bd Bz
    have hopen : IsOpen (Ioi B) := isOpen_Ioi
    have hpre : IsPreconnected (Ioi B) := isPreconnected_Ioi
    have hdiffOn : DifferentiableOn Real f (Ioi B) := by
      intro x hx
      exact (hdiff x ((le_max_left Bd Bz).trans_lt hx)).differentiableWithinAt
    have hderivOn : Set.EqOn (deriv f) 0 (Ioi B) := by
      intro x hx
      exact hBz x ((le_max_right Bd Bz).trans_lt hx)
    obtain ⟨c, hc⟩ :=
      hopen.exists_is_const_of_deriv_eq_zero hpre hdiffOn hderivOn
    by_cases hc0 : c = 0
    · exact Or.inl ⟨B, fun x hx ↦ (hc x hx).trans hc0⟩
    · exact Or.inr ⟨B, fun x hx ↦ (hc x hx).trans_ne hc0⟩
  · right
    rw [← not_hasUnboundedZeros_iff_eventuallyNowhereZero]
    intro hzero
    apply hderivNonzero.not_hasUnboundedZeros
    intro B
    obtain ⟨a, ha, hfa⟩ := hzero (max B Bd)
    have haB : B < a := (le_max_left B Bd).trans_lt ha
    have haBd : Bd < a := (le_max_right B Bd).trans_lt ha
    obtain ⟨b, hab, hfb⟩ := hzero a
    have hcontinuous : ContinuousOn f (Icc a b) := by
      exact (show DifferentiableOn Real f (Icc a b) from fun x hx ↦
        (hdiff x (haBd.trans_le hx.1)).differentiableWithinAt).continuousOn
    obtain ⟨c, hc, hdc⟩ :=
      exists_deriv_eq_zero hab hcontinuous (hfa.trans hfb.symm)
    exact ⟨c, haB.trans hc.1, hdc⟩

section Primitive

variable [Differential K]

/-- Primitive polynomial closure over a differential field represented in
tail germs.  No injectivity or transcendence premise is needed. -/
theorem representativeTailDichotomy_primitive
    (Phi : K[X] →+* TailGerm)
    (representative : K[X] → Real → Real) (c : K)
    (hrep : Represents Phi representative)
    (hdiff : EventuallyDifferentiable representative)
    (hD : GermRealizesDerivation Phi
      (Differential.implicitDeriv (C c))) :
    RepresentativeTailDichotomy representative := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp0 : p = 0
      · subst p
        exact Or.inl (eventuallyZero_zeroRepresentative hrep)
      · let q : K[X] := p * C p.leadingCoeff⁻¹
        have hlc0 : p.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hp0
        have hqmonic : q.Monic :=
          Polynomial.monic_mul_leadingCoeff_inv hp0
        let Dq := Differential.implicitDeriv (C c) q
        have hDqDichotomy :
            EventuallyZero (representative Dq) ∨
              EventuallyNowhereZero (representative Dq) := by
          by_cases hDq0 : Dq = 0
          · rw [hDq0]
            exact Or.inl (eventuallyZero_zeroRepresentative hrep)
          · have hqdeg : q.natDegree = p.natDegree := by
              dsimp [q]
              exact Polynomial.natDegree_mul_C (inv_ne_zero hlc0)
            have hlt : Dq.natDegree < n := by
              rw [← hn, ← hqdeg]
              exact natDegree_implicitDeriv_translation_lt_of_monic
                c hqmonic hDq0
            exact ih Dq.natDegree hlt Dq rfl
        have hderivDichotomy :=
          derivativeDichotomy_of_germRealizes hrep hD q hDqDichotomy
        have hqDichotomy : EventuallyZero (representative q) ∨
            EventuallyNowhereZero (representative q) :=
          tailDichotomy_of_derivativeDichotomy
            (hdiff q) hderivDichotomy
        rcases hqDichotomy with hqZero | hqNonzero
        · left
          have hpq : p = q * C p.leadingCoeff := by
            dsimp [q]
            rw [mul_assoc, ← C_mul]
            simp [hlc0]
          have heq₁ := eventuallyEq_of_polynomial_eq hrep hpq
          have heq₂ := eventuallyEq_mul hrep q (C p.leadingCoeff)
          exact (eventuallyZero_congr (heq₁.trans heq₂)).2
            (eventuallyZero_mul_right hqZero)
        · right
          have hqp : q = p * C p.leadingCoeff⁻¹ := rfl
          have heq₁ := eventuallyEq_of_polynomial_eq hrep hqp
          have heq₂ := eventuallyEq_mul hrep p (C p.leadingCoeff⁻¹)
          have hprod :=
            (eventuallyNowhereZero_congr (heq₁.trans heq₂)).1 hqNonzero
          exact eventuallyNowhereZero_left_of_mul hprod

end Primitive

section Exponential

variable [Differential K]

/-- Exponential polynomial closure over a differential field represented in
tail germs.  `hX` is the expected eventual nonvanishing of the exponential
generator. -/
theorem representativeTailDichotomy_exponential
    (Phi : K[X] →+* TailGerm)
    (representative : K[X] → Real → Real) (c : K)
    (hrep : Represents Phi representative)
    (hdiff : EventuallyDifferentiable representative)
    (hX : EventuallyNowhereZero (representative X))
    (hD : GermRealizesDerivation Phi
      (Differential.implicitDeriv (C c * X))) :
    RepresentativeTailDichotomy representative := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp0 : p = 0
      · subst p
        exact Or.inl (eventuallyZero_zeroRepresentative hrep)
      · by_cases hconst : p.coeff 0 = 0
        · let r := p.divX
          have hrlt : r.natDegree < n := by
            rw [← hn]
            exact natDegree_divX_lt_of_coeff_zero
              hp0 hconst
          have hrDichotomy := ih r.natDegree hrlt r rfl
          have hpEq : p = X * r := by
            have hhorner := Polynomial.X_mul_divX_add p
            rw [hconst, C_0, add_zero] at hhorner
            exact hhorner.symm
          have heq₁ := eventuallyEq_of_polynomial_eq hrep hpEq
          have heq₂ := eventuallyEq_mul hrep X r
          have heq := heq₁.trans heq₂
          rcases hrDichotomy with hrZero | hrNonzero
          · left
            have hprod : EventuallyZero
                (representative X * representative r) := by
              obtain ⟨B, hB⟩ := hrZero
              exact ⟨B, fun x hx ↦ by simp [hB x hx]⟩
            exact (eventuallyZero_congr heq).2 hprod
          · right
            exact (eventuallyNowhereZero_congr heq).2
              (eventuallyNowhereZero_mul hX hrNonzero)
        · let q : K[X] := C (p.coeff 0)⁻¹ * p
          have hqconst : q.coeff 0 = 1 := by
            simp [q, hconst]
          let Dq := Differential.implicitDeriv (C c * X) q
          have hDqconst : Dq.coeff 0 = 0 :=
            coeff_zero_implicitDeriv_euler_of_coeff_zero_eq_one c hqconst
          have hDqDichotomy :
              EventuallyZero (representative Dq) ∨
                EventuallyNowhereZero (representative Dq) := by
            by_cases hDq0 : Dq = 0
            · rw [hDq0]
              exact Or.inl (eventuallyZero_zeroRepresentative hrep)
            · let r := Dq.divX
              have hqdeg : q.natDegree = p.natDegree := by
                dsimp [q]
                exact Polynomial.natDegree_C_mul (inv_ne_zero hconst)
              have hDqle : Dq.natDegree ≤ q.natDegree :=
                Proposition31.natDegree_implicitDeriv_euler_le c q
              have hrlt : r.natDegree < n := by
                have hrltDq :=
                  natDegree_divX_lt_of_coeff_zero hDq0 hDqconst
                rw [← hn, ← hqdeg]
                exact hrltDq.trans_le hDqle
              have hrDichotomy := ih r.natDegree hrlt r rfl
              have hDqEq : Dq = X * r := by
                have hhorner := Polynomial.X_mul_divX_add Dq
                rw [hDqconst, C_0, add_zero] at hhorner
                exact hhorner.symm
              have heq₁ := eventuallyEq_of_polynomial_eq hrep hDqEq
              have heq₂ := eventuallyEq_mul hrep X r
              have heq := heq₁.trans heq₂
              rcases hrDichotomy with hrZero | hrNonzero
              · left
                have hprod : EventuallyZero
                    (representative X * representative r) := by
                  obtain ⟨B, hB⟩ := hrZero
                  exact ⟨B, fun x hx ↦ by simp [hB x hx]⟩
                exact (eventuallyZero_congr heq).2 hprod
              · right
                exact (eventuallyNowhereZero_congr heq).2
                  (eventuallyNowhereZero_mul hX hrNonzero)
          have hderivDichotomy :=
            derivativeDichotomy_of_germRealizes hrep hD q hDqDichotomy
          have hqDichotomy : EventuallyZero (representative q) ∨
              EventuallyNowhereZero (representative q) :=
            tailDichotomy_of_derivativeDichotomy
              (hdiff q) hderivDichotomy
          rcases hqDichotomy with hqZero | hqNonzero
          · left
            have hpq : p = C (p.coeff 0) * q := by
              dsimp [q]
              rw [← mul_assoc, ← C_mul]
              simp [hconst]
            have heq₁ := eventuallyEq_of_polynomial_eq hrep hpq
            have heq₂ := eventuallyEq_mul hrep (C (p.coeff 0)) q
            have hprod : EventuallyZero
                (representative (C (p.coeff 0)) * representative q) :=
              by
                simpa [mul_comm] using eventuallyZero_mul_right
                  (g := representative (C (p.coeff 0))) hqZero
            exact (eventuallyZero_congr (heq₁.trans heq₂)).2 hprod
          · right
            have hqp : q = C (p.coeff 0)⁻¹ * p := rfl
            have heq₁ := eventuallyEq_of_polynomial_eq hrep hqp
            have heq₂ := eventuallyEq_mul hrep (C (p.coeff 0)⁻¹) p
            have hprod :=
              (eventuallyNowhereZero_congr (heq₁.trans heq₂)).1 hqNonzero
            obtain ⟨B, hB⟩ := hprod
            refine ⟨B, fun x hx hpx ↦ ?_⟩
            exact hB x hx (by simp [hpx])

end Exponential

end

end Natfunbasis.Wilkie.RichardsonGermExtension
