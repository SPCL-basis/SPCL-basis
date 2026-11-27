import Natfunbasis.OriginalTermAnalyticAdjunction

/-!
# The integer-to-real transfer, proved

Every original unary term has a germ at `+∞` lying in a differential field
of analytic germs built from `ℝ` by finitely many primitive and exponential
adjunctions.  The Richardson descent already formalized for one such
adjunction (`primitiveUnitDichotomy`, `exponentialUnitDichotomy`) makes every
element of such a field either eventually zero or eventually nowhere zero.

Consequently two original terms which agree at arbitrarily large positive
inputs agree on a whole tail, hence (by analyticity) on the whole positive
axis.  This proves `OriginalTermAtInfinityIdentity` and therefore
`OriginalTermIntegerToReal` with no premise.
-/

open Filter Polynomial Set Topology
open scoped Differential

namespace Natfunbasis.Wilkie

noncomputable section

open RichardsonAnalyticAdjunction RichardsonAnalyticFraction

/-- A differential field embedded in analytic germs at `+∞`, compatibly with
differentiation. -/
structure GermHardyField where
  K : Type
  [instField : Field K]
  [instDifferential : Differential K]
  iota : K →+* AnalyticTailGerm
  hiota : ∀ a : K, (iota a)′ = iota a′

attribute [instance] GermHardyField.instField GermHardyField.instDifferential

namespace GermHardyField

instance : Nontrivial AnalyticTailGerm := inferInstance

theorem zero_or_isUnit (H : GermHardyField) {F : AnalyticTailGerm}
    (hF : F ∈ H.iota.range) : F = 0 ∨ IsUnit F := by
  obtain ⟨a, rfl⟩ := hF
  by_cases ha : a = 0
  · left; simp [ha]
  · right; exact (isUnit_iff_ne_zero.2 ha).map H.iota

theorem deriv_mem (H : GermHardyField) {F : AnalyticTailGerm}
    (hF : F ∈ H.iota.range) : F′ ∈ H.iota.range := by
  obtain ⟨a, rfl⟩ := hF
  exact ⟨a′, (H.hiota a).symm⟩

theorem exists_eq_iota_of_logDeriv (H : GermHardyField)
    {S L : AnalyticTailGerm} (hS : S ∈ H.iota.range) (hSu : IsUnit S)
    (hL : L′ * S = S′) : ∃ c : H.K, L′ = H.iota c := by
  obtain ⟨a, rfl⟩ := hS
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hSu
  refine ⟨a′ * a⁻¹, ?_⟩
  have hinv : H.iota a * H.iota a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  calc L′ = L′ * H.iota a * H.iota a⁻¹ := by rw [mul_assoc, hinv, mul_one]
    _ = (H.iota a)′ * H.iota a⁻¹ := by rw [hL]
    _ = H.iota (a′ * a⁻¹) := by rw [H.hiota, map_mul]

/-- One primitive adjunction. -/
theorem exists_extension_primitive (H : GermHardyField)
    (θ : AnalyticTailGerm) (c : H.K) (hθ : θ′ = H.iota c) :
    ∃ H' : GermHardyField, H.iota.range ≤ H'.iota.range ∧ θ ∈ H'.iota.range := by
  have hD := polynomialEvalHom_deriv_primitive H.iota θ c H.hiota hθ
  have hunit := primitiveUnitDichotomy (polynomialEvalHom H.iota θ) c hD
  letI := hunit
  let H' : GermHardyField :=
    { K := FractionRing (polynomialTailRange (polynomialEvalHom H.iota θ))
      instDifferential := fractionDifferential (polynomialEvalHom H.iota θ)
        (Differential.implicitDeriv (C c)) hD hunit
      iota := fractionMap (polynomialEvalHom H.iota θ) hunit
      hiota := fractionMap_extend_commutes (polynomialEvalHom H.iota θ)
        (Differential.implicitDeriv (C c)) hD hunit }
  refine ⟨H', ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨coefficientMap (polynomialEvalHom H.iota θ) a,
      fractionMap_polynomialEval_coefficient H.iota θ hunit a⟩
  · exact ⟨generator (polynomialEvalHom H.iota θ),
      fractionMap_polynomialEval_generator H.iota θ hunit⟩

/-- One exponential adjunction. -/
theorem exists_extension_exponential (H : GermHardyField)
    (θ : AnalyticTailGerm) (hθu : IsUnit θ) (c : H.K)
    (hθ : θ′ = H.iota c * θ) :
    ∃ H' : GermHardyField, H.iota.range ≤ H'.iota.range ∧ θ ∈ H'.iota.range := by
  have hD := polynomialEvalHom_deriv_exponential H.iota θ c H.hiota hθ
  have hX : IsUnit ((toTailPolynomialHom (polynomialEvalHom H.iota θ)) X) := by
    have := hθu.map TailGerm.analyticSubring.subtype
    simpa [toTailPolynomialHom, polynomialEvalHom] using this
  have hunit := exponentialUnitDichotomy (polynomialEvalHom H.iota θ) c hX hD
  letI := hunit
  let H' : GermHardyField :=
    { K := FractionRing (polynomialTailRange (polynomialEvalHom H.iota θ))
      instDifferential := fractionDifferential (polynomialEvalHom H.iota θ)
        (Differential.implicitDeriv (C c * X)) hD hunit
      iota := fractionMap (polynomialEvalHom H.iota θ) hunit
      hiota := fractionMap_extend_commutes (polynomialEvalHom H.iota θ)
        (Differential.implicitDeriv (C c * X)) hD hunit }
  refine ⟨H', ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨coefficientMap (polynomialEvalHom H.iota θ) a,
      fractionMap_polynomialEval_coefficient H.iota θ hunit a⟩
  · exact ⟨generator (polynomialEvalHom H.iota θ),
      fractionMap_polynomialEval_generator H.iota θ hunit⟩

end GermHardyField

/-! ## The base field and germs of positive-axis functions -/

/-- Constant germs. -/
def constGerm : Real →+* AnalyticTailGerm :=
  ((Filter.Germ.coeRingHom (atTop : Filter Real)).comp
      (Pi.constRingHom Real Real)).codRestrict TailGerm.analyticSubring
    (fun _ ↦ TailGerm.eventuallyAnalytic_coe
      (Eventually.of_forall fun _ ↦ analyticAt_const))

theorem constGerm_deriv (a : Real) : (constGerm a)′ = 0 := by
  apply Subtype.ext
  change TailGerm.deriv ((fun _ : Real ↦ a : Real → Real) : TailGerm) = 0
  rw [TailGerm.deriv_coe]
  apply Filter.EventuallyEq.germ_eq
  exact Eventually.of_forall fun x ↦ by simp

/-- `ℝ` with the zero derivation, embedded as constant germs. -/
def base : GermHardyField := by
  letI : Differential Real := ⟨0⟩
  exact
    { K := Real
      iota := constGerm
      hiota := fun a ↦ by
        have h : (a′ : Real) = 0 := rfl
        rw [h, map_zero]
        exact constGerm_deriv a }

/-- The germ of a function analytic on the positive axis. -/
def posGerm (f : Real → Real) (hf : ∀ x, 0 < x → AnalyticAt Real f x) :
    AnalyticTailGerm :=
  ⟨(f : TailGerm), TailGerm.eventuallyAnalytic_coe
    ((eventually_gt_atTop 0).mono fun x hx ↦ hf x hx)⟩

theorem posGerm_congr {f g : Real → Real}
    {hf : ∀ x, 0 < x → AnalyticAt Real f x}
    {hg : ∀ x, 0 < x → AnalyticAt Real g x}
    (h : ∀ x, 0 < x → f x = g x) : posGerm f hf = posGerm g hg := by
  apply Subtype.ext
  exact Filter.EventuallyEq.germ_eq
    ((eventually_gt_atTop 0).mono fun x hx ↦ h x hx)

theorem posGerm_deriv (f : Real → Real)
    (hf : ∀ x, 0 < x → AnalyticAt Real f x) :
    (posGerm f hf)′ = posGerm (deriv f) (fun x hx ↦ (hf x hx).deriv) := by
  apply Subtype.ext
  exact TailGerm.deriv_coe f

theorem posGerm_isUnit (f : Real → Real)
    (hf : ∀ x, 0 < x → AnalyticAt Real f x)
    (hne : ∀ x, 0 < x → f x ≠ 0) : IsUnit (posGerm f hf) :=
  AnalyticTailGerm.isUnit_of_coe_isUnit
    (tailGerm_isUnit_of_eventuallyNowhereZero ⟨0, fun x hx ↦ hne x hx⟩)

theorem posGerm_mul (f g : Real → Real)
    (hf : ∀ x, 0 < x → AnalyticAt Real f x)
    (hg : ∀ x, 0 < x → AnalyticAt Real g x) :
    posGerm f hf * posGerm g hg =
      posGerm (fun x ↦ f x * g x) (fun x hx ↦ (hf x hx).mul (hg x hx)) :=
  rfl

/-- The logarithmic derivative identity `(log f)′ · f = f′`. -/
theorem posGerm_log_deriv_mul (f : Real → Real)
    (hf : ∀ x, 0 < x → AnalyticAt Real f x)
    (hpos : ∀ x, 0 < x → 0 < f x) :
    (posGerm (fun x ↦ Real.log (f x))
        (fun x hx ↦ (hf x hx).log (hpos x hx)))′ * posGerm f hf =
      (posGerm f hf)′ := by
  rw [posGerm_deriv, posGerm_deriv, posGerm_mul]
  apply posGerm_congr
  intro x hx
  have h := ((hf x hx).differentiableAt.hasDerivAt.log
    (ne_of_gt (hpos x hx))).deriv
  rw [h, div_mul_cancel₀ _ (ne_of_gt (hpos x hx))]

/-- The exponential derivative identity `(exp g)′ = g′ · exp g`. -/
theorem posGerm_exp_deriv (g : Real → Real)
    (hg : ∀ x, 0 < x → AnalyticAt Real g x) :
    (posGerm (fun x ↦ Real.exp (g x)) (fun x hx ↦ (hg x hx).rexp'))′ =
      (posGerm g hg)′ *
        posGerm (fun x ↦ Real.exp (g x)) (fun x hx ↦ (hg x hx).rexp') := by
  rw [posGerm_deriv, posGerm_deriv, posGerm_mul]
  apply posGerm_congr
  intro x hx
  rw [((hg x hx).differentiableAt.hasDerivAt.exp).deriv, mul_comm]

/-! ## Germs of original terms -/

/-- The real function of an original unary term. -/
def termFun (e : UnaryExpr) : Real → Real :=
  fun x ↦ RealExpression.eval (fun _ ↦ x) e

theorem termFun_pos (e : UnaryExpr) {x : Real} (hx : 0 < x) :
    0 < termFun e x :=
  RealExpression.eval_pos (fun _ ↦ x) (fun _ ↦ hx) e

theorem termFun_analyticAt (e : UnaryExpr) (x : Real) (hx : 0 < x) :
    AnalyticAt Real (termFun e) x := by
  obtain ⟨E, hE, hEe⟩ := UnaryExpr.evalReal_isPositiveAnalytic e
  apply (hE x hx).congr
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact (hEe ⟨y, hy⟩).symm

/-- The germ at `+∞` of an original unary term. -/
def termGerm (e : UnaryExpr) : AnalyticTailGerm :=
  posGerm (termFun e) (termFun_analyticAt e)

/-- The germ of the identity function. -/
def xGerm : AnalyticTailGerm :=
  posGerm (fun x ↦ x) (fun _ _ ↦ analyticAt_id)

theorem xGerm_deriv : xGerm′ = constGerm 1 := by
  rw [xGerm, posGerm_deriv]
  apply Subtype.ext
  apply Filter.EventuallyEq.germ_eq
  exact Eventually.of_forall fun x ↦ by simp

theorem termGerm_one : termGerm .one = 1 := by
  apply Subtype.ext
  apply Filter.EventuallyEq.germ_eq
  exact Eventually.of_forall fun x ↦ rfl

theorem termGerm_var (u : Unit) : termGerm (.var u) = xGerm :=
  rfl

theorem termGerm_add (s t : UnaryExpr) :
    termGerm (.add s t) = termGerm s + termGerm t :=
  rfl

theorem termGerm_mul (s t : UnaryExpr) :
    termGerm (.mul s t) = termGerm s * termGerm t :=
  rfl

theorem termGerm_pow (s t : UnaryExpr) :
    termGerm (.pow s t) =
      posGerm (fun x ↦ Real.exp (Real.log (termFun s x) * termFun t x))
        (fun x hx ↦ (((termFun_analyticAt s x hx).log (termFun_pos s hx)).mul
          (termFun_analyticAt t x hx)).rexp') := by
  apply posGerm_congr
  intro x hx
  change Real.rpow (termFun s x) (termFun t x) = _
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (termFun_pos s hx)]

/-! ## Every term germ lies in a germ Hardy field -/

namespace GermHardyField

theorem exists_base : ∃ H : GermHardyField, xGerm ∈ H.iota.range := by
  obtain ⟨H, _, hx⟩ := base.exists_extension_primitive xGerm 1
    (by rw [xGerm_deriv]; rfl)
  exact ⟨H, hx⟩

theorem exists_termGerm_mem (e : UnaryExpr) :
    ∀ H : GermHardyField, xGerm ∈ H.iota.range →
      ∃ H' : GermHardyField, H.iota.range ≤ H'.iota.range ∧
        termGerm e ∈ H'.iota.range := by
  induction e with
  | one =>
      intro H _
      exact ⟨H, le_rfl, by rw [termGerm_one]; exact one_mem _⟩
  | var u =>
      intro H hx
      exact ⟨H, le_rfl, by rw [termGerm_var]; exact hx⟩
  | add s t ihs iht =>
      intro H hx
      obtain ⟨H1, h1, hs⟩ := ihs H hx
      obtain ⟨H2, h2, ht⟩ := iht H1 (h1 hx)
      exact ⟨H2, h1.trans h2, by rw [termGerm_add]; exact add_mem (h2 hs) ht⟩
  | mul s t ihs iht =>
      intro H hx
      obtain ⟨H1, h1, hs⟩ := ihs H hx
      obtain ⟨H2, h2, ht⟩ := iht H1 (h1 hx)
      exact ⟨H2, h1.trans h2, by rw [termGerm_mul]; exact mul_mem (h2 hs) ht⟩
  | pow s t ihs iht =>
      intro H hx
      obtain ⟨H1, h1, hs⟩ := ihs H hx
      obtain ⟨H2, h2, ht⟩ := iht H1 (h1 hx)
      have hs2 := h2 hs
      -- adjoin `log s`, a primitive over `H2`
      let L : AnalyticTailGerm :=
        posGerm (fun x ↦ Real.log (termFun s x))
          (fun x hx ↦ (termFun_analyticAt s x hx).log (termFun_pos s hx))
      have hSu : IsUnit (termGerm s) :=
        posGerm_isUnit _ _ fun x hx ↦ ne_of_gt (termFun_pos s hx)
      have hL : L′ * termGerm s = (termGerm s)′ :=
        posGerm_log_deriv_mul (termFun s) (termFun_analyticAt s)
          (fun x hx ↦ termFun_pos s hx)
      obtain ⟨c, hc⟩ := H2.exists_eq_iota_of_logDeriv hs2 hSu hL
      obtain ⟨H3, h3, hL3⟩ := H2.exists_extension_primitive L c hc
      -- adjoin `exp (log s · t)`, an exponential over `H3`
      let G : AnalyticTailGerm :=
        posGerm (fun x ↦ Real.log (termFun s x) * termFun t x)
          (fun x hx ↦ ((termFun_analyticAt s x hx).log
            (termFun_pos s hx)).mul (termFun_analyticAt t x hx))
      have hG : G ∈ H3.iota.range := by
        have : G = L * termGerm t := rfl
        rw [this]
        exact mul_mem hL3 (h3 ht)
      obtain ⟨c', hc'⟩ := H3.deriv_mem hG
      let P : AnalyticTailGerm :=
        posGerm (fun x ↦ Real.exp (Real.log (termFun s x) * termFun t x))
          (fun x hx ↦ (((termFun_analyticAt s x hx).log
            (termFun_pos s hx)).mul (termFun_analyticAt t x hx)).rexp')
      have hPu : IsUnit P :=
        posGerm_isUnit _ _ fun x _ ↦ ne_of_gt (Real.exp_pos _)
      have hP : P′ = H3.iota c' * P := by
        rw [hc']
        exact posGerm_exp_deriv _ _
      obtain ⟨H4, h4, hP4⟩ := H3.exists_extension_exponential P hPu c' hP
      exact ⟨H4, h1.trans (h2.trans (h3.trans h4)),
        by rw [termGerm_pow]; exact hP4⟩

theorem exists_pair (e d : UnaryExpr) :
    ∃ H : GermHardyField,
      termGerm e ∈ H.iota.range ∧ termGerm d ∈ H.iota.range := by
  obtain ⟨H0, hx⟩ := exists_base
  obtain ⟨H1, h1, he⟩ := exists_termGerm_mem e H0 hx
  obtain ⟨H2, h2, hd⟩ := exists_termGerm_mem d H1 (h1 hx)
  exact ⟨H2, h2 he, hd⟩

end GermHardyField

/-! ## The dichotomy and the transfer -/

/-- The difference of two original terms is eventually zero or eventually
nowhere zero. -/
theorem termFun_sub_dichotomy (e d : UnaryExpr) :
    EventuallyZero (fun x ↦ termFun e x - termFun d x) ∨
      EventuallyNowhereZero (fun x ↦ termFun e x - termFun d x) := by
  obtain ⟨H, he, hd⟩ := GermHardyField.exists_pair e d
  rcases H.zero_or_isUnit (sub_mem he hd) with h | h
  · left
    rw [eventuallyZero_iff_tailGerm_eq_zero]
    exact congrArg Subtype.val h
  · right
    rw [← tailGerm_isUnit_iff_eventuallyNowhereZero]
    exact (AnalyticTailGerm.isUnit_iff_coe_isUnit _).1 h

/-- **Identity at infinity.** Two original unary terms which agree at
arbitrarily large positive inputs are equal on the whole positive axis. -/
theorem originalTermAtInfinityIdentity : OriginalTermAtInfinityIdentity := by
  intro e d hunb
  rcases termFun_sub_dichotomy e d with ⟨B, hB⟩ | ⟨B, hB⟩
  · obtain ⟨E, hE, hEe⟩ := UnaryExpr.evalReal_isPositiveAnalytic e
    obtain ⟨D, hD, hDd⟩ := UnaryExpr.evalReal_isPositiveAnalytic d
    have h0 : max B 0 + 1 ∈ positiveAxis := by
      show (0 : Real) < max B 0 + 1
      linarith [le_max_right B 0]
    have hED : E =ᶠ[𝓝 (max B 0 + 1)] D := by
      filter_upwards [isOpen_Ioi.mem_nhds
        (show max B 0 < max B 0 + 1 by linarith)] with y hy
      have hy0 : 0 < y := lt_of_le_of_lt (le_max_right B 0) hy
      have hyB : B < y := lt_of_le_of_lt (le_max_left B 0) hy
      rw [← hEe ⟨y, hy0⟩, ← hDd ⟨y, hy0⟩]
      exact sub_eq_zero.1 (hB y hyB)
    have hEq := hE.eqOn_of_preconnected_of_eventuallyEq hD
      positiveAxis_isPreconnected h0 hED
    funext y
    rw [hEe, hDd]
    exact hEq y.2
  · exfalso
    obtain ⟨y, hy, hyeq⟩ := hunb B
    exact hB y.1 hy (sub_eq_zero.2 hyeq)

/-- **The integer-to-real transfer**, with no premise. -/
theorem originalTermIntegerToReal : OriginalTermIntegerToReal :=
  originalTermIntegerToReal_of_atInfinityIdentity originalTermAtInfinityIdentity

end

end Natfunbasis.Wilkie

namespace Natfunbasis.NormalForm

/-- `f ^ g` is `+`-atomic for every natural `f` and nonconstant `+`-atomic `g`,
assuming only Wilkie's algebraic independence. -/
theorem canonical_pow_addAtomic_of_wilkie
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f g : NaturalFunction) (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) :=
  canonical_pow_addAtomic Wilkie.originalTermIntegerToReal hindependent
    f g hg_nonconstant hg_atomic

/-- The additive basis theorem, assuming only Wilkie's algebraic independence. -/
theorem canonical_exists_basisSum_unique_of_wilkie
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f : NaturalFunction) :
    ∃ s : BasisSum, s.Valid ∧ s.value = f ∧
      ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms :=
  canonical_exists_basisSum_unique Wilkie.originalTermIntegerToReal
    hindependent f

end Natfunbasis.NormalForm
