import Natfunbasis.CanonicalNormalizer

/-!
# A sharper reduction of the unary integer-to-real bridge

The downstream normalizer only needs the following consequence: if two
original terms agree at every positive integer, their positive-real
interpretations agree everywhere.  The previously isolated
`OriginalTermFiniteOrIdentical` hypothesis is sufficient but stronger than
necessary.

This file isolates the exact at-infinity uniqueness property used by the
integer sequence.  It also proves the ordinary analytic identity principle
for equality points accumulating at an interior positive point.  Consequently
the unresolved content is now sharply located at `+∞`: the positive integers
have no accumulation point inside the positive real axis, and local real
analyticity alone cannot bridge that gap.
-/

namespace Natfunbasis.Wilkie

open Filter Set Topology

noncomputable section

/-! ## What ordinary analyticity does prove -/

/-- Two original-term functions coincide when they agree along a sequence of
distinct positive points converging to an interior positive point.

This is the standard real-analytic identity theorem, specialized to the
analytic extensions constructed in `OriginalTermAnalyticity`. -/
theorem UnaryExpr.evalReal_eq_of_accumulation
    (e d : UnaryExpr) {u : Nat → PositiveReal} {y₀ : PositiveReal}
    (hu : Tendsto (fun n ↦ (u n).1) atTop (𝓝 y₀.1))
    (hne : ∀ᶠ n in atTop, (u n).1 ≠ y₀.1)
    (heq : ∀ᶠ n in atTop,
      UnaryExpr.evalReal e (u n) = UnaryExpr.evalReal d (u n)) :
    UnaryExpr.evalReal e = UnaryExpr.evalReal d := by
  obtain ⟨E, hE, hErestrict⟩ := UnaryExpr.evalReal_isPositiveAnalytic e
  obtain ⟨D, hD, hDrestrict⟩ := UnaryExpr.evalReal_isPositiveAnalytic d
  have hclosure :
      y₀.1 ∈ closure ({x : Real | E x = D x} \ {y₀.1}) := by
    apply mem_closure_of_tendsto hu
    filter_upwards [hne, heq] with n hn hEq
    constructor
    · change E (u n).1 = D (u n).1
      rw [← hErestrict (u n), ← hDrestrict (u n)]
      exact hEq
    · simpa using hn
  have hEqOn : Set.EqOn E D positiveAxis :=
    hE.eqOn_of_preconnected_of_mem_closure hD
      positiveAxis_isPreconnected y₀.2 hclosure
  funext y
  rw [hErestrict y, hDrestrict y]
  exact hEqOn y.2

/-- On every compact subset of the positive axis, two distinct original-term
functions have only finitely many equality points.

This is the strongest compact form of the isolated-zero principle needed to
locate the remaining obstruction: an infinite equality set can only evade
this theorem by escaping every compact subset, as the positive integers do. -/
theorem UnaryExpr.evalReal_eq_or_finite_eqOn_compact
    (e d : UnaryExpr) {K : Set PositiveReal} (hK : IsCompact K) :
    UnaryExpr.evalReal e = UnaryExpr.evalReal d ∨
      (K ∩ {y | UnaryExpr.evalReal e y = UnaryExpr.evalReal d y}).Finite := by
  obtain ⟨E, hE, hErestrict⟩ := UnaryExpr.evalReal_isPositiveAnalytic e
  obtain ⟨D, hD, hDrestrict⟩ := UnaryExpr.evalReal_isPositiveAnalytic d
  rcases hE.eqOn_or_eventually_ne_of_preconnected hD
      positiveAxis_isPreconnected with hEqOn | hNe
  · left
    funext y
    rw [hErestrict y, hDrestrict y]
    exact hEqOn y.2
  · right
    let KReal : Set Real := (fun y : PositiveReal ↦ y.1) '' K
    have hKReal : IsCompact KReal := hK.image continuous_subtype_val
    have hKRealSub : KReal ⊆ positiveAxis := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hNeK : {x : Real | E x ≠ D x} ∈ codiscreteWithin KReal :=
      Filter.codiscreteWithin_mono hKRealSub hNe
    have hFiniteReal : (KReal \ {x : Real | E x ≠ D x}).Finite :=
      hKReal.finite_sdiff_of_mem_codiscreteWithin hNeK
    apply Set.Finite.of_finite_image
    · refine hFiniteReal.subset ?_
      rintro x ⟨y, ⟨hyK, hyEq⟩, rfl⟩
      constructor
      · exact ⟨y, hyK, rfl⟩
      · intro hne
        apply hne
        rw [← hErestrict y, ← hDrestrict y]
        exact hyEq
    · exact Subtype.val_injective.injOn

/-! ## The exact at-infinity input -/

/-- At-infinity uniqueness for original one-variable terms.

Unlike `OriginalTermFiniteOrIdentical`, this permits an arbitrary bounded
equality set.  It asks only that equality points unbounded toward `+∞` force
the two positive-real term functions to be identical.  This is the precise
Hardy-field/o-minimal content needed by the positive-integer sequence. -/
def OriginalTermAtInfinityIdentity : Prop :=
  ∀ e d : UnaryExpr,
    (∀ B : Real, ∃ y : PositiveReal,
      B < y.1 ∧ UnaryExpr.evalReal e y = UnaryExpr.evalReal d y) →
    UnaryExpr.evalReal e = UnaryExpr.evalReal d

/-- Agreement on every positive integer supplies equality points arbitrarily
far out on the positive real axis.  Thus at-infinity uniqueness implies the
exact integer-to-real transfer consumed by the canonical normalizer. -/
theorem originalTermIntegerToReal_of_atInfinityIdentity
    (hatInfinity : OriginalTermAtInfinityIdentity) :
    OriginalTermIntegerToReal := by
  intro e d hsem
  apply hatInfinity e d
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let m : PosNat := ⟨n + 1, by omega⟩
  refine ⟨integerRealInput m, ?_, ?_⟩
  · change B < ((n + 1 : Nat) : Real)
    exact hn.trans_le (by exact_mod_cast Nat.le_succ n)
  · simpa only [UnaryExpr.evalReal_integer] using
      congrArg (fun value : Nat ↦ (value : Real)) (hsem m)

/-- The old finite-zero-set alternative implies the sharper at-infinity
property.  Hence the new reduction weakens the visible source premise without
changing any downstream conclusion. -/
theorem originalTermAtInfinityIdentity_of_finiteOrIdentical
    (hfinite : OriginalTermFiniteOrIdentical) :
    OriginalTermAtInfinityIdentity := by
  intro e d hunbounded
  rcases hfinite e d with heq | hzeroFinite
  · exact heq
  · let Z : Set PositiveReal :=
      {y | UnaryExpr.evalReal e y = UnaryExpr.evalReal d y}
    have hvaluesFinite : ((fun y : PositiveReal ↦ y.1) '' Z).Finite := by
      exact hzeroFinite.image _
    obtain ⟨B, hB⟩ := hvaluesFinite.bddAbove
    obtain ⟨y, hyB, hyEq⟩ := hunbounded B
    have hyZ : y ∈ Z := hyEq
    have hyLeB : y.1 ≤ B := hB ⟨y, hyZ, rfl⟩
    exact False.elim ((not_lt_of_ge hyLeB) hyB)

/-- Compatibility check: the sharper factorization recovers the existing
finite-zero-to-integer-to-real theorem. -/
theorem originalTermIntegerToReal_of_finiteOrIdentical_via_atInfinity
    (hfinite : OriginalTermFiniteOrIdentical) :
    OriginalTermIntegerToReal :=
  originalTermIntegerToReal_of_atInfinityIdentity
    (originalTermAtInfinityIdentity_of_finiteOrIdentical hfinite)

end

end Natfunbasis.Wilkie

namespace Natfunbasis.NormalForm

noncomputable section

/-- The final power-atomicity theorem with the Macintyre premise reduced to
the weaker at-infinity identity property. -/
theorem canonical_pow_addAtomic_of_atInfinityIdentity
    (hatInfinity : Wilkie.OriginalTermAtInfinityIdentity)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f g : NaturalFunction)
    (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) :=
  canonical_pow_addAtomic
    (Wilkie.originalTermIntegerToReal_of_atInfinityIdentity hatInfinity)
    hindependent f g hg_nonconstant hg_atomic

/-- The additive-basis existence-and-uniqueness theorem under the same
sharper at-infinity premise. -/
theorem canonical_exists_basisSum_unique_of_atInfinityIdentity
    (hatInfinity : Wilkie.OriginalTermAtInfinityIdentity)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f : NaturalFunction) :
    ∃ s : BasisSum,
      s.Valid ∧ s.value = f ∧
        ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms :=
  canonical_exists_basisSum_unique
    (Wilkie.originalTermIntegerToReal_of_atInfinityIdentity hatInfinity)
    hindependent f

end

end Natfunbasis.NormalForm
