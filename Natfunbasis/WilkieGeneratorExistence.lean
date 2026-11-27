import Natfunbasis.WilkieGenerators

/-!
# Existence of a one-variable Wilkie generator sequence

This module constructs an actual `GeneratorSequence equalityDerivability`.
The construction enumerates *global polynomial pairs*, rather than their
many possible finite-stage presentations.  Each non-filler pair is delayed
to an odd index beyond the stages of a chosen finite presentation.  The
remaining indices are filled bijectively by the stage-zero pairs
`(Y, Y^(m+1))`.  Thus every admissible pair occurs exactly once and every
entry mentions only earlier auxiliary variables.

This is a countability/scheduling result.  It does not prove normalization or
algebraic independence.
-/

namespace Natfunbasis.Wilkie

open MvPolynomial

noncomputable section

/-! ## Canonical global targets and finite presentations -/

/-- A global polynomial which has some finite W1 base presentation. -/
def IsGlobalBase (p : GlobalPolynomial) : Prop :=
  ∃ stage : Nat, ∃ base : Base stage, base.toGlobal = p

/-- A base modulo the irrelevant choice of a finite presentation stage. -/
abbrev GlobalBase := {p : GlobalPolynomial // IsGlobalBase p}

/-- A global coefficient-one nonconstant monomial with some finite-stage
presentation. -/
def IsGlobalExponent (p : GlobalPolynomial) : Prop :=
  ∃ stage : Nat, ∃ exponent : NonconstantMonomial stage, exponent.toGlobal = p

/-- An exponent modulo the irrelevant choice of a finite presentation stage. -/
abbrev GlobalExponent := {p : GlobalPolynomial // IsGlobalExponent p}

/-- The canonical object enumerated by a generator sequence: one global base
and one global exponent polynomial. -/
abbrev GeneratorTarget := GlobalBase × GlobalExponent

namespace GlobalBase

/-- A chosen finite stage at which a global base is presented. -/
def presentationStage (base : GlobalBase) : Nat :=
  Classical.choose base.2

/-- A chosen finite presentation of a global base. -/
def presentation (base : GlobalBase) : Base base.presentationStage :=
  Classical.choose (Classical.choose_spec base.2)

theorem presentation_toGlobal (base : GlobalBase) :
    base.presentation.toGlobal = base.1 :=
  Classical.choose_spec (Classical.choose_spec base.2)

end GlobalBase

namespace GlobalExponent

/-- A chosen finite stage at which a global exponent is presented. -/
def presentationStage (exponent : GlobalExponent) : Nat :=
  Classical.choose exponent.2

/-- A chosen finite presentation of a global exponent. -/
def presentation (exponent : GlobalExponent) :
    NonconstantMonomial exponent.presentationStage :=
  Classical.choose (Classical.choose_spec exponent.2)

theorem presentation_toGlobal (exponent : GlobalExponent) :
    exponent.presentation.toGlobal = exponent.1 :=
  Classical.choose_spec (Classical.choose_spec exponent.2)

end GlobalExponent

namespace GeneratorTarget

/-- A stage after which both chosen presentations of a target are legal. -/
def bound (target : GeneratorTarget) : Nat :=
  max target.1.presentationStage target.2.presentationStage

/-- Turn a target into an entry at any index beyond its presentation bound. -/
def toEntry (target : GeneratorTarget) (index : Nat)
    (hbound : target.bound ≤ index) : GeneratorEntry index where
  baseStage := target.1.presentationStage
  baseStage_le := (le_max_left _ _).trans hbound
  base := target.1.presentation
  exponentStage := target.2.presentationStage
  exponentStage_le := (le_max_right _ _).trans hbound
  exponent := target.2.presentation

end GeneratorTarget

/-- Forget the finite presentations of an entry and retain its canonical
global target. -/
def GeneratorEntry.target {index : Nat} (entry : GeneratorEntry index) :
    GeneratorTarget :=
  (⟨entry.base.toGlobal, ⟨entry.baseStage, entry.base, rfl⟩⟩,
   ⟨entry.exponent.toGlobal, ⟨entry.exponentStage, entry.exponent, rfl⟩⟩)

@[simp]
theorem GeneratorTarget.target_toEntry (target : GeneratorTarget) (index : Nat)
    (hbound : target.bound ≤ index) :
    (target.toEntry index hbound).target = target := by
  apply Prod.ext
  · apply Subtype.ext
    exact target.1.presentation_toGlobal
  · apply Subtype.ext
    exact target.2.presentation_toGlobal

/-! ## An infinite family of stage-zero fillers -/

/-- The monomial `Y^(m+1)`, presented without auxiliary variables. -/
def fillerExponent (m : Nat) : NonconstantMonomial 0 where
  exponents := Finsupp.single 0 (m + 1)
  nonzero := by
    intro hzero
    have := congrArg (fun exponents : StageVar 0 →₀ Nat ↦ exponents 0) hzero
    simp at this

/-- The canonical target `(Y,Y^(m+1))`. -/
def fillerTarget (m : Nat) : GeneratorTarget :=
  (⟨originalPolynomial, ⟨0, Base.original, Base.original_toGlobal 0⟩⟩,
   ⟨(fillerExponent m).toGlobal, ⟨0, fillerExponent m, rfl⟩⟩)

/-- A filler target already presented at stage zero. -/
def fillerEntry (index m : Nat) : GeneratorEntry index where
  baseStage := 0
  baseStage_le := Nat.zero_le index
  base := .original
  exponentStage := 0
  exponentStage_le := Nat.zero_le index
  exponent := fillerExponent m

@[simp]
theorem fillerEntry_target (index m : Nat) :
    (fillerEntry index m).target = fillerTarget m := by
  apply Prod.ext
  · apply Subtype.ext
    exact Base.original_toGlobal 0
  · rfl

/-- Different filler codes give different global polynomial pairs. -/
theorem fillerTarget_injective : Function.Injective fillerTarget := by
  intro m n hmn
  have hpoly := congrArg (fun target : GeneratorTarget ↦ target.2.1) hmn
  simp only [fillerTarget, fillerExponent, NonconstantMonomial.toGlobal,
    NonconstantMonomial.polynomial, StagePolynomial.toGlobal,
    MvPolynomial.rename_monomial] at hpoly
  have hexponents := MvPolynomial.monomial_left_injective (R := Int)
    one_ne_zero hpoly
  have hatOriginal := congrArg (fun exponents : GlobalVar →₀ Nat ↦
    exponents .original) hexponents
  simp only [Finsupp.mapDomain_single] at hatOriginal
  have hsucc : m + 1 = n + 1 := by
    simpa [stageVarEmbedding] using hatOriginal
  omega

/-- Being a filler is a property of the canonical global target. -/
def IsFiller (target : GeneratorTarget) : Prop :=
  ∃ m : Nat, fillerTarget m = target

/-- The targets scheduled explicitly at delayed odd indices. -/
abbrev NonfillerTarget := {target : GeneratorTarget // ¬ IsFiller target}

/-! ## Delayed scheduling -/

local instance globalPolynomialCountable : Countable GlobalPolynomial :=
  AddMonoidAlgebra.coeff_injective.countable

/-- A fixed injective natural-number code for non-filler targets. -/
@[implicit_reducible]
def nonfillerEncoding : Encodable NonfillerTarget :=
  Classical.choice (nonempty_encodable NonfillerTarget)

/-- Schedule a non-filler target at an odd index beyond its presentation
bound. -/
def scheduledIndex (target : NonfillerTarget) : Nat :=
  2 * Nat.pair (@Encodable.encode NonfillerTarget nonfillerEncoding target)
      target.1.bound + 1

theorem target_bound_le_scheduledIndex (target : NonfillerTarget) :
    target.1.bound ≤ scheduledIndex target := by
  calc
    target.1.bound ≤ Nat.pair
        (@Encodable.encode NonfillerTarget nonfillerEncoding target)
        target.1.bound := Nat.right_le_pair _ _
    _ ≤ scheduledIndex target := by simp [scheduledIndex]; omega

theorem scheduledIndex_injective : Function.Injective scheduledIndex := by
  intro left right heq
  have hpair :
      Nat.pair (@Encodable.encode NonfillerTarget nonfillerEncoding left)
          left.1.bound =
        Nat.pair (@Encodable.encode NonfillerTarget nonfillerEncoding right)
          right.1.bound := by
    have hmul :
        2 * Nat.pair (@Encodable.encode NonfillerTarget nonfillerEncoding left)
            left.1.bound =
          2 * Nat.pair (@Encodable.encode NonfillerTarget nonfillerEncoding right)
            right.1.bound := by
      exact Nat.succ.inj (by simpa [scheduledIndex] using heq)
    exact Nat.mul_left_cancel (by decide) hmul
  have hencode := (Nat.pair_eq_pair.mp hpair).1
  exact @Encodable.encode_injective NonfillerTarget nonfillerEncoding left right hencode

/-- Indices not occupied by the delayed non-filler schedule. -/
def FreeIndex := {index : Nat // ∀ target : NonfillerTarget,
  scheduledIndex target ≠ index}

/-- Every even index is free, so the free-index type is infinite. -/
def evenFreeEmbedding : Nat ↪ FreeIndex where
  toFun n := ⟨2 * n, by
    intro target heq
    simp only [scheduledIndex] at heq
    omega⟩
  inj' := by
    intro m n hmn
    have hvals := congrArg Subtype.val hmn
    exact Nat.mul_left_cancel (by decide) hvals

local instance freeIndexCountable : Countable FreeIndex :=
  Subtype.countable

local instance freeIndexInfinite : Infinite FreeIndex :=
  Infinite.of_injective evenFreeEmbedding evenFreeEmbedding.injective

/-- A fixed bijection used to put exactly one distinct filler in every free
index. -/
def freeIndexEquivNat : FreeIndex ≃ Nat :=
  Classical.choice (nonempty_equiv_of_countable (α := FreeIndex) (β := Nat))

/-! ## The enumerated entry at each index -/

/-- The entry at `index`: use its scheduled non-filler when one exists;
otherwise use the uniquely assigned stage-zero filler. -/
def enumeratedEntry (index : Nat) : GeneratorEntry index := by
  classical
  by_cases hscheduled : ∃ target : NonfillerTarget,
      scheduledIndex target = index
  · let target := Classical.choose hscheduled
    have hbound : target.1.bound ≤ index := by
      rw [← Classical.choose_spec hscheduled]
      exact target_bound_le_scheduledIndex target
    exact target.1.toEntry index hbound
  · let free : FreeIndex := ⟨index, by
      intro target heq
      exact hscheduled ⟨target, heq⟩⟩
    exact fillerEntry index (freeIndexEquivNat free)

theorem enumeratedEntry_target_of_scheduled (index : Nat)
    (hscheduled : ∃ target : NonfillerTarget,
      scheduledIndex target = index) :
    (enumeratedEntry index).target = (Classical.choose hscheduled).1 := by
  rw [enumeratedEntry]
  simp only [dif_pos hscheduled]
  exact GeneratorTarget.target_toEntry _ _ _

theorem enumeratedEntry_target_of_free (index : Nat)
    (hfree : ¬ ∃ target : NonfillerTarget,
      scheduledIndex target = index) :
    (enumeratedEntry index).target =
      fillerTarget (freeIndexEquivNat ⟨index, by
        intro target heq
        exact hfree ⟨target, heq⟩⟩) := by
  rw [enumeratedEntry]
  simp only [dif_neg hfree]
  exact fillerEntry_target _ _

/-- Every non-filler target occurs at its explicitly scheduled index. -/
theorem enumeratedEntry_target_scheduled (target : NonfillerTarget) :
    (enumeratedEntry (scheduledIndex target)).target = target.1 := by
  let hexists : ∃ other : NonfillerTarget,
      scheduledIndex other = scheduledIndex target := ⟨target, rfl⟩
  rw [enumeratedEntry_target_of_scheduled _ hexists]
  congr 1
  exact scheduledIndex_injective (Classical.choose_spec hexists)

/-- Every filler target occurs at the free index assigned to its code. -/
theorem enumeratedEntry_target_filler (m : Nat) :
    (enumeratedEntry (freeIndexEquivNat.symm m).1).target = fillerTarget m := by
  let free := freeIndexEquivNat.symm m
  have hfree : ¬ ∃ target : NonfillerTarget,
      scheduledIndex target = free.1 := by
    rintro ⟨target, htarget⟩
    exact free.2 target htarget
  rw [enumeratedEntry_target_of_free free.1 hfree]
  have hsubtype : (⟨free.1, by
      intro target heq
      exact hfree ⟨target, heq⟩⟩ : FreeIndex) = free :=
    Subtype.ext rfl
  rw [hsubtype, freeIndexEquivNat.apply_symm_apply]

/-- The canonical target attached to the enumerated entries is injective. -/
theorem enumeratedEntry_target_injective :
    Function.Injective (fun index : Nat ↦ (enumeratedEntry index).target) := by
  intro left right htargets
  classical
  change (enumeratedEntry left).target = (enumeratedEntry right).target at htargets
  by_cases hleft : ∃ target : NonfillerTarget,
      scheduledIndex target = left
  · by_cases hright : ∃ target : NonfillerTarget,
        scheduledIndex target = right
    · rw [enumeratedEntry_target_of_scheduled left hleft,
          enumeratedEntry_target_of_scheduled right hright] at htargets
      have hchosen : Classical.choose hleft = Classical.choose hright :=
        Subtype.ext htargets
      rw [← Classical.choose_spec hleft, ← Classical.choose_spec hright,
        hchosen]
    · rw [enumeratedEntry_target_of_scheduled left hleft,
          enumeratedEntry_target_of_free right hright] at htargets
      exact False.elim ((Classical.choose hleft).2
        ⟨_, htargets.symm⟩)
  · by_cases hright : ∃ target : NonfillerTarget,
        scheduledIndex target = right
    · rw [enumeratedEntry_target_of_free left hleft,
          enumeratedEntry_target_of_scheduled right hright] at htargets
      exact False.elim ((Classical.choose hright).2
        ⟨_, htargets⟩)
    · rw [enumeratedEntry_target_of_free left hleft,
          enumeratedEntry_target_of_free right hright] at htargets
      have hcodes := fillerTarget_injective htargets
      have hfree :
          (⟨left, by
            intro target heq
            exact hleft ⟨target, heq⟩⟩ : FreeIndex) =
          ⟨right, by
            intro target heq
            exact hright ⟨target, heq⟩⟩ :=
        freeIndexEquivNat.injective hcodes
      exact congrArg Subtype.val hfree

/-- Every canonical admissible target occurs in the enumeration. -/
theorem enumeratedEntry_target_surjective :
    Function.Surjective (fun index : Nat ↦ (enumeratedEntry index).target) := by
  intro target
  by_cases hfiller : IsFiller target
  · obtain ⟨m, rfl⟩ := hfiller
    exact ⟨(freeIndexEquivNat.symm m).1, enumeratedEntry_target_filler m⟩
  · exact ⟨scheduledIndex ⟨target, hfiller⟩,
      enumeratedEntry_target_scheduled ⟨target, hfiller⟩⟩

/-! ## The actual sequence -/

/-- A concrete, source-faithful paired W1--W2 enumeration with literal
polynomial equality as its coverage relation. -/
def canonicalGeneratorSequence : GeneratorSequence equalityDerivability where
  pair := enumeratedEntry
  w1_noRepeatedPair := by
    intro i j hij hsem
    apply hij
    apply enumeratedEntry_target_injective
    apply Prod.ext
    · apply Subtype.ext
      exact PolynomialSemEq.eq hsem.1
    · apply Subtype.ext
      exact PolynomialSemEq.eq hsem.2
  w2_irreducible := by
    intro baseStage exponentStage p hp exponent
    let target : GeneratorTarget :=
      (⟨p.toGlobal, ⟨baseStage, Base.irreducible p hp, rfl⟩⟩,
       ⟨exponent.toGlobal, ⟨exponentStage, exponent, rfl⟩⟩)
    obtain ⟨index, hindex⟩ := enumeratedEntry_target_surjective target
    refine ⟨index, ?_, ?_⟩
    · exact congrArg (fun entryTarget : GeneratorTarget ↦ entryTarget.1.1) hindex
    · exact congrArg (fun entryTarget : GeneratorTarget ↦ entryTarget.2.1) hindex
  w2_original := by
    intro exponentStage exponent
    let target : GeneratorTarget :=
      (⟨originalPolynomial, ⟨0, Base.original, Base.original_toGlobal 0⟩⟩,
       ⟨exponent.toGlobal, ⟨exponentStage, exponent, rfl⟩⟩)
    obtain ⟨index, hindex⟩ := enumeratedEntry_target_surjective target
    refine ⟨index, ?_, ?_⟩
    · exact congrArg (fun entryTarget : GeneratorTarget ↦ entryTarget.1.1) hindex
    · exact congrArg (fun entryTarget : GeneratorTarget ↦ entryTarget.2.1) hindex

/-- The concrete W1--W3 system obtained by equipping the canonical sequence
with its canonical well-founded real realization. -/
def canonicalGeneratorSystem : GeneratorSystem equalityDerivability where
  sequence := canonicalGeneratorSequence
  realization := canonicalGeneratorSequence.canonicalRealization

end

end Natfunbasis.Wilkie
