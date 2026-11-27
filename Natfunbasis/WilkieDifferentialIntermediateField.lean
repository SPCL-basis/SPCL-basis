import Natfunbasis.WilkieFractionConstants
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Differential intermediate fields in a fixed ambient field

Wilkie's differential-algebra argument repeatedly passes between fields of
analytic functions inside one common ambient differential field.  This file
packages exactly that situation: an intermediate field whose carrier is
closed under the ambient derivation.

The induced derivation on the subtype is definitionally the restriction of
the ambient derivation.  We also provide the two closure constructions used
later in the adjunction steps:

* adjoining generators over the coefficient field, provided the derivatives
  of the coefficients and generators lie in the resulting field; and
* adjoining generators over an already differential intermediate field.

Finally, if the ambient differential field has no constants beyond the
coefficient field, neither does any differential intermediate field.  A
nested pair of such fields therefore has the same constants, which is the
constant-field hypothesis in Wilkie's Propositions 3.1 and 3.2.
-/

namespace Natfunbasis.Wilkie

open scoped Differential

noncomputable section

universe u v

/-- An intermediate field of `K / C` closed under the derivation of `K`. -/
structure DifferentialIntermediateField
    (C : Type u) (K : Type v) [Field C] [Field K] [Algebra C K]
    [Differential K] where
  toIntermediateField : IntermediateField C K
  deriv_mem' : ∀ {x : K}, x ∈ toIntermediateField → x′ ∈ toIntermediateField

namespace DifferentialIntermediateField

variable {C : Type u} {K : Type v} [Field C] [Field K] [Algebra C K]
  [Differential K]

instance : SetLike (DifferentialIntermediateField C K) K where
  coe F := F.toIntermediateField
  coe_injective F G h := by
    cases F with
    | mk F hF =>
      cases G with
      | mk G hG =>
        have hFG : F = G := SetLike.coe_injective h
        subst G
        rfl

instance : Coe (DifferentialIntermediateField C K) (IntermediateField C K) :=
  ⟨toIntermediateField⟩

instance : PartialOrder (DifferentialIntermediateField C K) :=
  PartialOrder.ofSetLike (DifferentialIntermediateField C K) K

instance : SubfieldClass (DifferentialIntermediateField C K) K where
  add_mem {s} := s.toIntermediateField.add_mem
  zero_mem {s} := s.toIntermediateField.zero_mem
  neg_mem {s} := s.toIntermediateField.neg_mem
  mul_mem {s} := s.toIntermediateField.mul_mem
  one_mem {s} := s.toIntermediateField.one_mem
  inv_mem {s} := s.toIntermediateField.inv_mem

instance : SMulMemClass (DifferentialIntermediateField C K) C K where
  smul_mem := fun _ _ hx ↦ IntermediateField.smul_mem _ hx

@[ext]
theorem ext {F G : DifferentialIntermediateField C K}
    (h : ∀ x : K, x ∈ F ↔ x ∈ G) : F = G :=
  SetLike.ext h

@[simp]
theorem mem_toIntermediateField (F : DifferentialIntermediateField C K)
    (x : K) : x ∈ F.toIntermediateField ↔ x ∈ F :=
  Iff.rfl

theorem algebraMap_mem (F : DifferentialIntermediateField C K) (c : C) :
    algebraMap C K c ∈ F :=
  F.toIntermediateField.algebraMap_mem c

/-- Closure under the ambient derivation. -/
theorem deriv_mem (F : DifferentialIntermediateField C K) {x : K}
    (hx : x ∈ F) : x′ ∈ F :=
  F.deriv_mem' hx

/-! ## Inherited field and algebra structures -/

instance toField (F : DifferentialIntermediateField C K) : Field F :=
  F.toIntermediateField.toField

instance toAlgebraBase (F : DifferentialIntermediateField C K) : Algebra C F :=
  IntermediateField.algebra' F.toIntermediateField

instance toAlgebraAmbient (F : DifferentialIntermediateField C K) : Algebra F K :=
  F.toIntermediateField.toAlgebra

instance isScalarTower (F : DifferentialIntermediateField C K) :
    IsScalarTower C F K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

@[simp, norm_cast]
theorem coe_algebraMap_base (F : DifferentialIntermediateField C K) (c : C) :
    ((algebraMap C F c : F) : K) = algebraMap C K c :=
  rfl

@[simp]
theorem algebraMap_ambient_apply (F : DifferentialIntermediateField C K)
    (x : F) : algebraMap F K x = (x : K) :=
  rfl

/-! ## Restricting the ambient derivation -/

/-- The ambient derivation, restricted to a derivative-closed intermediate
field. -/
def derivation (F : DifferentialIntermediateField C K) : Derivation Int F F :=
  Derivation.mk'
    ({
      toFun := fun x ↦ ⟨(x : K)′, F.deriv_mem x.2⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero Differential.deriv
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add Differential.deriv (x : K) (y : K)
    } : F →+ F).toIntLinearMap
    (by
      intro x y
      apply Subtype.ext
      exact Differential.deriv.leibniz (x : K) (y : K))

instance instDifferential (F : DifferentialIntermediateField C K) :
    Differential F where
  deriv := F.derivation

@[simp, norm_cast]
theorem coe_deriv (F : DifferentialIntermediateField C K) (x : F) :
    ((x′ : F) : K) = (x : K)′ :=
  rfl

/-- Inclusion in the ambient field commutes with differentiation. -/
instance differentialAlgebraAmbient (F : DifferentialIntermediateField C K) :
    DifferentialAlgebra F K where
  deriv_algebraMap _ := rfl

/-- If the coefficient field is itself differential and its embedding into
the ambient field is differential, then so is its embedding into every
differential intermediate field. -/
instance differentialAlgebraBase (F : DifferentialIntermediateField C K)
    [Differential C] [DifferentialAlgebra C K] :
    DifferentialAlgebra C F where
  deriv_algebraMap c := by
    apply Subtype.ext
    exact deriv_algebraMap c

/-! ## Inclusions of nested differential intermediate fields -/

/-- The canonical algebra homomorphism between nested differential
intermediate fields. -/
def inclusion {F G : DifferentialIntermediateField C K} (hFG : F ≤ G) :
    F →ₐ[C] G :=
  IntermediateField.inclusion hFG

theorem inclusion_injective {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) : Function.Injective (inclusion hFG) :=
  IntermediateField.inclusion_injective hFG

@[simp, norm_cast]
theorem coe_inclusion {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) (x : F) : ((inclusion hFG x : G) : K) = (x : K) :=
  rfl

@[simp]
theorem deriv_inclusion {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) (x : F) :
    (inclusion hFG x)′ = inclusion hFG x′ := by
  apply Subtype.ext
  rfl

/-- The algebra structure on a larger differential intermediate field induced
by a specified inclusion.  It is kept as an explicit definition because the
containment proof is mathematical data, not a typeclass parameter. -/
@[reducible]
def inclusionAlgebra {F G : DifferentialIntermediateField C K} (hFG : F ≤ G) :
    Algebra F G :=
  (inclusion hFG).toRingHom.toAlgebra

@[simp]
theorem algebraMap_inclusion {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) :
    letI := inclusionAlgebra hFG
    ∀ x : F, algebraMap F G x = inclusion hFG x := by
  intro x
  rfl

/-- With the inclusion algebra structure, a nested inclusion is a
differential algebra. -/
theorem differentialAlgebraOfLE {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) :
    letI := inclusionAlgebra hFG
    DifferentialAlgebra F G := by
  letI := inclusionAlgebra hFG
  refine ⟨?_⟩
  intro x
  exact deriv_inclusion hFG x

/-! ## Elementary constructions -/

/-- The ambient field is a differential intermediate field of itself. -/
def top : DifferentialIntermediateField C K where
  toIntermediateField := ⊤
  deriv_mem' := fun {_} _ ↦ trivial

@[simp]
theorem mem_top (x : K) : x ∈ (top : DifferentialIntermediateField C K) :=
  trivial

/-- The intersection of two differential intermediate fields is
differential. -/
def inf (F G : DifferentialIntermediateField C K) :
    DifferentialIntermediateField C K where
  toIntermediateField := F.toIntermediateField ⊓ G.toIntermediateField
  deriv_mem' := by
    intro x hx
    exact ⟨F.deriv_mem hx.1, G.deriv_mem hx.2⟩

@[simp]
theorem mem_inf {F G : DifferentialIntermediateField C K} {x : K} :
    x ∈ inf F G ↔ x ∈ F ∧ x ∈ G :=
  Iff.rfl

/-- Derivative closure of a field generated over `C`.  The coefficient
hypothesis is stated as membership, so this also applies when `C` has a
nonzero derivation whose image remains in the generated field. -/
theorem deriv_mem_adjoin (s : Set K)
    (hcoeff : ∀ c : C, (algebraMap C K c)′ ∈ IntermediateField.adjoin C s)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin C s)
    {x : K} (hx : x ∈ IntermediateField.adjoin C s) :
    x′ ∈ IntermediateField.adjoin C s := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hgenerator x hx
  | algebraMap c => exact hcoeff c
  | add x y hx hy hdx hdy =>
      rw [map_add]
      exact add_mem hdx hdy
  | inv x hx hdx =>
      rw [(Differential.deriv : Derivation Int K K).leibniz_inv]
      change -x⁻¹ ^ 2 * x′ ∈ IntermediateField.adjoin C s
      exact mul_mem (neg_mem (pow_mem (inv_mem hx) 2)) hdx
  | mul x y hx hy hdx hdy =>
      rw [Differential.deriv.leibniz]
      change x * y′ + y * x′ ∈ IntermediateField.adjoin C s
      exact add_mem (mul_mem hx hdy) (mul_mem hy hdx)

/-- Adjoin a set whose elements and coefficients have derivatives in the
resulting field. -/
def adjoin (s : Set K)
    (hcoeff : ∀ c : C, (algebraMap C K c)′ ∈ IntermediateField.adjoin C s)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin C s) :
    DifferentialIntermediateField C K where
  toIntermediateField := IntermediateField.adjoin C s
  deriv_mem' := deriv_mem_adjoin s hcoeff hgenerator

@[simp]
theorem mem_adjoin (s : Set K)
    (hcoeff : ∀ c : C, (algebraMap C K c)′ ∈ IntermediateField.adjoin C s)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin C s)
    (x : K) :
    x ∈ adjoin s hcoeff hgenerator ↔ x ∈ IntermediateField.adjoin C s :=
  Iff.rfl

theorem subset_adjoin (s : Set K)
    (hcoeff : ∀ c : C, (algebraMap C K c)′ ∈ IntermediateField.adjoin C s)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin C s) :
    s ⊆ adjoin s hcoeff hgenerator :=
  IntermediateField.subset_adjoin C s

theorem adjoin_le {s : Set K}
    (hcoeff : ∀ c : C, (algebraMap C K c)′ ∈ IntermediateField.adjoin C s)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin C s)
    {F : DifferentialIntermediateField C K} :
    adjoin s hcoeff hgenerator ≤ F ↔ s ⊆ F :=
  IntermediateField.adjoin_le_iff

/-- Common specialization of `adjoin` when the ambient derivation kills the
coefficient field. -/
def adjoinOfConstants (s : Set K)
    (hcoeff : ∀ c : C, (algebraMap C K c)′ = 0)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin C s) :
    DifferentialIntermediateField C K :=
  adjoin s (fun c ↦ by rw [hcoeff c]; exact zero_mem _) hgenerator

/-- Derivative closure after adjoining generators over an already
differential intermediate field. -/
theorem deriv_mem_adjoinOver (F : DifferentialIntermediateField C K)
    (s : Set K)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin F s)
    {x : K} (hx : x ∈ IntermediateField.adjoin F s) :
    x′ ∈ IntermediateField.adjoin F s := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hgenerator x hx
  | algebraMap c =>
      change (c : K)′ ∈ IntermediateField.adjoin F s
      rw [← F.coe_deriv c]
      exact IntermediateField.algebraMap_mem _ c′
  | add x y hx hy hdx hdy =>
      rw [map_add]
      exact add_mem hdx hdy
  | inv x hx hdx =>
      rw [(Differential.deriv : Derivation Int K K).leibniz_inv]
      change -x⁻¹ ^ 2 * x′ ∈ IntermediateField.adjoin F s
      exact mul_mem (neg_mem (pow_mem (inv_mem hx) 2)) hdx
  | mul x y hx hy hdx hdy =>
      rw [Differential.deriv.leibniz]
      change x * y′ + y * x′ ∈ IntermediateField.adjoin F s
      exact add_mem (mul_mem hx hdy) (mul_mem hy hdx)

/-- Adjoin generators over an existing differential intermediate field and
regard the result again as an intermediate field over `C`. -/
def adjoinOver (F : DifferentialIntermediateField C K) (s : Set K)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin F s) :
    DifferentialIntermediateField C K where
  toIntermediateField := (IntermediateField.adjoin F s).restrictScalars C
  deriv_mem' := by
    intro x hx
    exact F.deriv_mem_adjoinOver s hgenerator hx

@[simp]
theorem mem_adjoinOver (F : DifferentialIntermediateField C K) (s : Set K)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin F s)
    (x : K) :
    x ∈ F.adjoinOver s hgenerator ↔ x ∈ IntermediateField.adjoin F s :=
  Iff.rfl

theorem le_adjoinOver (F : DifferentialIntermediateField C K) (s : Set K)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin F s) :
    F ≤ F.adjoinOver s hgenerator := by
  intro x hx
  let y : F := ⟨x, hx⟩
  exact IntermediateField.algebraMap_mem (IntermediateField.adjoin F s) y

theorem subset_adjoinOver (F : DifferentialIntermediateField C K) (s : Set K)
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin F s) :
    s ⊆ F.adjoinOver s hgenerator :=
  IntermediateField.subset_adjoin F s

theorem adjoinOver_le {F G : DifferentialIntermediateField C K} {s : Set K}
    (hgenerator : ∀ x ∈ s, x′ ∈ IntermediateField.adjoin F s)
    (hFG : F ≤ G) (hsG : s ⊆ G) :
    F.adjoinOver s hgenerator ≤ G := by
  intro x hx
  change x ∈ IntermediateField.adjoin F s at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hsG hx
  | algebraMap c => simpa using hFG c.2
  | add _ _ _ _ hx hy => exact G.toIntermediateField.add_mem hx hy
  | inv _ _ hx => exact G.toIntermediateField.inv_mem hx
  | mul _ _ _ _ hx hy => exact G.toIntermediateField.mul_mem hx hy

/-! ## Descent of the constant field -/

/-- If all ambient constants come from `C`, the same is true in every
differential intermediate field. -/
instance containConstants (F : DifferentialIntermediateField C K)
    [Differential.ContainConstants C K] :
    Differential.ContainConstants C F where
  mem_range_of_deriv_eq_zero {x} hx := by
    have hxK : (x : K)′ = 0 := by
      rw [← F.coe_deriv x]
      exact congrArg Subtype.val hx
    obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero C hxK
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc

/-- Nested differential intermediate fields have the same constants whenever
the ambient constants already come from `C`.  This is the exact
constant-field input needed in the later Singer--Rosenlicht adjunction
lemmas. -/
theorem containConstantsOfLE {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) [Differential.ContainConstants C K] :
    letI := inclusionAlgebra hFG
    Differential.ContainConstants F G := by
  letI := inclusionAlgebra hFG
  refine ⟨?_⟩
  intro x hx
  have hxK : (x : K)′ = 0 := by
    rw [← G.coe_deriv x]
    exact congrArg Subtype.val hx
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero C hxK
  let y : F := algebraMap C F c
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact (F.coe_algebraMap_base c).trans hc

/-- For a differential inclusion, an element of the smaller field is constant
exactly when its image in the larger field is constant. -/
theorem deriv_inclusion_eq_zero_iff {F G : DifferentialIntermediateField C K}
    (hFG : F ≤ G) (x : F) :
    (inclusion hFG x)′ = 0 ↔ x′ = 0 := by
  rw [deriv_inclusion]
  constructor
  · intro hx
    apply inclusion_injective hFG
    simpa using hx
  · intro hx
    rw [hx]
    exact map_zero (inclusion hFG)

/-! ## The concrete analytic ambient field -/

/-- In the analytic fraction field, every differential intermediate field
over `Real` has exactly the real constants. -/
example (F : DifferentialIntermediateField Real PositiveAnalyticFractionField) :
    Differential.ContainConstants Real F :=
  inferInstance

/-- Concrete same-constant-field package for nested analytic differential
fields. -/
theorem analyticContainConstantsOfLE
    {F G : DifferentialIntermediateField Real PositiveAnalyticFractionField}
    (hFG : F ≤ G) :
    letI := inclusionAlgebra hFG
    Differential.ContainConstants F G :=
  containConstantsOfLE hFG

end DifferentialIntermediateField

end

end Natfunbasis.Wilkie
