import Natfunbasis.MonomialSums
import Natfunbasis.TowerBasis

/-!
# Consequences of the one-variable Wilkie normal form

This module isolates the exact non-elementary inputs still missing from the
project.  `NormalFormPackage` contains only normalization and its arithmetic
rules; `FaithfulNormalFormPackage` adds uniqueness.  All results below are
conditional on explicit values of those structures; no field is installed as
an axiom or a typeclass instance.

The packages are deliberately smaller than HSI* completeness. Their intended
construction uses the one-variable normalization in
Alsulami--Jackson--Kinyon (AJK), Lemma 2.6, the fixed generator conditions
(W1)--(W3), and the difficult semantic-equality-to-polynomial-equality
direction in AJK, Theorem 2.7. The reverse direction follows elementarily
from pointwise representation, as proved in `NormalFormConstruction`.
-/

namespace Natfunbasis

open MvPolynomial

namespace NormalForm

noncomputable section

/-- Exponent vectors for monomials in the fixed countable normal-form
variables.  Variable zero may be used for the original input and successors
for the auxiliary generators. -/
abbrev Monomial := Nat →₀ Nat

/-- A polynomial consisting of one monomial with coefficient one. -/
def IsCoeffOneMonomial (p : MvPolynomial Nat Nat) : Prop :=
  ∃ m : Monomial, p = monomial m 1

/-- The normal-form facts used to prove that the candidate basis elements are
additively atomic.

Source accounting for the fields:

* `nf_nonzero`, `nf_one`, `nf_add`, and `nf_mul` are the one-variable,
  nonnegative-coefficient output and the corresponding constructor cases of
  AJK Lemma 2.6 (pp. 7--8).
* Because `nf` is defined on extensional `NaturalFunction`s rather than on
  expression syntax, constructing `nf` already uses the forward direction of
  AJK Theorem 2.7: two expressions defining the same function must receive
  the same representing polynomial.
* `nf_tower` is the tower induction obtained from the power case of AJK
  Lemma 2.6, specifically Case 2, Subcases 2.2--2.3, using the common
  generator conditions (W1)--(W3).  Its `m ≠ 0` clause records that the
  tower monomial is nonconstant.

The construction of a value of this structure remains the deep formalization
obligation.  Merely supplying it as a parameter keeps that obligation visible
in every theorem below.
-/
structure NormalFormPackage where
  nf : NaturalFunction → MvPolynomial Nat Nat
  nf_nonzero : ∀ f, nf f ≠ 0
  nf_one : nf 1 = 1
  nf_add : ∀ f g, nf (f + g) = nf f + nf g
  nf_mul : ∀ f g, nf (f * g) = nf f * nf g
  nf_tower : ∀ {t}, IsTower t →
    ∃ m : Monomial, m ≠ 0 ∧ nf t = monomial m 1

/-- The additional injectivity interface needed only to compare two basis
expansions. For a normal form constructed from raw expression polynomials,
this field follows from pointwise representation; see
`FixedFamilyCertificate.semanticNF_injective`. It is separated here so that
power atomicity needs only the smaller arithmetic interface. -/
structure FaithfulNormalFormPackage extends NormalFormPackage where
  faithful : Function.Injective nf

variable (P : NormalFormPackage)

/-- Products of towers have coefficient-one monomial normal forms. -/
theorem nf_prod_of_towers (towers : List NaturalFunction)
    (htowers : ∀ t ∈ towers, IsTower t) :
    ∃ m : Monomial, P.nf towers.prod = monomial m 1 := by
  induction towers with
  | nil =>
      refine ⟨0, ?_⟩
      simpa using P.nf_one
  | cons t towers ih =>
      obtain ⟨mt, hmt_ne, hmt⟩ := P.nf_tower (htowers t (by simp))
      obtain ⟨mr, hmr⟩ := ih (fun u hu ↦ htowers u (by simp [hu]))
      refine ⟨mt + mr, ?_⟩
      rw [List.prod_cons, P.nf_mul, hmt, hmr, MvPolynomial.monomial_mul]
      simp

/-- Every candidate basis element has a coefficient-one monomial normal
form.  The monomial may be constant only for the empty tower product. -/
theorem nf_basis {b : NaturalFunction} (hb : IsBasis b) :
    IsCoeffOneMonomial (P.nf b) := by
  obtain ⟨towers, htowers, rfl⟩ := hb
  exact nf_prod_of_towers P towers htowers

/-- A basis element packaged together with its membership proof. -/
abbrev BasisElement := {b : NaturalFunction // IsBasis b}

/-- The exponent vector of the coefficient-one monomial attached to a basis
element. -/
noncomputable def basisExponent (b : BasisElement) : Monomial :=
  Classical.choose (nf_basis P b.2)

theorem nf_basisExponent (b : BasisElement) :
    P.nf b.1 = monomial (basisExponent P b) 1 :=
  Classical.choose_spec (nf_basis P b.2)

/-- Faithfulness of normal forms makes the exponent-vector encoding of basis
elements injective. -/
theorem basisExponent_injective (Q : FaithfulNormalFormPackage) :
    Function.Injective (basisExponent Q.toNormalFormPackage) := by
  intro a b hab
  apply Subtype.ext
  apply Q.faithful
  rw [nf_basisExponent Q.toNormalFormPackage a,
    nf_basisExponent Q.toNormalFormPackage b, hab]

namespace BasisSumFacts

/-- Turn the terms of a valid basis sum into actual `BasisElement`s. -/
def basisTerms : (s : BasisSum) → s.Valid → List BasisElement
  | .single b, hb => [⟨b, hb⟩]
  | .cons b rest, h => ⟨b, h.1⟩ :: basisTerms rest h.2

@[simp]
theorem basisTerms_map_value (s : BasisSum) (hs : s.Valid) :
    (basisTerms s hs).map (fun b ↦ b.1) = s.terms := by
  induction s with
  | single b => rfl
  | cons b rest ih =>
      change b :: (basisTerms rest hs.2).map (fun b ↦ b.1) =
        b :: rest.terms
      rw [ih hs.2]

/-- The normal form of the value of a valid sum is the sum of the monomials
of its basis terms. -/
theorem nf_value_eq_monomialSums (s : BasisSum) (hs : s.Valid) :
    P.nf s.value =
      NormalPolynomial.monomialSum
        ((basisTerms s hs).map (basisExponent P)) := by
  induction s with
  | single b =>
      simpa [basisTerms, NormalPolynomial.monomialSum] using
        nf_basisExponent P (⟨b, hs⟩ : BasisElement)
  | cons b rest ih =>
      rw [Natfunbasis.BasisSum.value_cons, P.nf_add, ih hs.2]
      simp only [basisTerms, List.map_cons, NormalPolynomial.monomialSum,
        List.sum_cons]
      rw [nf_basisExponent P (⟨b, hs.1⟩ : BasisElement)]

end BasisSumFacts

/-- A basis element is additively atomic, conditionally on the normal-form
package. -/
theorem addAtomic_of_basis (P : NormalFormPackage) {b : NaturalFunction}
    (hb : IsBasis b) :
    NaturalFunction.AddAtomic b := by
  obtain ⟨m, hm⟩ := nf_basis P hb
  rintro ⟨a, c, hdecomp⟩
  apply NormalPolynomial.weight_one_forbids_add
      (p := P.nf b) (q := P.nf a) (r := P.nf c)
  · rw [hdecomp, P.nf_add]
  · exact P.nf_nonzero a
  · exact P.nf_nonzero c
  · rw [hm]
    exact NormalPolynomial.weight_monomial_one m

/-- Additive atoms are exactly finite products of nondegenerate towers. -/
theorem addAtomic_iff_isBasis (P : NormalFormPackage) (f : NaturalFunction) :
    NaturalFunction.AddAtomic f ↔ IsBasis f := by
  constructor
  · exact isBasis_of_addAtomic
  · exact addAtomic_of_basis P

/-- Valid additive expansions of the same natural function have the same
terms, including multiplicity, up to order. -/
theorem basisSum_terms_perm (Q : FaithfulNormalFormPackage) {s t : BasisSum}
    (hs : s.Valid) (ht : t.Valid)
    (hvalue : s.value = t.value) : s.terms.Perm t.terms := by
  let P := Q.toNormalFormPackage
  have hnf : P.nf s.value = P.nf t.value := congrArg P.nf hvalue
  rw [BasisSumFacts.nf_value_eq_monomialSums P s hs,
    BasisSumFacts.nf_value_eq_monomialSums P t ht] at hnf
  have hexponents :
      ((BasisSumFacts.basisTerms s hs).map (basisExponent P)).Perm
        ((BasisSumFacts.basisTerms t ht).map (basisExponent P)) :=
    (NormalPolynomial.monomialSum_eq_iff_perm _ _).mp hnf
  have hbasis :
      (BasisSumFacts.basisTerms s hs).Perm
        (BasisSumFacts.basisTerms t ht) :=
    (List.map_perm_map_iff (basisExponent_injective Q)).mp hexponents
  have hvalues := hbasis.map (fun b : BasisElement ↦ b.1)
  simpa only [BasisSumFacts.basisTerms_map_value] using hvalues

/-- Every natural function has a valid additive basis expansion, and every
other valid expansion has the same terms (with multiplicity) up to order.
This packages elementary existence together with normal-form uniqueness. -/
theorem exists_basisSum_unique (Q : FaithfulNormalFormPackage)
    (f : NaturalFunction) :
    ∃ s : BasisSum,
      s.Valid ∧ s.value = f ∧
        ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms := by
  obtain ⟨s, hs, hsf⟩ := exists_basisSum f
  refine ⟨s, hs, hsf, ?_⟩
  intro t ht htf
  exact basisSum_terms_perm Q hs ht (hsf.trans htf.symm)

/-- The elementary reduction of power atomicity to atomicity of the candidate
basis. Nonconstancy is essential: the atomic constant exponent one would
otherwise give `f ^ 1 = f`. -/
theorem pow_addAtomic_of_basis_atomic
    (basis_atomic : ∀ {b : NaturalFunction}, IsBasis b →
      NaturalFunction.AddAtomic b)
    (f g : NaturalFunction)
    (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) := by
  have hg_basis : IsBasis g := isBasis_of_addAtomic hg_atomic
  apply basis_atomic
  by_cases hf : f = (1 : NaturalFunction)
  · rw [hf, NaturalFunction.one_pow_function]
    exact IsBasis.one
  · exact BasisSum.basis_pow_of_nonconstant hf hg_basis hg_nonconstant

/-- Corrected natural-power atomicity from the normalization package. -/
theorem pow_addAtomic (P : NormalFormPackage) (f g : NaturalFunction)
    (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) :=
  pow_addAtomic_of_basis_atomic (addAtomic_of_basis P) f g
    hg_nonconstant hg_atomic

/-- Special case: `n ↦ f(n)^n` is additively atomic. -/
theorem pow_input_addAtomic (P : NormalFormPackage) (f : NaturalFunction) :
    NaturalFunction.AddAtomic (f ^ NaturalFunction.input) :=
  pow_addAtomic P f NaturalFunction.input
    NaturalFunction.input_nonconstant NaturalFunction.input_addAtomic

/-- Expression-level form of `pow_addAtomic`, with exactly the intended
mathematical hypotheses on the exponent. -/
theorem expr_pow_addAtomic (P : NormalFormPackage) (f g : UnaryExpr)
    (hg_nonconstant : UnaryExpr.Nonconstant g)
    (hg_atomic : UnaryExpr.AddAtomic g) :
    UnaryExpr.AddAtomic (.pow f g) := by
  rw [← NaturalFunction.ofExpr_addAtomic_iff]
  rw [NaturalFunction.ofExpr_pow]
  apply pow_addAtomic P
  · exact (NaturalFunction.ofExpr_nonconstant_iff g).2 hg_nonconstant
  · exact (NaturalFunction.ofExpr_addAtomic_iff g).2 hg_atomic

/-- Expression-level special case `n ↦ f(n)^n`. -/
theorem expr_pow_variable_addAtomic (P : NormalFormPackage) (f : UnaryExpr) :
    UnaryExpr.AddAtomic (.pow f (.var ())) :=
  expr_pow_addAtomic P f (.var ()) UnaryExpr.variable_nonconstant
    UnaryExpr.variable_addAtomic

end

end NormalForm

end Natfunbasis
