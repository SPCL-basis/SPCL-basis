import Natfunbasis.MainTheorems
import Natfunbasis.Examples2

/-!
# Corollaries of the additive basis theorem

* `pow_addAtomic_iff`: `f ^ g` is `+`-atomic iff `f` is, or `g ≠ 1` and `g` is
  not of the form `1 + g'`.
* `mul_addAtomic_iff`: `F * G` is `+`-atomic iff `F` and `G` both are.
* `not_exists_add_one_eq`: `n ↦ (n+1)^(n+1) - 1` is not a natural function.
* `basis_linearIndependent`: distinct elements of the basis, viewed as
  functions of a positive real variable, are linearly independent over `ℝ`;
  `basis_linearIndependent_sum` is the same statement for finite sums.
-/

namespace Natfunbasis.Main

open NormalForm NaturalFunction

/-- `f ^ g` is `+`-atomic iff `f` is, or `g ≠ 1` and `g ≠ 1 + g'` for all `g'`. -/
theorem pow_addAtomic_iff (f g : NaturalFunction) :
    (f ^ g).AddAtomic ↔ f.AddAtomic ∨ (g ≠ 1 ∧ ∀ g', g ≠ 1 + g') :=
  Examples2.pow_addAtomic_iff f g

/-- `F * G` is `+`-atomic iff `F` and `G` both are. -/
theorem mul_addAtomic_iff (F G : NaturalFunction) :
    (F * G).AddAtomic ↔ F.AddAtomic ∧ G.AddAtomic :=
  Examples2.mul_addAtomic_iff F G

/-- `(n+1)^(n+1)` is not of the form `1 + g'`, i.e. `n ↦ (n+1)^(n+1) - 1` is not
a natural function. -/
theorem not_exists_add_one_eq :
    ¬ ∃ g' : NaturalFunction, (input + 1) ^ (input + 1) = 1 + g' :=
  Examples2.N_add_one_pow_ne_one_add

/-- The canonical raw normal form of an expression of a basis element is a
coefficient-one monomial. -/
theorem canonicalRaw_eq_monomial_of_isBasis {e : UnaryExpr}
    (he : IsBasis (ofExpr e)) :
    ∃ m : Nat →₀ Nat, canonicalRaw e = MvPolynomial.monomial m 1 := by
  obtain ⟨m, hm⟩ := nf_basis normalFormPackage he
  exact ⟨m, (FixedFamilyCertificate.semanticNF_ofExpr (canonicalCertificate
    Wilkie.originalTermIntegerToReal Wilkie.canonicalWilkieIndependence) e).symm.trans hm⟩

/-- Expressions with the same canonical raw normal form denote the same
natural function. -/
theorem ofExpr_eq_of_canonicalRaw_eq {e d : UnaryExpr}
    (h : canonicalRaw e = canonicalRaw d) : ofExpr e = ofExpr d :=
  ofExpr_eq_iff.2 (FixedFamilyCertificate.semEq_of_raw_eq (canonicalCertificate
    Wilkie.originalTermIntegerToReal Wilkie.canonicalWilkieIndependence) h)

/-- **Linear independence of the basis.** Distinct elements of the basis,
viewed as functions of a positive real variable, are linearly independent
over `ℝ`. -/
theorem basis_linearIndependent {ι : Type*} (e : ι → UnaryExpr)
    (he : ∀ i, IsBasis (ofExpr (e i)))
    (hinj : Function.Injective (fun i ↦ ofExpr (e i))) :
    LinearIndependent ℝ
      (fun i (y : Wilkie.PositiveReal) ↦ Wilkie.UnaryExpr.evalReal (e i) y) := by
  choose m hm using fun i ↦ canonicalRaw_eq_monomial_of_isBasis (he i)
  have hm_inj : Function.Injective m := by
    intro i j hij
    apply hinj
    exact ofExpr_eq_of_canonicalRaw_eq (by rw [hm i, hm j, hij])
  have haeval : Function.Injective
      (MvPolynomial.aeval Wilkie.canonicalRealCoordinates :
        MvPolynomial Nat Real → (Wilkie.PositiveReal → Real)) :=
    Wilkie.canonicalWilkieIndependence_iff_aeval_injective.1
      Wilkie.canonicalWilkieIndependence
  have hli := ((MvPolynomial.basisMonomials Nat Real).linearIndependent.comp m
    hm_inj).map' (MvPolynomial.aeval Wilkie.canonicalRealCoordinates).toLinearMap
    (LinearMap.ker_eq_bot.2 haeval)
  have hfam : (fun i (y : Wilkie.PositiveReal) ↦ Wilkie.UnaryExpr.evalReal (e i) y) =
      (MvPolynomial.aeval Wilkie.canonicalRealCoordinates).toLinearMap ∘
        (MvPolynomial.basisMonomials Nat Real) ∘ m := by
    funext i y
    rw [← canonicalRaw_represents_real, hm i]
    simp [ExpressionNormalizerAssembly.evaluateReal, AlgebraicIndependence.natAeval,
      AlgebraicIndependence.mappedAeval, MvPolynomial.map_monomial]
  rw [hfam]
  exact hli

/-- Finite-sum form of `basis_linearIndependent`: if a real linear combination
of distinct basis elements vanishes at every positive real, all its
coefficients vanish. -/
theorem basis_linearIndependent_sum {ι : Type*} (e : ι → UnaryExpr)
    (he : ∀ i, IsBasis (ofExpr (e i)))
    (hinj : Function.Injective (fun i ↦ ofExpr (e i)))
    (s : Finset ι) (c : ι → ℝ)
    (hsum : ∀ y : Wilkie.PositiveReal,
      ∑ i ∈ s, c i * Wilkie.UnaryExpr.evalReal (e i) y = 0) :
    ∀ i ∈ s, c i = 0 := by
  refine linearIndependent_iff'.1 (basis_linearIndependent e he hinj) s c ?_
  funext y
  simpa [Finset.sum_apply] using hsum y

end Natfunbasis.Main
