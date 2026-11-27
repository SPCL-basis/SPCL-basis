import Natfunbasis.WilkieExpDarboux

/-!
# Non-tangency of a polynomial at a top variable

Let `G` be an algebraically independent finite set in a differential field `K`
with real constants, and let a polynomial derivation `Dp` of `ℝ[G]` realize
`w·(d/dx)` for some `w = aeval Wp`.  Let `U ∈ ℝ[G]` be relatively prime to
`Wp`, not divisible by a variable `t` which it contains, and suppose all other
variables of `U` lie in `gens ⊆ G` on which a derivation `D₀` realizes
`c·(d/dx)` while `c·t′ = N·t` with `N ∈ ℝ[gens]`.  Then `U ∤ Dp U`.

This packages the exponential Darboux argument of `WilkieExpDarboux` for the
stage coordinate ring.
-/

open MvPolynomial
open scoped Differential

namespace Natfunbasis.NonTangency

noncomputable section

variable {K : Type*} [Field K] [Differential K] [Algebra ℝ K]

omit [Differential K] in
/-- Evaluation of polynomials in `t` with coefficients in `ℝ[gens]` is
injective when `insert t gens` is algebraically independent and `t ∉ gens`. -/
theorem eval₂_injective_of_insert {gens : Set K} {t : K} (htg : t ∉ gens)
    (hins : AlgebraicIndepOn ℝ (id : K → K) (insert t gens)) :
    Function.Injective (Polynomial.eval₂RingHom
      (MvPolynomial.aeval (R := ℝ) ((↑) : gens → K)).toRingHom t) := by
  obtain ⟨hs, htr⟩ := (AlgebraicIndepOn.insert_iff htg).1 hins
  rw [Set.image_eq_range] at htr
  have hs' : AlgebraicIndependent ℝ (fun x : gens ↦ id (x : K)) := hs
  intro Q₁ Q₂ h
  apply Polynomial.map_injective hs'.aevalEquiv.toAlgHom.toRingHom
    hs'.aevalEquiv.injective
  apply transcendental_iff_injective.1 htr
  simp only [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact h

theorem optionEquivLeft_rename_some {gens : Type*}
    (a : MvPolynomial gens ℝ) :
    optionEquivLeft ℝ gens (rename some a) = Polynomial.C a := by
  have : (optionEquivLeft ℝ gens).toRingHom.comp
      (rename (R := ℝ) (some : gens → Option gens)).toRingHom =
      Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [optionEquivLeft_C]
    · intro g
      simp [optionEquivLeft_X_some]
  exact DFunLike.congr_fun this a

theorem not_dvd_of_darbouxData {G : Set K} (hG : AlgebraicIndepOn ℝ (id : K → K) G)
    (hconst : ∀ z : K, z′ = 0 → ∃ r : ℝ, z = algebraMap ℝ K r)
    (Dp : MvPolynomial G ℝ →+ MvPolynomial G ℝ) (Wp : MvPolynomial G ℝ)
    (hDp : ∀ p, aeval ((↑) : G → K) (Dp p) =
      aeval ((↑) : G → K) Wp * (aeval ((↑) : G → K) p)′)
    (U : MvPolynomial G ℝ) (hUW : IsRelPrime U Wp)
    (t : G) (htU : ¬ X t ∣ U) (htv : t ∈ U.vars)
    (gens : Set K) (hgens : gens ⊆ G) (htg : (t : K) ∉ gens)
    (hvars : ∀ v ∈ U.vars, (v : K) ∈ gens ∨ v = t)
    (D₀ : MvPolynomial gens ℝ →+ MvPolynomial gens ℝ) (N : MvPolynomial gens ℝ)
    (c : K) (hc : c ≠ 0) (hcG : c ∈ Algebra.adjoin ℝ G)
    (hD₀ : ∀ a, aeval ((↑) : gens → K) (D₀ a) =
      c * (aeval ((↑) : gens → K) a)′)
    (hN : aeval ((↑) : gens → K) N * t = c * (t : K)′) :
    ¬ U ∣ Dp U := by
  classical
  intro hdvd
  -- the embedding of `Option gens` into `G`
  let φ : Option gens → G := fun o ↦ o.elim t (fun g ↦ ⟨g, hgens g.2⟩)
  have hφ : Function.Injective φ := by
    rintro (_ | a) (_ | b) h
    · rfl
    · have h' : (t : K) = b := by simpa [φ] using congrArg (Subtype.val : G → K) h
      exact absurd (h' ▸ b.2) htg
    · have h' : (a : K) = t := by simpa [φ] using congrArg (Subtype.val : G → K) h
      exact absurd (h' ▸ a.2) htg
    · have h' : (a : K) = b := by simpa [φ] using congrArg (Subtype.val : G → K) h
      exact congrArg some (Subtype.ext h')
  have hrange : (U.vars : Set G) ⊆ Set.range φ := by
    intro v hv
    rcases hvars v hv with hg | rfl
    · exact ⟨some ⟨v, hg⟩, rfl⟩
    · exact ⟨none, rfl⟩
  obtain ⟨U₁, hU₁⟩ := exists_rename_eq_of_vars_subset_range U φ hφ hrange
  let e := optionEquivLeft ℝ gens
  let P : Polynomial (MvPolynomial gens ℝ) := e U₁
  let ιs : Polynomial (MvPolynomial gens ℝ) →+* MvPolynomial G ℝ :=
    (rename φ).toRingHom.comp e.symm.toRingHom
  let ρ : MvPolynomial G ℝ →+* Polynomial (MvPolynomial gens ℝ) :=
    e.toRingHom.comp (killCompl hφ).toRingHom
  have hρ : ∀ Q, ρ (ιs Q) = Q := by
    intro Q
    simp [ρ, ιs, killCompl_rename_app]
  have hιsP : ιs P = U := by
    simp [ιs, P, hU₁]
  let ev : Polynomial (MvPolynomial gens ℝ) →+* K :=
    Polynomial.eval₂RingHom (MvPolynomial.aeval (R := ℝ) ((↑) : gens → K)).toRingHom t
  -- evaluation is compatible with the embedding
  have hevOpt : ∀ V : MvPolynomial (Option gens) ℝ,
      aeval (((↑) : G → K) ∘ φ) V = ev (e V) := by
    intro V
    induction V using MvPolynomial.induction_on with
    | C r => simp [ev, e, optionEquivLeft_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p o hp =>
        rw [map_mul, map_mul, map_mul, hp]
        congr 1
        rcases o with _ | g
        · simp [ev, e, optionEquivLeft_X_none, φ]
        · simp [ev, e, optionEquivLeft_X_some, φ]
  have hev_comp : ∀ Q, aeval ((↑) : G → K) (ιs Q) = ev Q := by
    intro Q
    have := hevOpt (e.symm Q)
    simp only [AlgEquiv.apply_symm_apply] at this
    rw [← this]
    simp [ιs, aeval_rename]
  have hins : AlgebraicIndepOn ℝ (id : K → K) (insert (t : K) gens) :=
    hG.mono (Set.insert_subset t.2 hgens)
  have hevInj : Function.Injective ev := eval₂_injective_of_insert htg hins
  have haevInj : Function.Injective (aeval ((↑) : G → K)) :=
    algebraicIndependent_iff_injective_aeval.1 hG
  -- the constant term and the degree of `P`
  have hX : ιs Polynomial.X = X t := by
    have : e.symm Polynomial.X = X none := by
      rw [AlgEquiv.symm_apply_eq]; simp [e, optionEquivLeft_X_none]
    simp [ιs, this, φ]
  have h0 : P.coeff 0 ≠ 0 := by
    intro h
    apply htU
    have hXP : Polynomial.X ∣ P := Polynomial.X_dvd_iff.2 h
    rw [← hX, ← hιsP]
    exact map_dvd ιs hXP
  have hdeg : 0 < P.natDegree := by
    by_contra hd
    push Not at hd
    have hPC : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hU' : U = rename (φ ∘ some) (P.coeff 0) := by
      rw [← hιsP, hPC]
      have : e.symm (Polynomial.C (P.coeff 0)) = rename some (P.coeff 0) := by
        rw [AlgEquiv.symm_apply_eq]; exact (optionEquivLeft_rename_some _).symm
      simp [ιs, this, rename_rename]
    rw [hU'] at htv
    obtain ⟨g, _, hg⟩ := Finset.mem_image.1 (vars_rename _ _ htv)
    apply htg
    rw [← hg]
    exact g.2
  -- the Darboux operator and the transported relation
  obtain ⟨Cp, hCp⟩ : ∃ Cp : MvPolynomial G ℝ, aeval ((↑) : G → K) Cp = c := by
    have hadj := Algebra.adjoin_range_eq_range_aeval ℝ ((↑) : G → K)
    rw [Subtype.range_coe] at hadj
    rw [hadj] at hcG
    exact hcG
  let Δ := ExpDarboux.expDarboux D₀ N P
  have hΔ : ev Δ = c * (ev P)′ :=
    ExpDarboux.eval₂_expDarboux (K := K) (MvPolynomial.aeval (R := ℝ) ((↑) : gens → K)).toRingHom
      (t : K) D₀ N c hD₀ hN P
  have hkey : Cp * Dp U = Wp * ιs Δ := by
    apply haevInj
    rw [map_mul, map_mul, hCp, hDp, hev_comp, hΔ, ← hιsP, hev_comp]
    ring
  have hdvd' : U ∣ ιs Δ := by
    have : U ∣ Wp * ιs Δ := hkey ▸ dvd_mul_of_dvd_right hdvd Cp
    exact hUW.dvd_of_dvd_mul_left this
  have hPΔ : P ∣ Δ := by
    have := map_dvd ρ hdvd'
    rwa [← hιsP, hρ, hρ] at this
  exact ExpDarboux.not_dvd_expDarboux (MvPolynomial.aeval ((↑) : gens → K)) (t : K)
    hevInj hconst D₀ N c hc hD₀ hN hdeg h0 hPΔ

end

end Natfunbasis.NonTangency
