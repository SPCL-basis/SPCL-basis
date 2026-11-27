import Mathlib

/-!
# Descent of coprimality and squarefreeness from `ℤ` to `ℝ`

For an irreducible integer multivariate polynomial `f`, its image
`realLift ι f = rename ι (map (Int.castRingHom ℝ) f)` under an injective
renaming of variables is squarefree over `ℝ`, and it is relatively prime to
`realLift ι g` whenever `f ∤ g`.

The proof is variable by variable: viewing `f` as a polynomial in one variable
over the other variables, Gauss's lemma and separability give a Bézout
relation `a f + b g = c` (resp. `a f + b ∂ᵢf = c`) with `c ≠ 0` free of that
variable.  A common real divisor therefore has degree zero in every variable,
hence is a unit.
-/

open MvPolynomial Polynomial

namespace Natfunbasis.RealDescent

noncomputable section

/-! ## Bézout relations over a fraction field -/

section Frac

variable {B : Type*} [CommRing B] [IsDomain B]

theorem exists_mul_add_mul_eq_C {F G : B[X]}
    (h : IsCoprime (F.map (algebraMap B (FractionRing B)))
      (G.map (algebraMap B (FractionRing B)))) :
    ∃ a b : B[X], ∃ d : B, d ≠ 0 ∧ a * F + b * G = Polynomial.C d := by
  obtain ⟨α, β, hαβ⟩ := h
  obtain ⟨bα, hbα, hα⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors B) α
  obtain ⟨bβ, hbβ, hβ⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors B) β
  refine ⟨Polynomial.C bβ * IsLocalization.integerNormalization
      (nonZeroDivisors B) α,
    Polynomial.C bα * IsLocalization.integerNormalization
      (nonZeroDivisors B) β, bα * bβ, ?_, ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.ne_zero hbα)
      (nonZeroDivisors.ne_zero hbβ)
  · apply Polynomial.map_injective (algebraMap B (FractionRing B))
      (IsFractionRing.injective B (FractionRing B))
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hα,
      hβ, Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
    linear_combination
      (Polynomial.C (algebraMap B (FractionRing B) bα) *
        Polynomial.C (algebraMap B (FractionRing B) bβ)) * hαβ

variable [IsGCDMonoid B]

theorem isCoprime_map_of_irreducible_of_not_dvd {F G : B[X]}
    (hF : Irreducible F) (hdeg : F.natDegree ≠ 0) (hFG : ¬ F ∣ G) :
    IsCoprime (F.map (algebraMap B (FractionRing B)))
      (G.map (algebraMap B (FractionRing B))) := by
  have hprim := hF.isPrimitive hdeg
  have hirr : Irreducible (F.map (algebraMap B (FractionRing B))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).1 hF
  rw [hirr.coprime_iff_not_dvd]
  exact fun h ↦ hFG (hprim.dvd_of_fraction_map_dvd_fraction_map h)

theorem isCoprime_map_derivative [CharZero B] {F : B[X]}
    (hF : Irreducible F) (hdeg : F.natDegree ≠ 0) :
    IsCoprime (F.map (algebraMap B (FractionRing B)))
      ((derivative F).map (algebraMap B (FractionRing B))) := by
  have hprim := hF.isPrimitive hdeg
  have hirr : Irreducible (F.map (algebraMap B (FractionRing B))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).1 hF
  rw [← Polynomial.derivative_map]
  exact (Polynomial.separable_def _).1 hirr.separable

end Frac

/-! ## Splitting off one variable -/

section Split

variable {σ : Type*} [DecidableEq σ]

/-- View an integer multivariate polynomial as a polynomial in the variable
`i` over the remaining variables. -/
def splitVar (i : σ) :
    MvPolynomial σ ℤ ≃ₐ[ℤ] Polynomial (MvPolynomial {b // b ≠ i} ℤ) :=
  (renameEquiv ℤ (Equiv.optionSubtypeNe i).symm).trans
    (optionEquivLeft ℤ {b // b ≠ i})

theorem natDegree_splitVar (i : σ) (p : MvPolynomial σ ℤ) :
    (splitVar i p).natDegree = degreeOf i p := by
  rw [degreeOf_eq_natDegree]
  rfl

theorem splitVar_X_self (i : σ) : splitVar i (X i) = Polynomial.X := by
  simp [splitVar]

theorem splitVar_X_ne (i j : σ) (h : j ≠ i) :
    splitVar i (X j) = Polynomial.C (X ⟨j, h⟩) := by
  simp [splitVar, Equiv.optionSubtypeNe_symm_of_ne h]

theorem splitVar_pderiv (i : σ) (p : MvPolynomial σ ℤ) :
    splitVar i (pderiv i p) = derivative (splitVar i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [splitVar]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul,
        map_mul, map_mul, hp, Polynomial.derivative_mul]
      by_cases hj : j = i
      · subst hj
        rw [pderiv_X_self, splitVar_X_self, Polynomial.derivative_X, map_one]
        ring
      · rw [pderiv_X_of_ne hj, splitVar_X_ne i j hj, Polynomial.derivative_C,
          map_zero]
        ring

theorem degreeOf_splitVar_symm_C (i : σ) (c : MvPolynomial {b // b ≠ i} ℤ) :
    degreeOf i ((splitVar i).symm (Polynomial.C c)) = 0 := by
  rw [← natDegree_splitVar, AlgEquiv.apply_symm_apply, Polynomial.natDegree_C]

theorem exists_bezout_of_not_dvd {f g : MvPolynomial σ ℤ}
    (hf : Irreducible f) {i : σ} (hi : degreeOf i f ≠ 0) (hfg : ¬ f ∣ g) :
    ∃ a b c : MvPolynomial σ ℤ, c ≠ 0 ∧ degreeOf i c = 0 ∧
      a * f + b * g = c := by
  set e := splitVar (σ := σ) i
  have hF : Irreducible (e f) := (MulEquiv.irreducible_iff e.toMulEquiv).2 hf
  have hdeg : (e f).natDegree ≠ 0 := by rwa [natDegree_splitVar]
  have hFG : ¬ e f ∣ e g := fun h ↦ hfg ((map_dvd_iff e).1 h)
  obtain ⟨a, b, d, hd, h⟩ :=
    exists_mul_add_mul_eq_C (isCoprime_map_of_irreducible_of_not_dvd hF hdeg hFG)
  refine ⟨e.symm a, e.symm b, e.symm (Polynomial.C d), ?_,
    degreeOf_splitVar_symm_C i d, ?_⟩
  · exact (map_ne_zero_iff e.symm e.symm.injective).2
      (Polynomial.C_ne_zero.2 hd)
  · have h' := congrArg e.symm h
    simpa only [map_add, map_mul, AlgEquiv.symm_apply_apply] using h'

theorem exists_bezout_pderiv {f : MvPolynomial σ ℤ}
    (hf : Irreducible f) {i : σ} (hi : degreeOf i f ≠ 0) :
    ∃ a b c : MvPolynomial σ ℤ, c ≠ 0 ∧ degreeOf i c = 0 ∧
      a * f + b * pderiv i f = c := by
  set e := splitVar (σ := σ) i
  have hF : Irreducible (e f) := (MulEquiv.irreducible_iff e.toMulEquiv).2 hf
  have hdeg : (e f).natDegree ≠ 0 := by rwa [natDegree_splitVar]
  obtain ⟨a, b, d, hd, h⟩ :=
    exists_mul_add_mul_eq_C (isCoprime_map_derivative hF hdeg)
  rw [← splitVar_pderiv] at h
  change a * e f + b * e (pderiv i f) = Polynomial.C d at h
  refine ⟨e.symm a, e.symm b, e.symm (Polynomial.C d), ?_,
    degreeOf_splitVar_symm_C i d, ?_⟩
  · exact (map_ne_zero_iff e.symm e.symm.injective).2
      (Polynomial.C_ne_zero.2 hd)
  · have h' := congrArg e.symm h
    simpa only [map_add, map_mul, AlgEquiv.symm_apply_apply] using h'

end Split

/-! ## Transport to real coefficients -/

section Real

variable {σ τ : Type*}

/-- Integer polynomial, renamed and read with real coefficients. -/
abbrev realLift (ι : σ → τ) (p : MvPolynomial σ ℤ) : MvPolynomial τ ℝ :=
  rename ι (MvPolynomial.map (Int.castRingHom ℝ) p)

theorem realLift_injective {ι : σ → τ} (hι : Function.Injective ι) :
    Function.Injective (realLift ι) :=
  (rename_injective ι hι).comp
    (MvPolynomial.map_injective _ Int.cast_injective)

theorem realLift_ne_zero {ι : σ → τ} (hι : Function.Injective ι)
    {p : MvPolynomial σ ℤ} (hp : p ≠ 0) : realLift ι p ≠ 0 := by
  intro h
  apply hp
  apply realLift_injective hι
  rw [h]
  simp [realLift]

theorem degreeOf_realLift {ι : σ → τ} (hι : Function.Injective ι) (i : σ)
    (p : MvPolynomial σ ℤ) : degreeOf (ι i) (realLift ι p) = degreeOf i p := by
  classical
  rw [degreeOf_rename_of_injective hι, degreeOf_def, degreeOf_def,
    degrees_map_of_injective _ Int.cast_injective]

theorem degreeOf_realLift_of_not_mem [DecidableEq τ] {ι : σ → τ}
    (p : MvPolynomial σ ℤ) (v : τ) (hv : v ∉ Set.range ι) :
    degreeOf v (realLift ι p) = 0 := by
  by_contra h
  rw [← Ne, ← mem_vars_iff_degreeOf_ne_zero] at h
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (vars_rename ι _ h)
  exact hv ⟨i, rfl⟩

theorem degreeOf_le_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    {h F : MvPolynomial τ R} (hd : h ∣ F) (hF : F ≠ 0) (v : τ) :
    degreeOf v h ≤ degreeOf v F := by
  obtain ⟨q, rfl⟩ := hd
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hF) (right_ne_zero_of_mul hF)]
  omega

theorem isUnit_of_degreeOf_eq_zero {h : MvPolynomial τ ℝ} (h0 : h ≠ 0)
    (hd : ∀ v, degreeOf v h = 0) : IsUnit h := by
  have hv : h.vars = ∅ :=
    Finset.eq_empty_of_forall_notMem fun v hv ↦
      (mem_vars_iff_degreeOf_ne_zero.1 hv) (hd v)
  rw [vars_eq_empty_iff_eq_C] at hv
  rw [hv]
  refine (isUnit_iff_ne_zero.2 ?_).map MvPolynomial.C
  intro hc
  apply h0
  rw [hv, hc, map_zero]

/-- A real divisor of `realLift ι f` which also divides, for each variable
occurring in `f`, a nonzero integer polynomial free of that variable, is a
unit. -/
theorem isUnit_of_dvd_realLift [DecidableEq τ] {ι : σ → τ}
    (hι : Function.Injective ι) {f : MvPolynomial σ ℤ} (hf0 : f ≠ 0)
    {h : MvPolynomial τ ℝ} (hhf : h ∣ realLift ι f)
    (hkill : ∀ i, degreeOf i f ≠ 0 → ∃ c : MvPolynomial σ ℤ,
      c ≠ 0 ∧ degreeOf i c = 0 ∧ h ∣ realLift ι c) : IsUnit h := by
  have hF0 := realLift_ne_zero hι hf0
  have h0 : h ≠ 0 := by
    rintro rfl
    exact hF0 (zero_dvd_iff.1 hhf)
  apply isUnit_of_degreeOf_eq_zero h0
  intro v
  by_cases hv : v ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hv
    by_cases hi : degreeOf i f = 0
    · have := degreeOf_le_of_dvd hhf hF0 (ι i)
      rw [degreeOf_realLift hι, hi] at this
      omega
    · obtain ⟨c, hc0, hci, hhc⟩ := hkill i hi
      have := degreeOf_le_of_dvd hhc (realLift_ne_zero hι hc0) (ι i)
      rw [degreeOf_realLift hι, hci] at this
      omega
  · have := degreeOf_le_of_dvd hhf hF0 v
    rw [degreeOf_realLift_of_not_mem f v hv] at this
    omega

theorem isRelPrime_realLift [DecidableEq σ] [DecidableEq τ] {ι : σ → τ}
    (hι : Function.Injective ι) {f g : MvPolynomial σ ℤ}
    (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    IsRelPrime (realLift ι f) (realLift ι g) := by
  intro h hhf hhg
  apply isUnit_of_dvd_realLift hι hf.ne_zero hhf
  intro i hi
  obtain ⟨a, b, c, hc0, hci, habc⟩ := exists_bezout_of_not_dvd hf hi hfg
  refine ⟨c, hc0, hci, ?_⟩
  rw [← habc]
  simp only [realLift, map_add, map_mul]
  exact dvd_add (dvd_mul_of_dvd_right hhf _) (dvd_mul_of_dvd_right hhg _)

theorem dvd_derivation_of_mul_self_dvd {R A : Type*} [CommSemiring R]
    [CommRing A] [Algebra R A] (D : Derivation R A A) {x y : A}
    (h : x * x ∣ y) : x ∣ D y := by
  obtain ⟨q, rfl⟩ := h
  simp only [D.leibniz, smul_eq_mul]
  exact ⟨x * D q + q * (D x + D x), by ring⟩

theorem squarefree_realLift [DecidableEq σ] [DecidableEq τ] {ι : σ → τ}
    (hι : Function.Injective ι) {f : MvPolynomial σ ℤ} (hf : Irreducible f) :
    Squarefree (realLift ι f) := by
  intro x hx
  have hxf : x ∣ realLift ι f := dvd_trans (dvd_mul_right x x) hx
  apply isUnit_of_dvd_realLift hι hf.ne_zero hxf
  intro i hi
  obtain ⟨a, b, c, hc0, hci, habc⟩ := exists_bezout_pderiv hf hi
  refine ⟨c, hc0, hci, ?_⟩
  have hder : x ∣ pderiv (ι i) (realLift ι f) :=
    dvd_derivation_of_mul_self_dvd (pderiv (ι i)) hx
  have hcomm : pderiv (ι i) (realLift ι f) = realLift ι (pderiv i f) := by
    simp only [realLift, pderiv_rename hι, pderiv_map]
  rw [hcomm] at hder
  rw [← habc]
  simp only [realLift, map_add, map_mul] at hder hxf ⊢
  exact dvd_add (dvd_mul_of_dvd_right hxf _) (dvd_mul_of_dvd_right hder _)

end Real

end

end Natfunbasis.RealDescent
