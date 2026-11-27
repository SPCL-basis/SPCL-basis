import Natfunbasis.ExpressionNormalizerAssembly
import Natfunbasis.PowerPolynomialReification
import Mathlib.Algebra.MvPolynomial.Supported

/-!
# Global finite-stage transport and the concrete power step

Every natural-coefficient polynomial in the countable Wilkie coordinate
family uses only finitely many coordinates.  This file transports such a
polynomial to the initial finite stage which contains its variables, without
renumbering those variables.  It then packages the finite-stage semantic
power identity as the concrete nonconstant-power step consumed by the
recursive expression normalizer.
-/

namespace Natfunbasis

open MvPolynomial

namespace Wilkie

noncomputable section

/-! ## Initial-segment presentations -/

/-- The largest coordinate used by a global natural polynomial.  The empty
variable set has bound zero, so the associated stage still contains the
original coordinate. -/
def natStageBound (p : MvPolynomial Nat Nat) : Nat :=
  p.vars.sup id

/-- Every variable of `p` belongs to the initial segment determined by
`natStageBound p`. -/
theorem mem_vars_lt_natStageBound_succ (p : MvPolynomial Nat Nat)
    {i : Nat} (hi : i ∈ p.vars) : i < natStageBound p + 1 := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)

/-- A polynomial whose variables lie in the first `k+1` global coordinates
can be presented at stage `k`, with the literal coordinate embedding
`Fin.val`. -/
theorem exists_stagePresentation (p : MvPolynomial Nat Nat) :
    ∃ q : StageNatPolynomial (natStageBound p),
      MvPolynomial.rename (fun i : StageVar (natStageBound p) ↦ i.1) q = p := by
  apply MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (fun i : StageVar (natStageBound p) ↦ i.1) Fin.val_injective
  intro i hi
  exact ⟨⟨i, mem_vars_lt_natStageBound_succ p hi⟩, rfl⟩

/-- The chosen initial-stage presentation of a global natural polynomial. -/
def toNatStage (p : MvPolynomial Nat Nat) :
    StageNatPolynomial (natStageBound p) :=
  Classical.choose (exists_stagePresentation p)

/-- The chosen presentation preserves the actual global coordinate indices. -/
theorem rename_toNatStage (p : MvPolynomial Nat Nat) :
    MvPolynomial.rename (fun i : StageVar (natStageBound p) ↦ i.1)
      (toNatStage p) = p :=
  Classical.choose_spec (exists_stagePresentation p)

/-- The canonical recursive stage assignment is exactly the restriction of
the canonical global real-coordinate family to that initial segment. -/
theorem canonical_recursiveAssignment_eq (k : Nat) (y : PositiveReal)
    (i : StageVar k) :
    recursiveAssignment
        canonicalGeneratorSequence.canonicalRealization.tau k y i =
      canonicalRealCoordinates i.1 y := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Evaluation of a finite-stage presentation agrees exactly with global
evaluation at the canonical Wilkie coordinates. -/
theorem evaluateReal_rename_stage {k : Nat} (p : StageNatPolynomial k)
    (y : PositiveReal) :
    NormalForm.ExpressionNormalizerAssembly.evaluateReal
        (MvPolynomial.rename (fun i : StageVar k ↦ i.1) p) y =
      p.evalReal
        (recursiveAssignment
          canonicalGeneratorSequence.canonicalRealization.tau k y) := by
  induction p using MvPolynomial.induction_on with
  | C n =>
      simp [NormalForm.ExpressionNormalizerAssembly.evaluateReal,
        StageNatPolynomial.evalReal]
  | add p q hp hq =>
      simpa [StageNatPolynomial.evalReal] using congrArg₂ (fun a b : Real ↦ a + b) hp hq
  | mul_X p i hp =>
      simpa [StageNatPolynomial.evalReal,
        canonical_recursiveAssignment_eq] using
        congrArg₂ (fun a b : Real ↦ a * b) hp
          (NormalForm.ExpressionNormalizerAssembly.evaluateReal_X i.1 y)

/-- In particular, evaluation of the chosen stage presentation is global
evaluation of the original polynomial. -/
theorem toNatStage_evalReal (p : MvPolynomial Nat Nat) (y : PositiveReal) :
    (toNatStage p).evalReal
        (recursiveAssignment
          canonicalGeneratorSequence.canonicalRealization.tau
          (natStageBound p) y) =
      NormalForm.ExpressionNormalizerAssembly.evaluateReal p y := by
  rw [← evaluateReal_rename_stage (toNatStage p), rename_toNatStage]

/-- Nonzeroness is reflected by the chosen finite-stage presentation. -/
theorem toNatStage_ne_zero {p : MvPolynomial Nat Nat} (hp : p ≠ 0) :
    toNatStage p ≠ 0 := by
  intro hzero
  apply hp
  rw [← rename_toNatStage p, hzero]
  simp

/-- Being different from one is reflected by the chosen finite-stage
presentation. -/
theorem toNatStage_ne_one {p : MvPolynomial Nat Nat} (hp : p ≠ 1) :
    toNatStage p ≠ 1 := by
  intro hone
  apply hp
  rw [← rename_toNatStage p, hone]
  simp

/-! ## Polynomial outputs for the finite W2/W3 grid -/

/-- Flatten the factor-by-monomial grid to the corresponding list of
auxiliary-generator indices. -/
def powerGridIndices {baseStage exponentStage : Nat}
    (factors : List (ClassifiedFactor baseStage))
    (monomials : List (NonconstantMonomial exponentStage))
    (index : ClassifiedFactor baseStage →
      NonconstantMonomial exponentStage → Nat) : List Nat :=
  factors.flatMap fun q ↦ monomials.map fun m ↦ index q m

/-- The natural polynomial obtained by multiplying the auxiliary variables
selected by a power grid. -/
def powerGridPolynomial {baseStage exponentStage : Nat}
    (factors : List (ClassifiedFactor baseStage))
    (monomials : List (NonconstantMonomial exponentStage))
    (index : ClassifiedFactor baseStage →
      NonconstantMonomial exponentStage → Nat) :
    MvPolynomial Nat Nat :=
  ((powerGridIndices factors monomials index).map fun i ↦
    (X (i + 1) : MvPolynomial Nat Nat)).prod

/-- A product over a flattened rectangular list is the corresponding nested
product. -/
theorem prod_map_powerGridIndices {baseStage exponentStage : Nat}
    (factors : List (ClassifiedFactor baseStage))
    (monomials : List (NonconstantMonomial exponentStage))
    (index : ClassifiedFactor baseStage →
      NonconstantMonomial exponentStage → Nat)
    {M : Type*} [CommMonoid M] (f : Nat → M) :
    ((powerGridIndices factors monomials index).map f).prod =
      (factors.map fun q ↦
        (monomials.map fun m ↦ f (index q m)).prod).prod := by
  induction factors with
  | nil => simp [powerGridIndices]
  | cons q factors ih =>
      simp only [powerGridIndices, List.flatMap_cons, List.map_append,
        List.prod_append, List.map_cons, List.prod_cons]
      unfold powerGridIndices at ih
      rw [ih, List.map_map]
      rfl

/-- Evaluation carries a finite product of auxiliary variables to the
corresponding product of canonical real coordinates. -/
theorem evaluateReal_product_auxiliaryVariables (indices : List Nat)
    (y : PositiveReal) :
    NormalForm.ExpressionNormalizerAssembly.evaluateReal
        (indices.map fun i ↦ (X (i + 1) : MvPolynomial Nat Nat)).prod y =
      (indices.map fun i ↦ canonicalRealCoordinates (i + 1) y).prod := by
  induction indices with
  | nil =>
      exact NormalForm.ExpressionNormalizerAssembly.evaluateReal_one y
  | cons i indices ih =>
      rw [List.map_cons, List.prod_cons,
        NormalForm.ExpressionNormalizerAssembly.evaluateReal_mul, ih,
        NormalForm.ExpressionNormalizerAssembly.evaluateReal_X]
      rfl

/-- Evaluation of the grid polynomial is the nested product occurring in
the finite-stage semantic power identity. -/
theorem evaluateReal_powerGridPolynomial
    {baseStage exponentStage : Nat}
    (factors : List (ClassifiedFactor baseStage))
    (monomials : List (NonconstantMonomial exponentStage))
    (index : ClassifiedFactor baseStage →
      NonconstantMonomial exponentStage → Nat)
    (y : PositiveReal) :
    NormalForm.ExpressionNormalizerAssembly.evaluateReal
        (powerGridPolynomial factors monomials index) y =
      (factors.map fun q ↦
        (monomials.map fun m ↦
          canonicalGeneratorSequence.canonicalRealization.tau
            (index q m) y).prod).prod := by
  rw [powerGridPolynomial, evaluateReal_product_auxiliaryVariables]
  rw [prod_map_powerGridIndices]
  simp only [canonicalRealCoordinates_succ]

/-- A finite product of auxiliary variables is one coefficient-one
monomial; its exponent vector records the list multiplicities. -/
theorem product_auxiliaryVariables_eq_monomial (indices : List Nat) :
    (indices.map fun i ↦ (X (i + 1) : MvPolynomial Nat Nat)).prod =
      monomial
        ((indices.map fun i ↦ Finsupp.single (i + 1) 1).sum) 1 := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih]
      change
        monomial (Finsupp.single (i + 1) 1) 1 *
            monomial
              ((indices.map fun j ↦ Finsupp.single (j + 1) 1).sum) 1 = _
      rw [MvPolynomial.monomial_mul]
      simp

/-- A nonempty product of auxiliary variables has a nonzero exponent
vector. -/
theorem sum_single_auxiliary_ne_zero {indices : List Nat}
    (hindices : indices ≠ []) :
    (indices.map fun i ↦ Finsupp.single (i + 1) 1).sum ≠ 0 := by
  cases indices with
  | nil => exact (hindices rfl).elim
  | cons i indices =>
      intro hzero
      have hvalue := congrArg
        (fun exponents : Nat →₀ Nat ↦ exponents (i + 1)) hzero
      simp at hvalue

/-- If both axes of a rectangular grid are nonempty, its flattened index
list is nonempty. -/
theorem powerGridIndices_ne_nil {baseStage exponentStage : Nat}
    {factors : List (ClassifiedFactor baseStage)}
    {monomials : List (NonconstantMonomial exponentStage)}
    (index : ClassifiedFactor baseStage →
      NonconstantMonomial exponentStage → Nat)
    (hfactors : factors ≠ []) (hmonomials : monomials ≠ []) :
    powerGridIndices factors monomials index ≠ [] := by
  cases factors with
  | nil => exact (hfactors rfl).elim
  | cons q factors =>
      cases monomials with
      | nil => exact (hmonomials rfl).elim
      | cons m monomials => simp [powerGridIndices]

/-! ## Global semantic reification -/

/-- Away from bases `0` and `1`, the finite-stage theorem produces an
actual global natural polynomial representing the power at every canonical
positive-real coordinate. -/
theorem exists_global_power_polynomial_of_ne_zero_one
    (base exponent : MvPolynomial Nat Nat)
    (hbaseZero : base ≠ 0) (hbaseOne : base ≠ 1)
    (hexponentZero : exponent ≠ 0) :
    ∃ output : MvPolynomial Nat Nat,
      ∀ y : PositiveReal,
        NormalForm.ExpressionNormalizerAssembly.evaluateReal output y =
          Real.rpow
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal base y)
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal exponent y) := by
  obtain ⟨factors, index, hfactors, hproduct, hexponentVisible,
      hcell, hidentity⟩ :=
    exists_arbitraryPolynomial_powerBranch_identity
      canonicalGeneratorSequence (toNatStage base) (toNatStage exponent)
      (toNatStage_ne_zero hbaseZero) (toNatStage_ne_one hbaseOne)
      (toNatStage_ne_zero hexponentZero)
  refine ⟨base ^ constantCoeff (toNatStage exponent) *
      powerGridPolynomial factors
        (toNatStage exponent).nonconstantMonomials index, ?_⟩
  intro y
  rw [NormalForm.ExpressionNormalizerAssembly.evaluateReal_mul,
    NormalForm.ExpressionNormalizerAssembly.evaluateReal_pow,
    evaluateReal_powerGridPolynomial]
  rw [← toNatStage_evalReal base y, ← toNatStage_evalReal exponent y]
  exact (hidentity canonicalGeneratorSequence.canonicalRealization y).symm

/-- The chosen finite-stage presentation of a nonconstant coefficient-one
monomial has zero constant coefficient. -/
theorem constantCoeff_toNatStage_monomial {m : Nat →₀ Nat} (hm : m ≠ 0) :
    constantCoeff (toNatStage (monomial m (1 : Nat))) = 0 := by
  have hconstant := congrArg MvPolynomial.constantCoeff
    (rename_toNatStage (monomial m (1 : Nat)))
  rw [MvPolynomial.constantCoeff_rename,
    MvPolynomial.constantCoeff_monomial, if_neg hm] at hconstant
  exact hconstant

/-- For a coefficient-one nonconstant monomial exponent, the global power
output itself can be chosen to be a coefficient-one nonconstant monomial. -/
theorem exists_global_monomial_power
    (base : MvPolynomial Nat Nat) (m : Nat →₀ Nat)
    (hbaseZero : base ≠ 0) (hbaseOne : base ≠ 1) (hm : m ≠ 0) :
    ∃ outputExponent : Nat →₀ Nat, outputExponent ≠ 0 ∧
      ∀ y : PositiveReal,
        NormalForm.ExpressionNormalizerAssembly.evaluateReal
            (monomial outputExponent (1 : Nat)) y =
          Real.rpow
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal base y)
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal
              (monomial m (1 : Nat)) y) := by
  have hexponentZero : (monomial m (1 : Nat) : MvPolynomial Nat Nat) ≠ 0 := by
    intro hzero
    exact one_ne_zero (MvPolynomial.monomial_eq_zero.mp hzero)
  obtain ⟨factors, index, hfactors, hproduct, hexponentVisible,
      hcell, hidentity⟩ :=
    exists_arbitraryPolynomial_powerBranch_identity
      canonicalGeneratorSequence (toNatStage base)
      (toNatStage (monomial m (1 : Nat)))
      (toNatStage_ne_zero hbaseZero) (toNatStage_ne_one hbaseOne)
      (toNatStage_ne_zero hexponentZero)
  have hconstant :
      constantCoeff (toNatStage (monomial m (1 : Nat))) = 0 :=
    constantCoeff_toNatStage_monomial hm
  have hmonomials :
      (toNatStage (monomial m (1 : Nat))).nonconstantMonomials ≠ [] := by
    rcases hexponentVisible with hconstantNonzero | hmonomials
    · exact (hconstantNonzero hconstant).elim
    · exact hmonomials
  let indices : List Nat :=
    powerGridIndices factors
      (toNatStage (monomial m (1 : Nat))).nonconstantMonomials index
  have hindices : indices ≠ [] := by
    exact powerGridIndices_ne_nil index hfactors hmonomials
  let outputExponent : Nat →₀ Nat :=
    (indices.map fun i ↦ Finsupp.single (i + 1) 1).sum
  refine ⟨outputExponent, ?_, ?_⟩
  · exact sum_single_auxiliary_ne_zero hindices
  · intro y
    calc
      NormalForm.ExpressionNormalizerAssembly.evaluateReal
          (monomial outputExponent (1 : Nat)) y =
          NormalForm.ExpressionNormalizerAssembly.evaluateReal
            (powerGridPolynomial factors
              (toNatStage (monomial m (1 : Nat))).nonconstantMonomials
              index) y := by
        apply congrArg
          (fun p : MvPolynomial Nat Nat ↦
            NormalForm.ExpressionNormalizerAssembly.evaluateReal p y)
        exact (product_auxiliaryVariables_eq_monomial indices).symm
      _ = (factors.map fun q ↦
          ((toNatStage (monomial m (1 : Nat))).nonconstantMonomials.map
            fun exponentMonomial ↦
              canonicalGeneratorSequence.canonicalRealization.tau
                (index q exponentMonomial) y).prod).prod :=
        evaluateReal_powerGridPolynomial _ _ _ y
      _ = (toNatStage base).evalReal
            (recursiveAssignment
              canonicalGeneratorSequence.canonicalRealization.tau
              (natStageBound base) y) ^
              constantCoeff (toNatStage (monomial m (1 : Nat))) *
            (factors.map fun q ↦
              ((toNatStage (monomial m (1 : Nat))).nonconstantMonomials.map
                fun exponentMonomial ↦
                  canonicalGeneratorSequence.canonicalRealization.tau
                    (index q exponentMonomial) y).prod).prod := by
        simp [hconstant]
      _ = Real.rpow
            ((toNatStage base).evalReal
              (recursiveAssignment
                canonicalGeneratorSequence.canonicalRealization.tau
                (natStageBound base) y))
            ((toNatStage (monomial m (1 : Nat))).evalReal
              (recursiveAssignment
                canonicalGeneratorSequence.canonicalRealization.tau
                (natStageBound (monomial m (1 : Nat))) y)) :=
        (hidentity canonicalGeneratorSequence.canonicalRealization y).symm
      _ = Real.rpow
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal base y)
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal
              (monomial m (1 : Nat)) y) := by
        rw [toNatStage_evalReal base y,
          toNatStage_evalReal (monomial m (1 : Nat)) y]

/-- A genuinely nonconstant natural polynomial is nonzero. -/
theorem ne_zero_of_not_isConstant {p : MvPolynomial Nat Nat}
    (hp : ¬ NormalizerCore.IsConstant p) : p ≠ 0 := by
  intro hzero
  apply hp
  simp [NormalizerCore.IsConstant, hzero]

/-- Every nonzero natural polynomial evaluates positively at the canonical
positive real coordinates. -/
theorem canonical_evaluateReal_pos (p : MvPolynomial Nat Nat) (hp : p ≠ 0)
    (y : PositiveReal) :
    0 < NormalForm.ExpressionNormalizerAssembly.evaluateReal p y := by
  rw [← toNatStage_evalReal p y]
  exact NormalizerCore.evalNatReal_positive (toNatStage p)
    (toNatStage_ne_zero hp)
    (recursiveAssignment
      canonicalGeneratorSequence.canonicalRealization.tau
      (natStageBound p) y)
    (canonicalGeneratorSequence.canonicalRealization.recursiveAssignment_pos
      (natStageBound p) y)

/-- Total semantic reification of a power with genuinely nonconstant
exponent.  The exceptional bases `0` and `1` are handled directly. -/
theorem exists_global_power_polynomial
    (base exponent : MvPolynomial Nat Nat)
    (hexponent : ¬ NormalizerCore.IsConstant exponent) :
    ∃ output : MvPolynomial Nat Nat,
      ∀ y : PositiveReal,
        NormalForm.ExpressionNormalizerAssembly.evaluateReal output y =
          Real.rpow
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal base y)
            (NormalForm.ExpressionNormalizerAssembly.evaluateReal exponent y) := by
  have hexponentZero : exponent ≠ 0 := ne_zero_of_not_isConstant hexponent
  by_cases hbaseZero : base = 0
  · subst base
    refine ⟨0, ?_⟩
    intro y
    rw [NormalForm.ExpressionNormalizerAssembly.evaluateReal_zero]
    exact (Real.zero_rpow
      (ne_of_gt (canonical_evaluateReal_pos exponent hexponentZero y))).symm
  · by_cases hbaseOne : base = 1
    · subst base
      refine ⟨1, ?_⟩
      intro y
      rw [NormalForm.ExpressionNormalizerAssembly.evaluateReal_one]
      exact (Real.one_rpow
        (NormalForm.ExpressionNormalizerAssembly.evaluateReal exponent y)).symm
    · exact exists_global_power_polynomial_of_ne_zero_one
        base exponent hbaseZero hbaseOne hexponentZero

end

end Wilkie

namespace NormalForm.ExpressionNormalizerAssembly

noncomputable section

/-- A semantic power output together with the exact coefficient-one
monomial shape required when its exponent is a nonconstant
coefficient-one monomial and its base is neither `0` nor `1`. -/
structure PowerOutputSpec (base exponent : MvPolynomial Nat Nat) where
  polynomial : MvPolynomial Nat Nat
  correct : ∀ y : Wilkie.PositiveReal,
    evaluateReal polynomial y =
      Real.rpow (evaluateReal base y) (evaluateReal exponent y)
  monomial : ∀ (m : Nat →₀ Nat), m ≠ 0 →
    exponent = MvPolynomial.monomial m 1 →
    base ≠ 0 → base ≠ 1 →
    ∃ out : Nat →₀ Nat, out ≠ 0 ∧
      polynomial = MvPolynomial.monomial out 1

/-- The simultaneous semantic-and-shape output exists for every genuinely
nonconstant exponent.  The monomial branch is selected before making the
classical choice, ensuring that the chosen polynomial has literal monomial
shape when the recursive tower proof asks for it. -/
theorem exists_powerOutputSpec (base exponent : MvPolynomial Nat Nat)
    (hexponent : ¬ NormalizerCore.IsConstant exponent) :
    Nonempty (PowerOutputSpec base exponent) := by
  by_cases hspecial :
      base ≠ 0 ∧ base ≠ 1 ∧
        ∃ m : Nat →₀ Nat, m ≠ 0 ∧
          exponent = MvPolynomial.monomial m 1
  · rcases hspecial with ⟨hbaseZero, hbaseOne, m, hm, rfl⟩
    obtain ⟨out, hout, hcorrect⟩ :=
      Wilkie.exists_global_monomial_power base m hbaseZero hbaseOne hm
    exact ⟨{
      polynomial := MvPolynomial.monomial out 1
      correct := hcorrect
      monomial := by
        intro next hnext hexponent hzero hone
        exact ⟨out, hout, rfl⟩ }⟩
  · obtain ⟨output, hcorrect⟩ :=
      Wilkie.exists_global_power_polynomial base exponent hexponent
    exact ⟨{
      polynomial := output
      correct := hcorrect
      monomial := by
        intro m hm heq hbaseZero hbaseOne
        exfalso
        exact hspecial ⟨hbaseZero, hbaseOne, m, hm, heq⟩ }⟩

/-- The chosen simultaneous output specification. -/
def chosenPowerOutput (base exponent : MvPolynomial Nat Nat)
    (hexponent : ¬ NormalizerCore.IsConstant exponent) :
    PowerOutputSpec base exponent :=
  Classical.choice (exists_powerOutputSpec base exponent hexponent)

/-- The concrete nonconstant-power step obtained from the finite-stage
factorization/reification theorem and the canonical W1--W3 sequence. -/
def canonicalNonconstantPowerStep : NonconstantPowerStep where
  normalize := fun base exponent hexponent ↦
    (chosenPowerOutput base exponent hexponent).polynomial
  evalReal_normalize := by
    intro base exponent hexponent y
    exact (chosenPowerOutput base exponent hexponent).correct y
  normalize_monomial := by
    intro base m hbaseZero hbaseOne hm
    exact (chosenPowerOutput base (MvPolynomial.monomial m 1)
      (monomial_one_not_constant hm)).monomial
        m hm rfl hbaseZero hbaseOne

end

end NormalForm.ExpressionNormalizerAssembly

end Natfunbasis
