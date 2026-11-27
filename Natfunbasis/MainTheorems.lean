import Natfunbasis.OriginalTermHardyTransfer
import Natfunbasis.WilkieFreshStageClosure

/-!
# The main theorems, with no premises

* `pow_addAtomic`: if `f` is a natural function and `g` is a nonconstant
  `+`-atomic natural function, then `f ^ g` is `+`-atomic.
* `pow_input_addAtomic`: in particular `n ↦ f(n) ^ n` is `+`-atomic.
* `addAtomic_iff_isBasis`: the `+`-atomic natural functions are exactly the
  finite products of towers.
* `exists_basisSum_unique`: every natural function is a finite sum of such
  products, uniquely up to order (with multiplicity).

The two former premises are now theorems: the integer-to-real transfer
(`Wilkie.originalTermIntegerToReal`, a Hardy-field argument) and Wilkie's
algebraic independence (`Wilkie.canonicalWilkieIndependence`).
-/

namespace Natfunbasis.Main

open NormalForm

/-- The normal-form package, constructed unconditionally. -/
noncomputable def normalFormPackage : NormalFormPackage :=
  canonicalNormalFormPackage Wilkie.originalTermIntegerToReal
    Wilkie.canonicalWilkieIndependence

/-- The faithful normal-form package, constructed unconditionally. -/
noncomputable def faithfulNormalFormPackage : FaithfulNormalFormPackage :=
  canonicalFaithfulNormalFormPackage Wilkie.originalTermIntegerToReal
    Wilkie.canonicalWilkieIndependence

/-- **`f ^ g` is `+`-atomic** for every natural `f` and every nonconstant
`+`-atomic natural `g`. -/
theorem pow_addAtomic (f g : NaturalFunction)
    (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) :=
  canonical_pow_addAtomic Wilkie.originalTermIntegerToReal
    Wilkie.canonicalWilkieIndependence f g hg_nonconstant hg_atomic

/-- **`n ↦ f(n) ^ n` is `+`-atomic** for every natural function `f`. -/
theorem pow_input_addAtomic (f : NaturalFunction) :
    NaturalFunction.AddAtomic (f ^ NaturalFunction.input) :=
  NormalForm.pow_input_addAtomic normalFormPackage f

/-- **The additive atoms are exactly the finite products of towers.** -/
theorem addAtomic_iff_isBasis (f : NaturalFunction) :
    NaturalFunction.AddAtomic f ↔ IsBasis f :=
  NormalForm.addAtomic_iff_isBasis normalFormPackage f

/-- **The additive basis theorem**: every natural function is a nonempty
finite sum of finite products of towers, unique up to permutation. -/
theorem exists_basisSum_unique (f : NaturalFunction) :
    ∃ s : BasisSum, s.Valid ∧ s.value = f ∧
      ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms :=
  canonical_exists_basisSum_unique Wilkie.originalTermIntegerToReal
    Wilkie.canonicalWilkieIndependence f

end Natfunbasis.Main
