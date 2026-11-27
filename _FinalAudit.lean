import Natfunbasis.MainTheorems
open Natfunbasis

-- the statements, restated by hand from the base definitions
example : ∀ (f g : NaturalFunction), g.Nonconstant → g.AddAtomic → (f ^ g).AddAtomic :=
  Main.pow_addAtomic
example : ∀ f : NaturalFunction, (f ^ NaturalFunction.input).AddAtomic :=
  Main.pow_input_addAtomic
example : ∀ f : NaturalFunction, f.AddAtomic ↔ IsBasis f := Main.addAtomic_iff_isBasis
example : ∀ f : NaturalFunction, ∃ s : BasisSum, s.Valid ∧ s.value = f ∧
    ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms := Main.exists_basisSum_unique
example : Wilkie.CanonicalWilkieIndependence := Wilkie.canonicalWilkieIndependence
example : Wilkie.OriginalTermIntegerToReal := Wilkie.originalTermIntegerToReal

-- the input really is the identity n ↦ n, and powers are natural powers
example (n : PosNat) : NaturalFunction.input n = n.1 := rfl
example (f g : NaturalFunction) (n : PosNat) : (f ^ g) n = f n ^ g n := rfl
#print NaturalFunction.AddAtomic
#print NaturalFunction.Nonconstant
#print IsTower
#print IsBasis

#print axioms Main.pow_addAtomic
#print axioms Main.pow_input_addAtomic
#print axioms Main.addAtomic_iff_isBasis
#print axioms Main.exists_basisSum_unique
#print axioms Wilkie.canonicalWilkieIndependence
#print axioms Wilkie.originalTermIntegerToReal
