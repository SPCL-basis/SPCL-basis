import Natfunbasis.WilkieFreshStagePrimeDerivation
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Perfect

#check RingHom.injective
#check IsFractionRing.lift
#check IsFractionRing.lift_injective
#check IsFractionRing.lift_algebraMap
#check MvPolynomial.map_injective
#check MvPolynomial.rename_map
#check MvPolynomial.map_rename
#check MvPolynomial.optionEquivLeft_map
#check MvPolynomial.degreeOf_eq_natDegree
#check MvPolynomial.mem_vars_iff_degreeOf_ne_zero
#check Polynomial.degree_map_eq_of_injective
#check Polynomial.Separable.squarefree
#check PerfectField.separable_iff_squarefree
#check Irreducible.isPrimitive
#check Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
#check Polynomial.separable_iff_derivative_ne_zero
#check Polynomial.natDegree_eq_zero_of_isUnit
#check Polynomial.natDegree_pos_of_not_isUnit
#check Polynomial.natDegree_mul
#check Polynomial.natDegree_le_of_dvd

open MvPolynomial

theorem optionEquivLeft_map_test {I R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : MvPolynomial (Option I) R) :
    optionEquivLeft S I (map f p) =
      Polynomial.map (map f) (optionEquivLeft R I p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      cases i with
      | none => simp [hp]
      | some i => simp [hp]
