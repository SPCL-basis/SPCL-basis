import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic independence and polynomial evaluation

This module isolates the elementary algebraic consequence used after an
algebraically independent family has been constructed: evaluation at that
family is injective.  It also records the corresponding statement for
multivariate polynomials with natural coefficients after casting them into a
characteristic-zero coefficient ring.

Nothing here proves that Wilkie's particular auxiliary functions are
algebraically independent.  In particular, this module supplies neither the
integer-to-real functional-identity bridge nor the analytic/differential input
behind Wilkie's independence theorem and AJK Theorem 2.7.
-/

namespace Natfunbasis.AlgebraicIndependence

open Function

noncomputable section

variable {ι R A : Type*}

section Generic

variable [CommRing R] [CommRing A] [Algebra R A]
variable (x : ι → A)

/-- An algebraically independent family gives an injective multivariate
polynomial evaluation map. -/
theorem aeval_injective (hx : AlgebraicIndependent R x) :
    Function.Injective (MvPolynomial.aeval x : MvPolynomial ι R → A) :=
  algebraicIndependent_iff_injective_aeval.mp hx

/-- Equality after evaluation at an algebraically independent family is
exactly formal polynomial equality. -/
theorem aeval_eq_iff (hx : AlgebraicIndependent R x)
    {p q : MvPolynomial ι R} :
    MvPolynomial.aeval x p = MvPolynomial.aeval x q ↔ p = q := by
  constructor
  · intro hpq
    exact aeval_injective x hx hpq
  · exact congrArg _

/-- A polynomial evaluates to zero at an algebraically independent family
exactly when it is the zero polynomial. -/
theorem aeval_eq_zero_iff (hx : AlgebraicIndependent R x)
    {p : MvPolynomial ι R} :
    MvPolynomial.aeval x p = 0 ↔ p = 0 := by
  simpa using (aeval_eq_iff x hx :
    MvPolynomial.aeval x p = MvPolynomial.aeval x 0 ↔ p = 0)

section CoefficientMap

variable {S : Type*} [CommSemiring S]

/-- First map coefficients from `S` to `R`, then evaluate at `x`. -/
def mappedAeval (coeff : S →+* R) (x : ι → A) : MvPolynomial ι S →+* A :=
  (MvPolynomial.aeval x).toRingHom.comp (MvPolynomial.map coeff)

/-- Injective coefficient extension followed by evaluation at an algebraically
independent family is injective. -/
theorem mappedAeval_injective (coeff : S →+* R)
    (hcoeff : Function.Injective coeff) (hx : AlgebraicIndependent R x) :
    Function.Injective (mappedAeval coeff x) :=
  (aeval_injective x hx).comp (MvPolynomial.map_injective coeff hcoeff)

end CoefficientMap

end Generic

section NatCoefficients

variable {K : Type*} [CommRing K]
variable [CommRing A] [Algebra K A]
variable (x : ι → A)

/-- Cast natural coefficients to `K`, then evaluate in the `K`-algebra `A`. -/
def natAeval (x : ι → A) : MvPolynomial ι ℕ →+* A :=
  mappedAeval (Nat.castRingHom K) x

@[simp]
theorem natAeval_C (n : ℕ) :
    natAeval (K := K) x (MvPolynomial.C n) = n := by
  simp [natAeval, mappedAeval]

@[simp]
theorem natAeval_X (i : ι) :
    natAeval (K := K) x (MvPolynomial.X i) = x i := by
  simp [natAeval, mappedAeval]

/-- Natural-coefficient polynomials remain distinct after casting into a
characteristic-zero ring and evaluating at a family algebraically independent
over that ring.  In particular this applies when `K` is a characteristic-zero
field and `A` is a commutative `K`-algebra. -/
theorem natAeval_injective [CharZero K] (hx : AlgebraicIndependent K x) :
    Function.Injective (natAeval (K := K) x) :=
  mappedAeval_injective x (Nat.castRingHom K) Nat.cast_injective hx

/-- The equality form of `natAeval_injective`, convenient for coefficient
comparison. -/
theorem natAeval_eq_iff [CharZero K] (hx : AlgebraicIndependent K x)
    {p q : MvPolynomial ι ℕ} :
    natAeval (K := K) x p = natAeval (K := K) x q ↔ p = q := by
  constructor
  · intro hpq
    exact natAeval_injective x hx hpq
  · exact congrArg _

end NatCoefficients

end

end Natfunbasis.AlgebraicIndependence
