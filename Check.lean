import Natfunbasis.OriginalTermAnalyticAdjunction
open Polynomial
open scoped Differential
namespace Natfunbasis.Wilkie
noncomputable section
namespace Test
variable {K : Type*} [Field K] [Differential K]
def polynomialEvalHom (i : K →+* AnalyticTailGerm) (t : AnalyticTailGerm) :
    K[X] →+* AnalyticTailGerm := Polynomial.eval₂RingHom i t
 theorem foo (i : K →+* AnalyticTailGerm) (t : AnalyticTailGerm) (v : K[X])
    (hi : ∀ a : K, (i a)′ = i a′)
    (ht : t′ = polynomialEvalHom i t v) (p : K[X]) :
    (polynomialEvalHom i t p)′ =
       polynomialEvalHom i t (Differential.implicitDeriv v p) := by
  letI : Algebra K AnalyticTailGerm := i.toAlgebra
  letI : DifferentialAlgebra K AnalyticTailGerm := ⟨hi⟩
  have h := Differential.deriv_aeval_eq_implicitDeriv t v ht p
  rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at h
  exact h
end Test
end
end Natfunbasis.Wilkie
