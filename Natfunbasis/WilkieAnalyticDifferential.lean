import Natfunbasis.WilkieAnalyticPrerequisites

/-!
# Differentiation on positive-axis analytic functions

This module equips `PositiveAnalyticFunction` with the ordinary derivative.
The implementation chooses an ambient analytic extension, but the resulting
function is independent of that choice because the positive axis is open.
Thus the analytic integral domain developed in
`WilkieAnalyticPrerequisites` is closed under differentiation.

This is still a ring, not Wilkie's field `F_0`: extending this derivation to
the fraction field and identifying its constants remain separate tasks.
-/

namespace Natfunbasis.Wilkie

open Set

noncomputable section

namespace PositiveAnalyticFunction

/-- Differentiate a chosen analytic extension and restrict back to the
positive axis. -/
def derivative (f : PositiveAnalyticFunction) : PositiveAnalyticFunction :=
  ⟨fun y ↦ deriv (extension f) y.1,
    ⟨deriv (extension f), (extension_analytic f).deriv, fun _ ↦ rfl⟩⟩

@[simp]
theorem derivative_apply (f : PositiveAnalyticFunction) (y : PositiveReal) :
    (derivative f).1 y = deriv (extension f) y.1 :=
  rfl

/-- Compute the bundled derivative using any analytic extension, not only the
one selected by `Classical.choose`. -/
theorem derivative_eq_deriv_of_extension
    (f : PositiveAnalyticFunction) (F : Real → Real)
    (_hF : AnalyticOnNhd Real F positiveAxis)
    (hFrestrict : ∀ y : PositiveReal, f.1 y = F y.1)
    (y : PositiveReal) :
    (derivative f).1 y = deriv F y.1 := by
  apply deriv_eqOn_positiveAxis_of_eqOn (f := extension f) (g := F) _ y.2
  intro x hx
  let z : PositiveReal := ⟨x, hx⟩
  exact (extension_restrict f z).symm.trans (hFrestrict z)

@[simp]
theorem derivative_zero : derivative (0 : PositiveAnalyticFunction) = 0 := by
  apply Subtype.ext
  funext y
  rw [derivative_eq_deriv_of_extension (0 : PositiveAnalyticFunction)
    (fun _ ↦ 0) analyticOnNhd_const (by simp) y]
  exact deriv_const _ _

@[simp]
theorem derivative_add (f g : PositiveAnalyticFunction) :
    derivative (f + g) = derivative f + derivative g := by
  apply Subtype.ext
  funext y
  rw [derivative_eq_deriv_of_extension (f + g)
    (extension f + extension g) ((extension_analytic f).add (extension_analytic g))]
  · change deriv (extension f + extension g) y.1 =
      deriv (extension f) y.1 + deriv (extension g) y.1
    exact deriv_add ((extension_analytic f y.1 y.2).differentiableAt)
      ((extension_analytic g y.1 y.2).differentiableAt)
  · intro z
    change f.1 z + g.1 z = extension f z.1 + extension g z.1
    rw [extension_restrict f z, extension_restrict g z]

@[simp]
theorem derivative_mul (f g : PositiveAnalyticFunction) :
    derivative (f * g) = f * derivative g + g * derivative f := by
  apply Subtype.ext
  funext y
  rw [derivative_eq_deriv_of_extension (f * g)
    (extension f * extension g) ((extension_analytic f).mul (extension_analytic g))]
  · change deriv (extension f * extension g) y.1 =
      f.1 y * deriv (extension g) y.1 +
        g.1 y * deriv (extension f) y.1
    rw [deriv_mul ((extension_analytic f y.1 y.2).differentiableAt)
      ((extension_analytic g y.1 y.2).differentiableAt),
      extension_restrict f y, extension_restrict g y]
    ring
  · intro z
    change f.1 z * g.1 z = extension f z.1 * extension g z.1
    rw [extension_restrict f z, extension_restrict g z]

/-- Differentiation as an additive homomorphism. -/
def derivativeAddHom :
    PositiveAnalyticFunction →+ PositiveAnalyticFunction where
  toFun := derivative
  map_zero' := derivative_zero
  map_add' := derivative_add

/-- Ordinary differentiation is an integer-linear derivation on the analytic
function ring. -/
def derivation : Derivation Int PositiveAnalyticFunction
    PositiveAnalyticFunction :=
  Derivation.mk' derivativeAddHom.toIntLinearMap (by
    intro f g
    change derivative (f * g) =
      f * derivative g + g * derivative f
    exact derivative_mul f g)

@[simp]
theorem derivation_apply (f : PositiveAnalyticFunction) :
    derivation f = derivative f :=
  rfl

/-- The analytic-function integral domain is a differential ring. -/
instance : Differential PositiveAnalyticFunction where
  deriv := derivation

end PositiveAnalyticFunction

end


end Natfunbasis.Wilkie
