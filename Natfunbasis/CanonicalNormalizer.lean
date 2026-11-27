import Natfunbasis.GlobalPowerNormalizer
import Natfunbasis.OriginalTermAnalyticity

/-!
# The concrete recursive normalizer and exact source boundary

This module instantiates the recursive expression assembly with the concrete
power step constructed from the canonical W1--W3 sequence.  The resulting
raw normalizer and precertificate are unconditional.  Upgrading them to a
certificate, and hence to the extensional normal-form packages, takes exactly
the two named source inputs: the Macintyre integer-to-real transfer and the
canonical Wilkie algebraic-independence conclusion.
-/

namespace Natfunbasis

namespace NormalForm

noncomputable section

/-- The fully assembled common-family raw polynomial normalizer. -/
def canonicalRaw : UnaryExpr → MvPolynomial Nat Nat :=
  ExpressionNormalizerAssembly.canonicalNonconstantPowerStep.raw

/-- Its unconditional fixed-family precertificate. -/
def canonicalPrecertificate : FixedFamilyPrecertificate :=
  ExpressionNormalizerAssembly.canonicalNonconstantPowerStep.toPrecertificate

/-- The canonical raw polynomial represents the original expression over all
positive real inputs. -/
theorem canonicalRaw_represents_real (e : UnaryExpr)
    (y : Wilkie.PositiveReal) :
    ExpressionNormalizerAssembly.evaluateReal (canonicalRaw e) y =
      Wilkie.UnaryExpr.evalReal e y := by
  exact
    ExpressionNormalizerAssembly.canonicalNonconstantPowerStep.raw_represents_real
      e y

/-- The canonical raw polynomial also represents the expression at every
positive integer input. -/
theorem canonicalRaw_represents (e : UnaryExpr) (n : PosNat) :
    ExpressionNormalizerAssembly.evaluate (canonicalRaw e) n =
      (UnaryExpr.eval e n : Int) := by
  exact
    ExpressionNormalizerAssembly.canonicalNonconstantPowerStep.raw_represents
      e n

/-- Supplying exactly the Macintyre and Wilkie source results upgrades the
unconditional precertificate to a canonical fixed-family certificate. -/
def canonicalCertificate
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence) :
    FixedFamilyCertificate :=
  ExpressionNormalizerAssembly.canonicalNonconstantPowerStep.toCertificate
    htransfer hindependent

/-- The extensional normalization package obtained at the exact two-source
boundary. -/
def canonicalNormalFormPackage
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence) :
    NormalFormPackage :=
  (canonicalCertificate htransfer hindependent).toNormalFormPackage

/-- The faithful extensional package obtained from the same two source
inputs. -/
def canonicalFaithfulNormalFormPackage
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence) :
    FaithfulNormalFormPackage :=
  (canonicalCertificate htransfer hindependent).toFaithfulNormalFormPackage

/-- Conditional final power atomicity, now with no normalizer/package
parameter: only the two explicitly named mathematical source results remain. -/
theorem canonical_pow_addAtomic
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f g : NaturalFunction)
    (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) :=
  pow_addAtomic (canonicalNormalFormPackage htransfer hindependent)
    f g hg_nonconstant hg_atomic

/-- The same final power theorem with the Macintyre transfer premise replaced
by the precise finite-zero/o-minimal alternative to which it has been
reduced. -/
theorem canonical_pow_addAtomic_of_finiteOrIdentical
    (hfinite : Wilkie.OriginalTermFiniteOrIdentical)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f g : NaturalFunction)
    (hg_nonconstant : NaturalFunction.Nonconstant g)
    (hg_atomic : NaturalFunction.AddAtomic g) :
    NaturalFunction.AddAtomic (f ^ g) :=
  canonical_pow_addAtomic
    (Wilkie.originalTermIntegerToReal_of_finiteOrIdentical hfinite)
    hindependent f g hg_nonconstant hg_atomic

/-- Expression-level form of the same conditional final theorem. -/
theorem canonical_expr_pow_addAtomic
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f g : UnaryExpr)
    (hg_nonconstant : UnaryExpr.Nonconstant g)
    (hg_atomic : UnaryExpr.AddAtomic g) :
    UnaryExpr.AddAtomic (.pow f g) :=
  expr_pow_addAtomic (canonicalNormalFormPackage htransfer hindependent)
    f g hg_nonconstant hg_atomic

/-- Conditional final existence-and-uniqueness theorem for additive basis
expansions.  Multiplicity is preserved by the resulting permutation. -/
theorem canonical_exists_basisSum_unique
    (htransfer : Wilkie.OriginalTermIntegerToReal)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f : NaturalFunction) :
    ∃ s : BasisSum,
      s.Valid ∧ s.value = f ∧
        ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms :=
  exists_basisSum_unique
    (canonicalFaithfulNormalFormPackage htransfer hindependent) f

/-- Additive-basis existence and uniqueness with the Macintyre transfer
premise replaced by its exact finite-zero/o-minimal reduction. -/
theorem canonical_exists_basisSum_unique_of_finiteOrIdentical
    (hfinite : Wilkie.OriginalTermFiniteOrIdentical)
    (hindependent : Wilkie.CanonicalWilkieIndependence)
    (f : NaturalFunction) :
    ∃ s : BasisSum,
      s.Valid ∧ s.value = f ∧
        ∀ t : BasisSum, t.Valid → t.value = f → s.terms.Perm t.terms :=
  canonical_exists_basisSum_unique
    (Wilkie.originalTermIntegerToReal_of_finiteOrIdentical hfinite)
    hindependent f

end

end NormalForm

end Natfunbasis
