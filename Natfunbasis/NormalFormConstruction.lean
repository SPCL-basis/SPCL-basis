import Natfunbasis.AlgebraicIndependence
import Natfunbasis.NormalFormConsequences

/-!
# Constructing semantic normal forms from a fixed auxiliary family

This module states, at expression level, the exact certificate from which the
normal-form packages used in `NormalFormConsequences` can be constructed.
The certificates are deliberately structures, not axioms or instances: a
later formalization of the Wilkie--AJK fixed family must provide actual
values.

The coordinate functions (the original input together with the auxiliary
generators) are integer-valued on the positive integers. A raw normal form has
natural coefficients, represents the original expression pointwise after
evaluation at those coordinates, and obeys the constructor and tower clauses
needed downstream.  The minimal certificate asks only that semantic equality
of original expressions gives equality of their raw polynomials.  A stronger
discrete algebraic-independence hypothesis is provided separately as one
sufficient way to establish that exact property.
-/

namespace Natfunbasis

namespace NormalForm

noncomputable section

/-- Expression-level data delivered by a fixed-family one-variable normalizer,
before proving that its output is canonical under semantic equality.

`coordinates` is the single common family used for every expression. Index
zero may be the original input and successor indices the Wilkie auxiliaries. The
`represents` field says that evaluating `raw e` at this family gives the
integer cast of the natural-valued function denoted by `e`, at every positive
integer.

The tower clause is stated for the syntactic tower predicate below.  This is
essential: before canonicity has been proved, a raw normalizer cannot transport
a monomial result from a tower representative to an arbitrary semantically
equal expression.  After canonicity is supplied, `toNormalFormPackage` performs
that transport and obtains the extensional `nf_tower` field.
-/
inductive SyntacticTower : UnaryExpr → Prop where
  | input : SyntacticTower (.var ())
  | pow {u t : UnaryExpr} :
      ¬ UnaryExpr.SemEq u .one → SyntacticTower t →
        SyntacticTower (.pow u t)

/-- A syntactic tower denotes a candidate tower natural function. -/
theorem SyntacticTower.isTower_ofExpr {e : UnaryExpr}
    (he : SyntacticTower e) : IsTower (NaturalFunction.ofExpr e) := by
  induction he with
  | input => exact IsTower.input
  | @pow u t hu ht ih =>
      rw [NaturalFunction.ofExpr_pow]
      apply IsTower.pow
      · intro hOne
        apply hu
        apply NaturalFunction.ofExpr_eq_iff.mp
        simpa using hOne
      · exact ih

/-- Every extensional tower has a syntactic tower representative. -/
theorem exists_syntacticTower_of_isTower {t : NaturalFunction}
    (ht : IsTower t) :
    ∃ e : UnaryExpr, SyntacticTower e ∧ NaturalFunction.ofExpr e = t := by
  induction ht with
  | input =>
      exact ⟨.var (), SyntacticTower.input, rfl⟩
  | @pow u t hu ht ih =>
      obtain ⟨towerExpr, htowerExpr, htowerValue⟩ := ih
      obtain ⟨baseExpr, hbaseExpr⟩ := NaturalFunction.exists_expr u
      have hbaseValue : u = NaturalFunction.ofExpr baseExpr :=
        NaturalFunction.ext hbaseExpr
      refine ⟨.pow baseExpr towerExpr, SyntacticTower.pow ?_ htowerExpr, ?_⟩
      · intro hsem
        apply hu
        calc
          u = NaturalFunction.ofExpr baseExpr := hbaseValue
          _ = NaturalFunction.ofExpr .one :=
            NaturalFunction.ofExpr_eq_iff.mpr hsem
          _ = 1 := NaturalFunction.ofExpr_one
      · rw [NaturalFunction.ofExpr_pow, ← hbaseValue, htowerValue]

structure FixedFamilyPrecertificate where
  coordinates : Nat → PosNat → Int
  raw : UnaryExpr → MvPolynomial Nat Nat
  raw_nonzero : ∀ e, raw e ≠ 0
  raw_one : raw .one = 1
  raw_add : ∀ e d, raw (.add e d) = raw e + raw d
  raw_mul : ∀ e d, raw (.mul e d) = raw e * raw d
  raw_tower : ∀ {e}, SyntacticTower e →
    ∃ m : Monomial, m ≠ 0 ∧ raw e = MvPolynomial.monomial m 1
  represents : ∀ e n,
    (AlgebraicIndependence.natAeval (K := Int) coordinates (raw e)) n =
      (UnaryExpr.eval e n : Int)

/-- The exact fixed-family certificate needed downstream.  `canonical` is
restricted to raw polynomials of original expressions.  This is deliberately
weaker than asserting algebraic independence of every polynomial relation on
the integer grid, and matches the scope in which AJK Theorem 2.7 is used. -/
structure FixedFamilyCertificate extends FixedFamilyPrecertificate where
  canonical : ∀ {e d : UnaryExpr}, UnaryExpr.SemEq e d → raw e = raw d

namespace FixedFamilyPrecertificate

variable (C : FixedFamilyPrecertificate)

/-- Full algebraic independence of the discrete coordinate functions is a
sufficient (but stronger than necessary) way to make a precertificate
canonical. -/
noncomputable def ofAlgebraicIndependent
    (hindependent : AlgebraicIndependent Int C.coordinates) :
    FixedFamilyCertificate where
  toFixedFamilyPrecertificate := C
  canonical := by
    intro e d h
    apply AlgebraicIndependence.natAeval_injective C.coordinates hindependent
    funext n
    rw [C.represents e n, C.represents d n]
    exact congrArg Int.ofNat (h n)

end FixedFamilyPrecertificate

namespace FixedFamilyCertificate

variable (C : FixedFamilyCertificate)

/-- Raw normal forms respect semantic equality.  This is the exact canonical
field retained by the minimal certificate. -/
theorem raw_eq_of_semEq {e d : UnaryExpr} (h : UnaryExpr.SemEq e d) :
    C.raw e = C.raw d :=
  C.canonical h

/-- Equality of raw polynomials implies semantic equality, directly from their
pointwise representation at the fixed family. -/
theorem semEq_of_raw_eq {e d : UnaryExpr} (h : C.raw e = C.raw d) :
    UnaryExpr.SemEq e d := by
  intro n
  have hcast : (UnaryExpr.eval e n : Int) = (UnaryExpr.eval d n : Int) := by
    calc
      (UnaryExpr.eval e n : Int) =
          (AlgebraicIndependence.natAeval (K := Int) C.coordinates (C.raw e)) n :=
        (C.represents e n).symm
      _ = (AlgebraicIndependence.natAeval (K := Int) C.coordinates (C.raw d)) n :=
        congrArg
          (fun p : MvPolynomial Nat Nat ↦
            (AlgebraicIndependence.natAeval (K := Int) C.coordinates p) n)
          h
      _ = (UnaryExpr.eval d n : Int) := C.represents d n
  exact Int.ofNat_injective hcast

/-- For a certified fixed family, semantic equality is exactly equality of raw
normal-form polynomials. -/
theorem raw_eq_iff_semEq {e d : UnaryExpr} :
    C.raw e = C.raw d ↔ UnaryExpr.SemEq e d :=
  ⟨C.semEq_of_raw_eq, C.raw_eq_of_semEq⟩

end FixedFamilyCertificate

/-- A chosen expression representative of an extensional natural function. -/
noncomputable def representative (f : NaturalFunction) : UnaryExpr :=
  Classical.choose (NaturalFunction.exists_expr f)

/-- The chosen representative evaluates to the given natural function. -/
theorem representative_spec (f : NaturalFunction) (n : PosNat) :
    f n = UnaryExpr.eval (representative f) n :=
  Classical.choose_spec (NaturalFunction.exists_expr f) n

/-- Re-embedding the chosen representative recovers the original extensional
natural function. -/
theorem ofExpr_representative (f : NaturalFunction) :
    NaturalFunction.ofExpr (representative f) = f := by
  apply NaturalFunction.ext
  intro n
  exact (representative_spec f n).symm

/-- If an expression denotes `f`, it is semantically equal to the chosen
representative of `f`. -/
theorem representative_semEq_of_eq {f : NaturalFunction} {e : UnaryExpr}
    (h : NaturalFunction.ofExpr e = f) :
    UnaryExpr.SemEq (representative f) e := by
  apply NaturalFunction.ofExpr_eq_iff.mp
  exact (ofExpr_representative f).trans h.symm

/-- Descend the expression-level raw normal form to extensional natural
functions by choosing a representative.  `raw_eq_of_semEq` proves below that
the result is independent of this choice. -/
noncomputable def semanticNF (C : FixedFamilyCertificate)
    (f : NaturalFunction) : MvPolynomial Nat Nat :=
  C.raw (representative f)

namespace FixedFamilyCertificate

/-- The semantic normal form agrees with the raw form of every expression,
not merely with the raw form of the chosen representative. -/
theorem semanticNF_ofExpr (C : FixedFamilyCertificate) (e : UnaryExpr) :
    semanticNF C (NaturalFunction.ofExpr e) = C.raw e := by
  apply C.raw_eq_of_semEq
  exact representative_semEq_of_eq rfl

/-- The normalization portion of the downstream package constructed from a
fixed-family expression certificate. -/
noncomputable def toNormalFormPackage (C : FixedFamilyCertificate) :
    NormalFormPackage where
  nf := semanticNF C
  nf_nonzero f := C.raw_nonzero (representative f)
  nf_one := by
    rw [← NaturalFunction.ofExpr_one, semanticNF_ofExpr, C.raw_one]
  nf_add f g := by
    rw [← ofExpr_representative f,
      ← ofExpr_representative g,
      ← NaturalFunction.ofExpr_add, semanticNF_ofExpr,
      semanticNF_ofExpr, semanticNF_ofExpr, C.raw_add]
  nf_mul f g := by
    rw [← ofExpr_representative f,
      ← ofExpr_representative g,
      ← NaturalFunction.ofExpr_mul, semanticNF_ofExpr,
      semanticNF_ofExpr, semanticNF_ofExpr, C.raw_mul]
  nf_tower := by
    intro t ht
    obtain ⟨e, heTower, heValue⟩ := exists_syntacticTower_of_isTower ht
    obtain ⟨m, hm_ne, hm⟩ := C.raw_tower heTower
    refine ⟨m, hm_ne, ?_⟩
    calc
      semanticNF C t = semanticNF C (NaturalFunction.ofExpr e) :=
        congrArg (semanticNF C) heValue.symm
      _ = C.raw e := semanticNF_ofExpr C e
      _ = MvPolynomial.monomial m 1 := hm

/-- Equality of semantic normal forms forces equality of extensional natural
functions. -/
theorem semanticNF_injective (C : FixedFamilyCertificate) :
    Function.Injective (semanticNF C) := by
  intro f g h
  have hsem :
      UnaryExpr.SemEq (representative f) (representative g) :=
    C.semEq_of_raw_eq h
  calc
    f = NaturalFunction.ofExpr (representative f) :=
      (ofExpr_representative f).symm
    _ = NaturalFunction.ofExpr (representative g) :=
      NaturalFunction.ofExpr_eq_iff.mpr hsem
    _ = g := ofExpr_representative g

/-- The full faithful downstream package constructed from a fixed-family
expression certificate. -/
noncomputable def toFaithfulNormalFormPackage (C : FixedFamilyCertificate) :
    FaithfulNormalFormPackage where
  toNormalFormPackage := C.toNormalFormPackage
  faithful := C.semanticNF_injective

end FixedFamilyCertificate

end

end NormalForm

end Natfunbasis
