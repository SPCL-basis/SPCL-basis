# Dependency graph and proof obligations

Status keys: **proved** means kernel-checked in this project; **source** means
checked against an accessible primary source but not formalized; **blocked**
means a mathematical dependency is not yet available in Lean; **false** marks
a printed claim refuted under its stated hypotheses, not a pending proof.

## Out of scope: full HSI* completeness

```text
original expression syntax and semantics                         [proved]
        |
eleven HSI schemes + derivability + generic soundness            [proved]
        |
positive integer polynomials and expanded L* syntax              [not started]
        |
exact HSI* factorization/translation schemes + soundness         [not started]
        |
W1--W3 predicates and consequences                              [proved/defined]
actual admissible generator system                              [proved]
V0/V1/V2 fresh-base classification and uniqueness               [proved; combinatorial]
        |
semantic common-family normalization needed here                 [proved]
full expression-level HSI* derivation form                       [not pursued]
        |
original-term analyticity + reduction to finite-zero alternative [proved]
finite-zero/o-minimal alternative                                [blocked]
real-constant analytic differential fraction field               [proved]
canonical generator analyticity + differential equations         [proved]
analytic log/rpow adjunction equations in domain and field        [proved]
differential intermediate fields + same constants                 [proved]
Wilkie Proposition 3.1(i) + simple-extension transport             [proved]
Proposition 3.1(ii), valid affine primitive classification         [proved]
printed integral slope without added rigidity                      [false]
stage-specific IntegralSlopeRigidity / II_i invariant              [blocked]
Wilkie Proposition 3.2(i),(ii), differential-field scope          [proved]
generator-specific log-base and W3 field equations               [proved]
base/exponent/log membership relations                            [proved]
F0 = R(x,log x), exact constants, pair independence               [proved]
recursive derivative-closed finite-stage fields                   [proved]
Real(x) logarithmic-derivative seed classification                [proved]
stage-generator field identities + independence successor rule    [proved]
fresh-log nonmembership + exclusion of tau power relations        [blocked]
finite-stage to full-coordinate independence handoff              [proved]
Wilkie 4.4 algebraic independence                                [blocked]
        |
representing-polynomial uniqueness (AJK Theorem 2.7)             [blocked]
        |
HSI* completeness (AJK Theorem 2.2)                              [blocked]
```

Full HSI* completeness is not required for the requested additive basis or
power-atomicity theorems. The existing HSI syntax and soundness module is
retained, but the project will not formalize AJK Theorem 2.2 merely as an
indirect route to the two goals.

The Proposition 3.2 nodes use a deliberately narrower Lean scope than the
source: Wilkie permits a differential-ring ambient extension `G`, whereas
`proposition32_i` and `proposition32_ii` assume a characteristic-zero
differential field extension. The proofs use Mathlib's field-based minimal
polynomial and divisibility APIs; no ring-general version is claimed.

The Proposition 3.1(ii) node is deliberately split. Its pole/degree argument
and affine classification are proved. Its printed integral-slope conclusion
is not a consequence of the printed same-constants hypotheses: in
`K = C(b)`, `b' = b/2`, `G = K(t)`, `t' = 1`, with `beta = b^2` and
`alpha = t`, the solution `X = b`, `Y = alpha/2` has slope `1/2`.
`WilkieProposition31II` therefore packages the missing extra content as
`IntegralSlopeRigidity beta` and proves the source-shaped result conditionally
on that property. The needed stage-specific instances are part of the still
blocked simultaneous `IIᵢ` induction, not an omitted routine lemma.

## Required targets: additive basis, uniqueness, and power atomicity

```text
extensional natural functions                                      [proved]
        |
towers + finite tower products                                     [proved]
        |
elementary nonempty additive generation                            [proved]

W1--W3 predicates + unconditional normalizer core                  [proved]
actual fixed paired generator sequence + canonical W3 realization [proved]
V0/V1/V2 fresh-base classification and uniqueness                  [proved; combinatorial]
integer factorization + global positive-associate sign choice      [proved]
positive-factor classification + non-auxiliary W2 coverage        [proved]
W3 auxiliary flattening + finite power-grid evaluation identity   [proved]
arbitrary exponent reification + semantic polynomial power branch [proved]
integer-coordinate recursion from any supplied sequence            [proved]
real/integer W3 compatibility from any supplied realization         [proved]
concrete canonical coordinate families and integer compatibility    [proved]
index-preserving global transport + concrete power step             [proved]
recursive canonical raw normalizer + precertificate                 [proved]
original-term analyticity + finite-zero transfer reduction          [proved]
finite-zero/o-minimal alternative                                   [blocked]
analytic differential fraction field + exact real constants         [proved]
canonical generator analyticity + differential equations            [proved]
analytic log/rpow adjunction equations in domain and field           [proved]
differential intermediate fields + same constants                    [proved]
Wilkie Proposition 3.1(i) + simple-extension transport                [proved]
Proposition 3.1(ii), valid affine primitive classification            [proved]
printed integral slope without added rigidity                         [false]
stage-specific IntegralSlopeRigidity / II_i invariant                 [blocked]
Wilkie Proposition 3.2(i),(ii), differential-field scope             [proved]
generator-specific log-base and W3 field equations                  [proved]
base/exponent/log membership relations                               [proved]
F0 = R(x,log x), exact constants, pair independence                  [proved]
recursive derivative-closed finite-stage fields                      [proved]
Real(x) logarithmic-derivative seed classification                   [proved]
stage-generator field identities + independence successor rule       [proved]
fresh-log nonmembership + exclusion of tau power relations           [blocked]
finite-stage to full-coordinate independence handoff                 [proved]
Wilkie 4.4 algebraic independence                                   [blocked]
        |
restricted original-term canonicity handoff                        [proved conditionally]
optional stronger real-to-discrete independence handoff            [proved conditionally]
        |
canonical FixedFamilyCertificate                                  [constructed conditionally]
        |
verified descent to an extensional polynomial map + faithfulness   [proved conditionally]
        |
canonical values of both normal-form packages                      [constructed conditionally]
        |
        +--> coefficient-one normal forms for basis elements       [proved conditionally]
        +--> basis elements are atomic                             [proved conditionally]
        +--> atoms are exactly basis elements                      [proved conditionally]
        +--> nonconstant atomic g implies f^g atomic               [proved conditionally]
        +--> expansion uniqueness by coefficient comparison        [proved conditionally]
        +--> existence-and-uniqueness basis theorem                 [proved conditionally]
```

The final conditional theorems no longer take an abstract normal-form package.
`canonical_pow_addAtomic` and `canonical_exists_basisSum_unique` take exactly
`OriginalTermIntegerToReal` and `CanonicalWilkieIndependence`. This is useful
verified factorization of the proof, not an unconditional result and not a
hidden axiom. Their `_of_finiteOrIdentical` corollaries replace the transfer
premise by `OriginalTermFiniteOrIdentical`, making the o-minimal boundary
literal. Finishing the goal means formalizing that finite-zero proposition and
Wilkie independence.

## Attached proof audit

The proof note's Sections 2--5 are mathematically coherent under its stated
Theorem 2.1 normal-form input. Formalization must make these hidden transports
explicit:

- all compared terms use one common fixed generator system;
- semantic equality transports atomicity/nonconstancy and normal forms;
- a semantically constant exponent is replaced by a positive numeral term;
- W2 coverage selects a joint base/exponent generator up to HSI* derivability;
- auxiliary-variable bases are flattened through their earlier W3 definition;
- the constructed power polynomial is identified with the canonical normal
  form by a sufficiently strong injectivity/normalizer theorem.

The proof does not improperly treat auxiliary positive polynomials as natural
expressions, and the induction in Lemma 4.2 is noncircular.

## Remaining obligations

1. Prove the finite-zero/o-minimal alternative
   `OriginalTermFiniteOrIdentical`; its implication to the required
   integer-to-positive-real bridge is already formalized.
2. Prove the stage-specific `IntegralSlopeRigidity`/`IIᵢ` invariant. The
   unconditional affine part of Proposition 3.1(ii) is formalized, but the
   printed integral-slope conclusion is false from the printed hypotheses
   alone, as witnessed by the slope-`1/2` differential-rational-field
   counterexample recorded in the source audit.
3. Complete the local induction steps of Wilkie Theorem 4.4: prove each fresh
   logarithm is not in the preceding stage and exclude the nonzero
   integral-power relation produced if a new `tau` is algebraic. The exact
   stage-field descriptions, independence successor rule, Proposition 3.2
   reductions, and finite-to-infinite handoff are already formalized, so these
   local transcendence/rigidity inputs are the remaining independence gap.
4. Apply those results to the already constructed
   `canonicalCertificate`, hence discharge the only premises of the
   conditional final theorems.

Here “well-defined” is substantive: `NormalFormPackage.nf` has domain
`NaturalFunction`, whose equality is extensional equality on positive natural
inputs. Defining it therefore uses the direction from semantic equality to
equality of representing polynomials. Once the raw polynomials represent their
expressions pointwise, the converse direction and hence the separate
`FaithfulNormalFormPackage.faithful` field are already derived in
`NormalFormConstruction`. The required canonical raw polynomial and its
representation theorem are now constructed; only the two named source inputs
remain for the canonicity direction.
