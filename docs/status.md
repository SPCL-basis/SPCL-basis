# Formalization status

## Update, 24 September 2026: the main theorems hold with no premises

`Natfunbasis/MainTheorems.lean` proves, with no hypotheses and depending only on
`propext`, `Classical.choice` and `Quot.sound`:

- `Main.pow_addAtomic`: `f ^ g` is `+`-atomic for every natural `f` and every
  nonconstant `+`-atomic natural `g`.
- `Main.pow_input_addAtomic`: `n ↦ f(n) ^ n` is `+`-atomic.
- `Main.addAtomic_iff_isBasis`: the atoms are exactly the finite products of
  towers.
- `Main.exists_basisSum_unique`: the additive basis theorem.

The two premises listed below as blocked are now proved:

- `Wilkie.originalTermIntegerToReal` (`OriginalTermHardyTransfer.lean`). Every
  original term germ lies in a differential field of analytic germs built by
  primitive and exponential adjunctions. The existing Richardson descent makes
  such fields satisfy the Hardy dichotomy, and analyticity finishes the proof.
- `Wilkie.canonicalWilkieIndependence` (`WilkieFreshStageClosure.lean`,
  `WilkieRealDescent.lean`, `WilkieExpDarboux.lean`, `WilkieNonTangency.lean`).
  Fresh-stage integral-slope rigidity is proved stage-locally:
  - the denominators of the generator derivatives are `x·∏ uᵢ`;
  - the real image of a fresh base is squarefree and coprime to them (descent
    from ℤ to ℝ by per-variable Bézout);
  - an exponential Darboux argument at its top variable shows it is not
    tangent;
  - the existing residue reduction then gives integral slopes.
  The finite-stage induction is closed without the former global premise.

The text below is the status before this update.

Last updated: 22 September 2026.

## Completed and compiled

- Reproducible Lean 4.32.2/mathlib v4.32.2 project with a resolved manifest.
- Original expression language with exactly `one`, variable, addition,
  multiplication, and binary exponentiation.
- Positive-assignment semantics and positivity of every evaluation.
- Positive numeral expressions built by repeated addition of `one`.
- Unary semantic equality, additive atomicity, and nonconstancy.
- Invariance of atomicity and nonconstancy under semantic equality.
- Equivalence between nonconstancy and failure to equal a positive constant.
- Regression results:
  - `one` is atomic;
  - the variable is nonconstant and atomic;
  - `n + 1` is not atomic;
  - `(n + 1)^1` is not atomic;
  - every `1^g` is atomic, so the base `f = 1` is allowed.
- Elementary inheritance:
  - atomicity of `A*B` implies atomicity of both factors;
  - atomicity of a positive constant power implies atomicity of its base.
- Exactly eleven original HSI axiom schemes.
- Equational derivability with reflexivity, symmetry, transitivity,
  substitution, and congruence.
- Soundness of HSI derivations in every algebra satisfying the eleven schemes,
  plus positive-natural semantic soundness.
- Standalone multivariate-polynomial invariants `constant` and `weight`, their
  additive/multiplicative laws, positivity of weight for nonzero `Nat`
  polynomials, and the polynomial-level weight-one obstruction to a nonzero
  two-summand decomposition. These are not yet attached to expression normal
  forms.
- Extensional `NaturalFunction`s: represented positive-natural functions with
  semantic equality built into the type, closed under `1`, addition,
  multiplication, and exponentiation.
- Semantic additive atomicity and nonconstancy, with equivalence to the
  original expression-level definitions.
- Nondegenerate towers and candidate basis elements as finite tower products.
- A nonempty `BasisSum` representation with verified closure under addition,
  distributed multiplication, and the exponentiation construction.
- Unconditional additive generation: `exists_basisSum` proves that every
  natural function is a nonempty finite sum of candidate basis elements.
- The elementary half of the characterization:
  `isBasis_of_addAtomic` proves that every additive atom is a candidate basis
  element, and `basis_pow_of_nonconstant` proves the closure step used for
  natural powers.
- Coefficient comparison: finite sums of coefficient-one monomials are equal
  exactly when their exponent-vector lists are permutations.
- The generic algebraic consequence of algebraic independence: multivariate
  polynomial evaluation is injective, including after casting natural
  coefficients into a characteristic-zero ring.
- An unconditional core normalizer that treats unresolved powers as temporary
  atoms, with exact evaluation/substitution laws, full handling of constant
  exponents, and kernel-checked HSI derivations for the finite splitting,
  distribution, grid, and flattening steps used in the real power branch.
- The algebraic factorization substep: every nonzero, non-one
  natural-coefficient multivariate polynomial embeds into `Int` as a nonunit
  and has a nonempty exact product factorization into irreducibles; signs can
  be chosen simultaneously so every factor is positive on the real orthant
  while the product remains exactly the original polynomial.
- Every resulting positive irreducible is classified as the original
  variable, an earlier auxiliary variable, or an admissible W1 base. The
  non-auxiliary cases have unique joint W2 witnesses. Auxiliary-variable
  factors are now flattened through their earlier W3 definitions, and the
  resulting factor-by-monomial witnesses are assembled into a complete finite
  power-grid evaluation identity.
- Every finite-stage natural exponent polynomial is reified exactly as its
  constant coefficient plus a finite list of coefficient-one nonconstant
  monomials, with coefficient multiplicity and both integer and real
  evaluation identities verified. The classified factor multiset is converted
  to a nonempty product-preserving list, yielding an arbitrary-polynomial
  semantic power-branch theorem.
- Every countable-coordinate natural polynomial is transported to an
  index-preserving initial finite stage. The arbitrary-polynomial power branch
  is reified as the concrete `canonicalNonconstantPowerStep`, including the
  exceptional bases `0` and `1` and the literal coefficient-one monomial law
  required for towers.
- The recursive common-family normalizer `canonicalRaw` and its
  `canonicalPrecertificate` are constructed unconditionally, with exact real
  and positive-integer representation theorems.
- A typed transcription of the one-variable W1.1--W3.2 generator conditions,
  including joint paired coverage, only-earlier-variable dependence,
  positivity, and uniqueness of a jointly covered index.
- The V0/V1/V2 base bookkeeping is formalized for every generator sequence:
  each base is constant, original, fresh, or repeats a unique earlier fresh
  base. This is a combinatorial classification using literal polynomial
  equality; it supplies no algebraic-independence conclusion.
- A concrete fixed generator sequence with literal polynomial-equality
  coverage. Its countable enumeration is delayed past every dependency stage,
  has no semantically repeated pair, and covers every admissible joint
  base/exponent pair. Every sequence also has a canonical well-founded real
  W3 realization; together these give `canonicalGeneratorSystem`.
- From any supplied triangular sequence, an unconditional course-of-values
  construction of its integer-valued auxiliary functions and the common
  coordinate family, with positivity and exact recursion equations. Any
  supplied real W3 realization is proved to agree with that recursion at
  positive integer inputs.
- Named concrete real and integer coordinate families for
  `canonicalGeneratorSystem`, with coordinatewise equality after casting at
  every positive integer input.
- The exact source handoff: an explicit integer-grid identity bridge together
  with algebraic independence of the real coordinate functions implies
  algebraic independence of the integer-valued coordinate family.
- Every original unary term is positive-axis analytic. The exact implication
  `OriginalTermFiniteOrIdentical → OriginalTermIntegerToReal` reduces the
  Macintyre handoff to the remaining finite-zero/o-minimal input.
- Positive-axis analytic functions form an integral domain with ordinary
  differentiation. Differentiation extends to its fraction field with the
  quotient rule, and the constants of that differential field are proved to
  be exactly the embedded real numbers.
- Every recursively defined W3 generator, and hence every canonical real
  coordinate, is positive-axis analytic. The exact logarithmic-derivative and
  denominator-free differential equations for positive real powers are
  kernel checked.
- Logarithm and positive real power are bundled in the analytic domain. Their
  exact adjunction equations are proved both without denominators
  (`mul_derivative_log`, `mul_derivative_rpow`) and in the fraction field
  (`derivation_log`, `derivation_rpow`).
- Differential intermediate fields are packaged inside a common ambient
  differential field. Their inclusions commute with derivation, and nested
  fields inherit the same-constants property from the ambient exact-constant
  theorem.
- Wilkie Proposition 3.1(i) is proved in exact rational-function coordinates.
  The development includes the rational eigenfunction core, exact orders at
  finite primes, elimination of an `X`-power denominator, the
  infinity/principal-polynomial argument, and the zero-primitive case. The
  final theorem is `Proposition31.rationalFunction_proposition31_i`.
  `WilkieRationalExtension` transports it to concrete transcendental simple
  extensions and simple intermediate fields.
- For a primitive adjunction, the full pole and degree calculation proves
  that `X` descends to the base field and `Y` is affine in the primitive with
  constant slope (`rationalFunction_proposition31_ii_affine`). The integral
  slope asserted in the printed Proposition 3.1(ii) does not follow from its
  printed same-constants hypotheses: the differential rational-field example
  `K = C(b)`, `b' = b/2`, `G = K(t)`, `t' = 1`, `beta = b^2`,
  `alpha = t`, `X = b`, `Y = alpha/2` has slope `1/2`. The source-shaped
  conclusion is therefore proved only from the explicit additional predicate
  `IntegralSlopeRigidity beta`.
- The zero-derivation specialization gives the complete base classification
  in `Real(x)`, including the concrete analytic theorem
  `BaseRationalClassification.analyticX_simpleAdjoin_classification`.
- Both clauses of Wilkie Proposition 3.2 are proved for characteristic-zero
  differential field extensions with no new constants. The source permits
  the ambient extension to be a differential ring; the formal statements use
  a field because the minimal-polynomial divisibility infrastructure used by
  the proof is field-based.
- The generic analytic adjunction equations are specialized to each canonical
  generator base and W3 function as `derivation_logBaseAnalytic` and
  `derivation_realTauAnalyticFunction`.
- Substituted bases and exponents are proved to belong to every differential
  intermediate field containing the input and the required earlier
  generators. Constant, original, fresh, and repeated base logarithms are
  handled uniformly by `logBaseAnalytic_mem_of_fresh_le`.
- The initial differential field `F₀ = ℝ(x, log x)` is constructed inside the
  analytic fraction field. It is the least differential intermediate field
  containing `x` and `log x`, has exactly the real constants, and the pair
  `(x, log x)` is algebraically independent over `ℝ`.
- Recursive finite-stage differential fields are constructed from `F₀`.
  At stage `k` the logarithm of the base is adjoined exactly when that base is
  fresh, followed by the W3 generator `tau_k`. Every stage is derivative
  closed and contains `x`, `log x`, all earlier generators, and every earlier
  fresh-base logarithm.
- The recursive stage generator sets are defined explicitly, and the
  underlying intermediate fields of the completed and pre-`tau` stages are
  proved equal to the corresponding fields adjoined over `Real`. The base set
  is algebraically independent, and a clean successor theorem reduces stage
  independence exactly to fresh-log transcendence (only when fresh) and
  current-`tau` transcendence.
- Proposition 3.2 now supplies the precise local reductions used in the
  induction: fresh-log nonmembership implies its transcendence, while
  algebraicity of `tau_n` forces a nonzero integral-power relation over the
  pre-`tau` stage.
- Independence of every finite stage is proved sufficient for independence
  of the increasing union and the full coordinate family. The canonical
  specialization `canonicalWilkieIndependence_of_transcendence` shows that the
  two families of local transcendence statements imply the exact
  `CanonicalWilkieIndependence` required downstream.
- `FixedFamilyPrecertificate` / `FixedFamilyCertificate`, plus checked descent
  theorems constructing both downstream packages from a common-family raw
  normalizer and exactly the needed semantic canonicity statement. Full
  discrete-coordinate algebraic independence is separately proved to be a
  stronger sufficient input. The raw tower obligation is syntactic before
  canonicity; every extensional tower has such a representative, and the
  certificate performs the semantic transport afterward.
- `canonicalCertificate`, `canonicalNormalFormPackage`, and
  `canonicalFaithfulNormalFormPackage` now instantiate that descent with
  exactly two explicit premises: `OriginalTermIntegerToReal` and
  `CanonicalWilkieIndependence`. The corresponding conditional final theorems
  are `canonical_pow_addAtomic` and `canonical_exists_basisSum_unique`; their
  `_of_finiteOrIdentical` corollaries replace the first premise by the exact
  finite-zero/o-minimal alternative.
- Explicit `NormalFormPackage` and `FaithfulNormalFormPackage` interfaces,
  with no global instance or axiom. From a supplied normalization package,
  Lean proves:
  - every candidate basis element is atomic;
  - `AddAtomic f ↔ IsBasis f`;
  - `f ^ g` is atomic when `g` is nonconstant and atomic.
  From the faithful extension it additionally proves that valid expansions
  are unique up to permutation, including multiplicity, and packages
  existence plus uniqueness in `exists_basisSum_unique`.

## Source-audited but not formalized

- AJK's definition of `L*` and the smaller HSI*.
- The expression-level HSI* derivation formulation of AJK Lemma 2.6 and full
  HSI* completeness. The semantic common-family normalizer needed for the two
  requested goals is now formalized.
- The two source results used in AJK Theorem 2.7's difficult canonicity
  direction remain represented by the explicit premises below.

AJK Theorem 2.2 is intentionally outside the required dependency chain: the
two requested results need Lemma 2.6 and Theorem 2.7, not full HSI*
completeness.

## Blocked / unresolved mathematical dependencies

- The finite-zero/o-minimal theorem represented by
  `OriginalTermFiniteOrIdentical`; its checked consequence is the exact
  integer-to-positive-real transfer used by the normalizer.
- The stage-specific `IntegralSlopeRigidity`/`IIᵢ` invariant needed to recover
  integral slopes in primitive adjunctions. The printed Proposition 3.1(ii)
  cannot supply this unconditionally because of the explicit slope-`1/2`
  counterexample above; the valid affine classification and the conditional
  integral form are already formalized.
- Wilkie Theorem 4.4's remaining algebraic-independence induction. The
  underlying analytic differential fraction field, its exact real constant
  field, Propositions 3.1(i) and 3.2 in their stated field-extension scope,
  the algebraically independent base pair, recursive finite-stage fields,
  generator differential equations, combinatorial V0/V1/V2 fresh-base
  bookkeeping, exact stage-generator fields, independence successor rule,
  and finite-to-infinite handoff are already formalized. What remains is the
  stage-specific proof that every fresh logarithm is outside the preceding
  field and that every new `tau` is transcendental (equivalently, excluding
  the integral-power relation isolated by Proposition 3.2), together with the
  simultaneous `IIᵢ` rigidity invariant. Once those local inputs are proved,
  no further infinite-family argument is missing.

These remaining items are not represented by `axiom`, `sorry`, or opaque
assumptions. The canonical certificate and package constructors take their
consequences as ordinary explicit theorem parameters; this exposes the exact
remaining boundary without claiming either premise has been proved.

## Verification commands

Focused commands used during development:

```sh
lake env lean Natfunbasis/Expressions.lean
lake env lean Natfunbasis/Equational.lean
lake env lean Natfunbasis/TowerBasis.lean
lake env lean Natfunbasis/NormalFormConsequences.lean
lake env lean Natfunbasis/GlobalPowerNormalizer.lean
lake env lean Natfunbasis/CanonicalNormalizer.lean
lake env lean Natfunbasis/OriginalTermAnalyticity.lean
lake env lean Natfunbasis/WilkieFractionConstants.lean
lake env lean Natfunbasis/WilkieGeneratorAnalyticity.lean
lake env lean Natfunbasis/WilkieFreshBases.lean
lake env lean Natfunbasis/WilkieDifferentialIntermediateField.lean
lake env lean Natfunbasis/WilkieProposition31.lean
lake env lean Natfunbasis/WilkieProposition31Full.lean
lake env lean Natfunbasis/WilkieRationalExtension.lean
lake env lean Natfunbasis/WilkieProposition31II.lean
lake env lean Natfunbasis/WilkieProposition32.lean
lake env lean Natfunbasis/WilkieGeneratorDifferentialEquations.lean
lake env lean Natfunbasis/WilkieOneVariableBaseField.lean
lake env lean Natfunbasis/WilkieOneVariableBaseIndependence.lean
lake env lean Natfunbasis/WilkieGeneratorFieldRelations.lean
lake env lean Natfunbasis/WilkieFiniteStageFields.lean
lake env lean Natfunbasis/WilkieBaseRationalClassification.lean
lake env lean Natfunbasis/WilkieStageAlgebraicIndependence.lean
lake env lean Natfunbasis/WilkieStageTranscendenceReductions.lean
lake env lean Natfunbasis/WilkieInfiniteIndependence.lean
```

Final verification for this milestone:

```sh
lake build
rg -n '\b(sorry|admit|sorryAx)\b|^[[:space:]]*(axiom|opaque|unsafe)[[:space:]]' \
  Natfunbasis --glob '*.lean'
```

The anchored declaration scan distinguishes the encoded HSI axiom *syntax*,
comments, and `#print axioms` commands from Lean declarations made with the
`axiom`, `opaque`, or `unsafe` commands.

`Natfunbasis/Audit.lean` completed successfully. The inspected foundational
theorems report only ordinary Lean/mathlib foundations: `propext`, and for the
noncomputable finite-support polynomial proof also `Classical.choice` and
`Quot.sound`. No project-specific mathematical axiom appears.

## Honest completion boundary

The candidate basis, additive generation, and all downstream consequences of
the explicit normal-form packages are verified. No unconditional theorem yet
constructs those packages. Consequently a successful build does not verify
Wilkie normal-form canonicity or the requested unconditional basis and
power-atomicity theorems.
