# Paper-to-Lean map

Status terminology in this table is deliberately strict:

- **proved (unconditional)** means a kernel-checked theorem with no
  project-specific mathematical hypothesis;
- **proved (conditional)** means a kernel-checked implication whose statement
  still takes an explicit `NormalFormPackage` or
  `FaithfulNormalFormPackage` argument;
- **defined** means that the relevant syntax or predicate has been encoded,
  not that its intended non-elementary instances have been constructed;
- **not formalized** means that no Lean theorem for that source result is being
  claimed.

## Elementary syntax and semantics

| Paper/prompt item | Lean declaration or file | Status |
|---|---|---|
| Natural-expression grammar | `Natfunbasis.Expr` | defined |
| Positive constants by repeated `1` | `Natfunbasis.Expr.posConst` | defined |
| Positive evaluation | `Natfunbasis.Expr.eval_pos` | proved (unconditional) |
| Unary semantic equality | `Natfunbasis.UnaryExpr.SemEq` | defined |
| Expression-level additive atomicity | `Natfunbasis.UnaryExpr.AddAtomic` | defined |
| Expression-level nonconstancy | `Natfunbasis.UnaryExpr.Nonconstant` | defined |
| Semantic invariance | `UnaryExpr.addAtomic_congr`, `UnaryExpr.nonconstant_congr` | proved (unconditional) |
| Constant/nonconstant equivalence | `UnaryExpr.nonconstant_iff_not_semEq_posConst` | proved (unconditional) |
| Elementary product inheritance | `UnaryExpr.addAtomic_factors` | proved (unconditional) |
| Elementary positive-constant-power inheritance | `UnaryExpr.addAtomic_of_pow_posConst` | proved (unconditional) |

## Extensional natural functions and the candidate basis

| Paper/prompt item | Lean declaration or file | Status |
|---|---|---|
| Represented functions with extensional equality | `Natfunbasis.NaturalFunction` | defined |
| Expression/function equality correspondence | `NaturalFunction.ofExpr_eq_iff` | proved (unconditional) |
| Closure under `1`, addition, multiplication, and pointwise exponentiation | instances in `NaturalFunctions.lean` | proved/defined (unconditional) |
| Function-level additive atomicity and nonconstancy | `NaturalFunction.AddAtomic`, `NaturalFunction.Nonconstant` | defined |
| Transfer from expressions | `NaturalFunction.ofExpr_addAtomic_iff`, `NaturalFunction.ofExpr_nonconstant_iff` | proved (unconditional) |
| Nondegenerate towers | `Natfunbasis.IsTower` | defined |
| Candidate basis: finite products of towers, including the empty product `1` | `Natfunbasis.IsBasis` | defined |
| Intrinsically nonempty finite sums | `Natfunbasis.BasisSum` and `BasisSum.Valid` | defined |
| Addition and distributed multiplication of valid basis sums | `BasisSum.valid_append`, `BasisSum.valid_mul` | proved (unconditional) |
| Exponentiation construction for valid basis sums | `BasisSum.exists_pow` | proved (unconditional) |
| Every natural function is a nonempty finite sum of candidate basis elements | `Natfunbasis.exists_basisSum` | proved (unconditional) |
| Every additive atom belongs to the candidate basis | `Natfunbasis.isBasis_of_addAtomic` | proved (unconditional) |
| A non-one base to a nonconstant basis exponent is again a basis element | `BasisSum.basis_pow_of_nonconstant` | proved (unconditional) |

Generation and the direction “atom implies candidate basis element” are
elementary. The converse—every candidate is an atom—needs the missing
normal-form input described below.

## Polynomial infrastructure

| Paper/prompt item | Lean declaration or file | Status |
|---|---|---|
| Polynomial constant coefficient and its laws | `NormalPolynomial.constant` | proved (unconditional) |
| Polynomial weight and its laws | `NormalPolynomial.weight` | proved (unconditional) |
| Positivity of weight for a nonzero `Nat` polynomial | `NormalPolynomial.weight_pos` | proved (unconditional) |
| Weight-one obstruction to a two-summand decomposition | `NormalPolynomial.weight_one_forbids_add` | proved (unconditional) |
| Finite sum of coefficient-one monomials | `NormalPolynomial.monomialSum` | defined |
| Equality of such sums iff their exponent lists are permutations | `NormalPolynomial.monomialSum_eq_iff_perm` | proved (unconditional) |
| Abstract algebraic independence makes `aeval` injective | `AlgebraicIndependence.aeval_injective` | proved (unconditional) |
| The same after an injective coefficient map | `AlgebraicIndependence.mappedAeval_injective` | proved (unconditional) |
| Natural-coefficient specialization in characteristic zero | `AlgebraicIndependence.natAeval_injective`, `natAeval_eq_iff` | proved (unconditional) |

The algebraic-independence declarations are generic consequences of an
explicit `AlgebraicIndependent` hypothesis. They do **not** prove that
Wilkie's particular coordinate and auxiliary functions satisfy that
hypothesis.

## Unconditional normalizer and generator scaffolding

| Item | Lean declaration or file | Status |
|---|---|---|
| Raw polynomialization with every power as a temporary atom | `NormalizerCore.rawPolynomial` | defined |
| Exact evaluation and substitution laws for raw polynomialization | `NormalizerCore.eval_rawPolynomial`, `rawPolynomial_subst` | proved (unconditional) |
| Recursive normalization of `1`, variables, sums, products, and polynomially constant exponents | `NormalizerCore.normalize` and its constructor lemmas | proved (unconditional) |
| Correctness, nonzeroness, and soundness of equality of core normal forms | `NormalizerCore.eval_normalize`, `normalize_ne_zero`, `semEq_of_normalize_eq` | proved (unconditional) |
| Nonempty irreducible factorization over `Int`, with simultaneously positive associates whose product is exactly the original polynomial | `NormalizerCore.exists_exact_positive_irreducible_factorization` | proved (unconditional) |
| Original/auxiliary/admissible classification of every positive factor, with W2 coverage outside the auxiliary case | `Wilkie.exists_classified_positive_irreducible_factorization`, `PositiveIrreducibleFactor.auxiliary_or_existsUnique_w2` | proved (unconditional from a supplied sequence) |
| Finite-stage monomial transport/product and exact global presentation | `NonconstantMonomial.lift_toGlobal`, `NonconstantMonomial.product_toGlobal` | proved (unconditional) |
| Auxiliary-variable W3 flattening and complete finite factor-by-monomial power-grid evaluation | `PositiveIrreducibleFactor.exists_flattened_generator`, `exists_powerBranch_grid_identity` | proved (unconditional from a supplied sequence and realization) |
| Constant-plus-nonconstant-monomial decomposition of every finite-stage natural polynomial, with exact multiplicities and Int/Real evaluation | `StageNatPolynomial.eq_C_constantCoeff_add_monomialSum`, `evalInt_eq_constant_add_monomials`, `evalReal_eq_constant_add_monomials` | proved (unconditional) |
| Classified factor list conversion and arbitrary-polynomial semantic power branch | `exists_classified_positive_irreducible_factor_list`, `exists_arbitraryPolynomial_powerBranch_identity` | proved (unconditional from a supplied sequence and realization) |
| Index-preserving global-to-finite-stage transport | `Wilkie.toNatStage`, `rename_toNatStage`, `toNatStage_evalReal` | proved (unconditional) |
| Concrete canonical nonconstant-power step, including the literal tower monomial law | `ExpressionNormalizerAssembly.canonicalNonconstantPowerStep` | constructed (unconditional) |
| Recursive common-family raw normalizer and precertificate | `NormalForm.canonicalRaw`, `canonicalPrecertificate`, `canonicalRaw_represents_real` | constructed/proved (unconditional) |
| Finite exponent splitting, base-product distribution, grid expansion, flattening, and literal positive powers in HSI | `NormalizerCore.PowerDerivations` | proved (unconditional) |
| Typed one-variable W1.1--W3.2 conditions | `Natfunbasis.Wilkie` structures in `WilkieGenerators.lean` | defined |
| Combinatorial V0/V1/V2 fresh-base bookkeeping | `GeneratorSequence.freshBase_unique`, `constant_original_fresh_or_repeated` | proved (unconditional); classifies literal base-polynomial repetitions only and does not prove Wilkie 4.4 independence |
| Actual fixed paired enumeration and W3 realization | `canonicalGeneratorSequence`, `GeneratorSequence.canonicalRealization`, `canonicalGeneratorSystem` | proved/constructed (unconditional) |
| Positivity and uniqueness consequences of those conditions | `Base.positiveOnOrthant`, `GeneratorSequence.index_unique_of_joint_derivation`, `GeneratorRealization.tau_pos` | proved (unconditional from explicit data) |
| Discrete recursive W3 coordinates from any supplied sequence | `GeneratorSequence.integerTau`, `integerCoordinates` and positivity lemmas in `WilkieIntegerEvaluation.lean` | proved (unconditional from explicit data) |
| Agreement of any supplied real W3 realization with the integer recursion at positive integers | `GeneratorRealization.tau_integer_compat` and assignment/base/exponent compatibility lemmas | proved (unconditional from explicit data) |
| Named concrete real/integer coordinate families and their coordinatewise agreement | `canonicalRealCoordinates`, `canonicalIntegerCoordinates`, `canonicalCoordinates_integer_compat` | proved (unconditional) |
| Real independence plus an explicit integer-grid identity bridge imply discrete-coordinate independence | `Wilkie.integer_algebraicIndependent_of_real` | proved (conditional only on the two named source inputs) |
| Positive-axis analyticity of every original term and reduction of integer-to-real transfer | `UnaryExpr.evalReal_isPositiveAnalytic`, `originalTermIntegerToReal_of_finiteOrIdentical` | proved; the finite-zero/o-minimal premise remains explicit |
| Positive-axis analytic differential domain and fraction-field quotient rule | `PositiveAnalyticFunction.derivation`, `PositiveAnalyticFractionField.derivation_div_algebraMap` | constructed/proved (unconditional) |
| Exact real constant field of the analytic differential fraction field | `PositiveAnalyticFractionField.derivation_eq_zero_iff_mem_range_algebraMap_real` | proved (unconditional) |
| Analytic canonical generators and their positive-power differential equation | `GeneratorSequence.realTau_isPositiveAnalytic`, `mul_deriv_positiveRpowExtension`, `canonicalAnalyticCoordinates` | proved/constructed (unconditional) |
| Exact logarithm/power adjunction equations in the analytic domain and fraction field | `PositiveAnalyticFunction.mul_derivative_log`, `mul_derivative_rpow`, `PositiveAnalyticFractionField.derivation_log`, `derivation_rpow` | proved (unconditional) |
| Differential intermediate-field inclusion and inherited same constants | `DifferentialIntermediateField.deriv_inclusion`, `containConstantsOfLE` | proved (unconditional) |
| Wilkie Proposition 3.1(i), including the finite-prime, `X`-adic, and infinity/principal-polynomial steps | `Proposition31.rationalFunction_proposition31_i` | proved (unconditional), in exact rational-function coordinates |
| Wilkie Proposition 3.2(i), algebraic exponential descent | `Proposition32.proposition32_i` | proved (unconditional) for characteristic-zero differential field extensions with no new constants |
| Wilkie Proposition 3.2(ii), algebraic primitive descent | `Proposition32.proposition32_ii` | proved (unconditional) in the same field-extension scope; the source permits the ambient extension to be only a differential ring |
| Generator-specific logarithm and W3 differential equations in the analytic fraction field | `PositiveAnalyticFractionField.derivation_logBaseAnalytic`, `derivation_realTauAnalyticFunction` | proved (unconditional) |
| Substituted-base/exponent membership and fresh/repeated logarithm reduction | `GeneratorSequence.baseAnalytic_mem`, `exponentAnalytic_mem`, `logBaseAnalytic_mem_of_fresh_le` | proved (unconditional from a supplied generator sequence) |
| Initial field `F₀ = ℝ(x, log x)`, its constants, and base-pair independence | `OneVariableBaseField.F0_le_iff`, `F0_containConstants`, `x_logX_algebraicIndependent` | proved (unconditional) |
| Recursive differential stages, earlier-generator/fresh-log membership, and derivative closure | `GeneratorSequence.finiteStageField_mono_step`, `tau_mem_finiteStageField`, `freshLog_mem_finiteStageField`, `logBase_mem_finiteStageBeforeTau`, `deriv_mem_finiteStageField` | proved (unconditional from a supplied generator sequence); this is field-membership infrastructure, not Theorem 4.4 independence |

The temporary `Atom.power` normalizer remains a useful independent core. The
new `canonicalRaw` instead uses the one fixed Wilkie family and has the full
unconditional representation and tower-shape laws. Its canonicity direction
is obtained conditionally from the two source propositions listed below.

## Normal-form consequences

| Paper/prompt item | Lean declaration or file | Status |
|---|---|---|
| One-variable normalization/arithmetic interface | `NormalForm.NormalFormPackage` | defined; `canonicalNormalFormPackage` supplied conditionally on the two source premises |
| Additional faithful-normal-form interface | `NormalForm.FaithfulNormalFormPackage` | defined; `canonicalFaithfulNormalFormPackage` supplied on the same premises |
| Basis elements have coefficient-one monomial normal forms | `NormalForm.nf_basis` | proved (conditional) |
| Exponent-vector encoding of basis elements is injective | `NormalForm.basisExponent_injective` | proved (conditional) |
| Every candidate basis element is additively atomic | `NormalForm.addAtomic_of_basis` | proved (conditional) |
| Atoms are exactly finite products of nondegenerate towers | `NormalForm.addAtomic_iff_isBasis` | proved (conditional) |
| Valid additive expansions are unique, including multiplicity, up to permutation | `NormalForm.basisSum_terms_perm` | proved (conditional) |
| Every function has a basis expansion unique up to permutation | `NormalForm.exists_basisSum_unique` | proved (conditional) |
| If `g` is nonconstant and additively atomic, then `f ^ g` is additively atomic | `NormalForm.pow_addAtomic` | proved (conditional) |
| Same power theorem with no abstract package parameter | `NormalForm.canonical_pow_addAtomic` | proved conditional exactly on Macintyre transfer and canonical Wilkie independence |
| Existence and uniqueness with no abstract package parameter | `NormalForm.canonical_exists_basisSum_unique` | proved conditional exactly on the same two premises |
| Final theorems at the sharper finite-zero boundary | `canonical_pow_addAtomic_of_finiteOrIdentical`, `canonical_exists_basisSum_unique_of_finiteOrIdentical` | proved conditional exactly on `OriginalTermFiniteOrIdentical` and canonical Wilkie independence |

`NormalForm.FixedFamilyCertificate` now gives the precise expression-level
input from which both downstream packages are constructed. Its `canonical`
field asks only for invariance of raw forms under semantic equality of
original expressions. `FixedFamilyPrecertificate.ofAlgebraicIndependent`
shows that full independence of the discrete coordinate family is one
stronger sufficient input, while `toNormalFormPackage` and
`toFaithfulNormalFormPackage` perform the verified descent to extensional
functions. The precertificate's tower clause is deliberately syntactic;
`exists_syntacticTower_of_isTower` and certificate canonicity perform the
otherwise-invalid transport to an arbitrary extensional tower representative.
`canonicalPrecertificate` is an unconditional value.
`canonicalCertificate htransfer hindependent` is the concrete certificate
constructor, with its only premises visibly naming the Macintyre transfer and
Wilkie independence propositions.

The nonconstancy premise in the final row is essential. Without it, the
atomic constant exponent `g = 1` would make `f ^ g = f`, which need not be
atomic.

These structures are theorem parameters, not Lean `axiom`s, opaque proofs, or
typeclass instances. In the source-based construction, defining `nf` on the
*extensional* type `NaturalFunction` requires the
semantic-equality-to-polynomial-equality direction of the fixed-system theorem.
The converse direction is proved elementarily from pointwise representation
in `NormalFormConstruction`, which then supplies
`FaithfulNormalFormPackage.faithful`. Thus `pow_addAtomic` needs only
`NormalFormPackage`, whereas expansion uniqueness uses the extended interface.

## Exact source accounting and remaining gap

| Source item | Use in this project | Status |
|---|---|---|
| Eleven original HSI schemes | `Natfunbasis.HSIAxiom` | defined |
| Equational derivability and model soundness | `Natfunbasis.Derives`, `HSIDerives.sound`, `hsiDerives_semEq` | proved (unconditional) |
| AJK HSI* | not needed for the elementary modules; needed by AJK's chosen normalizer construction | not formalized |
| Fixed W1--W3 generator system | `canonicalGeneratorSystem` in `WilkieGeneratorExistence.lean` | constructed (unconditional) |
| AJK Lemma 2.6 / Wilkie Theorem 2.8 | supplies common-family natural-coefficient normal forms and the tower power case | the semantic normalizer needed here is formalized as `canonicalRaw`; the stronger expression-level HSI* derivation presentation is not pursued |
| Macintyre integer-to-real bridge | used before applying Wilkie's real-function independence result | reduced to `OriginalTermFiniteOrIdentical`; the finite-zero/o-minimal premise is not formalized |
| Wilkie Proposition 3.1(i) | classifies logarithmic-derivative solutions in a transcendental exponential extension | fully proved in rational-function coordinates by `Proposition31.rationalFunction_proposition31_i` |
| Wilkie Proposition 3.1(ii) | primitive transcendental-adjunction classification used for `II₀` and fresh-log steps | not formalized |
| Wilkie Proposition 3.2 | algebraic exponential and primitive descent | both clauses are proved for characteristic-zero differential **field** extensions; Wilkie's ambient `G` may be a differential ring, a genuine scope difference recorded explicitly |
| Wilkie Theorem 4.4 | supplies algebraic independence of the particular fixed auxiliary family | the independent base pair `(x, log x)`, Propositions 3.1(i)/3.2 in the scopes above, V0/V1/V2 bookkeeping, and recursive derivative-closed finite stages are proved; the simultaneous independence induction is not formalized |
| AJK Theorem 2.7 | its difficult semantic-equality-to-polynomial-equality direction is needed to make `nf` well defined; the converse follows in Lean from pointwise representation | reduced in Lean to the two explicit source premises; concrete conditional certificate and descent formalized |
| AJK Theorem 2.2 (full HSI* completeness) | not used by either requested target | intentionally not pursued |

The project contains a concrete constructor for `FixedFamilyCertificate` and
both downstream packages from the two displayed source premises. It does not
claim either requested final result unconditionally until those premises are
formalized.

## Relation to the attached power-atomicity note

| Attached-note item | Lean treatment | Status |
|---|---|---|
| Lemma 2.2, weight-one argument | polynomial core `NormalPolynomial.weight_one_forbids_add`; its use on natural functions occurs in `NormalForm.addAtomic_of_basis` | unconditional core; conditional application |
| Lemma 3.1, power factorization | not used by the shorter implemented proof | not formalized |
| Lemma 4.2, atomic-exponent induction | not used by the shorter implemented proof | not formalized |
| Theorem 5.1, power atomicity | `NormalForm.pow_addAtomic`, proved through the basis characterization and with the necessary nonconstancy premise | proved conditional on the normalization-only `NormalFormPackage` |

This is an independent Lean proof organization, not a transcription of the
note's Lemma 3.1--Lemma 4.2 chain.

## Audit policy

Before advertising either target as unconditional, run both `#print` and
`#print axioms` on the final theorem, inspect every theorem parameter and
imported declaration, and search the entire project for `sorry`, `admit`,
`sorryAx`, unsafe proof escapes, and project-specific declarations made with
the Lean `axiom` or `opaque` commands. An empty or noncustom axiom list alone
does not eliminate hidden theorem parameters; in particular, the printed type
must not contain either package once the final result is claimed.

`Natfunbasis/Audit.lean` currently prints and audits both the strongest
unconditional declarations and the explicitly conditional downstream
theorems. The latter are included to expose their parameter, not to label
them unconditional.
