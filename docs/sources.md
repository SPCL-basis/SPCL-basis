# Sources and exact scope

Last audited: 22 September 2026.

## Development environment

- OS: macOS 26.5.2 (Darwin 25.5.0, arm64).
- Lean: `4.32.2`, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- Lake: `5.0.0-src+f3b06c7`.
- elan: `4.2.4`.
- mathlib input revision: tag `v4.32.2`.
- mathlib resolved commit: `905b95818eb32af7874a58b427f50c1711a5e96c`.

The exact dependency graph is recorded by `lake-manifest.json`; the toolchain is
recorded by `lean-toolchain`.

## Alsulami--Jackson--Kinyon (AJK)

Tumadhir Alsulami, Marcel Jackson, and Michael Kinyon,
*Multiplicatively idempotent HSI algebras satisfy all equations of N*,
arXiv:2609.16922v1, 15 September 2026.

- Abstract page: <https://arxiv.org/abs/2609.16922v1>
- HTML: <https://arxiv.org/html/2609.16922v1>
- PDF: <https://arxiv.org/pdf/2609.16922v1>

The HTML and PDF were accessible during this audit. The following is the scope
that the Lean statements must preserve.

### Language and HSI (Section 1, HTML lines 63--69)

The original language is `L = {1, +, multiplication, binary exponentiation}`.
There is no zero constant. HSI consists of exactly eleven schemes:

1. commutativity and associativity of addition;
2. commutativity and associativity of multiplication;
3. left distributivity of multiplication over addition;
4. `x * 1 = x`;
5. `x^(y+z) = x^y * x^z`;
6. `(x*y)^z = x^z * y^z`;
7. `(x^y)^z = x^(y*z)`;
8. `1^x = 1`;
9. `x^1 = x`.

The count is eleven because the first three numbered groups contain five
separate semiring equations. The intended carrier `N` in this discussion is
the positive integers.

### Positive polynomials and the expanded language (Section 2, lines 114--125)

AJK uses integer-coefficient multivariate polynomials.

- "positive" means positive-valued on the strictly positive real orthant;
  negative coefficients are allowed;
- "strictly positive" means that every nonzero coefficient is a positive
  integer, so the polynomial is a term over `1,+,*`;
- `Irr_k` consists of positive polynomials irreducible over the integers,
  excluding `1` and individual variables;
- `M_k` consists of nonconstant coefficient-one monomials.

For every positive polynomial `rho` of arity `k`, `L*` adds a `k`-ary symbol
`t_rho` interpreted by polynomial evaluation. HSI* is HSI plus:

1. factorization identities identifying `t_rho` with a product of the symbols
   for positive irreducible factors whenever a strictly positive `rho`
   factors that way; and
2. translation identities `t_rho = rho` for strictly positive `rho`, where
   the right side is its ordinary `1,+,*` term.

This is the smaller HSI* used by AJK. It must not be replaced by Wilkie's
larger collection of all true exponentiation-free identities in `L*`.

The displayed formula at HTML line 124 suppresses operation arguments and
variable bookkeeping. Its formal transcription must make arities,
substitution, variable factors, units, and prime constant factors explicit.

### Theorem 2.2 (lines 126--130)

"The expanded set of laws HSI* is complete for the equational theory of
`<N,+,*,^,1>`." In formal scope: for every finite set of variables and every
pair of original-language terms, equality on all positive-integer assignments
implies HSI* derivability of their embeddings. Soundness is the converse.

### Admissible generators (lines 149--195)

For a fixed number `n` of original variables, the pairs `(p_i,q_i)` satisfy:

- W1.1: `p_(k+1)` is an admissible positive irreducible polynomial operation
  involving only original variables and earlier auxiliary variables, or one
  original variable;
- W1.2: `q_(k+1)` is a nonconstant coefficient-one monomial operation using
  only the permitted earlier variables;
- W1.3: distinct indices do not give the same base and exponent pair
  simultaneously on `N`;
- W2.1: every admissible irreducible-base/monomial-exponent pair is covered;
- W2.2: every original-variable/monomial-exponent pair is covered;
- W3.1: `tau_1 = p_1 ^ q_1`;
- W3.2: recursively substitute the earlier `tau` terms into `p_(i+1)` and
  `q_(i+1)`, then set `tau_(i+1) = u_(i+1) ^ s_(i+1)`.

Coverage is joint coverage of a base/exponent pair, not two unrelated
enumerations. The HTML rendering at lines 165--170 has a malformed brace in
one displayed `t_rho`; the surrounding prose determines the intended
application but the source TeX/PDF should be consulted when transcribing it.

### Lemma 2.6 (lines 197--230)

For every original-language term `f` in `n` variables, a recursive procedure
produces a strictly positive representing polynomial `rho_f` in the original
and finitely many auxiliary variables, and HSI* derives `f` equal to the
corresponding polynomial operation after substituting the `tau` generators.
AJK states that this expands Wilkie's Theorem 2.8 and checks that only HSI* is
used. Addition and multiplication map to polynomial addition and
multiplication; exponentiation uses exponent splitting, integer polynomial
factorization, generator coverage, and flattening `(x^y)^z = x^(yz)`.

### Independence and Theorem 2.7 (lines 231--240)

AJK attributes algebraic independence of the original variables and all
`tau_i` to Wilkie, Theorem 4.4. It invokes the proof of Wilkie, Theorem 1.9,
for the bridge from positive-integer semantic equality to equality of
representing polynomials. AJK Theorem 2.7 then says that two terms are equal
on positive integers iff they have the same representing polynomial.

No matching theorem for Wilkie's particular functions exists in the pinned
mathlib. The abstract predicate `AlgebraicIndependent` is infrastructure, not
this missing proof.

## Wilkie chapter

A. J. Wilkie, *On exponentiation---a solution to Tarski's High School Algebra
problem*, in *Connections between Model Theory and Algebraic and Analytic
Geometry*, Quaderni di Matematica 6, pp. 107--129; manuscript circulated in
1980. AJK gives the publication year as 2000, while the archived author
preprint and some catalogues use 2001 or 2002. Volume and page numbers are
stable, so this project does not assert a stronger date claim.

A primary author preprint was located and inspected through the
[Internet Archive capture of Wilkie's Oxford PostScript
file](https://web.archive.org/web/20010604065027id_/http://www.maths.ox.ac.uk:80/~wilkie/on-exp.ps).
It is a 15-page author preprint with SHA-256
`a66b2c612483eeab8a0c39342151ff0b1bd7cd60d4ded7fb8a64fa89d701d1f5`;
its title, author, and theorem numbering match AJK.

- Theorem 1.9: if original-language terms `f,g` agree on `N`, then Wilkie's
  larger theory EXP* derives `f=g`. Wilkie explicitly does not claim this for
  arbitrary expanded-language terms.
- Theorem 2.8: every original-language term has a strictly positive polynomial
  normal form in finitely many fixed `tau` generators, derivably in EXP*.
  Wilkie allows `m = 0`; AJK's `m in Z+` requires unstated dummy-variable
  padding in the base cases.
- Proposition 3.1(i): the logarithmic-derivative classification in a
  transcendental exponential adjunction. Its full rational-function form is
  formalized as `Proposition31.rationalFunction_proposition31_i`, and
  `WilkieRationalExtension` transports it to concrete simple extensions.
- Proposition 3.1(ii): the corresponding primitive transcendental-adjunction
  calculation. The pole/degree argument does prove that `X` belongs to the
  base field and `Y` is affine in the primitive with constant slope; this is
  formalized by `Proposition31II.rationalFunction_proposition31_ii_affine`
  and its simple-extension variants. The additional claim that the slope is
  an integer is false under the hypotheses printed before the proposition.
  A differential-rational-field counterexample is
  `K = C(b)`, `b' = b/2`, `G = K(t)`, `t' = 1`, with `beta = b^2` and
  `alpha = t`: then `alpha' = beta'/beta`, while `X = b` and
  `Y = alpha/2` satisfy `X' = Y' X` with nonintegral slope `1/2`.
  The Lean development therefore defines `IntegralSlopeRigidity beta` and
  proves the source-shaped integral conclusion only with that explicit extra
  premise. The `Real(x)` base classification is nevertheless proved
  unconditionally because its zero coefficient derivation and nonzero
  translation speed force the affine slope to vanish.
- Proposition 3.2: the two algebraic-extension descent clauses. Wilkie states
  them for differential rings `F ⊆ G`, with `F` a field and common constant
  field. `Proposition32.proposition32_i` and `proposition32_ii` formalize both
  clauses under the stronger assumption that `G` is a characteristic-zero
  differential field; this restriction reflects the field-based `minpoly`
  API used by the Lean proofs.
- Theorem 4.4: a simultaneous differential-algebraic induction whose relevant
  consequence is algebraic independence, over `R`, of the coordinate
  functions and the `tau_i` as real functions on the positive orthant. It is
  substantially stronger and more technical than merely applying mathlib's
  abstract `AlgebraicIndependent` predicate. The base pair `(x, log x)`, the
  derivative-closed finite-stage tower, exact generator-set descriptions,
  algebraic-independence successor bookkeeping, Proposition 3.2
  transcendence reductions, and the finite-to-infinite coordinate handoff are
  formalized. The remaining content is local but substantive: fresh-log
  nonmembership, exclusion of the nonzero integral-power relation for each
  new `tau`, and the simultaneous `IIᵢ` rigidity invariant needed to justify
  integral slopes. No unconditional positive-stage independence theorem or
  full simultaneous induction is claimed.

Wilkie explicitly cites Angus Macintyre, *The laws of exponentiation*, Lecture
Notes in Mathematics 890 (1981), 185--197,
<https://doi.org/10.1007/BFb0095664>, for the bridge saying that equality of
the relevant terms on all positive-integer assignments gives equality of their
functions on the positive real orthant. Only after that bridge does Wilkie
apply Theorem 4.4. AJK lines 231--235 compress this step. The Macintyre chapter
was not independently available during this audit, so this bridge remains a
separate blocked dependency; analyticity alone cannot replace it.

### Source defects requiring explicit resolution

- Wilkie Proposition 3.1(ii)'s printed hypotheses do not force its asserted
  integral affine slope; the differential-rational-field slope-`1/2`
  counterexample above satisfies the same-constants primitive-extension
  hypotheses. The formalization separates the valid affine conclusion from
  the additional `IntegralSlopeRigidity` needed for the integral form.
- AJK's official v1 TeX has `t_{rho(...)} ` in W2.1; Wilkie's condition 2.3
  confirms that `t_rho(...)` is intended.
- W2.2 suppresses the arguments of `t_mu`.
- The paragraph introducing W1/W2 omits W1.3 from its list even though W1.3 is
  displayed immediately afterward and is essential.
- AJK restricts two W2.1 indices to positive integers where Wilkie uses natural
  numbers including zero; equivalence would require explicit dummy variables.
- Lemma 2.6 Subcase 2.2 conflates literal equality with HSI*-derivable
  equality and contains a `rho_i`/`rho_j` index typo.
- "same representing polynomial" requires a fixed common enumeration,
  compatible variable embeddings, and a precise coefficient-level equality.

## Attached proof note

Local source:
`natural_power_atomicity_package1/natural_power_atomicity.pdf`, version 1.0,
18 September 2026. SHA-256:
`75c7f746ab9d00658e4c00272874928512f322992bf7ecf3bd9b5816ddd90fb1`.
The matching TeX source has SHA-256
`79b240ce9a91f3bd3d4e777e83cd9b467eba081dcda05e2038e71b33e06f1ae9`.

All seven PDF pages were rendered locally with macOS PDFKit/CoreGraphics and
visually inspected. The rendering is legible and complete. The mathematical
audit finds the elementary atomicity argument sound **conditional on** the
strong fixed-system normalization, generator coverage, and uniqueness facts.
The hard missing input remains Wilkie's independence theorem and the bridge
from equality on the positive-integer grid to polynomial uniqueness.

One formalization-sensitive compression occurs near TeX line 268: identifying
the newly constructed polynomial with `P_(U^V)` needs either a proof that it is
exactly the normalizer's output or injectivity for every polynomial in the
fixed generators, not merely uniqueness among already assigned expression
normal forms.

## Pinned mathlib matches

The following declarations were checked in the local `v4.32.2` checkout:

- positive naturals: `PNat`, notation `N+`, `PNat.pos`, `Nat.toPNat` in
  `Mathlib.Data.PNat.Basic`;
- multivariate polynomials: `MvPolynomial.constantCoeff`, `eval`, `eval₂`,
  `eval₂Hom`, and the evaluation lemmas in
  `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`;
- abstract algebraic independence: `AlgebraicIndependent`,
  `algebraicIndependent_iff_injective_aeval`, and
  `AlgebraicIndependent.eq_zero_of_aeval_eq_zero` in
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`;
- first-order terms: `Language.Term.var`, `.func`, `.subst`, `.relabel`, and
  `Term.realize_subst` in `Mathlib.ModelTheory.Syntax` and semantics imports.

Mathlib does not provide the required equational proof system or Wilkie's
specific independence theorem; this project defines the former explicitly.

## Related formalizations checked

Two public projects were inspected for a reusable verified replacement:

- Joseph Tassarotti's Coq project `jtassarotti/tarski-hsap`, commit
  `54c609d`, formalizes the Burris--Yeats finite countermodel and
  nonderivability of Wilkie's example. It does not contain the positive
  normalizer, W1--W3 construction, completeness, or algebraic-independence
  theorem needed here.
- `bsubercaseaux/HighSchoolAlgebraSAT`, commit `5c751649`, verifies a SAT
  encoding and the order-11 lower bound for finite HSI countermodels. It has
  no Wilkie normal form or independence result. The inspected commit also had
  no license file, so its source is not copied into this project.

Searches of the pinned mathlib/Archive trees and public Lean repositories found
no importable statement of AJK Lemma 2.6, AJK Theorem 2.7, Wilkie Theorem 4.4,
or the Macintyre bridge. This is a scoped search result, not a claim about
unpublished developments.
