/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Verso
import VersoManual
import VersoBlueprint
import CAS
import CAS.Polynomial.RealRoot.Automatic
import CAS.Polynomial.RealRoot.AutomaticGlobal
import CAS.Polynomial.RealRoot.ClosedForm

/-!
## Verified exact symbolic computation

The exact symbolic language, its semantics, and its checked CAS.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"

-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false
-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Verified Exact Symbolic Computation" =>

An exact residual proof often ends with a cancellation. To establish
$`A(x)/B(x)=C(x)` on a domain $`\Omega`, we can normalize
$`A(x)-B(x)C(x)` to zero and prove that $`B(x)\ne0` throughout
$`\Omega`. Polynomial arithmetic can settle the first question; a sign,
interval, or root-exclusion argument can settle the second. The domain
determines where we may use the resulting equality.

The normalization and polynomial-root certificates of the exact core cover
conditional cancellation, real powers and exponentials, exact polynomial
division, and Sturm chains. The calculus bridges use such identities to
justify derivatives and antiderivatives.

:::group "symbolic.exact"
Exact symbolic computation
:::

:::definition "symbolic.expression" (parent := "symbolic.exact") (lean := "CAS.Verified.Expr")
The core expression type is an inductive syntax tree indexed by its variable
type. It contains rational constants, arithmetic operations, natural powers,
real powers with an arbitrary real exponent (Mathlib's `Real.rpow`),
trigonometric functions, exponential and logarithmic functions, square roots,
and the inverse tangent, sine, and cosine. Evaluation uses Lean's total
real functions. A separate validity predicate records sufficient conditions
for their analytic rules: a nonzero denominator or logarithm argument, a
positive square-root argument or power base, and an inverse sine or cosine
argument different from $`\pm1`. These conditions are needed by the
calculus bridges; an equality about total values need not require them.

Schematically, the reflected language and its semantics are

$$`e ::= q\mid x_i\mid \pi\mid \mathrm e
  \mid -e\mid e_1\mathbin\circ e_2\mid e^n\mid e_1^{\,e_2}
  \mid \sin e\mid\cos e\mid\arctan e\mid\arcsin e\mid\arccos e
  \mid\exp e\mid\log e\mid\sqrt e,
\qquad
\operatorname{eval}: \operatorname{Expr}(\iota)\to(\iota\to\mathbb R)\to\mathbb R.`

Here $`\circ\in\{+,-,\times,/\}`, the exponent $`n` of $`e^n` is a natural
number while $`e_2` in $`e_1^{\,e_2}` is an arbitrary expression, and rational
literals with zero denominator are rejected by the well-formedness layer.
:::

:::theorem "symbolic.normalization_sound" (parent := "symbolic.exact") (lean := "CAS.Verified.Expr.Alg.eval_eq_zero_of_normalize_eq_zero") (uses := "symbolic.expression")
If the executable normalizer reduces an expression to literal zero, evaluating
the original expression in any real environment gives zero. The computation
therefore proposes a normal form, while this theorem is the kernel-checked
semantic justification.

$$`\operatorname{normalize}(e)=0
  \quad\Longrightarrow\quad
  \forall\rho,\ \operatorname{eval}(e,\rho)=0.`
:::

:::proof "symbolic.normalization_sound"
The normalizer is accompanied by an invariant equating evaluation of each
intermediate form with evaluation of the input. Specializing that invariant
to a returned literal zero identifies the original value with the evaluation
of zero, hence with zero in every environment.
:::

:::theorem "symbolic.side_normalization_sound" (parent := "symbolic.exact") (lean := "CAS.Verified.Expr.Alg.eval_eq_zero_of_normalizeWithSide_eq_zero") (uses := "symbolic.normalization_sound")
Rational cancellation and other conditional rewrites return the nonzero
conditions they require. Under those conditions, reduction to zero again
implies equality of the original real expression.

If normalization returns a zero expression together with side conditions
$`S`, then

$$`\operatorname{normalizeWithSide}(e)=(0,S)
  \land\operatorname{SideHolds}(\rho,S)
  \quad\Longrightarrow\quad
  \operatorname{eval}(e,\rho)=0.`
:::

:::proof "symbolic.side_normalization_sound"
The side-aware route proves evaluation preservation conditionally on every
emitted nonzero or branch requirement. Once `SideHolds` supplies those
requirements, the route's final zero expression evaluates to zero, so the
original expression does as well.
:::

:::definition "symbolic.side_claim_route" (parent := "symbolic.exact") (uses := "symbolic.expression, symbolic.side_normalization_sound") (lean := "CAS.Verified.Expr.SideClaimRoute, CAS.Verified.Expr.SideClaimRoute.sound, CAS.Verified.Expr.SideClaimRoute.exact, CAS.Verified.Expr.SideClaimRoute.sound_of_nonzero_eq_nil")
Every checked symbolic transformation is recorded by one route type. A
`SideClaimRoute` stores the source and target expressions, the list of
expressions that must not vanish, and a proof that the target and source
evaluate equally wherever that list holds; a positivity requirement is encoded
as the nonvanishing of a square root. An unconditional transformation is the
same object with an empty list of assumptions.

For a route with source $`l`, target $`r`, and assumption list $`S`,

$$`\operatorname{SideHolds}(\rho,S)
  \quad\Longrightarrow\quad
  \operatorname{eval}(r,\rho)=\operatorname{eval}(l,\rho),
\qquad
S=[\,]\quad\Longrightarrow\quad
  \forall\rho,\ \operatorname{eval}(r,\rho)=\operatorname{eval}(l,\rho).`
:::

:::theorem "symbolic.real_power_normal_form" (parent := "symbolic.exact") (uses := "symbolic.side_normalization_sound") (lean := "CAS.Verified.Expr.eval_realPowerDeepCleanup")
The side-conditioned pipeline contains a pass for the algebra of real powers
and of the exponential, which it treats as the power of $`\mathrm e`. Inside
a product or quotient all powers of one base collect into a single power,
nested powers flatten, powers of products distribute, exponents are put into
a polynomial normal form, and a literal exponent is read back as a natural
power, a reciprocal, or a square root. Each rewrite that Mathlib states for a
positive base records the positivity of that base as a condition unless the
base is structurally positive (a positive numeral, $`\pi`, $`\mathrm e`, an
exponential, or a product of these); rewrites valid for the total
`Real.rpow`, and the exponential identities, record nothing.

Writing $`(e',S)` for the output of the pass on $`e`,

$$`\operatorname{SideHolds}(\rho,S)
  \quad\Longrightarrow\quad
  \operatorname{eval}(e',\rho)=\operatorname{eval}(e,\rho).`
:::

:::proof "symbolic.real_power_normal_form"
Each local rewrite uses the corresponding identity for real powers, square
roots, or exponentials under its recorded positivity conditions. The
bottom-up traversal retains every condition from the rewrites it applies. Induction over
the traversal composes the local evaluation equalities into the equality for
the whole tree; when the expression contains no power atom the pass returns it
unchanged.
:::

:::theorem "symbolic.polynomial_interval_evaluation" (parent := "symbolic.exact") (lean := "CAS.Polynomial.RealRoot.evalInterval_sound, CAS.Polynomial.RealRoot.centredInterval_sound, CAS.Polynomial.RealRoot.enclosure_sound")
Exact interval evaluation encloses the value of a sparse rational polynomial
at every real point of a rational panel. The root checks first try the
centred form, the exact Taylor shift of the polynomial to the midpoint of the
panel bounded term by term over its radius, and use termwise evaluation when
the centred interval does not exclude zero. This theorem is the semantic basis
for both root exclusion and derivative-sign checks.

$$`x\in[a,b]
  \quad\Longrightarrow\quad
  p(x)\in\operatorname{enclosure}(p,[a,b]).`
:::

:::proof "symbolic.polynomial_interval_evaluation"
Termwise evaluation encloses each monomial with interval multiplication and
natural powers and combines the terms with interval addition. The basic
interval operations preserve membership, so induction over the sparse term
list shows that the real polynomial value lies between the computed rational
endpoints. For the centred form, write $`p(x)=\sum_k c_k(x-m)^k` with the
exact shifted coefficients $`c_k`, where $`m` is the midpoint and $`r` the
radius of the panel. Since $`|x-m|\le r`, an even power $`(x-m)^k` lies in
$`[0,r^k]` and an odd one in $`[-r^k,r^k]`, so every term lies in a rational
interval and their sum encloses $`p(x)`. The enclosure returns one of these
two sound intervals.
:::

:::theorem "symbolic.root_free_interval" (parent := "symbolic.exact") (uses := "symbolic.polynomial_interval_evaluation") (lean := "CAS.Polynomial.RealRoot.nonzeroOn_of_rootFree_eq_true, CAS.Polynomial.RealRoot.nonzeroOn_of_rootFreeOn_eq_true")
If checked interval evaluation excludes zero, the polynomial is nonzero
throughout the panel. The result can be used directly as a side condition for
an ordinary real-expression theorem.

$$`\operatorname{rootFree}(p,[a,b])=\mathrm{true}
  \quad\Longrightarrow\quad
  \forall x\in[a,b],\ p(x)\neq0.`
:::

:::proof "symbolic.root_free_interval"
Sound interval evaluation places every $`p(x)` in the computed range.
The Boolean root-free test proves that zero is outside that range. Therefore
no enclosed value can equal zero.
:::

For example, on $`[2,3]`, interval arithmetic gives
$`x^2-1\in[3,8]`. This one enclosure proves that the denominator
$`x^2-1` never vanishes there and also gives
$`1/(x^2-1)\in[1/8,1/3]`. The nonvanishing fact justifies an exact
cancellation; the two numerical endpoints control the size of the
reciprocal. Exact reasoning and CEGA draw on the same domain information.

:::theorem "symbolic.unique_root_bracket" (parent := "symbolic.exact") (uses := "symbolic.polynomial_interval_evaluation") (lean := "CAS.Polynomial.RealRoot.RootBracket.existsUnique_root")
Endpoint values satisfying $`p(a)\le0\le p(b)`, or the reversed
inequalities, give a root by the intermediate value theorem. A checked
strict derivative sign makes the polynomial strictly monotone in the
corresponding direction. Together they prove that the rational bracket
contains exactly one real root, possibly at an endpoint.

For every valid bracket certificate,

$$`\exists!\,x\in[a,b],\qquad p(x)=0.`
:::

:::proof "symbolic.unique_root_bracket"
Continuity and the weak endpoint inequalities give existence by the intermediate
value theorem. The derivative enclosure has one strict sign on the whole
panel, so the mean value theorem makes $`p` strictly monotone there. A
strictly monotone function has at most one zero, proving uniqueness.
:::

:::theorem "symbolic.root_atlas_cover" (parent := "symbolic.exact") (uses := "symbolic.root_free_interval, symbolic.unique_root_bracket") (lean := "CAS.Polynomial.RealRoot.RootAtlas.root_mem_region, CAS.Polynomial.RealRoot.GlobalRootAtlas.root_mem_region")
A root atlas combines root-free and uniquely rooted panels with a proved
cover. Every real root in the outer domain therefore belongs to one of the
atlas's isolated root regions.

If $`\mathcal A` is an atlas over $`D`, its projection is

$$`x\in D\land p(x)=0
  \quad\Longrightarrow\quad
  \exists R\in\mathcal A.\mathrm{rootRegions},\ x\in R.`

For a global atlas the premise $`x\in D` is removed by its outer-root bound.
:::

:::proof "symbolic.root_atlas_cover"
Take a root in the covered domain and choose an atlas panel containing it.
A root-free panel is impossible because its certificate excludes zero.
Consequently the chosen panel is one of the root regions, which proves the
covering conclusion. The global version first uses the outer bound to place
the root in the covered domain.
:::

:::theorem "symbolic.cauchy_root_bound" (parent := "symbolic.exact") (lean := "CAS.Polynomial.RealRoot.CauchyBoundCertificate.abs_lt_bound")
A checked rational Cauchy certificate gives an explicit outer interval
containing every real root. Its exact monic decomposition is verified before
the resulting coefficient bound is used.

For its derived rational bound $`B`,

$$`p(x)=0\quad\Longrightarrow\quad |x|<B.`
:::

:::proof "symbolic.cauchy_root_bound"
Use the checked monic decomposition to rewrite a hypothetical root equation.
If $`|x|` were at least the computed coefficient bound, the leading term would
strictly dominate the sum of all lower-degree terms, contradicting that their
sum is zero. Hence every root lies inside $`(-B,B)`.
:::

*Understanding a root certificate.*

The isolated root need not be rational. A root atlas identifies it by a
rational interval and a uniqueness theorem, which is often exactly what a PDE
side-condition proof needs. The covering and uniqueness theorems of the
`RootAtlas` and `GlobalRootAtlas` interfaces can discharge nonvanishing,
domain, and monotonicity side conditions in later symbolic or PDE arguments.
Those theorems have the same form whether an atlas was assembled from
interval exclusion, Sturm subdivision, or both.

*The Cauchy root bound in detail.*

For a polynomial with rational coefficients, write it in monic form

$$`p(x) = s \cdot \left(x^n + \sum_{k=0}^{n-1} a_k x^k\right),`

where $`s \neq 0` is the leading scalar. The checked bound is

$$`B = 1 + \sum_{k=0}^{n-1} |a_k|.`

A `CauchyBoundCertificate` stores only the decomposition fields (scale $`s`,
degree $`n`, and the lower-degree tail). The bound $`B` is computed from that
tail. An independent checker
validates:

1. the scale is nonzero;
2. every exponent in the tail is strictly below $`n`;
3. the sparse identity $`p = s \cdot (x^n + \text{tail})` holds after normalization.

When $`n=0`, the checked tail is empty and $`p=s\ne0`, so there are no
roots. For $`n>0`, the soundness proof (`abs_lt_bound`) proceeds by
contradiction. If $`|x|\ge B` and $`p(x)=0`, dividing by $`s` gives
$`x^n=-\text{tail}(x)`. Since $`|x|\ge B\ge1`, each lower-degree term
satisfies $`|a_k||x|^k\le|a_k||x|^{n-1}`. Hence

$$`|x|^n\le\left(\sum_{k=0}^{n-1}|a_k|\right)|x|^{n-1}.`

Dividing by the positive factor $`|x|^{n-1}` gives
$`|x|\le\sum|a_k|<B`, a contradiction. The Lean proof implements this
leading-term estimate with exact sparse evaluation and cancellation by the
checked nonzero scale.

*Example: isolating roots of $`x^2 + x - 1`.*

Consider the polynomial $`p(x) = x^2 + x - 1`. A hand calculation shows the
certificate data; the generator may choose different split points.

1. *Cauchy bound.* In monic form the tail is $`x - 1`, whose coefficient
   absolute values sum to $`1 + 1 = 2`. The checked bound is $`B = 1 + 2 = 3`,
   so all roots lie in $`(-3, 3)`.

2. *Square-free reduction.* The gcd of $`p` and $`p' = 2x + 1` is $`1`, so
   `p` is already square-free and its radical is `p` itself.

3. *Sturm chain construction.*
  - $`S_0 = x^2 + x - 1`,
  - $`S_1 = p'(x) = 2x + 1`,
  - Euclidean division gives
    $`S_0 = (\frac{x}{2}+\frac14)S_1 - \frac54`, so
    $`S_2 = \frac54`, a nonzero constant.

  The terminal polynomial $`S_2 = 5/4` has zero derivative and nonzero value,
  hence is globally nonzero (proved using the mean value theorem).

4. *Variation counting.* At $`x = -3`, the signs are $`(+, -, +)`, giving
   two sign changes. At $`x = 3`, they are $`(+, +, +)`, giving none. The
   drop $`V(-3) - V(3) = 2` confirms that `p` has exactly two distinct real
   roots.

5. *Bisection.* At $`x = 0`, the signs are $`(-, +, +)`, giving one sign
   change. Thus $`V(-3) - V(0) = 1` and $`V(0) - V(3) = 1`. The intervals
   $`(-3,0)` and $`(0,3)` each contain exactly one root.

6. *Atlas assembly.* The global root atlas records the two isolated intervals,
   together with the checked Sturm certificate that proves their root counts.

*The Sturm chain algorithm.*

A Sturm chain for a polynomial $`p` is a sequence $`S_0, S_1, \ldots, S_m` satisfying:

$$`S_0 = p, \quad S_1 = p', \quad S_{i-1} = Q_i S_i - S_{i+1} \quad (i = 1, \ldots, m-1),`

where the last element $`S_m` is a nonzero constant. This signed Euclidean
remainder sequence is the ordinary Euclidean algorithm with the sign of each
remainder reversed. The certificate checker (`SturmCertificate.valid`)
validates every recurrence by exact polynomial arithmetic, independently of
the generator that proposed the chain. The variation count $`V(c)` is the
number of sign changes in $`(S_0(c),S_1(c),\ldots,S_m(c))`, zeros omitted;
{bpref "symbolic.sturm_root_count"}[Sturm's theorem] turns its drop
between two endpoints into a root count.

*The subdivision certificate.*

A Sturm subdivision is a binary tree of rational intervals over a search
interval, such as the Cauchy-bounded $`[-B,B]`: every leaf has Sturm count at
most one, and every split is at a rational point that is not a root. SymLean
checks such a tree when a caller supplies it and has no generator for it; the
root and sign commands use their own root-cover search and root-list checkers.
Leaves whose Sturm count is one are the isolated root regions.

*Sparse polynomial representation.*

The polynomial subsystem uses `Verified.Expr.Alg.MvPoly n`, a raw list of
rational coefficient–monomial pairs. A monomial is a function
$`\text{Fin}(n) \to \mathbb{N}` recording the exponent of each variable.
The type permits repeated monomials and zero coefficients. The executable
normalization combines terms, removes zeros, and orders the result without
changing the polynomial's value.

Interpreting these lists as Mathlib polynomials over $`\mathbb Q` preserves
evaluation. Importing a Mathlib multivariate polynomial and exporting it
again returns the original polynomial. In the other direction, different
lists can represent the same
polynomial, so a raw list need not equal its own round trip.

Key operations include:
- *Euclidean division:* exact quotient and remainder satisfying
  $`p=qs+r` for univariate polynomials.
- *Square-free factorization* (`squareFreeFactors?`): a Yun-style candidate
  generator proposes factors indexed by intended multiplicity. Its output is a
  proposal; the semantic contract belongs to the radical certificate built
  from it.
- *Rational factors* (`RationalFactorization.split`): linear and quadratic
  factors are kept; `x` is split off by exact division while it divides a
  factor of degree three or more; any other factor of degree three or more is
  split only by a factor provider, Hex's factorizer through the optional
  `CASHex`, whose proper factors are accepted when their product is that
  factor, and otherwise stays whole. Rational integration uses the list as a
  proposal and checks its final primitive by differentiation.
- *Exact evaluation* (`evalRat`): evaluates at rational points with exact
  arithmetic, used for sign determination in Sturm chains.
- *Interval evaluation* (`evalInterval`): rigorous enclosure of the
  polynomial's range on a rational panel.

:::theorem "symbolic.exact_division_certificate" (parent := "symbolic.exact") (lean := "CAS.Polynomial.Sparse.Univariate.DivisionResult.polynomial_identity")
An exact quotient-and-remainder candidate is accepted only after sparse
polynomial normalization proves the corresponding identity. The checked
identity is then projected to Mathlib's `Polynomial ℚ`.

Every accepted certificate proves the polynomial identity

$$`P=DQ+R`

in `Polynomial ℚ`, including the exact quotient and remainder supplied by the
candidate.
:::

:::proof "symbolic.exact_division_certificate"
Translate the candidate quotient and remainder into the sparse normal form and
normalize $`P-DQ-R`. Acceptance means this difference has zero normal form.
Normalization soundness gives the polynomial identity over the rationals,
which is then transported to Mathlib's polynomial representation.
:::

:::theorem "symbolic.square_free_radical_certificate" (parent := "symbolic.exact") (uses := "symbolic.exact_division_certificate") (lean := "CAS.Polynomial.RealRoot.RadicalCertificate.evalReal_eq_zero_iff, CAS.Polynomial.RealRoot.RadicalCertificate.derivative_ne_zero_at_root, CAS.Polynomial.RealRoot.RadicalCertificate.generate?")
A radical certificate proves that a proposed square-free reduction has exactly
the same real zero set as the original polynomial and has nonzero derivative
at every root. The executable Yun-style generator returns only a certificate that
passes the independent check of two divisibility identities and a Bézout identity.

Writing the checked radical as $`r`,

$$`\forall x\in\mathbb R,\qquad
  p(x)=0\Longleftrightarrow r(x)=0,
  \qquad
  r(x)=0\Longrightarrow r'(x)\neq0.`
:::

:::proof "symbolic.square_free_radical_certificate"
The checked division identities certify the gcd decomposition used by the
square-free reduction. They show that removing repeated factors preserves
exactly the zero set. Coprimality of the reduced polynomial and its derivative
then rules out a point where both vanish, so every remaining root is simple.
:::

:::theorem "symbolic.sturm_chain_validation" (parent := "symbolic.exact") (uses := "symbolic.exact_division_certificate") (lean := "CAS.Polynomial.RealRoot.SturmCertificate.first_polynomial, CAS.Polynomial.RealRoot.SturmCertificate.second_polynomial, CAS.Polynomial.RealRoot.SturmCertificate.recurrence_head_identity, CAS.Polynomial.RealRoot.SturmCertificate.recurrence_terminal_nonzero")
An accepted Sturm certificate begins with the requested polynomial and its
formal derivative, satisfies every signed Euclidean recurrence exactly, and
ends in a polynomial that is nonzero on the real line. These are structural
facts about the checked chain, before any root-counting theorem is applied.

For a chain $`S_0,\ldots,S_m`, validation establishes

$$`S_0=p,\qquad S_1=p',\qquad
  S_{i-1}=Q_iS_i-S_{i+1},\qquad
  \forall x\in\mathbb R,\ S_m(x)\neq0.`
:::

:::proof "symbolic.sturm_chain_validation"
The independent checker verifies the first two entries and every signed
quotient-remainder identity using exact polynomial normalization. At the
terminal entry it checks a zero formal derivative and a nonzero value at zero.
The mean value theorem makes that polynomial constant, hence nowhere zero.
Collecting these checked equalities yields the defining Sturm-chain
conditions.
:::

:::theorem "symbolic.sturm_root_count" (parent := "symbolic.exact") (uses := "symbolic.sturm_chain_validation") (lean := "CAS.Polynomial.RealRoot.SturmCertificate.variationDifference_eq_rootSet_ncard")
For an accepted chain and ordered rational endpoints that are not roots, the
drop in endpoint sign variations equals the number of distinct real roots in
the intervening open interval. This is the analytic Sturm theorem that gives
the executable variation count its mathematical meaning.

$$`V(a)-V(b)
  =\#\{x\in(a,b)\mid p(x)=0\}.`
:::

:::proof "symbolic.sturm_root_count"
Along an interval containing no endpoint root, sign variation is locally
constant except when crossing a root of $`p`. The signed Euclidean recurrence
shows that noninitial chain entries cannot create a net jump, while each
distinct root of $`p` decreases the variation by one. Summing the jumps from
$`a` to $`b` gives the root count.
:::

:::definition "symbolic.sturm_chain_generation" (parent := "symbolic.exact") (uses := "symbolic.sturm_chain_validation") (lean := "CAS.Polynomial.RealRoot.SturmCertificate.valid")
A signed Euclidean chain is proposed outside the checker and accepted only
when the independent structural checker `SturmCertificate.valid` accepts
every initial, recurrence, degree, and terminal condition. SymLean has no
chain generator: a caller supplies the chain.

$$`\mathrm{valid}(p, C)=\mathrm{true}
  \quad\Longrightarrow\quad
  C\text{ is a validated Sturm certificate for }p.`
:::

:::theorem "symbolic.sturm_interval_subdivision" (parent := "symbolic.exact") (uses := "symbolic.root_atlas_cover, symbolic.sturm_root_count, symbolic.sturm_chain_generation") (lean := "CAS.Polynomial.RealRoot.SturmIntervalCertificate.existsUnique_root, CAS.Polynomial.RealRoot.SturmSubdivisionCertificate.nodeCount_eq_rootSet_ncard, CAS.Polynomial.RealRoot.SturmSubdivisionCertificate.toRootAtlas")
Sturm counts certify unique-root intervals and exact root counts for a checked
subdivision tree. An accepted finite subdivision therefore projects to the
same root-atlas interface used by interval and monotonicity certificates.

For each accepted node $`N` with interval $`I_N`,

$$`N.\mathrm{rootCount}
  =\#\{x\in I_N^\circ\mid p(x)=0\},`

and every leaf with count one projects to an
$`\exists!\,x\in I_N,\ p(x)=0` certificate.
:::

:::proof "symbolic.sturm_interval_subdivision"
Apply the Sturm count theorem at every node. A node of count zero is root-free;
a node of count one contains a root and cannot contain two distinct roots.
For a split node, additivity of root counts over its adjacent children
preserves the parent's exact count. Structural induction over the accepted
subdivision tree therefore produces the root atlas.
:::

:::definition "symbolic.global_polynomial_isolation" (parent := "symbolic.exact") (uses := "symbolic.root_atlas_cover, symbolic.cauchy_root_bound, symbolic.square_free_radical_certificate, symbolic.sturm_interval_subdivision") (lean := "CAS.Polynomial.RealRoot.RootAtlas.transportAlongRadical, CAS.Polynomial.RealRoot.PolynomialIsolationCertificate.toRootAtlas, CAS.Polynomial.RealRoot.GlobalPolynomialIsolationCertificate.toGlobalRootAtlas")
The isolation certificates combine square-free reduction, a Sturm
subdivision, transport back to the original zero set, and a checked rational
Cauchy outer bound. `GlobalPolynomialIsolationCertificate.valid` checks every
stage, and the noncomputable `toGlobalRootAtlas` projection then yields a
global atlas covering every distinct real root; a nonzero constant has an
empty atlas. SymLean checks these certificates when a caller supplies them and
has no generator for them.

The final global contract is

$$`p(x)=0
  \quad\Longrightarrow\quad
  \exists R\in\mathcal A.\mathrm{rootRegions},\ x\in R,`

with each root-bearing region carrying a unique-root theorem.
:::

*Scope of the exact core.*

The decision procedures of the exact core work inside its reflected real
language, with rational polynomial coefficients. A bounded search that returns
`none` has found no supported certificate within its budget; the statement
itself may still be true.
