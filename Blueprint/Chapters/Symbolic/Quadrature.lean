/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.TaylorModels
import Blueprint.Commands.Figures
import CAS.Continuum.Quadrature.Gaussian.GaussLegendreTwo
import CAS.Continuum.Quadrature.Gaussian.Remainder
import CAS.Continuum.Quadrature.Gaussian.Recurrence
import CAS.Continuum.Quadrature.Gaussian.Characterization
import CAS.Continuum.Quadrature.Gaussian.Roots
import CAS.Continuum.Quadrature.Gaussian.Nodal
import CAS.Continuum.Quadrature.Legendre.Identification
import CAS.Continuum.Quadrature.Legendre.WeightCertificates
import CAS.Continuum.Quadrature.NewtonCotes
import CAS.Continuum.Quadrature.PanelRule
import CAS.Continuum.Quadrature.SecondOrder
import CAS.Continuum.Quadrature.PositiveRule
import CAS.Continuum.Quadrature.IntervalRange
import CAS.Continuum.Quadrature.RationalRule
import CAS.Continuum.Quadrature.CompositeGaussLegendre
import CAS.Continuum.Quadrature.RationalComposite
import CAS.Continuum.Quadrature.CompositeSimpson
import CAS.Continuum.Quadrature.Planning

/-!
## Certified quadrature

Verified quadrature rules, error bounds, and tolerance planning.
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
#doc (Manual) "Certified Quadrature" =>

A quadrature certificate bounds the difference between a proposed value and
the integral. Exactness on polynomials and bounds on derivatives control
the analytic error; interval evaluation controls the error in computing the
finite weighted sum. These two errors add.

:::definition "symbolic.quadrature_certificate" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate") (lean := "CAS.Continuum.QuadratureCert")
A quadrature certificate stores a proposed value of a Bochner interval
integral, an explicit error budget, and a proof of the corresponding norm
estimate. The certificate is indexed by the ordinary Lean integrand and
endpoints, so no symbolic expression type appears in theorem statements.

Its trusted field is

$$`q.\mathrm{sound}:\qquad
  \left\|\int_a^b f(x)\,dx-q.\mathrm{value}\right\|
  \leq q.\mathrm{error}.`
:::

*A complete certificate: Simpson on $`x^2`.*

Take $`f(x)=x^2` on $`[0,1]`. One Simpson panel uses the values at
$`0`, $`1/2`, and $`1`, so its exact-real value is

$$`\frac16 f(0)+\frac46 f\left(\frac12\right)+\frac16 f(1)
  =\frac13.`

Because Simpson's rule is exact for every polynomial of degree at most three,
its {bpref "symbolic.quadrature_certificate"}[quadrature certificate] has:

* the stored value is $`1/3`;
* the stored error is $`0`;
* soundness proves $`\left|\int_0^1x^2\,dx-\frac13\right|\leq0`.

The third field is the mathematical content. The first two fields are data
that later planners can inspect and combine. Since the integrand is a
continuous polynomial, it is also interval integrable; that fact is separate
because `QuadratureCert` itself is stated for Mathlib's totalized interval
integral.

For a nonpolynomial integrand, the shape of the object is unchanged. A
Simpson or Gauss–Legendre theorem supplies a positive analytic error, and a
verified numerical backend may replace the exact-real weighted sum with a
computed value by adding a separately proved roundoff error. The final
`sound` field always states one inequality about the original integral.

The first polynomial beyond Simpson's exactness range shows what the error
constant measures. For $`f(x)=x^4` on $`[0,1]`,

$$`
S(f)=\frac46\frac1{16}+\frac16=\frac5{24},
\qquad
\int_0^1x^4\,dx=\frac15,
\qquad
S(f)-\int_0^1f=\frac1{120}.
`

Here $`f^{(4)}=24`, so the sharp Simpson bound is
$`24/2880=1/120`, exactly the observed error. The fourth derivative
measures the first behavior that the degree-three exactness does not
reproduce.

:::theorem "symbolic.integration_stability" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate, symbolic.quadrature_certificate") (lean := "CAS.Continuum.QuadratureCert.norm_intervalIntegral_sub_le, CAS.Continuum.QuadratureCert.transportApprox")
If both functions are interval integrable, uniform approximation on
$`[[a,b]]` transports through interval integration with error
$`\varepsilon |b-a|`. Consequently a quadrature certificate for a
finite or symbolic model becomes a certificate for the original integrand,
with model and quadrature errors added explicitly.
:::

:::proof "symbolic.integration_stability"
Integrate the pointwise difference and apply the norm bound for an interval
integral. Uniform approximation bounds the integrand norm by
$`\varepsilon`, while the integral of that constant over the oriented
interval contributes $`|b-a|`. A final triangle inequality adds this model
error to the existing quadrature error.
:::

:::theorem "symbolic.interval_range_quadrature" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge, symbolic.quadrature_certificate") (lean := "CAS.Continuum.QuadratureCert.integral_mem_Icc, CAS.Continuum.QuadratureCert.ofIntervalRange")
If the scalar integrand is interval integrable and one backend interval contains every value on
$`[[a,b]]`, its midpoint defines a constant integral model and its radius gives
the uniform pointwise error. The resulting certificate has value
$`(b-a)c` and error $`r|b-a|`, with no endpoint-order assumption and no
backend-specific integration theorem. Exact rational ranges, directed
floating-point ranges, Taylor enclosures, and adaptive local ranges therefore
share the same analytic bridge.
:::

:::proof "symbolic.interval_range_quadrature"
Write the enclosure as center $`c` and radius $`r`. Interval membership gives
$`|f(x)-c|\leq r` uniformly, so integration stability compares $`f` with the
constant function $`c`. The constant integral is $`(b-a)c`, and its
transported error is $`r|b-a|`.
:::

*How the error budget is assembled.*

A certificate constructor assembles the error budget in five steps:

1. prove exactness on a polynomial model or prove a Peano-kernel remainder;
2. obtain any required derivative bound as an ordinary theorem;
3. sum local analytic errors when the interval is subdivided;
4. enclose the finite weighted sum if it is evaluated numerically;
5. add the proved roundoff radius to the analytic budget.

The quadrature rule chooses nodes and weights. The derivative theorem controls
truncation. The numerical backend controls finite evaluation. Keeping those
proofs separate makes it possible to replace one backend or one subdivision
policy without changing the statement about the integral.

*Quadrature rules implemented.*

The certificate constructors use four normalized rules, each stored as an
exact list of (weight, node) pairs on $`[0,1]`. Each error formula assumes
the stated derivative bound and the corresponding $`C^2` or $`C^4`
regularity on an ordered interval $`[a,b]`.

* *Trapezoidal rule:* two nodes at $`\{0, 1\}` with weights $`\{1/2, 1/2\}`.
  Exact for polynomials of degree at most 1. Error on $`[a,b]`:
  $`\zeta(b-a)^3/12` where $`\zeta` bounds $`|f''|`.

* *Midpoint rule:* one node at $`1/2` with weight $`1`. Exact for polynomials
  of degree at most 1. Error on $`[a,b]`: $`\zeta(b-a)^3/24`, half the
  trapezoid constant.

* *Simpson's rule:* three nodes at $`\{0, 1/2, 1\}` with weights
  $`\{1/6, 4/6, 1/6\}`. Exact for polynomials of degree at most 3. The sharp
  Peano-kernel error on $`[a,b]`: $`C(b-a)^5/2880` where $`C` bounds
  $`|f^{(4)}|`.

* *Two-point Gauss–Legendre:* two nodes at
  $`\{1/2 - 1/(2\sqrt{3}), 1/2 + 1/(2\sqrt{3})\}` with weights
  $`\{1/2, 1/2\}`. With only two nodes it is exact for polynomials of degree
  at most 3, like Simpson's three-node rule. The sharp Peano-kernel error:
  $`C(b-a)^5/4320`, which is $`2/3` of Simpson's error constant.

The Gauss–Legendre rule has irrational nodes ($`1/2 \pm \sqrt{3}/6`), which
are represented exactly in the real-valued `QuadratureRule`. Numerical
evaluation encloses the exact weighted terms by proved intervals. A
`RationalQuadratureRule`, by contrast, has rational nodes.

*The Peano kernel approach.*

The sharp error constants (1/2880 for Simpson, 1/4320 for Gauss–Legendre) come
from the Peano kernel method. For a rule $`Q` that is exact on polynomials of
degree at most $`d` and an integrand $`f \in C^{d+1}[a,b]`, the integration
error equals

$$`\int_a^b f(x)\,dx - Q(f) = \int_a^b K_{d+1}(t) f^{(d+1)}(t)\,dt,`

where $`K_{d+1}` is the Peano kernel of order $`d+1`: the functional
$`f \mapsto \int f - Q(f)` applied to the truncated power
$`(x-t)_+^d / d!`. If $`K_{d+1}` has constant sign, the integral is bounded
by $`\|f^{(d+1)}\|_\infty \cdot \int |K_{d+1}|`.

*Example: composite Simpson on $`\int_0^1 e^x\,dx`.*

First plan the exact-real composite value to analytic tolerance
$`\tau = 10^{-8}`. A computed replacement must also fit its evaluation error
within the remaining budget before claiming this same total tolerance.

1. *Derivative bound.* On $`[0,1]`, $`f^{(4)}(x) = e^x \leq e < 3`. Set $`C = 3`.

2. *Error constant.* $`B = C(b-a)^5/2880 = 3/2880 = 1/960`.

3. *Panel planning.* Solve $`B/N^4 \leq \tau`:
   $`N \geq (B/\tau)^{1/4} = (10^8/960)^{1/4} \approx 17.97`.
   The planner rounds up to $`N = 18`: exactly,
   $`960\cdot17^4<10^8\leq960\cdot18^4`.

4. *Certificate construction.* Build 18 Simpson panels of width $`1/18`.
   Summing their sharp errors gives
   $`1/(960\cdot18^4)\approx9.923\times10^{-9}<10^{-8}`.

5. *Value computation.* The panel-major schedule contains 54 weighted samples,
   with $`2\cdot18+1=37` distinct nodes because adjacent endpoints coincide.
   A numerical backend must provide enclosures for those samples and their
   weighted sum; the analytic panel count alone supplies no evaluation precision.

6. *Final certificate.* The `QuadratureCert` stores:
   - value: the midpoint of the weighted-sum enclosure,
   - error: the analytic Simpson error plus the weighted-sum roundoff radius,
   - sound: the proof that $`|\int_0^1 e^x\,dx - \text{value}| \leq \text{error}`.

This final error is at most $`10^{-8}` only if the certified evaluation radius
is at most $`10^{-8}-1/(960\cdot18^4)`. Otherwise, refine the evaluation or
replan the analytic mesh with a smaller reserved budget.

*Adaptive quadrature and the tree structure.*

Composite rules use a fixed number of equal panels, which may be inefficient
for integrands with localized difficulty (near-singularities, rapid
oscillation). The adaptive framework addresses this with a binary
`QuadratureTree` whose leaves are local certificates and whose branches split
an interval at a point. Because soundness depends only on the leaf
certificates and their composition, an adaptive algorithm may choose the
subdivision by any heuristic, including Richardson extrapolation, derivative
estimates, or a priori knowledge of integrand behavior.

:::definition "symbolic.normalized_quadrature_rule" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate") (lean := "CAS.Continuum.QuadratureRule")
A normalized quadrature rule is an ordered list of exact-real weights and
nodes in $`[0,1]`. The order remains explicit for verified finite-precision
evaluation. Generic definitions transport the rule affinely to any oriented
interval, while moment identities characterize exactness independently of a
particular numerical backend.
:::

:::theorem "symbolic.rational_rule_compilation" (parent := "symbolic.cega") (uses := "symbolic.normalized_quadrature_rule, symbolic.interval_bridge") (lean := "CAS.Verified.Expr.evalRat?_sound, CAS.Continuum.RationalQuadratureRule.symbolicTermsOn?_sound, CAS.Continuum.RationalQuadratureRule.cast_valueOn")
The rational algebraic fragment of the shared expression language has a
fail-closed exact evaluator. Every successful result is proved equal to the
existing real expression semantics. A quadrature rule with rational weights
and nodes can therefore sample a symbolic integrand exactly, preserve the
ordered rule schedule, and cast term-for-term to the existing transported
`QuadratureRule`. Transcendental nodes, malformed literals, and sampled zero
denominators are rejected. Optional
finite-precision backends consume the exact table through the same interval
and weighted-sum interfaces.

At the expression boundary,

$$`\operatorname{evalRat?}(e,\rho)=\operatorname{some}(q)
  \quad\Longrightarrow\quad
  \operatorname{eval}(e,\rho_{\mathbb R})=(q:\mathbb R).`

For a successfully compiled rule, casting every rational term preserves the
analytic schedule and value:

$$`\operatorname{cast}\!\left(\sum_j w_j e(x_j)\right)
  =\sum_j (w_j:\mathbb R)\,
    \operatorname{eval}(e,(x_j:\mathbb R)).`
:::

:::proof "symbolic.rational_rule_compilation"
Prove the rational evaluator correct by structural induction on the algebraic
expression, rejecting precisely the division cases with zero denominator.
Apply that equality at each rational quadrature node. Casting commutes with
the finite products and sum, so the compiled ordered table has the same real
weighted value as the analytic rule.
:::

:::theorem "symbolic.polynomial_quadrature_exactness" (parent := "symbolic.cega") (uses := "symbolic.normalized_quadrature_rule") (lean := "CAS.Continuum.QuadratureRule.exactFor_polynomial, CAS.Continuum.simpsonRule.exactUpTo_three, CAS.Continuum.gaussLegendreTwoRule.exactUpTo_three")
If a normalized rule has the exact moments through degree $`d`, it exactly
integrates every real polynomial of degree at most $`d`. Affine transport
preserves this conclusion on arbitrary oriented intervals. Both the three-node
Simpson rule and the two-point Gauss–Legendre rule have the exact moments
through degree three, hence exactly integrate every cubic and generate
zero-error `QuadratureCert`s.
:::

:::proof "symbolic.polynomial_quadrature_exactness"
Expand a polynomial of degree at most $`d` in the monomial basis. Linearity of
both integration and the weighted rule reduces exactness to each monomial,
where it is exactly the assumed moment identity. Affine substitution
transports the normalized-interval result to any oriented interval.
:::

:::theorem "symbolic.quadrature_rule_stability" (parent := "symbolic.cega") (uses := "symbolic.normalized_quadrature_rule, symbolic.integration_stability") (lean := "CAS.Continuum.QuadratureRule.abs_valueOn_sub_le, CAS.Continuum.QuadratureRule.certOfApproxEvaluated")
If two scalar integrands differ uniformly by $`\varepsilon` on
$`[[a,b]]`, their values under a normalized rule differ by at most
$`|b-a|\,V\varepsilon`, where $`V` is the sum of the absolute rule weights.
This estimate lets a rule that is exact on a nearby model be evaluated on the
original integrand while accounting separately for integral-model error and
sample-value perturbation.
:::

:::proof "symbolic.quadrature_rule_stability"
At every node, the sample difference is at most $`\varepsilon`. Apply the
triangle inequality to the weighted sum, bound each term by
$`|w_j|\varepsilon`, and sum to obtain $`V\varepsilon` on the normalized
interval. Affine transport contributes the factor $`|b-a|`.
:::

# Nodes, weights, and degree of exactness

A normalized rule lives on $`[0,1]` and is moved to $`[a,b]` affinely. For
the general theory it is simpler to let the nodes sit anywhere on the real
line and to integrate against a weight function. A `NodalRule` is just that:
$`m` real nodes $`x_i` and $`m` real weights $`w_i`, with value
$`Q(f)=\sum_i w_i f(x_i)`. It carries no interval and no weight function of
its own. Exactness is a property relative to an interval and a weight, which
is what lets one rule be read against several weights, and it is stated with
Mathlib's interval integral, so exactness does not assert integrability.

The central number attached to a rule is its degree of exactness, the largest
$`d` such that $`Q(p)=\int_a^b p\,w` for every polynomial of degree at most
$`d`. The trapezoid and midpoint rules have degree one, Simpson's rule three,
and a Gauss rule with $`n` nodes $`2n-1`. A high degree of exactness is what
turns smoothness of $`f` into a small error: if $`f` is close to some
polynomial of degree $`d`, a rule exact to degree $`d` can only see the
difference.

:::definition "symbolic.nodal_rule" (parent := "symbolic.cega") (uses := "symbolic.normalized_quadrature_rule") (lean := "CAS.Continuum.NodalRule, CAS.Continuum.NodalRule.eval, CAS.Continuum.NodalRule.ExactToDegree, CAS.Continuum.NodalRule.Positive, CAS.Continuum.NodalRule.NodesIn, CAS.Continuum.QuadratureRule.toNodalRule")
A nodal rule consists of a size $`m`, nodes $`x_0,\dots,x_{m-1}\in\mathbb R`,
and weights $`w_0,\dots,w_{m-1}\in\mathbb R`. It is exact to degree $`d`
for the weight $`w` on $`a..b` when

$$`\sum_{i<m} w_i\,p(x_i)=\int_a^b p(x)\,w(x)\,dx
  \qquad\text{for every real polynomial }p\text{ with }\deg p\le d.`

It is positive when every $`w_i\ge0`, and its nodes lie in $`s` when every
$`x_i\in s`. A normalized `QuadratureRule` becomes a nodal rule on
$`[a,b]` with nodes $`a+t_i(b-a)` and weights $`(b-a)w_i`.
:::

:::theorem "symbolic.nodal_rule_exactness" (parent := "symbolic.cega") (uses := "symbolic.nodal_rule, symbolic.polynomial_quadrature_exactness") (lean := "CAS.Continuum.NodalRule.exactToDegree_iff_monomial, CAS.Continuum.NodalRule.ExactToDegree.transport, CAS.Continuum.QuadratureRule.toNodalRule_exactToDegree, CAS.Continuum.QuadratureRule.toNodalRule_positive")
For a weight continuous on $`[[a,b]]`, a nodal rule is exact to degree $`d`
exactly when it integrates the monomials $`1,x,\dots,x^d`. Exactness moves
with the rule under the affine map sending $`a,b` to $`c,d`: if $`Q` is exact
to degree $`n` on $`[a,b]` for the pulled-back weight, the transported rule,
with nodes mapped and weights scaled by $`(d-c)/(b-a)`, is exact to degree
$`n` on $`[c,d]` for the original weight. A normalized rule with the moments
through degree $`d` is exact to degree $`d` on every interval for the unit
weight, and a normalized rule with nonnegative weights is positive on every
ordered interval.
:::

:::proof "symbolic.nodal_rule_exactness"
Both sides of the exactness identity are linear in the integrand, so a
polynomial written in the monomial basis reduces to its monomials. The
continuity of $`w` supplies the integrability that splitting the integral
needs. For transport, substitute $`x=c+(t-a)(d-c)/(b-a)`: the change of
variables formula turns $`\int_c^d f\,v` into $`(d-c)/(b-a)` times an
integral over $`[a,b]`, and composing a polynomial with an affine map does not
raise its degree.
:::

The most direct way to obtain exactness is to integrate an interpolant. Given
$`m` distinct nodes, let $`\ell_i` be the Lagrange basis polynomial that is
$`1` at $`x_i` and $`0` at the other nodes, and put
$`w_i=\int_a^b\ell_i\,w`. A polynomial $`p` of degree below $`m` equals its
interpolant $`\sum_i p(x_i)\ell_i`, so integrating gives $`Q(p)=\int_a^b p\,w`.
With equally spaced nodes including both endpoints this is the closed
Newton–Cotes family: two points give the trapezoid rule and three give
Simpson's rule.

:::theorem "symbolic.newton_cotes" (parent := "symbolic.cega") (uses := "symbolic.nodal_rule_exactness") (lean := "CAS.Continuum.NodalRule.interpolatory_exactToDegree, CAS.Continuum.newtonCotes_exactToDegree, CAS.Continuum.newtonCotes_two_eval, CAS.Continuum.newtonCotes_nodesIn, CAS.Continuum.NodalRule.interpolatory, CAS.Continuum.newtonCotes")
Let $`w` be continuous on $`[[a,b]]` and let $`x_0,\dots,x_{m-1}` be
$`m\ge1` distinct nodes. The interpolatory rule with weights
$`w_i=\int_a^b\ell_i\,w` is exact to degree $`m-1`. For $`n\ge2` and
$`a\ne b`, the closed Newton–Cotes rule on the nodes
$`a+i(b-a)/(n-1)`, $`i=0,\dots,n-1`, is exact to degree $`n-1` for the
unit weight; its nodes lie in $`[a,b]` when $`a\le b`, and for $`n=2` its
value is $`\frac{b-a}2\bigl(f(a)+f(b)\bigr)`.
:::

:::proof "symbolic.newton_cotes"
A polynomial of degree below $`m` coincides with its Lagrange interpolant on
the $`m` nodes, and the rule applied to it is the integral of that
interpolant against $`w`. The Newton–Cotes nodes are distinct because the
spacing $`(b-a)/(n-1)` is nonzero. For two nodes the Lagrange basis
polynomials are linear and each integrates to $`(b-a)/2`.
:::

Interpolation fixes $`m` weights from $`m` nodes, and the resulting degree
$`m-1` is all that can be said for a general choice of nodes. Simpson's rule
does better than its three nodes promise, reaching degree three, because its
middle node sits at the symmetric point. Gaussian quadrature asks how far
this can go when all the nodes are free.

# Orthogonal polynomials

Fix a weight $`w` that is continuous and strictly positive on $`[a,b]`,
$`a<b`. The pairing

$$`\langle p,q\rangle=\int_a^b p(x)\,q(x)\,w(x)\,dx`

is an inner product on real polynomials: it is bilinear and symmetric, and
$`\langle p,p\rangle>0` for $`p\ne0`, because a nonzero polynomial has only
finitely many zeros, so $`p^2w` is positive on some open subinterval.
Orthogonalizing $`1,x,x^2,\dots` gives one monic polynomial $`p_n` of each
degree, orthogonal to every polynomial of lower degree. For the unit weight on
$`[-1,1]` these are the monic Legendre polynomials

$$`p_1=x,\qquad p_2=x^2-\tfrac13,\qquad p_3=x^3-\tfrac35x,\qquad
  p_4=x^4-\tfrac67x^2+\tfrac3{35}.`

More generally, a linear functional $`L` on $`\mathbb R[X]` that is
positive on nonzero squares defines the inner product
$`\langle p,q\rangle=L(pq)`. Subtracting the orthogonal projection of
$`X^n` onto polynomials of degree below $`n` constructs $`p_n`.
Integration against a positive weight is one instance.

:::definition "symbolic.orthogonal_polynomial" (parent := "symbolic.cega") (uses := "symbolic.nodal_rule") (lean := "CAS.Continuum.orthogonalPolynomial, CAS.Continuum.integralOrthogonalPolynomial, CAS.Continuum.orthogonalPolynomial_orthogonal, CAS.Continuum.orthogonalPolynomial_unique, CAS.Continuum.exists_monic_orthogonal, CAS.Continuum.polynomialIntegral_square_pos, CAS.Continuum.momentInnerCore")
Let $`L:\mathbb R[X]\to\mathbb R` be linear with $`L(q^2)>0` for every
$`q\ne0`. The monic orthogonal polynomial $`p_n` of $`L` is monic of degree
$`n` and satisfies $`L(p_nq)=0` for every $`q` with $`\deg q<n`. It is
unique: any monic polynomial of degree $`n` with this property equals
$`p_n`. For a weight $`w` continuous on $`[[a,b]]` and strictly positive on
$`[a,b]`, $`a<b`, the functional $`p\mapsto\int_a^b p\,w` is positive on
nonzero squares, and its orthogonal polynomials are the ones used for Gaussian
quadrature.
:::

Uniqueness is short and gets used repeatedly. If $`p` and $`p_n` are both monic
of degree $`n` and orthogonal to lower degrees, their difference $`r` has
degree below $`n`, so $`L(r^2)=L(pr)-L(p_nr)=0`, and positivity forces
$`r=0`. Every identification of a concrete polynomial with $`p_n` goes
through this argument.

Orthogonal polynomials satisfy a three-term recurrence. Since
$`xp_{n+1}` is monic of degree $`n+2`, the difference
$`xp_{n+1}-p_{n+2}` has degree at most $`n+1`, and its expansion in
$`p_0,\dots,p_{n+1}` has only two nonzero coefficients: for $`k<n` the
coefficient of $`p_k` is proportional to $`L(xp_{n+1}p_k)=L(p_{n+1}\cdot xp_k)`,
which vanishes because $`xp_k` has degree below $`n+1`.

:::theorem "symbolic.three_term_recurrence" (parent := "symbolic.cega") (uses := "symbolic.orthogonal_polynomial") (lean := "CAS.Continuum.orthogonalPolynomial_recurrence, CAS.Continuum.recurrenceBeta_eq_norm_ratio, CAS.Continuum.recurrenceBeta_pos, CAS.Continuum.orthogonalPolynomial_zero, CAS.Continuum.orthogonalPolynomial_one, CAS.Continuum.recurrenceAlpha, CAS.Continuum.recurrenceBeta")
With $`\alpha_n=L(xp_n^2)/L(p_n^2)` and
$`\beta_n=L(xp_{n+1}p_n)/L(p_n^2)`, the monic orthogonal polynomials of $`L`
satisfy $`p_0=1`, $`p_1=x-\alpha_0`, and

$$`p_{n+2}=(x-\alpha_{n+1})\,p_{n+1}-\beta_n\,p_n\qquad(n\ge0).`

Moreover $`\beta_n=L(p_{n+1}^2)/L(p_n^2)`, so $`\beta_n>0`.
:::

:::proof "symbolic.three_term_recurrence"
The right side is monic of degree $`n+2`. It is orthogonal to $`p_{n+1}` by
the choice of $`\alpha_{n+1}`, to $`p_n` by the choice of $`\beta_n`, and to
every polynomial of degree below $`n` because $`L(xp_{n+1}p_k)=0` for $`k<n`.
Uniqueness
identifies it with $`p_{n+2}`. For the second formula, $`xp_n-p_{n+1}` has
degree at most $`n`, so orthogonality of $`p_{n+1}` gives
$`L(xp_{n+1}p_n)=L(p_{n+1}^2)`.
:::

For the unit weight on $`[-1,1]` the symmetry $`x\mapsto-x` makes every
$`\alpha_n` vanish. From $`L(1)=2` and $`L(p_1^2)=\tfrac23` one gets
$`\beta_0=\tfrac13` and $`p_2=x^2-\tfrac13`; then
$`L(p_2^2)=\tfrac8{45}`, $`\beta_1=\tfrac4{15}`, and
$`p_3=x\,p_2-\tfrac4{15}x=x^3-\tfrac35x`, as in the Legendre list.

The roots of $`p_n` are the nodes of the Gauss rule, and three facts about
them are needed: they are real, simple, and inside $`(a,b)`. All three come
from one observation. Suppose $`q` divides $`p_n`, say $`p_n=qr` with
$`\deg r<n`. Orthogonality gives $`\int_a^b q\,r^2w=\int_a^b p_n\,r\,w=0`.
If $`q` had no zero on $`[a,b]` it would have constant sign there, and so
would $`qr^2w`, which is not identically zero; the integral could not
vanish. So every nonconstant factor of $`p_n` has a root in $`[a,b]`.

:::theorem "symbolic.orthogonal_roots" (parent := "symbolic.cega") (uses := "symbolic.orthogonal_polynomial") (lean := "CAS.Continuum.orthogonal_root_mem_Ioo, CAS.Continuum.orthogonal_factor_has_root, CAS.Continuum.orthogonal_squarefree, CAS.Continuum.orthogonal_splits, CAS.Continuum.exists_nodes_of_monic_splits_squarefree")
Let $`w` be continuous on $`[[a,b]]` and strictly positive on $`[a,b]`,
$`a<b`, and let $`p\ne0` be orthogonal against $`w` to every polynomial of
lower degree. Then every nonconstant divisor of $`p` has a root in
$`[a,b]`, $`p` is squarefree and splits over $`\mathbb R`, and every root of
$`p` lies in the open interval $`(a,b)`. Consequently the monic orthogonal
polynomial $`p_n` has exactly $`n` distinct real roots, all in $`(a,b)`,
and they can be listed as $`x_0,\dots,x_{n-1}` so that the nodal polynomial
$`\prod_i(x-x_i)` equals $`p_n`.
:::

:::proof "symbolic.orthogonal_roots"
The divisor statement is the sign argument for $`\int_a^b q\,r^2w`. An
irreducible real factor
of degree two has no real root, so it cannot divide $`p`, and $`p` splits.
If $`q^2` divides $`p` with $`q` nonconstant, write $`p=q^2r`; then
$`L((qr)^2)=L(p\,r)=0`, contradicting positivity, so $`p` is squarefree. A
root at the endpoint $`a` would give $`p=(x-a)r` with
$`\int_a^b(x-a)\,r^2w=0`, but $`(x-a)w` is a weight that is positive on
the interior; the endpoint $`b` is symmetric. A monic squarefree polynomial
that splits is the product of $`x-x_i` over its distinct roots.
:::

{leanpde_figure "gauss-legendre-nodes"}

The figure lists the roots of $`p_n` for the Legendre weight, $`n=1` to
$`8`, and draws $`P_n`, the Legendre polynomial rescaled so that
$`P_n(1)=1`, for the highlighted row. The roots stay strictly inside
$`(-1,1)`, as the theorem requires, and they crowd toward the endpoints as
$`n` grows. The disc areas are the Gauss weights constructed next.

# Gaussian quadrature

The degree of exactness of a rule with $`n` nodes can never reach $`2n`.
The nodal polynomial $`\omega(x)=\prod_i(x-x_i)` has degree $`n`, so
$`\omega^2` has degree $`2n`; the rule returns $`\sum_iw_i\omega(x_i)^2=0`,
while $`\int_a^b\omega^2w>0`. Gauss's theorem says that degree $`2n-1` is
reached, for one choice of nodes only.

Why must the nodes be the roots of $`p_n`? Suppose a rule with nodes
$`x_i` is exact to degree $`2n-1`. For any $`q` of degree below $`n` the
product $`\omega q` has degree below $`2n`, and it vanishes at every node,
so

$$`\int_a^b\omega\,q\,w=Q(\omega q)=\sum_i w_i\,\omega(x_i)\,q(x_i)=0.`

Thus $`\omega` is monic of degree $`n` and orthogonal to all lower degrees,
and uniqueness forces $`\omega=p_n`. Conversely, take the nodes to be the
roots of $`p_n` and the weights interpolatory. Any $`p` of degree below
$`2n` divides as $`p=p_nq+r` with $`\deg q,\deg r<n`. The rule sees only
$`r`, since $`p_n` vanishes at the nodes, and it integrates $`r` exactly;
the integral sees only $`r` as well, since $`\int p_nq\,w=0`. So
$`Q(p)=\int_a^b p\,w`.

:::theorem "symbolic.gaussian_quadrature" (parent := "symbolic.cega") (uses := "symbolic.orthogonal_roots, symbolic.newton_cotes") (lean := "CAS.Continuum.exists_gaussian_quadrature, CAS.Continuum.exists_nodalRule_gaussian, CAS.Continuum.gaussian_exact, CAS.Continuum.gaussian_weight_pos, CAS.Continuum.interpolatory_exact")
Let $`w` be continuous on $`[[a,b]]` and strictly positive on $`[a,b]`,
$`a<b`, and let $`n\ge1`. There are $`n` distinct nodes in $`(a,b)` whose
interpolatory weights $`w_i=\int_a^b\ell_i\,w` are all strictly positive and
for which

$$`\sum_{i<n}w_i\,p(x_i)=\int_a^b p(x)\,w(x)\,dx\qquad\text{whenever }\deg p<2n.`

As a `NodalRule`, the rule is positive, has its nodes in $`[a,b]`, and is
exact to degree $`2n-1`.
:::

:::proof "symbolic.gaussian_quadrature"
Take the nodes to be the roots of $`p_n`. The interpolatory rule on $`n`
distinct nodes reproduces every polynomial of degree below $`n`. For
$`\deg p<2n`, divide by the monic nodal polynomial: the quotient term is
annihilated by the rule, because the nodal polynomial vanishes at the nodes,
and by the integral, by orthogonality; the remainder has degree below
$`n`. For the weights, apply exactness to $`\ell_i^2`, which has degree
$`2n-2`: the rule returns $`w_i`, and the integral
$`\int_a^b\ell_i^2w` is positive.
:::

The nodes determine the weights, and the weights are positive. This
positivity will give convergence for continuous integrands.

:::definition "symbolic.gaussian_rule_structure" (parent := "symbolic.cega") (uses := "symbolic.gaussian_quadrature") (lean := "CAS.Continuum.GaussianRule, CAS.Continuum.GaussianRule.value")
A Gaussian rule with $`n` nodes for the weight $`w` on $`[a,b]` is a
structure `GaussianRule a b w hw n`, where `hw` records that $`w` is
continuous on $`[[a,b]]`. It holds nodes $`x_0,\dots,x_{n-1}`, weights
$`w_0,\dots,w_{n-1}`, and four facts: the nodes are pairwise distinct, they lie
in the open interval $`(a,b)`, the weights are strictly positive, and

$$`\sum_{i<n}w_i\,p(x_i)=\int_a^b p(x)\,w(x)\,dx\qquad\text{whenever }\deg p<2n.`

Its value on a function $`f` is $`\sum_iw_if(x_i)`. For $`n=0` the rule is
empty and the exactness field says nothing, so the theorems about Gaussian
rules assume $`n>0`.
:::

Distinct nodes give the Lagrange and Hermite interpolants behind the
characterization and the remainder formula. Interior nodes let a bound
that holds on $`[a,b]` be applied at every node, and positive weights turn such
a bound into the stability and convergence estimates.

:::definition "symbolic.gaussian_rule" (parent := "symbolic.cega") (uses := "symbolic.gaussian_rule_structure, symbolic.gaussian_quadrature") (lean := "CAS.Continuum.gaussianRule, CAS.Continuum.GaussianRule.toNodalRule, CAS.Continuum.GaussianRule.sum_weights, CAS.Continuum.GaussianRule.weight_le_mass")
For $`a<b`, a weight that is strictly positive on $`[a,b]`, and $`n>0`,
`gaussianRule` is the Gaussian rule of the existence theorem, with nodes at the
roots of $`p_n` and interpolatory weights. Every Gaussian rule with $`n>0` is a
positive `NodalRule` exact to degree $`2n-1`. Exactness on the constant $`1`
makes its weights add up to $`\int_a^b w`, so each weight is at most
$`\int_a^b w`.
:::

:::theorem "symbolic.gaussian_characterization" (parent := "symbolic.cega") (uses := "symbolic.gaussian_rule, symbolic.orthogonal_polynomial") (lean := "CAS.Continuum.GaussianRule.nodal_eq_integralOrthogonalPolynomial, CAS.Continuum.GaussianRule.nodal_orthogonal, CAS.Continuum.GaussianRule.weights_eq_interpolatoryWeight")
For every Gaussian rule with $`n` nodes for a continuous weight that is
strictly positive on $`[a,b]`, the nodal polynomial $`\prod_i(x-x_i)` is the
monic orthogonal polynomial $`p_n` of $`w`, and the weight at $`x_i` is the
interpolatory weight $`\int_a^b\ell_i\,w`, the Christoffel number. A Gaussian
rule is therefore unique up to the order of its nodes.
:::

:::proof "symbolic.gaussian_characterization"
The nodal polynomial times any $`q` of degree below $`n` has degree below
$`2n` and vanishes at every node, so its integral is its rule value, zero.
Uniqueness of the monic orthogonal polynomial identifies the nodal
polynomial. For the weights, apply exactness to $`\ell_i`, which has degree
$`n-1` and takes the value $`1` at $`x_i` and $`0` at the other nodes.
:::

{leanpde_figure "gauss-exactness-limit"}

The figure shows both halves of the argument for $`n=3` and the Legendre
weight. On the left, $`p_3(x)\,x` has degree four; the rule returns zero,
and orthogonality makes the integral zero too. On the right, $`p_3^2` has
degree six; the rule still returns zero, but the integral is
$`\tfrac8{175}`. That positive number reappears as the constant in the
error formula.

The error of a Gauss rule is found by comparing $`f` with its Hermite
interpolant $`H`, the polynomial of degree below $`2n` that matches $`f` and
$`f'` at the $`n` nodes. The rule is exact on $`H` and cannot tell $`f`
from $`H`, so the error is $`\int_a^b(f-H)\,w`. The pointwise remainder is
the familiar one for interpolation, with every node counted twice:

$$`f(x)-H(x)=\frac{f^{(2n)}(\eta_x)}{(2n)!}\,\omega(x)^2
  \qquad\text{for some }\eta_x\in[a,b].`

Because $`\omega^2w\ge0`, a mean-value argument for the integral pulls the
derivative out at a single point.

:::theorem "symbolic.gaussian_remainder" (parent := "symbolic.cega") (uses := "symbolic.gaussian_characterization") (lean := "CAS.Continuum.GaussianRule.remainder_orthogonal, CAS.Continuum.GaussianRule.remainder, CAS.Continuum.GaussianRule.abs_error_le, CAS.Continuum.hermite_remainder, CAS.Continuum.hermiteInterpolant, CAS.Continuum.exists_derivative_chain_zero_of_double_zeros, CAS.Continuum.integral_eq_value_mul_of_pointwise_image")
Let $`w` be continuous on $`[[a,b]]` and strictly positive on $`[a,b]`,
$`a<b`, let $`Q` be a Gaussian rule with $`n\ge1` nodes, and let
$`f\in C^{2n}` on $`[a,b]`. There is $`\xi\in[a,b]` with

$$`\int_a^b f(x)\,w(x)\,dx-Q(f)
  =\frac{f^{(2n)}(\xi)}{(2n)!}\int_a^b \omega(x)^2\,w(x)\,dx,`

where $`\omega=\prod_i(x-x_i)` is the nodal polynomial, equal to $`p_n` by the
characterization. Here $`f^{(2n)}` is the iterated derivative within $`[a,b]`, so smoothness
is needed only on the closed interval. If $`|f^{(2n)}|\le M` on $`[a,b]`,
the error is at most $`M/(2n)!\,\int_a^bp_n^2w`.
:::

:::proof "symbolic.gaussian_remainder"
Fix $`x` away from the nodes and choose $`c` so that
$`G=f-H-c\,\omega^2` vanishes at $`x`. Then $`G` has double zeros at the $`n`
nodes and a simple zero at $`x`, $`2n+1` zeros counted with multiplicity. A
generalized Rolle theorem, proved for a chain of functions each the
derivative of the previous one on the open interval, gives a zero $`\eta_x`
of $`G^{(2n)}`. Since $`H^{(2n)}=0` and $`(\omega^2)^{(2n)}=(2n)!`, this is
the pointwise remainder. Multiply by $`w` and integrate. The continuous
function $`f^{(2n)}` takes values between its minimum and maximum on
$`[a,b]`, so the integral of $`(f-H)w` lies between those extremes times
$`\int\omega^2w`, and the intermediate value theorem produces $`\xi`.
Finally $`\omega=p_n` by the characterization.
:::

For $`n=2` and the Legendre weight the constant is
$`\int_{-1}^1p_2^2=\tfrac8{45}`. Rescaled to an interval of length $`h`,
where $`\int p_2^2` scales by $`(h/2)^5`, the formula gives error
$`f^{(4)}(\xi)\,h^5/4320`, the same constant as the sharp two-point
Gauss–Legendre certificate, which is proved by a Peano kernel. For $`n=3` the
constant on
$`[-1,1]` is $`\tfrac8{175}/6!=\tfrac1{15750}`.

The first four Gauss–Legendre rules have closed forms in radicals. On
$`[-1,1]` the one-point rule is the midpoint rule with weight $`2`, the
two-point rule has nodes $`\pm1/\sqrt3` and weights $`1`, the three-point rule
has nodes $`0,\pm\sqrt{3/5}` and weights $`\tfrac89,\tfrac59`, and the
four-point rule has nodes $`\pm\sqrt{(15\mp2\sqrt{30})/35}` with weights
$`(18\pm\sqrt{30})/36`, the larger weight at the inner pair. The library stores
them in the normalized convention on $`[0,1]`, checks the moments degree by
degree, and then identifies each with the orthogonal-polynomial
construction.

:::theorem "symbolic.gauss_legendre_rules" (parent := "symbolic.cega") (uses := "symbolic.gaussian_characterization, symbolic.polynomial_quadrature_exactness") (lean := "CAS.Continuum.Legendre.four_nodal_eq, CAS.Continuum.Legendre.three_nodal_eq, CAS.Continuum.Legendre.two_nodal_eq, CAS.Continuum.Legendre.one_nodal_eq, CAS.Continuum.Legendre.three_exact, CAS.Continuum.Legendre.four_exact, CAS.Continuum.Legendre.monicPolynomial, CAS.Continuum.Legendre.threeGaussian, CAS.Continuum.Legendre.fourGaussian, CAS.Continuum.GaussianRule.value_eq_gaussLegendreTwoRule_valueOn, CAS.Continuum.GaussianRule.nodes_eq_gaussLegendreTwo")
The normalized three- and four-point Gauss–Legendre rules, written in
radicals, are exact through degrees five and seven. Transported to
$`[-1,1]`, the midpoint rule, the two-point rule, and these two rules are
Gaussian rules for the unit weight, and the nodal polynomial of the
$`n`-point rule is the monic Legendre polynomial of degree $`n`, defined as
the monic orthogonal polynomial of that weight, for $`n=1,2,3,4`. For
$`n=2` and any $`a<b`, every Gaussian rule for the unit weight on $`[a,b]`
has the transported two-point nodes and weights and the same value as the
two-point `QuadratureRule`.
:::

:::proof "symbolic.gauss_legendre_rules"
Exactness through degree $`2n-1` is a finite list of moment identities, each
checked by normal-form arithmetic using $`(\sqrt{3/5})^2=\tfrac35` or the
squares of the four-point radicals. Positivity of the weights and the ordering
of the nodes are inequalities between radicals. The characterization theorem
then identifies each nodal polynomial with the monic Legendre polynomial,
and for $`n=2` it pins down the nodes, whose weights are then fixed by
exactness.
:::

Beyond four points the nodes are no longer convenient radicals, and the
library certifies them instead. A sparse rational polynomial $`p` with
$`\int_{-1}^1p\,x^k\,dx=0` for $`k<n`, a condition checked in rational
arithmetic from the moments of $`x^k`, is the monic Legendre polynomial of
degree $`n` as soon as it is monic of degree $`n`. Its roots are isolated by
certified brackets ({bpref "symbolic.unique_root_bracket"}[root brackets]): a rational
interval with a sign change at the ends and a derivative enclosure of fixed
sign, so exactly one root lies inside. Ordered disjoint brackets inside
$`(-1,1)` then define a Gaussian rule at any order $`n`, with no stored table
of nodes.

:::theorem "symbolic.gauss_legendre_root_certificates" (parent := "symbolic.cega") (uses := "symbolic.gaussian_rule, symbolic.gaussian_characterization, symbolic.unique_root_bracket") (lean := "CAS.Continuum.Legendre.RootCertificates.nodal_eq, CAS.Continuum.Legendre.RootCertificates.orthogonal_of_shiftedMoments, CAS.Continuum.Legendre.RootCertificates.nodes_mem, CAS.Continuum.Legendre.RootCertificates.nodes_strictMono, CAS.Continuum.Legendre.RootCertificates.rule, CAS.Continuum.Legendre.RootCertificates.shiftedMoment")
Let $`p` be a sparse rational polynomial and let $`n` valid root brackets for
$`p` be ordered, each strictly to the left of the next. The bracketed roots
are strictly increasing and lie in their brackets. If $`p` is monic of degree
$`n` over $`\mathbb R`, its nodal polynomial on these roots is $`p` itself.
If moreover the brackets lie inside $`(-1,1)` and the rational moments
$`\int_{-1}^1p(x)x^k\,dx` vanish for $`k<n`, the roots are the nodes of a
Gaussian rule for the unit weight on $`[-1,1]`, with the interpolatory
weights.
:::

:::proof "symbolic.gauss_legendre_root_certificates"
Each valid bracket contains a unique root, and the ordering of the brackets
orders the roots. A monic polynomial of degree $`n` with $`n` distinct roots
is the product of the corresponding linear factors. The vanishing moments,
extended linearly to every $`q` of degree below $`n`, make the nodal
polynomial orthogonal to lower degrees; the Gaussian exactness and weight
positivity arguments then apply without change.
:::

The weights of a certified rule are enclosed from the same brackets. At a
simple root $`r` of $`p` the Lagrange basis polynomial is
$`p(x)/\bigl((x-r)\,p'(r)\bigr)`, so the Christoffel number is

$$`w_r=\frac{1}{p'(r)}\int_{-1}^1\frac{p(x)}{x-r}\,dx.`

Synthetic division writes the integral as a polynomial in $`r` with
rational coefficients, so the weight is a rational function of the single
root $`r`, and interval evaluation over the bracket encloses it.

:::theorem "symbolic.gauss_legendre_weight_certificates" (parent := "symbolic.cega") (uses := "symbolic.gauss_legendre_root_certificates, symbolic.interval_bridge") (lean := "CAS.Continuum.Legendre.RootCertificates.weight_mem, CAS.Continuum.Legendre.RootCertificates.interpolatoryWeight_eq_quotient, CAS.Continuum.Legendre.RootCertificates.weightInterval_sound, CAS.Continuum.Legendre.RootCertificates.integral_quotient, CAS.Continuum.Legendre.RootCertificates.weightInterval")
If the nodal polynomial of a family of nodes is $`p` and $`r_i` is a root,
the interpolatory weight at $`r_i` is $`\tilde p(r_i)/p'(r_i)`, where
$`\tilde p` is the rational polynomial `integratedQuotient p` with
$`\tilde p(r)=\int_{-1}^1p(x)/(x-r)\,dx`. For a valid bracket the rational
interval `weightInterval p bracket` contains this quotient at the bracketed
root, and each Christoffel number of the certified rule lies in the interval
computed from its own bracket.
:::

:::proof "symbolic.gauss_legendre_weight_certificates"
The Lagrange basis polynomial at a node is the nodal polynomial divided by
$`x-r_i` and by the nodal weight, which equals $`p'(r_i)` for a simple root.
The division by $`x-r` is carried out monomial by monomial through
$`(x^k-r^k)/(x-r)=\sum_{j<k}x^jr^{k-1-j}`, and integrating the result term
by term gives $`\tilde p`. The bracket's direction fixes the sign of
$`p'` on it, so dividing the numerator enclosure by the derivative enclosure
is sound.
:::

# Convergence of positive rules

The error formula needs $`2n` derivatives, and the constant
$`M_{2n}/(2n)!` need not stay small for a function that is merely
continuous. A different argument gives convergence for every continuous
$`f`, and it uses exactly one property beyond exactness: positive weights.

:::theorem "symbolic.positive_rule_convergence" (parent := "symbolic.cega") (uses := "symbolic.quadrature_rule_stability, symbolic.nodal_rule") (lean := "CAS.Continuum.NodalRule.tendsto_eval_of_positive, CAS.Continuum.NodalRule.abs_eval_sub_integral_le_of_polynomial_approx, CAS.Continuum.QuadratureRule.tendsto_valueOn_of_nonneg")
Let $`w` be continuous on $`[a,b]` and let $`Q_n` be rules with nonnegative
weights and nodes in $`[a,b]`, where $`Q_n` integrates every polynomial of
degree at most $`d_n` exactly against $`w` and $`d_n\to\infty`. Then
$`Q_n(f)\to\int_a^b f\,w` for every $`f` continuous on $`[a,b]`. This is the
theorem of Pólya and Steklov. The same statement holds for normalized rules
with nonnegative weights transported to $`[a,b]`.
:::

:::proof "symbolic.positive_rule_convergence"
Exactness on constants makes the weights of $`Q_n` sum to $`\int_a^b w`. If a
polynomial $`p` of degree at most $`d_n` is within $`\delta` of $`f` on
$`[a,b]`, positivity bounds $`|Q_n(f)-Q_n(p)|` by $`\delta\int_a^b w`, and
$`|\int_a^b (p-f)w|` is at most $`\delta\int_a^b|w|`. Since $`Q_n(p)` is the
integral of $`p w`, the error on $`f` is at most
$`\delta(\int_a^b w+\int_a^b|w|)`, a bound independent of $`n`. The
Weierstrass theorem supplies $`p` for every $`\delta>0`, and $`d_n\to\infty`
makes $`p` admissible for all large $`n`.
:::

A Gauss rule with $`n+1` nodes is positive, has its nodes in $`[a,b]`, and
has degree $`2n+1`, so the theorem applies directly.

:::theorem "symbolic.gaussian_convergence" (parent := "symbolic.cega") (uses := "symbolic.positive_rule_convergence, symbolic.gaussian_rule") (lean := "CAS.Continuum.gaussian_rules_converge, CAS.Continuum.GaussianRule.tendsto_value")
Let $`w` be continuous on $`[[a,b]]` with $`a\le b`, and for each $`n` let
$`Q_n` be a Gaussian rule with $`n+1` nodes for $`w`. Then
$`Q_n(f)\to\int_a^b f\,w` for every $`f` continuous on $`[a,b]`. In
particular the rules of the existence theorem converge whenever $`w` is
strictly positive and $`a<b`.
:::

:::proof "symbolic.gaussian_convergence"
The rules are positive with nodes in $`[a,b]` and are exact to degree
$`2(n+1)-1`, which tends to infinity. Apply the Pólya–Steklov theorem.
:::

{leanpde_figure "positive-rule-convergence"}

Positivity is not a technicality. The figure integrates the Runge function
$`1/(1+25x^2)` over $`[-1,1]` with the closed Newton–Cotes rule and the
Gauss–Legendre rule, $`n=2,\dots,24` points. Both are exact to degree at
least $`n-1`, so both would converge if only exactness mattered. Newton–Cotes
weights become negative at nine points and from eleven points on, the sum
$`\sum_i|w_i|` grows geometrically, and the error grows with it. The
Gauss weights stay positive, their absolute sum is always $`2`, and the error
decreases steadily. The divergence of Newton–Cotes is a classical
computation shown here for contrast; the library proves the positive side.

# Panel rules of any order

For a smooth integrand the practical way to reduce error is to cut the
interval into $`N` equal panels and apply a low-order rule on each. The only
information the composite construction needs about the local rule is a
one-panel bound of the form

$$`\left\|\int_a^b f-Q(f)\right\|\le\frac{M\,(b-a)^{m+1}}{D}
  \qquad\text{whenever }\|f^{(m)}\|\le M\text{ on }[a,b].`

Summing $`N` such bounds over panels of length $`(b-a)/N` gives
$`C(b-a)^{m+1}/(DN^m)`. The library records the pair (rule, $`D`) with the
proof of the one-panel bound as a `PanelRule m`, and builds composite
certificates, tolerance planning, and adaptive bisection once for every
order $`m`.

:::definition "symbolic.panel_rule" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate, symbolic.normalized_quadrature_rule") (lean := "CAS.Continuum.PanelRule, CAS.Continuum.PanelRule.composite, CAS.Continuum.PanelRule.composite_error, CAS.Continuum.PanelRule.search, CAS.Continuum.simpsonRule.fourthOrder, CAS.Continuum.gaussLegendreTwoRule.fourthOrder")
A panel rule of order $`m` is a normalized rule $`Q` with a positive
constant $`D` and a proof that, on every ordered interval $`[a,b]`, every
$`f\in C^m[a,b]` with $`\|f^{(m)}\|\le M` there satisfies
$`\|\int_a^b f-Q(f)\|\le M(b-a)^{m+1}/D`. Its composite certificate on $`N>0` equal panels, given a
panelwise derivative bounder with common bound $`C`, has error budget
$`C(b-a)^{m+1}/(DN^m)`. Simpson's rule and the two-point Gauss–Legendre rule
are panel rules of order four.
:::

:::theorem "symbolic.second_order_panel_rules" (parent := "symbolic.cega") (uses := "symbolic.panel_rule") (lean := "CAS.Continuum.norm_integral_sub_trapezoidRule_valueOn_le, CAS.Continuum.norm_integral_sub_midpointRule_valueOn_le, CAS.Continuum.trapezoidRule.secondOrder, CAS.Continuum.midpointRule.secondOrder, CAS.Continuum.trapezoidRule.exactUpTo_one, CAS.Continuum.midpointRule.exactUpTo_one")
On an ordered interval, for $`f\in C^2[a,b]` with
$`\|f''\|\le C` there,

$$`\left\|\int_a^bf-\frac{b-a}2\bigl(f(a)+f(b)\bigr)\right\|
  \le\frac{C(b-a)^3}{12},\qquad
  \left\|\int_a^bf-(b-a)f\!\left(\tfrac{a+b}2\right)\right\|
  \le\frac{C(b-a)^3}{24}.`

Both rules are exact through degree one, and they are panel rules of order
two with $`D=12` and $`D=24`.
:::

:::proof "symbolic.second_order_panel_rules"
Two integrations by parts write each error as $`\int_a^bK(t)f''(t)\,dt`.
For the trapezoid rule the kernel is $`(t-a)(b-t)/2\ge0`, of mass
$`(b-a)^3/12`. For the midpoint rule it is $`(t-a)^2/2` on the left half and
$`(b-t)^2/2` on the right, of mass $`(b-a)^3/24`. Bound $`f''` by $`C`.
:::

{leanpde_figure "composite-error-decay"}

The figure measures the composite error for $`\int_0^1e^x\,dx` against the
panel count on logarithmic axes. On the left are the two second-order rules,
on the right Simpson's rule and the two-point Gauss rule. Each measured error
sits below its dashed proved bound $`e/(DN^m)`, and each curve has slope
$`-m`, so halving the panel width divides the error by $`4` or by $`16`. The
constants fall in the order the denominators $`12`, $`24`, $`2880`, $`4320`
predict: at every panel count the midpoint error is about half the trapezoid
error, and the Gauss error about two thirds of Simpson's.

Because the budget is an explicit function of $`N`, the number of panels
needed for a tolerance $`\varepsilon` can be computed in advance. The planner
never evaluates the integrand; it needs only the derivative bound $`C`.

:::theorem "symbolic.panel_rule_planning" (parent := "symbolic.cega") (uses := "symbolic.panel_rule") (lean := "CAS.Continuum.PanelRule.compositeToTolerance_sound_le, CAS.Continuum.PanelRule.compositeToTolerance_error_le, CAS.Continuum.PanelPlan.uniformCompositeError_le, CAS.Continuum.PanelPlan.errorConstant_div_requiredPanels_pow_le, CAS.Continuum.PanelPlan.requiredPanels, CAS.Continuum.PanelRule.compositeToTolerance")
Let $`m\ne0`, $`D>0`, $`a\le b`, $`C\ge0` and $`\varepsilon>0`, put
$`B=C(b-a)^{m+1}/D`, and let
$`N=\max(1,\lceil(B/\varepsilon)^{1/m}\rceil)`. Then
$`B/N^m\le\varepsilon`. Consequently, for a panel rule of
order $`m`, an integrand in $`C^m[a,b]`, $`a<b`, and a derivative bounder whose
bound on every subinterval is at most $`C`, the composite certificate on the
planned mesh has error budget at most $`\varepsilon`, and its value is within
$`\varepsilon` of $`\int_a^bf`.
:::

:::proof "symbolic.panel_rule_planning"
The ceiling gives $`N\ge(B/\varepsilon)^{1/m}`, and raising both sides to the
power $`m` gives $`N^m\ge B/\varepsilon`. The composite budget is
$`B/N^m`, and certificate soundness bounds the actual error by the budget.
:::

For $`m=4` we use the classical one-panel constants for Simpson's rule and the
two-point Gauss rule. We prove their composite bounds and choose meshes with
planners in exact rational arithmetic that run inside Lean.

:::theorem "symbolic.simpson_fourth_order_certificate" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate, symbolic.polynomial_quadrature_exactness") (lean := "CAS.Continuum.norm_integral_sub_simpsonRule_valueOn_le, CAS.Continuum.simpsonRule.fourthOrderCert")
For an ordered interval $`[a,b]`, a $`C^4` scalar integrand, and a bound $`C`
on its fourth within-derivative, the Peano-kernel argument gives the classical
one-panel Simpson estimate
$`\lVert\int_a^b f-S(f)\rVert\le C(b-a)^5/2880`, returned as a
`QuadratureCert`.
:::

:::proof "symbolic.simpson_fourth_order_certificate"
Represent the Simpson error as the integral of the fourth derivative against
its Peano kernel, whose two polynomial pieces live on $`[a,(a+b)/2]` and
$`[(a+b)/2,b]`; four integrations by parts produce it, and cubic exactness
cancels all boundary polynomial terms. The kernel has fixed sign and exact
mass $`(b-a)^5/2880`. Bounding the fourth derivative by $`C` gives the stated
norm estimate.
:::

:::theorem "symbolic.gauss_legendre_fourth_order_certificate" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate, symbolic.polynomial_quadrature_exactness") (lean := "CAS.Continuum.norm_integral_sub_gaussLegendreTwoRule_valueOn_le, CAS.Continuum.gaussLegendreTwoRule.fourthOrderCert")
For an ordered interval $`[a,b]`, a $`C^4` scalar integrand, and a bound $`C`
on its fourth within-derivative, the two-point Gauss–Legendre Peano kernel is
nonnegative and has mass $`(b-a)^5/4320`. Consequently
$`\lVert\int_a^b f-G_2(f)\rVert\le C(b-a)^5/4320`, with the irrational
nodes treated exactly; the estimate is returned as a `QuadratureCert`.
:::

:::proof "symbolic.gauss_legendre_fourth_order_certificate"
Use cubic exactness to express the rule error through the fourth-order Peano
kernel. The exact two Gauss nodes make the boundary terms vanish, and the
kernel is nonnegative with mass $`(b-a)^5/4320`. The uniform fourth-derivative
bound therefore yields the claimed certificate.
:::

:::theorem "symbolic.uniform_composite_fourth_order" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate") (lean := "CAS.Continuum.weightedSum_uniformCompositeTerms, CAS.Continuum.QuadratureCert.uniformCompositeFourthOrder")
Any local quadrature constructor with certified error
$`C(v-u)^5/D` can be accumulated over $`N>0` equal panels. The generic theorem
produces error $`C(b-a)^5/(DN^4)` and a canonical flattened ordered term list
whose exact weighted sum equals the composite value. Smoothness is assumed
only on the root interval, and one `IteratedDerivativeBounderOn` supplies each
panel's within-derivative bound together with a common upper bound $`C`.
Analytic composition and finite-precision execution therefore share one
rule-independent boundary.
:::

:::proof "symbolic.uniform_composite_fourth_order"
Split the interval into $`N` equal panels and add the local integral
identities. The triangle inequality sums the local errors. Since each panel
has length $`(b-a)/N`, the sum of $`N` terms
$`C((b-a)/N)^5/D` simplifies to $`C(b-a)^5/(DN^4)`. Flattening the panel
term lists preserves the same finite weighted sum.
:::

:::theorem "symbolic.composite_simpson_quadrature" (parent := "symbolic.cega") (uses := "symbolic.simpson_fourth_order_certificate, symbolic.uniform_composite_fourth_order") (lean := "CAS.Continuum.QuadratureCert.compositeSimpson_error, CAS.Continuum.QuadratureCert.compositeSimpson")
For $`N>0` equal Simpson panels, an integrand that is $`C^4` on $`[a,b]`,
and certified panelwise fourth within-derivative bounds at most $`C`, summing
the sharp local certificates gives
$`\lVert\int_a^b f-S_N(f)\rVert\le C(b-a)^5/(2880N^4)`.
Each panel consists of the usual two half-subintervals.
:::

:::proof "symbolic.composite_simpson_quadrature"
Instantiate the generic composite theorem with the sharp one-panel Simpson
certificate and denominator $`2880`. The common fourth-derivative bound
dominates every panel certificate, and the generic error calculation gives
the displayed $`N^{-4}` estimate.
:::

:::theorem "symbolic.composite_gauss_legendre_quadrature" (parent := "symbolic.cega") (uses := "symbolic.gauss_legendre_fourth_order_certificate, symbolic.uniform_composite_fourth_order") (lean := "CAS.Continuum.QuadratureCert.compositeGaussLegendreTwo_error, CAS.Continuum.QuadratureCert.compositeGaussLegendreTwo")
For $`N>0` equal two-point Gauss–Legendre panels and the same root-local
smoothness and panelwise derivative-bound hypotheses, the composite certificate has error
$`C(b-a)^5/(4320N^4)`. Its ordered term list retains the two exact irrational
nodes on every panel and is proved equal to the analytic composite value.
:::

:::proof "symbolic.composite_gauss_legendre_quadrature"
Instantiate the uniform composite construction with the sharp two-point
Gauss–Legendre certificate and denominator $`4320`. Summing the panel
certificates gives the global error, while the generic flattening theorem
retains the exact ordered nodes and weights.
:::

:::theorem "symbolic.composite_simpson_terms" (parent := "symbolic.cega") (uses := "symbolic.normalized_quadrature_rule, symbolic.composite_simpson_quadrature, symbolic.uniform_composite_fourth_order") (lean := "CAS.Continuum.weightedSum_compositeSimpsonTerms")
The composite rule has a canonical flattened list of ordered weighted terms.
Its exact-real weighted sum is proved equal to the analytic composite Simpson
value. Verified rational, interval, or floating-point evaluators can therefore
evaluate the same term list.

For the canonical panel-major list $`T_N(f,a,b)`,

$$`\operatorname{weightedSum}\!\left(T_N(f,a,b)\right)
  =S_N(f;[a,b]).`

The canonical term list fixes the nodes and accumulation order; this equality
certifies its exact-real value. Equality of sums alone would not fix an order.
:::

:::proof "symbolic.composite_simpson_terms"
Unfold the uniform composite rule panel by panel. On each panel the three
listed weighted terms are definitionally the transported Simpson value.
Induction over the panel list shows that flattening and then taking the
weighted sum equals the sum of the analytic panel values.
:::

:::theorem "symbolic.rational_uniform_composition" (parent := "symbolic.cega") (uses := "symbolic.rational_rule_compilation, symbolic.uniform_composite_fourth_order") (lean := "CAS.Continuum.RationalQuadratureRule.uniformComposite_toQuadratureRule_termsOn, CAS.Continuum.RationalQuadratureRule.uniformComposite_toQuadratureRule_valueOn")
Every normalized exact-rational rule compiles uniformly to `N > 0` panels by
mapping a source term $`(w,\xi)` on panel $`k` to
$`(w/N,(k+\xi)/N)`. The cast rule is proved equal term-for-term to the
canonical analytic uniform-composite list. This preserves both the exact-real
value and the panel-major accumulation schedule used by verified numerical
backends.
:::

:::proof "symbolic.rational_uniform_composition"
Map every rational source node and weight by the affine panel formula and cast
the result to the reals. Field identities show term by term that the cast node
and weight equal those of the analytic transported rule. Mapping this equality
over panels and flattening proves equality of both schedules and values.
:::

:::theorem "symbolic.real_fourth_order_tolerance_plan" (parent := "symbolic.cega") (uses := "symbolic.uniform_composite_fourth_order") (lean := "CAS.Continuum.PanelPlan.errorConstant_div_requiredPanels_pow_le")
Let $`B=C(b-a)^5/D`. For a positive tolerance, choosing
$`N=\max(1,\lceil(B/\mathrm{tolerance})^{1/4}\rceil)` proves
$`B/N^4\leq\mathrm{tolerance}`. This is the case $`m=4` of the planner for an
error model $`B/N^m` of any order $`m>0`, and it is the rule-independent
planner behind every fourth-order uniform composite rule.
:::

:::proof "symbolic.real_fourth_order_tolerance_plan"
If $`B<0` the bound holds for every $`N`. Otherwise the ceiling construction gives
$`N\geq(B/\tau)^{1/4}` and $`N\geq1`. Positivity permits raising the first
inequality to the fourth power, yielding $`N^4\geq B/\tau`. Rearranging with
$`\tau>0` proves $`B/N^4\leq\tau`.
:::

:::theorem "symbolic.rational_fourth_order_tolerance_plan" (parent := "symbolic.cega") (uses := "symbolic.real_fourth_order_tolerance_plan") (lean := "CAS.Continuum.PanelPlan.div_ratRequiredPanels_pow_le")
For exact rational error data, the executable planner rounds
$`B/\mathrm{tolerance}` upward and takes one more than the integer fourth root
of the result (Mathlib's `Nat.nthRoot 4`). The resulting positive natural panel
count satisfies the same fourth-order inequality without evaluating a
noncomputable real root.
:::

:::proof "symbolic.rational_fourth_order_tolerance_plan"
Mathlib's `Nat.lt_pow_nthRoot_add_one` says that one more than the integer
fourth root of $`\lceil B/\tau\rceil` has fourth power above it, so the chosen
natural's fourth power is at least the exact rational ratio. Rearranging with
$`\tau>0` gives the same tolerance estimate as the real planner.
:::

:::theorem "symbolic.simpson_executable_tolerance_plan" (parent := "symbolic.cega") (uses := "symbolic.rational_fourth_order_tolerance_plan, symbolic.composite_simpson_quadrature") (lean := "CAS.Continuum.PanelPlan.div_ratRequiredPanels_pow_le")
Substituting the sharp Simpson denominator $`D=2880` into the executable
rational planner produces a panel count whose composite error bound
$`C(b-a)^5/(2880N^4)` is at most the requested rational tolerance.
:::

:::proof "symbolic.simpson_executable_tolerance_plan"
Apply the rational fourth-order planner with denominator $`2880`, the error
constant $`B=C(b-a)^5/2880` of the composite Simpson theorem: its panel count
$`N` satisfies $`B/N^4\leq\tau` in exact rational arithmetic.
:::

:::theorem "symbolic.gauss_legendre_executable_tolerance_plan" (parent := "symbolic.cega") (uses := "symbolic.rational_fourth_order_tolerance_plan, symbolic.composite_gauss_legendre_quadrature") (lean := "CAS.Continuum.PanelPlan.div_ratRequiredPanels_pow_le")
Substituting the two-point Gauss–Legendre denominator $`D=4320` gives the
corresponding executable panel count, whose composite error bound
$`C(b-a)^5/(4320N^4)` is at most the requested rational tolerance.
:::

:::proof "symbolic.gauss_legendre_executable_tolerance_plan"
Apply the same executable fourth-order planner with denominator $`4320`, the
error constant of the composite two-point Gauss–Legendre theorem: its panel
count $`N` satisfies $`C(b-a)^5/(4320N^4)\leq\tau` in exact rational arithmetic.
:::

:::theorem "symbolic.fourth_order_tolerance_certificates" (parent := "symbolic.cega") (uses := "symbolic.real_fourth_order_tolerance_plan, symbolic.composite_simpson_quadrature, symbolic.composite_gauss_legendre_quadrature") (lean := "CAS.Continuum.PanelRule.compositeToTolerance_sound_le, CAS.Continuum.simpsonRule.fourthOrder, CAS.Continuum.gaussLegendreTwoRule.fourthOrder")
Given root-interval smoothness and certified panelwise fourth-derivative
bounds, the planned Simpson and two-point Gauss–Legendre constructors return
ordinary `QuadratureCert`s whose semantic error is at most the user's positive
tolerance. The public conclusion refers only to the integral, computed rule
value, and tolerance; panel selection remains an internal construction.

For either planned fourth-order rule $`Q_{N(\tau)}`,

$$`\left|\int_a^b f(x)\,dx-Q_{N(\tau)}(f)\right|
  \leq\tau.`
:::

:::proof "symbolic.fourth_order_tolerance_certificates"
The planner chooses a positive panel count whose formula is below
$`\tau`. Build the corresponding composite Simpson or Gauss–Legendre
certificate from the supplied smoothness and derivative bounds, then compose
its analytic error estimate with the planner inequality.
:::

:::definition "symbolic.trapezoidal_quadrature" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate") (lean := "CAS.Continuum.QuadratureCert.trapezoidal")
Mathlib's composite trapezoidal rule is exposed through the common certificate
interface. Assume $`f` is $`C^2` on $`S=[\min(a,b),\max(a,b)]` and
$`|D^2_S f(x)|\leq\zeta` for every real $`x`, where $`D^2_S` denotes the
second iterated within-derivative. For $`N>0` subintervals the error is at most
$`|b-a|^3\zeta/(12N^2)`.
:::

:::theorem "symbolic.tolerance_planning" (parent := "symbolic.cega") (uses := "symbolic.trapezoidal_quadrature") (lean := "CAS.Continuum.QuadratureCert.trapezoidalToTolerance_sound_le")
Under these same regularity and derivative-bound hypotheses, for a positive
tolerance the checked planner chooses
$`N=\max(1,\lceil\sqrt{B/\mathrm{tolerance}}\rceil)` with
$`B=|b-a|^3\zeta/12`. The bound forces $`\zeta\ge 0`, and the resulting composite trapezoidal
certificate has error at most the requested tolerance. The square-root choice
retains the standard $`O(\mathrm{tolerance}^{-1/2})` mesh scaling.
:::

:::proof "symbolic.tolerance_planning"
The ceiling square-root choice ensures $`N^2\geq B/\tau` and $`N>0`.
Rearranging gives $`B/N^2\leq\tau`; substituting the trapezoidal error
constant $`B=|b-a|^3\zeta/12` into the composite trapezoidal certificate
proves the result.
:::

:::theorem "symbolic.adaptive_quadrature" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate, symbolic.trapezoidal_quadrature") (lean := "CAS.Continuum.QuadratureTree.sound")
A `QuadratureTree` records a rule-independent binary subdivision. Each leaf
contains an ordinary local quadrature certificate and integrability evidence;
adjacent children compose by interval-integral additivity. The root therefore
certifies the sum of all leaf values with the sum of their error budgets. An
adaptive tactic or external checker may choose the tree; soundness does not
depend on that choice.

If $`\mathcal L(T)` is the set of leaves, then the root certificate states

$$`\left\|\int_a^b f(x)\,dx
  -\sum_{\ell\in\mathcal L(T)}Q_\ell\right\|
  \leq\sum_{\ell\in\mathcal L(T)}E_\ell.`
:::

:::proof "symbolic.adaptive_quadrature"
Induct on the binary tree. A leaf is exactly its stored local certificate. At
a branch, interval-integral additivity splits the root integral across the two
adjacent children; apply the two inductive estimates and the triangle
inequality. Their values and budgets add, giving the recursively stored root
certificate.
:::
