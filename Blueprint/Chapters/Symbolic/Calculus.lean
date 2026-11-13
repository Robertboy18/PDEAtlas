/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.Exact
import PDE.Symbolic.Calculus.PointwiseResidualSemantics
import PDE.Symbolic.ClosedForm.Differential.Equation
import CAS.Integration

/-!
# Symbolic calculus

Verified differentiation, integration, and analytic bridge theorems.
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
#doc (Manual) "Symbolic Calculus and Analytic Bridges" =>

:::group "symbolic.calculus"
Symbolic calculus
:::

For a scalar field $`u`, the coordinate derivative is
$`\partial_i u(x)=Du(x)[e_i]`: evaluate its Fréchet derivative on the
$`i`th basis vector. A symbolic derivative must recover this same linear
approximation. The partial-derivative bridge proves that it does, under the domain
conditions of the expression being differentiated. For example,
$`\partial_x\log(x^2+y^2)=2x/(x^2+y^2)` is valid whenever
$`(x,y)\ne(0,0)`; neither coordinate has to be nonzero on its own.

:::theorem "symbolic.partial_derivative_bridge" (parent := "symbolic.calculus") (uses := "symbolic.expression") (lean := "CAS.Verified.Expr.partialDeriv_eval_eq") (tags := "provenance:leanpde")
At every point satisfying the generated validity conditions, symbolic
differentiation in coordinate $`i` agrees with our analytic Euclidean
partial derivative:
$`(\operatorname{diff}_i e)^\sharp(x)=\partial_i(e^\sharp)(x)`.
:::

:::proof "symbolic.partial_derivative_bridge"
Structural induction on the expression constructs its Fréchet derivative
using the analytic sum, product, quotient, power, and elementary chain rules.
The validity hypotheses discharge each rule's domain conditions. Evaluating
the resulting continuous linear map on $`e_i` gives exactly the evaluated
symbolic derivative, hence the stated coordinate identity.
:::

:::theorem "symbolic.regularity_bridge" (parent := "symbolic.calculus") (uses := "symbolic.expression, symbolic.partial_derivative_bridge") (lean := "CAS.Verified.Expr.contDiffAt_eval, CAS.Verified.Expr.differentiableAt_eval, CAS.Verified.Expr.contDiffOn_eval_paramEmbed, CAS.Verified.Expr.contDiff_eval_paramEmbed, CAS.Verified.Expr.contDiff_eval_lineEmbed, CAS.Verified.Expr.differentiable_eval_lineEmbed") (tags := "provenance:leanpde")
The validity predicate that justifies one symbolic derivative also certifies
regularity of every order. At a point where `ValidAt` holds, evaluation of a
reflected expression is $`C^m` for every smoothness order $`m`, the analytic
order included, because each constructor is interpreted by an elementary
function that Mathlib proves smooth of every order away from its
singularities; the `On` and global forms assume validity at every point of
the set or the space. The theorems are stated for the two conventions of the
theorem-facing tactics, functions on $`\mathbb R^n` and functions on
$`\mathbb R` with frozen parameters, and they are what `cas` applies
to a `DifferentiableAt`, `Differentiable`, `ContDiffAt`, `ContDiffOn`, or
`ContDiff` goal:

$$`\operatorname{ValidAt}(x,e)
  \quad\Longrightarrow\quad
  e^\sharp\text{ is }C^m\text{ at }x
  \qquad\text{for every }m\in\{0,1,2,\ldots,\infty,\omega\}.`
:::

:::proof "symbolic.regularity_bridge"
Structural induction on the expression. Constants and coordinate projections
are smooth; sums, products, and negations preserve `ContDiffAt`; quotients,
logarithms, square roots, real powers, and the inverse sine and cosine are
smooth at every point satisfying the validity clause of their constructor, by
Mathlib's `ContDiffAt` lemmas for the elementary functions and the field
operations; the remaining elementary functions are smooth everywhere. The derivative bridge also gives differentiability, and the set and global
forms quantify these pointwise statements over their domain.
:::

:::theorem "symbolic.vector_calculus_bridge" (parent := "symbolic.calculus") (lean := "CAS.Verified.Expr.closedGradient_eval_eq_gradient, CAS.Verified.Expr.closedLaplacian_eval_eq_laplacian, CAS.Verified.Expr.closedDivergence_eval_eq_divergence, CAS.Verified.Expr.closedCurl3_zero_eval_eq_partialDeriv, CAS.Verified.Expr.closedCurl3_one_eval_eq_partialDeriv, CAS.Verified.Expr.closedCurl3_two_eval_eq_partialDeriv") (tags := "provenance:leanpde")
At a point where the scalar inputs being differentiated are valid, the
coordinatewise bridge gives gradient, divergence, and three-dimensional curl
formulas. The Laplacian bridge additionally assumes validity of every first
symbolic partial at that point. Hessians, Jacobians, symmetric
gradients, tensor divergence, and vector Laplacians use the same finite-indexed
construction. In particular,
$`(\nabla_{\mathrm{sym}}e)^\sharp(x)=\nabla(e^\sharp)(x)`,
$`(\Delta_{\mathrm{sym}}e)^\sharp(x)=\Delta(e^\sharp)(x)`,
$`(\operatorname{div}_{\mathrm{sym}}F)^\sharp(x)=\operatorname{div}(F^\sharp)(x)`,
and
$`(\operatorname{curl}_{\mathrm{sym}}F)^\sharp(x)=\operatorname{curl}(F^\sharp)(x)`.
:::

:::proof "symbolic.vector_calculus_bridge"
For each coordinate, {uses "symbolic.partial_derivative_bridge"}[] identifies
evaluation of the reflected partial derivative with the corresponding
analytic derivative. The reflected gradient is the vector of these
coordinates, divergence is their finite sum, the Laplacian is the sum of the
diagonal second derivatives, and curl is the stated alternating combination.
Function extensionality and finite-sum congruence assemble the coordinate
identities into the four displayed operator identities.

For the Laplacian, applying the first-derivative identity only at $`x`
would not suffice: two functions can agree at one point and have different
derivatives there. Validity persists on a neighborhood of $`x`, so the
analytic first partial and the evaluated symbolic first partial agree
throughout that neighborhood. Their derivatives at $`x` therefore agree.
Validity of the first symbolic partial justifies the second application of
the derivative bridge. These are sufficient conditions on the intermediate
formulas; the largest domain of smoothness can be bigger.
:::

:::theorem "symbolic.advection_bridge" (parent := "symbolic.calculus") (lean := "CAS.advectionIntegrand_eval_eq_advectiveDerivative, CAS.convectiveDerivative_eval_eq_advectiveDerivative, CAS.transportResidualIntegrand_eval_eq_advectiveDerivative_sub") (uses := "symbolic.vector_calculus_bridge, foundations.operators.advection") (tags := "provenance:leanpde")
If the advected scalar expression is valid at the evaluation point,
checked symbolic advection evaluates directly to our analytic
`advectiveDerivative`. The componentwise convection and source-subtracted
transport residual theorems use the same bridge, so later proofs need not
depend on the reflected evaluator's coordinate-sum representation:
$`\operatorname{Adv}(b^\sharp,u^\sharp)(x)
  =\sum_i b_i^\sharp(x)\,\partial_i u^\sharp(x)`.
:::

:::proof "symbolic.advection_bridge"
Expand symbolic advection as a finite coordinate sum and apply
{uses "symbolic.partial_derivative_bridge"}[] to each derivative term. The
analytic operator is $`Du(x)[b(x)]`; expanding $`b(x)` in the Euclidean
basis identifies it with that sum.
:::

:::theorem "symbolic.pointwise_system_residual_bridges" (parent := "symbolic.calculus") (lean := "CAS.eulerMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub, CAS.navierStokesMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub_lap_sub, CAS.conservationResidualIntegrand_eval_eq_sum_partialDeriv_sub") (uses := "symbolic.advection_bridge, symbolic.vector_calculus_bridge") (tags := "provenance:leanpde")
For momentum component $`i`, assume `ValidAt` at $`x` for $`u_i` and $`p`.
The Navier–Stokes bridge also assumes validity of every first symbolic partial
of $`u_i`; the conservation bridge assumes validity of every flux component.
These give the stationary Euler and Navier–Stokes momentum residuals and the
divergence-form conservation residual. Incompressibility is a separate equation.
The undifferentiated viscosity and source terms need no validity hypotheses
for these identities. Componentwise, the Euler bridge gives
$`R_i^{E}(x)=\sum_j u_j(x)\partial_j u_i(x)+\partial_i p(x)-f_i(x)`,
while the Navier–Stokes bridge adds $`-\nu(x)\Delta u_i(x)` and the
conservation bridge gives
$`R^{C}(x)=\sum_i\partial_i F_i(x)-f(x)`.
:::

:::proof "symbolic.pointwise_system_residual_bridges"
Normalize each reflected residual, rewrite its differentiated components using
{uses "symbolic.vector_calculus_bridge"}[], and identify the transport term
with {uses "symbolic.advection_bridge"}[]. The remaining sums and products
evaluate definitionally.
:::

The viscosity term here is specifically $`-\nu(x)\Delta u_i`. For a
variable coefficient this differs from divergence-form diffusion:

$$`
-\nabla\cdot(\nu\nabla u_i)
=-\nu\Delta u_i-\nabla\nu\cdot\nabla u_i.
`

The extra term vanishes for constant viscosity. Keeping the exact operator
visible matters when applying a residual bridge: a certificate for one of
these expressions says nothing about the other.

:::theorem "symbolic.residual_bridge" (parent := "symbolic.calculus") (uses := "symbolic.expression") (lean := "CAS.DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt") (tags := "provenance:leanpde")
In positive dimension, lower a differential equation against a closed-form
ansatz to a symbolic residual. If that residual evaluates to zero at the point
and its analytic side conditions hold there, then
$`R_{\mathrm{closed}}=0\ \Longrightarrow\
  R_{\mathrm{analytic}}(u^\sharp,x)=0`.
:::

:::proof "symbolic.residual_bridge"
Rewrite the analytic residual as the evaluation of the lowered residual,
using the analytic side conditions. `ClosedResidualVanishesAt` is exactly the
assertion that this evaluation is zero, so it finishes the proof. A side-aware
normalizer is one way to supply that vanishing proof after its denominator
and branch conditions have been discharged.
:::

:::theorem "symbolic.integration_sound" (parent := "symbolic.calculus") (uses := "symbolic.expression") (lean := "CAS.Verified.Expr.Alg.proportionality?_sound, CAS.integrate?, CAS.IntegrationPlanner.candidate?, CAS.IntegrationCheck.certifyCandidate?, CAS.Verified.Expr.sideHolds_of_compactNonzero, CAS.IntegrationCheck.AntiderivativeCert.eval_diff_eq, CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single") (tags := "provenance:leanpde")
The integration entry point accepts a candidate $`F` only after checking
that $`\operatorname{diff}_iF-f` normalizes to zero. Its certificate records
requirements for the primitive, the integrand, and the conditional
cancellations used in that check.

Fix a coordinate line $`\gamma(s)=x+s e_i`. At each point where those
requirements hold, the evaluated primitive has derivative
$`f^\sharp(\gamma(s))`. If they hold for every
$`s\in[\min(a,b),\max(a,b)]`, then

$$`
\int_a^b f^\sharp(\gamma(s))\,ds
=F^\sharp(\gamma(b))-F^\sharp(\gamma(a)).
`

The interval hypothesis is `Set.uIcc a b` in Lean. It includes both
endpoints and every point between them, regardless of their order.
Validity of the integrand supplies continuity and hence interval
integrability; validity of the primitive supplies the derivative needed by
the fundamental theorem of calculus. Every search method uses this same
certificate. At the reflected API, `IntegrationCheck.certifyCandidate?`
takes the coordinate, original integrand, and proposed primitive explicitly,
so it can check a candidate without running primitive search. The ordinary
interval tactic uses this boundary for a supplied function or a common
function reconstructed from the requested endpoint difference. It reflects
the integrand and candidate over one parameter table, so each coefficient
has the same meaning in both expressions. Checking a candidate against its
own derivative would not establish the requested integral.
:::

:::proof "symbolic.integration_sound"
For substitutions, the proportionality checker validates its proposed factor with
{uses "symbolic.side_normalization_sound"}[]. Polynomial, rational,
substitution, and integration-by-parts passes only propose candidates. The
integration checker validates the symbolic derivative identity with
{uses "symbolic.side_normalization_sound"}[]. Under the certificate's
requirements, {uses "symbolic.partial_derivative_bridge"}[] turns it into
an analytic derivative along $`\gamma`. The interval-wide requirements also
make the evaluated integrand continuous there, so the fundamental theorem
gives the endpoint difference.
:::

*The differentiation rule tree in detail.*

`DiffRule` names the differentiation rules, and `DiffDerivation` records
their application to an expression. For an expression `e` and variable index
`i`, this tree connects the raw derivative `e.diff i` to the analytic partial
derivative. Its rules are:

* *Constant rule.* Every rational literal, $`\pi`, and $`\mathrm e` differentiates to zero: $`\partial_i c = 0`.

* *Variable rule.* A coordinate $`x_j` differentiates to the Kronecker delta: $`\partial_i x_j = \delta_{ij}`.

* *Sum, difference, and negation.* These distribute linearly: $`\partial_i(e_1 \pm e_2) = \partial_i e_1 \pm \partial_i e_2`.

* *Product rule.* For $`e_1 \cdot e_2`: the derivative is $`(\partial_i e_1) e_2 + e_1 (\partial_i e_2)`.

* *Quotient rule.* For $`e_1 / e_2` with $`e_2 \neq 0` at the evaluation point: the derivative is $`((\partial_i e_1)e_2 - e_1(\partial_i e_2))/e_2^2`.

* *Natural power rule.* For $`e^n`: the derivative is $`n \cdot e^{n-1} \cdot \partial_i e`.

* *Real power rule.* For $`e_1^{\,e_2}` with $`e_1 > 0` at the evaluation point: the derivative is $`(\partial_i e_1)\, e_2\, e_1^{\,e_2-1} + (\partial_i e_2)\, e_1^{\,e_2} \log e_1`, the two terms of Mathlib's `HasDerivAt.rpow`; a literal natural exponent is lowered to the natural power rule instead.

* *Transcendental chain rules.* Each elementary function composes with the inner derivative $`\partial_i e`:
  - $`\partial_i(\sin e) = (\cos e)(\partial_i e)`,
  - $`\partial_i(\cos e) = -(\sin e)(\partial_i e)`,
  - $`\partial_i(\arctan e) = (\partial_i e)/(1+e^2)`,
  - $`\partial_i(\arcsin e) = (\partial_i e)/\sqrt{1-e^2}` and $`\partial_i(\arccos e) = -(\partial_i e)/\sqrt{1-e^2}` (requiring $`e \neq \pm1`),
  - $`\partial_i(\exp e) = (\exp e)(\partial_i e)`,
  - $`\partial_i(\log e) = (\partial_i e)/e` (requiring $`e \neq 0` under Mathlib's total real logarithm),
  - $`\partial_i(\sqrt{e}) = (\partial_i e)/(2\sqrt{e})` (requiring $`e > 0`).

The raw derivative is simplified by evaluating constant arithmetic,
eliminating multiplication by zero or one, and removing addition of zero.
These transformations preserve its value.
A theorem may request a form that this simplifier does not reach, such as a
factored heat-kernel derivative or a square-root expression needing
$`(\sqrt u)^2=u`. The derivative tactic then tries the side-conditioned
normalizer, whose real-power and square-root rules identify the two forms
under the recorded conditions.

*Example: differentiating $`\sin(xy)`.*

Consider the expression $`e = \sin(x \cdot y)` with variables $`x = x_0` and
$`y = x_1` in $`\mathbb{R}^2`. Differentiating with respect to $`x_0`:

1. The outermost constructor is sin, so the sine chain rule applies.
2. The inner expression is $`x_0 \cdot x_1`, which uses the product rule.
3. Differentiating $`x_0` gives 1 (variable rule, Kronecker delta).
4. Differentiating $`x_1` with respect to $`x_0` gives 0 (variable rule).
5. The product rule yields $`1 \cdot x_1 + x_0 \cdot 0`.
6. The chain rule produces $`\cos(x_0 x_1) \cdot (1 \cdot x_1 + x_0 \cdot 0)`.
7. The simplifier reduces this to $`x_1 \cos(x_0 x_1)`.

The bridge theorem then proves $`\partial_{x_0}[\sin(xy)](p) = y\cos(xy)` at every point $`p = (x,y)`, as an identity in Lean's real analysis library.

*Supported antiderivative patterns.*

The bounded antiderivative search `IntegrationPlanner.candidateWithFuel?`
combines seven mechanisms.

*Polynomial integration.* Sparse multivariate polynomials are integrated
term by term. Each monomial $`c \cdot x_i^k` integrates in coordinate $`i` to $`c \cdot x_i^{k+1}/(k+1)`. The sparse representation avoids allocating zero coefficients.

*Calibrated substitution.* For an integrand $`f(x)`, the planner collects a list of substitution primitives. These include $`\log g` for quotients by $`g`, inverse-power primitives, $`\exp(g)`, $`-\cos(g)`, and $`\sin(g)`. For each primitive, the proportionality checker (`Alg.proportionality?`) verifies whether the integrand equals the primitive's derivative times a factor independent of the integration coordinate. If successful, the candidate is that constant factor times the primitive.

*Integration by parts.* The LIATE heuristic ranks factors by their
suitability for differentiation. Logarithmic and inverse-trigonometric factors
receive rank 5, algebraic polynomial factors rank 4, trigonometric factors rank 3, and exponential factors rank 2.
For a product $`u \cdot v'`, the planner recursively integrates $`v'`, forms $`uv - \int u'v`, recursively integrates the correction, and validates the result. The initial recursion fuel is 96; this bounds recursive depth, not the total number of calls across search branches.

*Exponential-trigonometric recurrences.* For integrands of the form $`e^{ax}(p(x)\sin(cx) + q(x)\cos(cx))`, the planner solves a finite coupled polynomial recurrence. Writing the antiderivative as $`e^{ax}(P(x)\sin(cx) + Q(x)\cos(cx))`, the amplitudes satisfy

$$`P' + aP - cQ = p, \qquad Q' + cP + aQ = q.`

When $`a^2 + c^2 \neq 0`, the constant matrix is invertible, and repeated matrix inversion lowers the polynomial degree. The process terminates in at most $`\max(\deg p, \deg q) + 1` steps.

The implemented route allows multivariate rational-polynomial amplitudes,
with the other coordinates treated as parameters, and common exponential and
trigonometric phases whose slopes in the selected coordinate are rational
constants.

*Trigonometric powers.* The planner proposes primitives for sine and cosine
powers with every fixed natural exponent. For positive powers, the phase
derivative must simplify to an expression independent of the selected
coordinate and different from literal zero. The final certificate records the
nonvanishing conditions needed for division. For constant nonzero slope
$`\alpha`, the low-power cases include:
- $`\int \sin(\alpha x)\,dx = -\cos(\alpha x)/\alpha`,
- $`\int \cos(\alpha x)\,dx = \sin(\alpha x)/\alpha`,
- $`\int \sin^2(\alpha x)\,dx = x/2 - \sin(\alpha x)\cos(\alpha x)/(2\alpha)`,
- $`\int \cos^2(\alpha x)\,dx = x/2 + \sin(\alpha x)\cos(\alpha x)/(2\alpha)`.

*Rational function integration.* For univariate rational functions $`p(x)/q(x)`, the pipeline proceeds in three stages:
  - *Polynomial division.* Exact sparse Euclidean division separates the improper part: $`p = s \cdot q + r` with $`\deg r < \deg q`. The polynomial quotient $`s` is integrated term by term.
  - *Hermite reduction.* The proper fraction $`r/q` undergoes Yun square-free decomposition of the denominator. For each repeated factor $`f^m`, the Hermite recurrence lowers the multiplicity by one at each step, producing rational correction terms that do not require logarithms.
  - *Elementary transcendental integration.* The terminal square-free fraction
    uses partial-fraction decomposition over the rationals. Linear factors give
    logarithms. For a quadratic denominator $`ax^2+bx+c`, separate off the
    logarithmic-derivative part. The remaining primitive uses arctangent when
    $`b^2-4ac<0` and real logarithms when $`b^2-4ac>0`.

The rational factor search combines rational-root extraction and exact
Kronecker search over `Rat`; extended Euclid supplies the modular inverses.
Irrational scales in quadratic primitives remain exact symbolic square roots.

Bronstein (2005, Chapter 2) gives the rational-integration methods behind these
stages. Here they are used in a bounded candidate search, and the accepted
primitive's derivative is checked.

*Compositional linearity.* Sums, differences, negations, and scalar-independent multiples are handled compositionally.

Before a certificate's nonzero conditions reach a proof, a checked compactor
collects square-root products, extracts common factors, splits products and
powers, normalizes factors, and deduplicates them. Its soundness theorem
recovers every raw obligation from the compact list.

*Example: integrating a rational function.*

Consider $`\int \frac{2x+3}{(x-1)^2(x+2)}\,dx`. The algebra to be checked is

$$`
\frac{2x+3}{(x-1)^2(x+2)}
=\frac{1}{9(x-1)}+\frac{5}{3(x-1)^2}-\frac{1}{9(x+2)}.
`

Thus, on any interval avoiding $`1` and $`-2`, a candidate primitive is

$$`
F(x)=\frac19\log|x-1|-\frac{5}{3(x-1)}
     -\frac19\log|x+2|.
`

Differentiating the middle term recovers the repeated pole; differentiating
the two logarithms recovers the simple poles. This concrete decomposition
explains the roles of the pipeline's stages:

1. *Polynomial division.* The numerator has lower degree, so the quotient is zero.

2. *Square-free decomposition.* The denominator factors as $`(x-1)^2(x+2)`. Yun decomposition identifies $`(x-1)` with multiplicity 2 and $`(x+2)` with multiplicity 1.

3. *Hermite reduction.* The recurrence absorbs the repeated factor, producing a rational correction and lowering the denominator to square-free form $`(x-1)(x+2)`.

4. *Partial fractions.* Modular inverse computation splits the residual into terms with denominators $`(x-1)` and $`(x+2)`.

5. *Elementary integration.* Each partial fraction $`c/(x-r)` integrates to $`c\log|x-r|`.

6. *Validation.* The complete candidate is differentiated symbolically, and the residual is normalized to zero by the checked route. The requirement set records $`x \neq 1` and $`x \neq -2`.

To use the endpoint formula, the entire closed interval must avoid both
poles. Checking only $`a\ne1,-2` and $`b\ne1,-2` is insufficient: the
endpoints $`a=0`, $`b=2` pass those tests but enclose the pole at $`1`.
This is why the integral theorem asks for nonvanishing at every point of
`Set.uIcc a b`, while a pointwise derivative theorem asks only at its
evaluation point.
