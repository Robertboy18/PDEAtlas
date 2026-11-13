/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.Quadrature
import CAS.Continuum.Quadrature.RationalAdaptive
import CAS.Continuum.Quadrature.Search

/-!
## Derivative bounds

Certified derivative enclosures and adaptive bound search.
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
#doc (Manual) "Derivative Bounds and Adaptive Search" =>

High-order quadrature and Taylor remainders require uniform bounds on the
analytic derivative. Checked symbolic derivatives are identified with
Mathlib's `iteratedDerivWithin` and then enclosed panel by panel on a declared
real domain.

Adaptive search consumes only these proved local bounds. It may accept a
panel, subdivide it, compare two certified trees, or exhaust its depth budget.
The search strategy is computational; the returned tree is useful because its
root error theorem is independent of that strategy.

*From $`x^4` to an analytic bound.*

Let the symbolic expression be $`e(x)=x^4`. Repeated checked differentiation
and normalization produce the constant fourth derivative `24`. The
variable-independent route can evaluate that expression once, obtaining the
degenerate enclosure $`[24,24]`, and reuse it on every requested panel.

The route then crosses two proof boundaries:

1. the differentiation theorem identifies the checked symbolic expression
   with Mathlib's `iteratedDerivWithin 4`;
2. the interval theorem turns membership in $`[24,24]` into an absolute-value
   upper bound.

The resulting `IteratedDerivativeBounderOn` proves, for every nondegenerate
panel $`[a,b]` in its declared domain and every $`x\in[a,b]`,

$$`\left\|\operatorname{iteratedDerivWithin}
  4\,(\lambda x,x^4)\,[a,b]\,x\right\|\leq24.`

For the polynomial, smoothness is proved analytically, and a quadrature
theorem receives that `ContDiffOn` proof separately from the numerical bound.

*A rational example with a side condition.*

For $`f(x)=1/(1+x)` on $`[0,1]`, the fourth derivative simplifies to
$`24/(1+x)^5`. The checked rational route also records the condition
$`1+x\neq0`. Interval positivity proves that condition uniformly because
$`1\leq1+x\leq2` on the domain.

A range provider can then enclose the simplified derivative. Even a
conservative enclosure such as $`[-24,24]` is sufficient: converting it to a
bound certificate yields the useful conclusion

$$`\left\|f^{(4)}(x)\right\|\leq24
\qquad (0\leq x\leq1).`

:::definition "symbolic.derivative_bounder" (parent := "symbolic.cega") (uses := "symbolic.interval_backend") (lean := "CAS.Continuum.IteratedDerivativeBounderOn")
An `IteratedDerivativeBounderOn n f s` produces a `BoundCert` for
$`\lVert f^{(n)}\rVert` on every requested nondegenerate compact interval
contained in `s`. The specialized interface stores only the scalar panel bound
and its direct proof for Mathlib's `iteratedDerivWithin`; its generic
`BoundCert` is a derived projection. Constructors accept a panelwise Lean
estimate, CEGA derivative enclosures, or any sound `RealIntervalBackend`.
Smoothness is a separate analytic hypothesis; an enclosure of a formal
derivative says nothing about differentiability of the original function.
:::

:::theorem "symbolic.iterated_derivative_semantics" (parent := "symbolic.cega") (uses := "symbolic.partial_derivative_bridge") (lean := "CAS.Verified.Expr.iteratedDerivWithin_univariateEval_eq_symbolicDerivative, CAS.Verified.Expr.contDiffOn_univariateEval")
On a set with `UniqueDiffOn ℝ s`, assume validity of the intermediate symbolic
derivatives at levels $`k<n`. The order-$`n` checked derivative then denotes
Mathlib's `iteratedDerivWithin`. This includes every nondegenerate closed
interval contained in the validity domain. The linked regularity theorem
uses the sufficient stronger assumption of validity through level $`n`
inclusive to prove `ContDiffOn ℝ n`: it establishes continuity of the final
derivative by proving that derivative differentiable.

If $`e^{[n]}` is the expression obtained by $`n` checked symbolic
derivatives, then on every admissible panel $`[a,b]` and every $`x\in[a,b]`,

$$`\operatorname{iteratedDerivWithin}
  n\,(\lambda y,\operatorname{eval}(e,y))\,[a,b]\,x
  =\operatorname{eval}\!\left(e^{[n]},x\right).`
:::

:::proof "symbolic.iterated_derivative_semantics"
Induct on the derivative order. The base case is evaluation itself. At the
successor step, apply the one-step symbolic derivative bridge to the current
derived expression and use the induction hypothesis to identify the analytic
within-derivative already constructed. The validity assumptions propagate to
every intermediate expression.
:::

:::theorem "symbolic.rational_derivative_route" (parent := "symbolic.cega") (uses := "symbolic.normalization_sound, symbolic.interval_evaluator_sound") (lean := "CAS.Verified.Expr.RationalCanonical.route_sound, CAS.Continuum.RationalInterval.CertifiedEvalContext.sideHolds_of_certifiesSideConditions, CAS.Continuum.RationalInterval.memReal_rationalHull")
The rational route proposes a polynomial-gcd cancellation, checks its semantic
equality through the exact normalizer, and turns generated denominator
conditions into interval obligations. Exact rational hulls cover arbitrary
real panels, and checked zero exclusion or an absolute lower bound discharges
the nonzero conditions on the whole declared domain.

Writing the checked route as $`\operatorname{route}(d)=(r,S)`, its semantic
boundary is the conditional identity

$$`\operatorname{SideHolds}(\rho,S)
  \quad\Longrightarrow\quad
  \operatorname{eval}(d,\rho)=\operatorname{eval}(r,\rho).`

The interval phase proves the premise uniformly on the panel.
:::

:::proof "symbolic.rational_derivative_route"
Polynomial gcd cancellation proposes the reduced rational expression, but the
exact normalizer proves the cross-multiplied identity. Checked interval facts
then show that every cancelled denominator is nonzero throughout the panel.
Substituting those side facts into the conditional normalization theorem gives
the pointwise equality used by the derivative bounder.
:::

:::definition "symbolic.panel_expression_range_provider" (parent := "symbolic.cega") (uses := "symbolic.interval_backend") (lean := "CAS.Continuum.ExprRangeProviderOn.ofPanelEvaluator")
A verified panel evaluator, checked variable boxes, and a proof of successful
evaluation define a total range provider for one symbolic expression. The
provider stores the returned backend interval together with its direct
enclosure theorem.

For every $`a<b` with $`[a,b]\subseteq s`, its total contract is

$$`\forall x\in[a,b],\qquad
  \operatorname{eval}(e,x)\in\operatorname{result}(a,b).`
:::

:::definition "symbolic.direct_expression_derivative_bounds" (parent := "symbolic.cega") (uses := "symbolic.derivative_bounder, symbolic.iterated_derivative_semantics, symbolic.panel_expression_range_provider") (lean := "CAS.Continuum.IteratedDerivativeBounderOn.ofExpr, CAS.Continuum.IteratedDerivativeBounderOn.ofExprWithRewrite")
The direct constructor encloses the structurally normalized symbolic
derivative. A second constructor accepts an explicitly proved rewrite before
range evaluation. In both cases the resulting certificate bounds Mathlib's
analytic iterated derivative.

For every accepted panel, the produced bound $`B(a,b)` satisfies

$$`\forall x\in[a,b],\qquad
  \left\|\operatorname{iteratedDerivWithin}
    n\,f\,[a,b]\,x\right\|\leq B(a,b).`
:::

:::definition "symbolic.side_conditioned_derivative_bounds" (parent := "symbolic.cega") (uses := "symbolic.direct_expression_derivative_bounds, symbolic.rational_derivative_route") (lean := "CAS.Continuum.IteratedDerivativeBounderOn.ofExprWithSideRoute, CAS.Continuum.IteratedDerivativeBounderOn.ofRationalExpr")
Side-aware constructors consume a checked equality route together with proofs
of every emitted nonzero condition. The rational specialization may cancel
polynomial factors, but its simplified derivative enters the bounder only
through that conditional semantic equality.

The constructor composes

$$`\left(\forall x\in[a,b],\operatorname{SideHolds}(x,S)\right)
  \land
  \left(\forall x\in[a,b],|\operatorname{eval}(r,x)|\leq B\right)
  \quad\Longrightarrow\quad
  \forall x\in[a,b],\|f^{(n)}(x)\|\leq B.`
:::

:::definition "symbolic.variable_independent_derivative_bounds" (parent := "symbolic.cega") (uses := "symbolic.derivative_bounder, symbolic.iterated_derivative_semantics, symbolic.panel_expression_range_provider") (lean := "CAS.Continuum.IteratedDerivativeBounderOn.ofIndependentExpr")
When the compiled derivative contains no occurrence of the interval variable,
one verified evaluation at an enclosure of zero supplies the same bound on
every real panel. This avoids asking a finite interval backend to represent
arbitrary real endpoints for a constant expression.

Variable independence gives

$$`x\notin\operatorname{vars}(d)
  \quad\Longrightarrow\quad
  \operatorname{eval}(d,\rho[x\mapsto t])
  =\operatorname{eval}(d,\rho[x\mapsto0])`

for every $`t`; a single enclosure of the right-hand side is therefore valid
on every requested panel.
:::

:::theorem "symbolic.adaptive_quadrature_error" (parent := "symbolic.cega") (uses := "symbolic.adaptive_quadrature") (lean := "CAS.Continuum.QuadratureTree.WithErrorAtMost.sound")
A successful adaptive result contains a quadrature tree together with a proof
that the sum of its leaf errors is at most the root tolerance. Projecting this
result gives the ordinary interval-integral estimate for the tree's accumulated
value.

For $`R:\mathrm{WithErrorAtMost}(f,a,b,\tau)`, the public theorem is

$$`\left\|\int_a^b f(x)\,dx
  -R.\mathrm{tree}.\mathrm{value}\right\|\leq\tau.`
:::

:::proof "symbolic.adaptive_quadrature_error"
The quadrature tree's soundness theorem bounds the root error by the sum of its
leaf budgets. The dependent result type stores a proof that this accumulated
budget is at most $`\tau`; transitivity gives the displayed estimate.
:::

:::definition "symbolic.adaptive_quadrature_search" (parent := "symbolic.cega") (uses := "symbolic.adaptive_quadrature_error") (lean := "CAS.Continuum.AdaptiveQuadrature.search")
The generic depth-bounded search takes a proved local panel builder and
interval integrability on every nondegenerate panel in the domain. It accepts
a panel when its certificate meets the local tolerance, even at depth zero.
Otherwise it bisects and gives each child half the budget if depth remains;
with no depth left, it returns `none`. This generic definition compares real
error bounds; the rational-budget interface supplies exact rational stopping
comparisons.

Every successful search satisfies

$$`\operatorname{search}(d,a,b,\tau)=\operatorname{some}(R)
  \quad\Longrightarrow\quad
  \left\|\int_a^b f-R.\mathrm{tree}.\mathrm{value}\right\|\leq\tau.`
:::

:::definition "symbolic.adaptive_simpson_search" (parent := "symbolic.cega") (uses := "symbolic.adaptive_quadrature_search, symbolic.simpson_fourth_order_certificate, symbolic.derivative_bounder") (lean := "CAS.Continuum.PanelRule.search, CAS.Continuum.simpsonRule.fourthOrder")
Adaptive Simpson search instantiates the generic engine with sharp local
Simpson certificates built from panelwise fourth-derivative bounds.

Every successful result therefore proves

$$`\operatorname{simpsonRule.fourthOrder.search}(\ldots)=\operatorname{some}(R)
  \quad\Longrightarrow\quad
  \left|\int_a^b f-R.\mathrm{tree}.\mathrm{value}\right|\leq\tau,`

with each accepted leaf justified by the fourth-order Simpson bound.
:::

:::definition "symbolic.adaptive_gauss_legendre_search" (parent := "symbolic.cega") (uses := "symbolic.adaptive_quadrature_search, symbolic.gauss_legendre_fourth_order_certificate, symbolic.derivative_bounder") (lean := "CAS.Continuum.PanelRule.search, CAS.Continuum.gaussLegendreTwoRule.fourthOrder")
Adaptive two-point Gauss–Legendre search uses the same subdivision policy with
the corresponding sharp Peano-kernel certificate at each accepted leaf.

Its successful-result contract is likewise

$$`\operatorname{gaussLegendreTwoRule.fourthOrder.search}(\ldots)
  =\operatorname{some}(R)
  \quad\Longrightarrow\quad
  \left|\int_a^b f-R.\mathrm{tree}.\mathrm{value}\right|\leq\tau.`
:::

*Why subdivision can improve a certificate.*

For $`f(x)=x^5` on $`[0,1]`, the fourth derivative is $`120x`. The root panel
may therefore receive the bound $`120`, while its left half receives the
sharper bound $`60`.
If the root certificate exceeds its assigned tolerance, adaptive search
bisects the interval and asks the same derivative-bound object for each child.

The sharp Simpson budget on a panel of width $`h` is
$`C h^5/2880`, where $`C` bounds the fourth derivative. Thus the unsplit
budget is $`120/2880=1/24`, while the two half-panel budgets are

$$`
\frac{60(1/2)^5}{2880}=\frac1{1536},
\qquad
\frac{120(1/2)^5}{2880}=\frac1{768}.
`

Their sum is $`1/512`. Most of the gain comes from the fifth power of the
panel width; the smaller derivative bound on the left improves it further.

In this construction, both children meet tolerance $`1/384`, and
adding the child certificates gives an estimate with analytic error
$`1/512`. The arithmetic that chooses to split plays no part in the proof,
which uses only the two local error bounds, interval
integrability, and additivity of the interval integral.

:::theorem "symbolic.rational_candidate_acceptance" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate") (lean := "CAS.Continuum.RationalBudgetCandidate.error_le_of_accepted")
A rational-budget candidate contains a client result, an exact rational upper
bound for its semantic error, and a proof relating the two.
When decidable rational comparison accepts the candidate, its real error is at
most the requested rational tolerance.

Precisely,

$$`\operatorname{accepted}(c,\tau)=\mathrm{true}
  \quad\Longrightarrow\quad
  \operatorname{error}(c.\mathrm{cert})\leq(\tau:\mathbb R).`
:::

:::proof "symbolic.rational_candidate_acceptance"
The candidate's proof bounds its semantic real error by the cast of its exact
rational budget. Boolean acceptance is precisely the decidable rational
comparison of that budget with $`\tau`. Casting this comparison to the reals
and composing the inequalities proves the result.
:::

:::definition "symbolic.rational_adaptive_system" (parent := "symbolic.cega") (uses := "symbolic.rational_candidate_acceptance") (lean := "CAS.Continuum.RationalAdaptiveSystem.searchPartial")
The generic rational adaptive kernel keeps endpoints, midpoints, and local
tolerances exact. A rejected or unavailable parent candidate is bisected at
its rational midpoint; accepted children are combined only through the
client's proved error-subadditivity theorem.

The dependent result type records the invariant

$$`\operatorname{searchPartial}(\ldots,\tau)=\operatorname{some}(R)
  \quad\Longrightarrow\quad
  \operatorname{error}(R.\mathrm{result})\leq(\tau:\mathbb R).`
:::

:::definition "symbolic.rational_adaptive_quadrature" (parent := "symbolic.cega") (uses := "symbolic.rational_adaptive_system, symbolic.adaptive_quadrature_error") (lean := "CAS.Continuum.RationalAdaptiveQuadrature.searchPartial")
The quadrature specialization stores accepted local `QuadratureCert`s in the
same backend-independent tree used by real-valued adaptive search. Local
interval-integrability evidence justifies composing adjacent panel integrals.
Both an over-budget root and a missing root candidate may therefore be
recovered by proved child certificates, while a failed finite search returns
`none`.

On success it returns exactly the root theorem

$$`\left|\int_a^b f(x)\,dx
  -R.\mathrm{tree}.\mathrm{value}\right|\leq(\tau:\mathbb R),`

where $`a`, $`b`, and $`\tau` are the input rationals cast to reals.
:::

:::theorem "symbolic.adaptive_selection" (parent := "symbolic.cega") (uses := "symbolic.adaptive_quadrature") (lean := "CAS.Continuum.QuadratureTree.selectLowerError_sound, CAS.Continuum.QuadratureTree.improveLeaves_error_le")
Competing subdivision trees for the same interval can be compared by their
proved error budgets. The selector returns a tree with the minimum budget.
More generally, a dependent leaf-refinement rule may propose a replacement
tree at every accepted leaf; retaining the better local alternative is proved
never to increase the accumulated root error. Candidate generation is
untrusted.

For two root trees $`T_1,T_2`,

$$`\left\|\int_a^b f
  -\operatorname{select}(T_1,T_2).\mathrm{value}\right\|
  \leq\min\!\left(E(T_1),E(T_2)\right),`

and leafwise improvement satisfies $`E(\operatorname{improve}(T))\leq E(T)`.
:::

:::proof "symbolic.adaptive_selection"
For two complete trees, choose the one whose stored error budget is smaller;
its existing soundness theorem supplies the integral estimate. For leafwise
refinement, use structural induction on the original tree. At each leaf retain
the original certificate or a proved-better replacement, and at each branch
add the two inductive error inequalities.
:::

:::theorem "symbolic.quadrature_candidate_search" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate, symbolic.adaptive_selection") (lean := "CAS.Continuum.QuadratureCandidateFamily.AcceptedCandidate.sound")
A candidate family associates mesh, rule, or arithmetic-schedule keys with
ordinary quadrature certificates and an executable Boolean acceptance test.
The policy proves that every accepted result meets the requested tolerance.
Finite search returns the first accepted key together with that theorem, or
`none` if every candidate fails.

If finite search returns an accepted key $`k`, its projection proves

$$`\left\|\int_a^b f(x)\,dx
  -\operatorname{candidate}(k).\mathrm{value}\right\|\leq\tau.`
:::

:::proof "symbolic.quadrature_candidate_search"
Finite search returns a key only together with evidence that the family's
acceptance predicate holds for that key. The policy theorem converts this
evidence into the requested tolerance bound, and the candidate's stored
quadrature soundness identifies the quantity being bounded. A failed search
has no conclusion to prove.
:::

Exact-rational candidate families obtain their Boolean test from rational
comparison and transport the result to a real error theorem. A FloatLib
enclosure of the exact rule value gives another such candidate: its certified
endpoint radius bounds replacement by the midpoint, and that radius is added
to the analytic error. For rounded endpoints, the radius must use their exact
decoded values. The derivative enclosure must still bound the analytic
derivative on the whole panel: order four supplies the Simpson remainder,
and order $`n+1` supplies the degree-$`n` Taylor remainder.

The common derivative object is used by the Simpson and two-point
Gauss–Legendre constructors for one panel, fixed composites, planned
tolerances, and adaptive subdivision. The total tolerance planner reserves
part of the budget for analytic error and accepts a replacement value only
when its proved numerical error fits the remainder.
