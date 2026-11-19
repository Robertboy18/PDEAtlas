/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Compactness
import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue
import PDE.Spaces.Sobolev.Calculus.Composition.C1DomainTruncation
import PDE.Spaces.Sobolev.Calculus.Composition.DomainLipschitz
import PDE.Spaces.Sobolev.Calculus.Composition.DomainTruncation
import PDE.Spaces.Sobolev.Calculus.Composition.Lipschitz
import PDE.Spaces.Sobolev.Calculus.Composition.OneDimensionalNonsmooth
import PDE.Spaces.Sobolev.Calculus.Composition.Reciprocal
import PDE.Spaces.Sobolev.Calculus.Composition.Truncation
import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives
import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakToClassical
import PDE.Spaces.Sobolev.Calculus.Product.HigherOrder
import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient
import PDE.Spaces.Sobolev.Calculus.Product.Operator
import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.Spaces.Sobolev.Calculus.Pullback.SecondOrder.Operator
import PDE.Spaces.Sobolev.Calculus.Pullback.SecondOrder.WeakChainRule
import PDE.Spaces.Sobolev.Calculus.Slicing.FundamentalTheorem
import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder
import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative
import PDE.Spaces.Sobolev.Calculus.Slicing.ACL
import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Model
import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Classical
import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Distribution
import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.WeakStep
import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.WeakConvergence
import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Domain
import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.Model
import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.WeakConvergence
import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.Fibers
import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.Lift
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.FiniteExponent

/-!
# Weak calculus

Weak product rules, one-dimensional fundamental
calculus, derivative extraction, and Sobolev coordinate transformations.
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
#doc (Manual) "Weak Products, Slices, and Coordinate Changes" =>

Weak derivatives support much of ordinary calculus, but each rule requires an
analytic proof because the functions are represented only almost everywhere.

There are two different compositions here. A coordinate change
$`u\mapsto u\circ E` changes where we sample the function. A nonlinear
composition $`u\mapsto F\circ u`, also called a Nemytskii operation,
changes its values at the same points: absolute value and clipping a function
to a fixed interval are examples. Their chain rules require different
estimates, so we keep the independent-variable map $`E` and the
value map $`F` distinct.

The recurring proof route is to localize, approximate by smooth functions,
apply the classical identity, and pass to the limit in an `Lp` space.
Derivative words are used instead of symmetric multi-indices so repeated
first-order weak differentiation can be expressed directly; permutation
invariance later shows that the ordering does not affect the resulting weak
derivative. The graph-space operators retain boundedness information needed
by variational and regularity estimates.

The domain-composition results go from general to specialized. The basic
local theorem assumes an open finite-measure set equipped with a bounded
first-order extension operator. An operational $`C^1` atlas is one way of
supplying that operator, so the nonlinear calculus holds on every extension
domain and not only on atlas domains.

:::group "sobolev.calculus"
Weak Sobolev calculus
:::

:::theorem "sobolev.weak_leibniz" (parent := "sobolev.calculus") (lean := "SobolevSpace.hasWeakDerivativeOn_weakLeibniz") (uses := "sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "261-262"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\zeta` be smooth with every derivative used in the expansion belonging
to $`L^\infty(\Omega)`.  Let $`D_\beta` be an $`L^p` family compatible under
successive first weak derivatives.  Then, for every derivative word
$`\alpha`, the product $`\zeta D_{\varnothing}` has weak derivative given by
the full Leibniz expansion over all ways of distributing the entries of
$`\alpha` between the two factors.
:::

:::proof "sobolev.weak_leibniz"
The proof inducts over the derivative word.  The first-order weak product rule
is applied at each step, and the list of splits records repeated coordinates,
including the multiplicities that become binomial or multinomial coefficients
in conventional notation.
:::

The Leibniz theorem is phrased for an abstract family $`D_\beta` of $`L^p`
functions closed under first weak derivatives. A graph-space element
$`U\in W^{k,p}(\Omega)` supplies exactly such a family through order $`k`,
namely its stored derivative rows, so the expansion applies to every
derivative word of length at most $`k`. That specialization is the multiplier
statement used for smooth cutoffs throughout the chapter.

:::theorem "sobolev.smooth_multiplier" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.WkpSpaceOn.hasWeakDerivativeOn_mul_smooth") (uses := "sobolev.weak_leibniz, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "261-262"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`U\in W^{k,p}(\Omega)` and a smooth multiplier $`\zeta` whose derivatives
through order $`k` are in $`L^\infty(\Omega)`, every derivative word of
$`\zeta U` of length at most $`k` is represented by the corresponding weak
Leibniz expansion.
:::

:::proof "sobolev.smooth_multiplier"
Use the graph-space representative of every weak derivative of $`U` through
order $`k`. The weak Leibniz theorem applies because each derivative of
$`\zeta` appearing in a split is essentially bounded. For every derivative
word $`\alpha`, the resulting finite sum is therefore the weak derivative of
$`\zeta U`.
:::

Multiplication by a regular factor is one of two ways of transporting weak
derivatives; the other is composition with a regular change of coordinates.
The Leibniz expansion is algebraic in the stored rows and holds for every
exponent $`1\leq p\leq\infty`, whereas the chain rule below is proved by
mollifying $`u` itself. The theorem below is the first-order, finite-exponent
form. The second-order chain rule appears later in this section, and pullback
by a chart with bounded target preserves every finite order for
$`1\leq p\leq\infty`
by a bounded pullback operator.

:::theorem "sobolev.coordinate_chain_rule" (parent := "sobolev.calculus") (lean := "SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp") (uses := "sobolev.weak_derivative, sobolev.mollifier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`1\leq p<\infty`.  Let $`E` be an open partial homeomorphism of
$`\mathbb R^n` whose forward and inverse maps are $`C^1`.  If
$`u\in L^p(E(\mathrm{source}))` has chosen first weak derivatives
$`d_j u\in L^p` on the target, then $`u\circ E` has the weak derivative

$$`
\partial_i(u\circ E)(x)
  =\sum_{j=1}^n (\partial_j u)(E(x))\,\partial_i E_j(x)
`

on the source.
:::

:::proof "sobolev.coordinate_chain_rule"
Mollify $`u` and its weak derivatives on compact subsets, apply the classical
chain rule to the smooth approximants, control pullback in `Lp` by local
Jacobian bounds, and pass to the limit in the distributional identity.
:::

In one dimension the basic identity is the fundamental theorem of calculus for
a continuous representative. Its proof is the first place where the smooth
multiplier theorem is used to localize: a cutoff equal to one on
the interval turns data given on an open set into compactly supported data on
the whole line, which can then be mollified.

:::theorem "sobolev.weak_fundamental_theorem" (parent := "sobolev.calculus") (lean := "SobolevSpace.FundamentalTheorem.intervalIntegral_weakDerivative_eq_sub_on") (uses := "sobolev.weak_derivative, sobolev.mollifier, sobolev.smooth_multiplier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U\subset\mathbb R` be open, let $`f:\mathbb R\to\mathbb R` be
continuous, and suppose $`f,g\in L^1(U)` with $`g` a weak derivative of
$`f` on $`U`. If the closed interval from $`a` to $`b` lies in $`U`, then

$$`
  \int_a^b g(t)\,dt=f(b)-f(a).
`
:::

:::proof "sobolev.weak_fundamental_theorem"
Choose a smooth cutoff equal to one on the interval, extend the localized
data by zero, and mollify. The classical FTC holds for every mollification.
Pointwise convergence of the mollified continuous representative and $`L^1`
convergence of the mollified weak derivative pass the identity to the limit.
:::

The fundamental theorem above takes the continuous representative as an input.
For a global $`W^{1,1}(\mathbb R)` element the critical one-dimensional
embedding provides such a representative, and the integral identity then
upgrades it: a function whose increments are integrals of an $`L^1` function
is absolutely continuous on compact intervals and differentiable almost
everywhere, with derivative equal to that function.

Absolute continuity strengthens ordinary continuity by controlling many
intervals at once. For every $`\varepsilon>0`, there is a
$`\delta>0` such that any finite disjoint family of intervals
$`(a_j,b_j)` in the fixed compact interval satisfies

$$`
\sum_j(b_j-a_j)<\delta
\quad\Longrightarrow\quad
\sum_j|\widetilde U(b_j)-\widetilde U(a_j)|<\varepsilon.
`

The integral formula proves this directly: the sum of the increments is
bounded by the integral of $`|G|` over the union of those intervals,
and an $`L^1` function has small integral on sets of sufficiently small
measure. This is the property that lets the weak derivative reconstruct
every increment of the representative.

:::theorem "sobolev.w11_absolute_continuous_representative" (parent := "sobolev.calculus") (lean := "SobolevSpace.AbsolutelyContinuousRepresentative.absolutelyContinuousOnInterval_representative, SobolevSpace.AbsolutelyContinuousRepresentative.ae_hasDerivAt_representative, SobolevSpace.AbsolutelyContinuousRepresentative.intervalIntegral_weakDerivativeRepresentative_eq_sub") (uses := "sobolev.weak_fundamental_theorem, sobolev.critical_one_dimensional_global")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every global $`U\in W^{1,1}(\mathbb R)` has a selected bounded continuous
representative $`\widetilde U` that is absolutely continuous on every compact
interval.  If $`G` is the stored weak derivative, then

$$`
  \widetilde U'(x)=G(x)\quad\text{for almost every }x,
  \qquad
  \widetilde U(b)-\widetilde U(a)=\int_a^b G(t)\,dt.
`

Thus the graph-space weak derivative agrees almost everywhere with the
classical derivative of the selected representative.
:::

:::proof "sobolev.w11_absolute_continuous_representative"
The critical one-dimensional Morrey theorem supplies a bounded continuous
representative.  The weak fundamental theorem expresses its increments as
the interval integral of the stored derivative.  Since that derivative is in
$`L^1`, Mathlib's indefinite-integral theorem makes the primitive absolutely
continuous, and Lebesgue differentiation identifies its derivative almost
everywhere.
:::

Composing the representative with the absolute value or with a clamp creates
kinks, and the chain rule at a kink requires knowing that the inner derivative
vanishes almost everywhere on the fiber where the kink is hit. That fact has
nothing to do with Sobolev spaces; it is a statement about Mathlib's total
derivative of an arbitrary real function.

:::theorem "sobolev.derivative_zero_on_level_sets" (parent := "sobolev.calculus") (lean := "PDE.Analysis.Calculus.ae_deriv_eq_zero_on_levelSet")
For every function $`f:\mathbb R\to\mathbb R` and every $`c\in\mathbb R`,

$$`
  f(x)=c\quad\Longrightarrow\quad \operatorname{deriv}f(x)=0
`

for almost every $`x`.  No regularity assumption on $`f` is needed: Mathlib's
total derivative is zero at nondifferentiability points, while the exceptional
isolated points of a level set form a countable set.
:::

:::proof "sobolev.derivative_zero_on_level_sets"
At every non-isolated point of the fiber $`f^{-1}(\{c\})`, the function is
frequently equal to $`c`, so Mathlib's derivative-of-a-frequently-constant
theorem gives derivative zero.  The remaining one-sided isolated points are
countable in the second-countable real line and therefore null.
:::

With the absolutely continuous representative and the level-set lemma in hand,
the one-dimensional nonsmooth chain rule follows at the level of
representatives. Away from a kink the classical chain rule applies; on a kink
fiber the inner derivative vanishes almost everywhere, and so does the
derivative of the composite.

:::theorem "sobolev.one_dimensional_nonsmooth_calculus" (parent := "sobolev.calculus") (lean := "SobolevSpace.OneDimensionalNonsmooth.ae_hasDerivAt_absRepresentative, SobolevSpace.OneDimensionalNonsmooth.ae_hasDerivAt_positivePartRepresentative, SobolevSpace.OneDimensionalNonsmooth.ae_hasDerivAt_negativePartRepresentative, SobolevSpace.OneDimensionalNonsmooth.ae_hasDerivAt_truncationRepresentative, SobolevSpace.OneDimensionalNonsmooth.intervalIntegral_truncationWeakDerivativeRepresentative_eq_sub") (uses := "sobolev.w11_absolute_continuous_representative, sobolev.derivative_zero_on_level_sets")
Let $`\widetilde U` be the selected representative of
$`U\in W^{1,1}(\mathbb R)` and let $`G` be its weak derivative.  Absolute
value, positive and negative parts, and every interval truncation
$`T_{a,b}` with $`a\leq b` are absolutely continuous on compact intervals.
Their derivatives agree almost everywhere with the expected finite-kink
formulas; in particular,

$$`
  (|\widetilde U|)'=\operatorname{sign}(\widetilde U)\,G
`

and

$$`
  (T_{a,b}\widetilde U)'
   =\frac{\operatorname{sign}(\widetilde U-a)
          -\operatorname{sign}(\widetilde U-b)}{2}\,G.
`

Each transformed representative satisfies the corresponding literal
fundamental theorem of calculus.
:::

:::proof "sobolev.one_dimensional_nonsmooth_calculus"
Away from a kink, apply the ordinary derivative chain rule.  On each kink
fiber, the level-set theorem makes the inner derivative vanish almost
everywhere.  The scalar maps are one-Lipschitz, so composition preserves
interval absolute continuity; integrating the almost-everywhere derivative
then gives the FTC identities.
:::

The one-dimensional theory passes to $`\mathbb R^{n+1}` one coordinate at a
time. Fixing a coordinate direction, almost every line parallel to it carries
a slice of $`U\in W^{1,1}(\mathbb R^{n+1})` that has an absolutely continuous
representative whose derivative is the slice of $`\partial_iU`. This absolute
continuity on lines is what makes composition with a nonsmooth outer function
accessible.

:::theorem "sobolev.coordinate_acl" (parent := "sobolev.calculus") (lean := "SobolevSpace.Slices.ae_coordinateSlice_acl, SobolevSpace.Slices.ae_coordinateACLRepresentative_eq, SobolevSpace.Slices.ae_absolutelyContinuousOnInterval_coordinateACLRepresentative, SobolevSpace.Slices.ae_hasDerivAt_coordinateACLRepresentative, SobolevSpace.Slices.absolutelyContinuousOnInterval_lineRepresentative") (uses := "sobolev.global_density, sobolev.w11_absolute_continuous_representative")
Let $`U\in W^{1,1}(\mathbb R^{n+1})` and choose any coordinate
$`i\in\{1,\ldots,n+1\}`. For almost every complementary-coordinate point
$`y\in\mathbb R^n`, the slice of $`U` on the line
$`t\mapsto (y,t)_i` has an explicit representative
$`\widetilde U_{i,y}` that is absolutely continuous on every compact
interval. It agrees almost everywhere with the selected Sobolev value slice,
and

$$`
  \frac{d}{dt}\widetilde U_{i,y}(t)
  =(\partial_i U)(y,t)_i
  \quad\text{for almost every }t.
`

Thus every global $`W^{1,1}` class is absolutely continuous on almost every
line parallel to every coordinate axis.

The interval form of the theorem fixes $`[a,b]` first, so its null set may
depend on the interval. A single null set also serves every interval: for almost every $`y`
the derivative slice is integrable, and the line representative of an
integrable derivative is absolutely continuous on every compact interval.
:::

:::proof "sobolev.coordinate_acl"
Separate the selected coordinate from its complement by Mathlib's
`Fin.insertNthEquiv`; the induced measurable equivalence preserves Euclidean
volume. Approximate $`U` in the completed graph norm by smooth compactly
supported functions. Fubini gives a subsequence whose value slices and
selected derivative slices converge in $`L^1(\mathbb R)` for almost every
$`y`. Each smooth slice satisfies the classical fundamental theorem. The
normalized line-representative closure theorem passes that identity to the
limit, gives compact-interval absolute continuity, and identifies the
classical derivative with the stored weak derivative almost everywhere.
:::

The ACL theorem is stated for $`W^{1,1}` only. Other exponents are reached by
localization: multiplying by a compactly supported smooth $`\psi` keeps a
$`W^{1,p}` element in $`W^{1,p}`, by the smooth multiplier theorem, and on the
finite-measure support of $`\psi` the exponent can then be lowered to one.
Packaging both steps as one bounded operator lets the next theorem apply a
$`W^{1,1}` identity to a localized $`W^{1,p}` element without changing any of
its coordinates.

:::definition "sobolev.cutoff_to_w11" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.cutoffToW11, SobolevSpace.GraphSpace.cutoffToW11_apply_ae, SobolevSpace.GraphSpace.cutoffToW11NormBound, SobolevSpace.GraphSpace.norm_cutoffToW11_le, SobolevSpace.GraphSpace.cutoffToW11CLM, SobolevSpace.GraphSpace.cutoffToW11CLM_apply, SobolevSpace.GraphSpace.norm_cutoffToW11CLM_le") (uses := "sobolev.finite_measure_support_exponent_restriction, sobolev.weak_leibniz")
Let $`1\le p\le\infty` and let $`\psi` be a smooth compactly supported
function on $`\mathbb R^n`. Multiplication by $`\psi`, followed by
finite-measure-support exponent restriction, defines a continuous linear map

$$`
T_\psi:W^{1,p}(\mathbb R^n)\longrightarrow W^{1,1}(\mathbb R^n).
`

Every coordinate of $`T_\psi U` agrees almost everywhere with the
corresponding coordinate of the localized $`W^{1,p}` value $`\psi U`.
Writing $`M_\psi` for the bounded cutoff operator and
$`S=\operatorname{tsupp}\psi`, one has

$$`
\|T_\psi U\|_{W^{1,1}}
\le
N_{n,1}^{\,1-1/p}\,
|S|^{\,1-1/p}\,
\|M_\psi\|\,
\|U\|_{W^{1,p}},
`

and the same expression bounds $`\|T_\psi\|`. Compactness of $`S` supplies
the finite-measure hypothesis. The localization step of the whole-space
weak-calculus arguments is thus a bounded operator.
:::

The two preceding results are the ingredients of the Lipschitz chain rule on
$`\mathbb R^n`. Rademacher's theorem differentiates $`F` outside a null set;
along almost every coordinate line the ACL representative is absolutely
continuous, so $`F\circ U` is again absolutely continuous on lines with the
expected derivative, and the converse ACL theorem rebuilds a global weak
derivative from these line identities. The cutoff operator extends the
conclusion from $`W^{1,1}` to every exponent.

:::theorem "sobolev.lipschitz_nemytskii_wp" (parent := "sobolev.calculus") (lean := "PDE.Analysis.Calculus.ae_deriv_eq_zero_on_preimage_null, PDE.Analysis.Calculus.LipschitzWith.ae_hasDerivAt_comp, SobolevSpace.Slices.hasWeakDerivativeOn_of_ae_coordinate_acl, SobolevSpace.GraphSpace.hasWeakDerivativeOn_comp_lipschitz, SobolevSpace.GraphSpace.lipschitzComposition_base_ae, SobolevSpace.GraphSpace.lipschitzComposition_derivative_ae") (uses := "sobolev.coordinate_acl, sobolev.cutoff_to_w11, sobolev.weak_derivative")
%%%
source := {
  document := "marcus-mizel-1972"
  spans := #[{
    page := "294-320"
    text := some { path := "Blueprint/Sources/MarcusMizel1972.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0`, let $`1\leq p\leq\infty`, let
$`F:\mathbb R\to\mathbb R` be Lipschitz with $`F(0)=0`, and let
$`U\in W^{1,p}(\mathbb R^n)`. Then $`F\circ U` belongs to
$`W^{1,p}(\mathbb R^n)`, and for every coordinate $`i`,

$$`
  \partial_i(F\circ U)
  =(\operatorname{deriv}F\circ U)\,\partial_iU
  \quad\text{almost everywhere}.
`

The completed graph-space element has base coordinate $`F\circ U` and the
displayed weak derivative coordinate. For finite $`p`, preserving the whole
global space requires $`F(0)=0`: composing with the zero function otherwise
produces a nonzero constant outside $`L^p(\mathbb R^n)`. At $`p=\infty`,
constants belong to $`L^\infty`, so this obstruction disappears. The theorem
uses the zero-preserving hypothesis uniformly across exponents.
:::

:::proof "sobolev.lipschitz_nemytskii_wp"
Rademacher's theorem makes $`F` differentiable outside a null set. The
one-dimensional null-preimage theorem proves that the derivative of an
absolutely continuous inner curve vanishes almost everywhere above that
exceptional set, so the classical Lipschitz chain rule holds almost
everywhere on each coordinate-line representative from
{uses "sobolev.coordinate_acl"}[]. The converse ACL theorem reconstructs
the global $`W^{1,1}` weak derivative by linewise integration by parts and
coordinate Fubini. For general $`p`, localize around an arbitrary test
function by a smooth cutoff. The bounded operator from
{uses "sobolev.cutoff_to_w11"}[] views the localized $`W^{1,p}` element in
$`W^{1,1}` without changing its coordinates almost everywhere. Apply the
$`W^{1,1}` identity and transport it back through the cutoff. Lipschitz
control and $`F(0)=0` give the required $`L^p` bounds, including at
$`p=\infty`, and the graph-space constructor assembles the result.
:::

For a test function supported inside $`\Omega`, we only need the values of
$`U` near that support. Choose a smooth cutoff $`\psi` that equals one there
and vanishes before reaching the boundary. Extending $`\psi U` by zero gives
a whole-space Sobolev function whose values and first derivatives agree with
$`U` wherever the test function contributes to the weak identity. This makes
the chain rule available on every open domain.

:::theorem "sobolev.open_domain_lipschitz_chain_rule" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.hasWeakDerivativeOn_comp_lipschitz_on") (uses := "sobolev.lipschitz_nemytskii_wp, sobolev.graph_space")
Let $`\Omega\subset\mathbb R^n` be open, let $`1\leq p\leq\infty`, and
let $`F:\mathbb R\to\mathbb R` be Lipschitz. For every
$`U\in W^{1,p}(\Omega)`, the composition has weak derivative

$$`
  \partial_i(F\circ U)
  =(\operatorname{deriv}F\circ U)\,\partial_iU.
`

No boundary regularity, finite-volume assumption, or condition on $`F(0)`
is needed for this local identity. The derivative belongs to $`L^p(\Omega)`.
:::

:::proof "sobolev.open_domain_lipschitz_chain_rule"
First subtract $`F(0)` so that the outer map fixes zero. Apply the whole-space
chain rule to the cutoff extension described above. On the support of the
test function, $`\psi=1` and $`\nabla\psi=0`, so the weak identity is exactly
the one for $`U`. Outside that support both test pairings vanish. Restoring
the constant $`F(0)` does not change the derivative.
:::

Global integrability is a separate step. If $`F(0)=0`, the bound
$`|F(U)|\leq\operatorname{Lip}(F)|U|` supplies it even on an unbounded
domain. More generally, finite measure makes the constant offset integrable,
so every Lipschitz scalar map acts on the Sobolev space.

:::theorem "sobolev.domain_lipschitz_nemytskii_wp" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.lipschitzCompositionOfMemLp_base_ae, SobolevSpace.GraphSpace.lipschitzCompositionOfMemLp_derivative_ae, SobolevSpace.GraphSpace.lipschitzCompositionOn_base_ae, SobolevSpace.GraphSpace.lipschitzCompositionOn_derivative_ae") (uses := "sobolev.open_domain_lipschitz_chain_rule")
Under the hypotheses above, if $`F\circ U\in L^p(\Omega)`, then
$`F\circ U\in W^{1,p}(\Omega)`, with the displayed weak derivative.
In particular, this holds for every Lipschitz $`F` when $`\Omega` has finite
measure, including every bounded $`C^1` domain.
:::

:::proof "sobolev.domain_lipschitz_nemytskii_wp"
The Lipschitz constant bounds $`|\operatorname{deriv}F|`, so multiplying
by each weak derivative of $`U` preserves its $`L^p` integrability. The graph
space constructor then has every row it needs. For finite measure, write
$`F(U)=(F(U)-F(0))+F(0)`: the first term is controlled by $`|U|`, and the
second is an integrable constant.
:::

Absolute value is one-Lipschitz and fixes zero, so the Lipschitz theorem
already places $`|U|` in $`W^{1,p}(\mathbb R^n)` with derivative
$`(\operatorname{deriv}|\cdot|\circ U)\,\partial_iU`. What that formula leaves
open is the behaviour of $`\partial_iU` itself on the zero set $`\{U=0\}`. The
theorem below supplies precisely this Stampacchia-type
information, that $`\partial_iU` vanishes almost everywhere on $`\{U=0\}`, and
that is what converts the sign formula into indicator formulas for the
positive and negative parts.

:::theorem "sobolev.finite_exponent_absolute_value" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.hasWeakDerivativeOn_abs, SobolevSpace.GraphSpace.absoluteValue_base_ae, SobolevSpace.GraphSpace.absoluteValue_derivative_ae, SobolevSpace.GraphSpace.positivePart_base_ae, SobolevSpace.GraphSpace.positivePart_derivative_indicator_ae, SobolevSpace.GraphSpace.negativePart_base_ae, SobolevSpace.GraphSpace.negativePart_derivative_indicator_ae, SobolevSpace.GraphSpace.derivative_eq_zero_ae_of_base_eq_zero") (uses := "sobolev.lipschitz_nemytskii_wp, sobolev.weak_derivative")
Let $`1\leq p\leq\infty` and
$`U\in W^{1,p}(\mathbb R^n)`. Then
$`|U|`, $`U^+`, and $`U^-` belong to
$`W^{1,p}(\mathbb R^n)`. For every coordinate $`i`,

$$`
  \partial_i |U|
  =\operatorname{sign}(U)\,\partial_i U
  \quad\text{almost everywhere}.
`

Every first weak derivative vanishes almost everywhere on the zero set
$`\{U=0\}`. Consequently, the positive and negative parts satisfy the sharp
formulas

$$`
  \partial_i U^+
  =\mathbf 1_{\{U>0\}}\,\partial_i U,
  \qquad
  \partial_i U^-
  =-\mathbf 1_{\{U<0\}}\,\partial_i U
`

almost everywhere. Their completed graph-space base coordinates agree with
$`\max(U,0)` and $`\max(-U,0)`, respectively.
:::

:::proof "sobolev.finite_exponent_absolute_value"
Absolute value is one-Lipschitz, fixes zero, and has Mathlib derivative
$`\operatorname{deriv}|\cdot|=\operatorname{sign}`, so the Lipschitz
chain rule gives the displayed formula. Positive and
negative parts are then the graph-space combinations
$`(U+|U|)/2` and $`(|U|-U)/2`. Applying the absolute-value rule again to
the nonnegative function $`U^+` and invoking uniqueness of weak derivatives
shows that $`\partial_iU=0` almost everywhere on $`\{U=0\}`; the indicator
formulas follow.
:::

Vanishing of the gradient on the zero set transfers to every level set
$`\{U=c\}`. The full level-set statement is what makes the derivative of a clamp an open-interval
indicator rather than a sign-difference coefficient that is ambiguous on the
two endpoint levels.

For a concrete clamp, let $`M>0` and set
$`T_M(t)=\max(-M,\min(t,M))`. It leaves values between $`-M` and $`M`
unchanged and caps values outside that interval. For
$`u\in W^{1,p}(\mathbb R^n)`, $`1\leq p<\infty`, the formula becomes

$$`
\nabla(T_Mu)=\mathbf 1_{\{|u|<M\}}\nabla u
\quad\text{a.e.},\qquad
\|\nabla(T_Mu)\|_p\leq\|\nabla u\|_p.
`

The corner in the scalar function $`T_M` produces no extra derivative
concentrated on $`\{u=\pm M\}`: the weak gradient of $`u` vanishes almost
everywhere on those level sets. Truncation therefore bounds the function's
values without increasing its gradient norm, a useful operation when choosing
test functions in energy estimates.

:::theorem "sobolev.finite_exponent_stampacchia_truncation" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.derivative_eq_zero_ae_of_base_eq, SobolevSpace.GraphSpace.hasWeakDerivativeOn_intervalTruncation, SobolevSpace.GraphSpace.intervalTruncation_base_ae, SobolevSpace.GraphSpace.intervalTruncation_derivative_indicator_ae") (uses := "sobolev.finite_exponent_absolute_value")
Let $`1\leq p<\infty`,
$`U\in W^{1,p}(\mathbb R^n)`, and $`c\in\mathbb R`. Every first weak
derivative vanishes almost everywhere on the full level set $`\{U=c\}`:

$$`
  U(x)=c\quad\Longrightarrow\quad \partial_iU(x)=0
  \quad\text{for almost every }x.
`

If $`a\leq0\leq b`, interval truncation defines a completed operation

$$`
  T_{a,b}:W^{1,p}(\mathbb R^n)\longrightarrow W^{1,p}(\mathbb R^n)
`

whose base coordinate is the pointwise clamp and whose derivatives satisfy

$$`
  \partial_i(T_{a,b}U)
  =\mathbf 1_{\{a<U<b\}}\,\partial_iU
  \quad\text{almost everywhere}.
`

The condition $`0\in[a,b]` is necessary for a global operation on the
infinite-measure domain: otherwise a truncated function can approach a
nonzero constant at infinity and fail to belong to $`L^p`.
:::

:::proof "sobolev.finite_exponent_stampacchia_truncation"
To transfer the zero-level Stampacchia theorem to $`\{U=c\}`, compose $`U`
with a smooth one-Lipschitz probe that vanishes at both $`0` and $`c` and
has nonzero derivative at $`c`. The smooth Nemytskii theorem places the probe
in $`W^{1,p}`; its gradient vanishes on its zero set, forcing
$`\partial_iU=0` on $`\{U=c\}`.

For truncation, approximate the clamp by smooth zero-preserving
one-Lipschitz maps. Their values converge pointwise to $`T_{a,b}`, and their
slopes converge to
$`(\operatorname{sign}(U-a)-\operatorname{sign}(U-b))/2`. Dominated
$`L^p` convergence and closedness of weak derivatives give the completed
operation. The full level-set theorem removes the endpoint ambiguity and
turns the sign coefficient into the displayed open-interval indicator.
:::

On finite-measure extension domains the condition $`0\in[a,b]` can be
dropped: restore the constant $`T_{a,b}(0)` after extension and restriction,
exactly as $`F(0)` was restored for Lipschitz maps.

:::theorem "sobolev.extension_domain_interval_truncation" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.hasWeakDerivativeOn_intervalTruncation_on_of_extension, SobolevSpace.GraphSpace.intervalTruncationOnOfExtension_base_ae, SobolevSpace.GraphSpace.intervalTruncationOnOfExtension_derivative_ae, SobolevSpace.GraphSpace.intervalTruncationOnOfExtension_derivative_indicator_ae") (uses := "sobolev.extension_operator, sobolev.finite_exponent_stampacchia_truncation")
Let $`\Omega\subset\mathbb R^n` be open, have finite measure, and be equipped
with a bounded first-order extension operator. Let $`1\leq p<\infty` and
$`U\in W^{1,p}(\Omega)`. For every ordered interval $`a\leq b`, including
intervals not containing zero, the completed truncation satisfies

$$`
  T_{a,b}(U)\in W^{1,p}(\Omega),
  \qquad
  \partial_i(T_{a,b}U)
  =\mathbf 1_{\{a<U<b\}}\,\partial_iU
`

almost everywhere on $`\Omega`. The sign-difference formula is also retained
before the endpoint level sets are removed.
:::

:::proof "sobolev.extension_domain_interval_truncation"
Apply the global truncation theorem to the centered clamp
$`T_{a,b}-T_{a,b}(0)` and the extension of $`U`. Restrict to $`\Omega` and
restore $`T_{a,b}(0)`. The restoration lemma supplies the base and
derivative coordinates, and extension-coordinate agreement replaces the
global extension rows by the original local rows. The level-set theorem then
turns the sign multiplier into the open-interval indicator.
:::

The bounded $`C^1` case follows by inserting the canonical extension operator,
completing for truncation the pattern already followed for Lipschitz and
smooth composition.

:::theorem "sobolev.c1_domain_interval_truncation" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.hasWeakDerivativeOn_intervalTruncation_on, SobolevSpace.GraphSpace.intervalTruncationOn_base_ae, SobolevSpace.GraphSpace.intervalTruncationOn_derivative_indicator_ae") (uses := "sobolev.extension_domain_interval_truncation, sobolev.c1_extension")
Let $`\Omega\subset\mathbb R^n` be a bounded operational $`C^1` domain,
let $`1\leq p<\infty`, and let $`U\in W^{1,p}(\Omega)`. For every ordered
interval $`a\leq b`, the pointwise clamp defines a completed operation

$$`
  T_{a,b}:W^{1,p}(\Omega)\longrightarrow W^{1,p}(\Omega)
`

without requiring $`0\in[a,b]`. Its base coordinate is $`T_{a,b}(U)` and

$$`
  \partial_i(T_{a,b}U)
  =\mathbf 1_{\{a<U<b\}}\,\partial_iU
  \quad\text{almost everywhere on }\Omega.
`

Equivalently, before using the level-set theorem, the weak derivative is
$`(\operatorname{sign}(U-a)-\operatorname{sign}(U-b))\partial_iU/2`.
:::

:::proof "sobolev.c1_domain_interval_truncation"
The operational atlas supplies a finite-measure open domain and the canonical
extension operator. Apply
{uses "sobolev.extension_domain_interval_truncation"}[].
:::

With these composition and truncation rules in place, the remaining slice
results return to supplied continuous representatives. The planar theorem is
the two-dimensional analogue of the one-dimensional fundamental theorem
above, proved by the same localize-and-mollify argument on the horizontal
lines of a rectangle. Unlike the ACL theorem it constructs no representative
and assumes $`F` continuous from the outset.

:::theorem "sobolev.planar_coordinate_acl" (parent := "sobolev.calculus") (lean := "SobolevSpace.Slices.ae_intervalIntegral_weakDerivative_firstCoordinate_eq_sub_on_rectangle") (uses := "sobolev.weak_fundamental_theorem, sobolev.mollifier, sobolev.smooth_multiplier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U\subset\mathbb R^2` be open. Suppose $`F` is continuous and has weak
first-coordinate derivative $`H` on $`U`. If the compact rectangle
$`[a,b]\times[c,d]` lies in $`U`, then for almost every $`s\in[c,d]`,

$$`
  \int_a^b H(r,s)\,dr=F(b,s)-F(a,s).
`

The weak derivative supplies the local integrability needed on a compact
neighborhood of the rectangle.
:::

:::proof "sobolev.planar_coordinate_acl"
Localize by a smooth cutoff supported in a relatively compact open
neighborhood of the rectangle. For the resulting global data, mollification
gives the classical identity on every line. Product-space $`L^1` convergence,
Fubini, and an almost-everywhere convergent subsequence pass the derivative
integrals to almost every transverse coordinate, while continuity controls
the endpoint values.
:::

In axisymmetric $`(r,z)` coordinates the natural one-dimensional paths are the
rays $`z=sr` of fixed slope rather than horizontal lines. Pulling the two weak
derivatives back through the smooth slope chart $`(r,s)\mapsto(r,rs)` with the
coordinate chain rule of this section converts the horizontal-line identity
into one along those rays.

:::theorem "sobolev.slope_coordinate_acl" (parent := "sobolev.calculus") (lean := "SobolevSpace.Slices.ae_intervalIntegral_slopeMap_weakDerivative_eq_sub") (uses := "sobolev.planar_coordinate_acl, sobolev.coordinate_chain_rule")
Let $`\delta>0`, let $`f` be continuous on $`\mathbb R^2`, and suppose that
$`g_r,g_z` are its weak coordinate derivatives on the region
$`\{(r,z):\delta<r\}`. Fix an interval $`[a,b]` contained in
$`\{r>\delta\}` and a bounded interval of slopes. Then for almost every
slope $`s` in that interval,

$$`
  \int_a^b \bigl(g_r(r,rs)+s g_z(r,rs)\bigr)\,dr
    = f(b,bs)-f(a,as).
`

Thus the weak derivative along the slope-chart ray $`r\mapsto(r,rs)` is the
expected chain-rule combination. The theorem concerns one fixed radial
interval; its exceptional null set may depend on the chosen endpoints.
:::

:::proof "sobolev.slope_coordinate_acl"
The proof localizes the two weak coordinate derivatives near the compact
family of rays, pulls them back through the smooth slope map, and applies the
planar coordinate-line FTC. The weak coordinate chain rule identifies the
pulled-back first derivative with $`g_r+s g_z`, while cutoff removal recovers
the original endpoint values.
:::

The slice identities hold for a continuous $`f` whose weak derivatives are
merely locally integrable. When the weak derivatives are themselves
continuous, integration along lines is no longer needed: mollification
converges locally uniformly together with its gradient, and $`f` is
classically differentiable at every point of $`\Omega`. Regularity theorems
use this step to pass from Sobolev solutions to classical ones.

:::theorem "sobolev.continuous_weak_derivatives_are_classical" (parent := "sobolev.calculus") (lean := "SobolevSpace.Approximation.hasFDerivAt_of_continuous_weakPartialDerivatives, SobolevSpace.Approximation.hasFDerivAt_of_continuous_weakPartialDerivativesOn") (uses := "sobolev.weak_derivative, sobolev.mollifier, sobolev.smooth_multiplier")
Let $`\Omega\subseteq\mathbb R^n` be open. Suppose $`f:\mathbb R^n\to\mathbb R`
and its chosen weak coordinate derivatives $`g_i` are continuous, with
$`\partial_i f=g_i` weakly on $`\Omega`. Then at every $`x\in\Omega`, $`f`
has the classical Fréchet derivative

$$`
Df(x)v=\sum_{i=1}^n g_i(x)v_i.
`

The global theorem is the specialization $`\Omega=\mathbb R^n`.
:::

:::proof "sobolev.continuous_weak_derivatives_are_classical"
Mollify $`f` and its continuous weak gradient. Weak differentiation commutes
with convolution, and the approximate identity converges locally uniformly
for both quantities. Mathlib's uniform-limit theorem for derivatives then
identifies the limiting Fréchet derivative. For an open domain, first multiply
by a compactly supported cutoff equal to one near the chosen interior point.
:::

The higher-order results that follow are organized around the graph-space
bundle: an element of $`W^{m,p}(\Omega)` stores an $`L^p` row for every
derivative word of length at most $`m`. Extracting the rows that begin with a
fixed word $`\alpha` leaves a bundle of any order $`r\leq m-|\alpha|`, and
this extraction is the operation that the successor-order assembly theorem
inverts and the higher-order multiplier iterates.

:::definition "sobolev.derivative_word_slice" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.derivativeWordCLM, SobolevSpace.GraphSpace.norm_derivativeWordCLM_apply_le") (uses := "sobolev.graph_space, sobolev.derivative_permutation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-262"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a derivative word $`\alpha` with $`|\alpha|+r\leq m`, coordinate
extraction defines a bounded linear map

$$`
  W^{m,p}(\Omega)\longrightarrow W^{r,p}(\Omega),
  \qquad U\longmapsto D^\alpha U.
`

For the finite-product graph norms used by PDEAtlas this map is contractive:
$`\|D^\alpha U\|_{W^{r,p}}\leq\|U\|_{W^{m,p}}`.
The target bundle contains the coordinates $`D^{\alpha+\beta}U` for
$`|\beta|\leq r`; permutation invariance of weak derivatives makes the map
independent of how the corresponding symmetric multi-index is listed.
:::

Assembly runs in the other direction. If every first derivative $`\partial_iU`
is the base coordinate of an order-$`m` bundle $`V_i`, retain the rows of $`U`
through order $`m` and select each new top-order row from one $`V_i`.
Composing weak-derivative identities certifies the selected rows. On an
arbitrary set the overlapping input rows need not agree; on an open domain,
weak-derivative uniqueness identifies them.

:::theorem "sobolev.successor_order_assembly" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.exists_succOrder_of_firstDerivatives, SobolevSpace.GraphSpace.exists_succOrder_of_firstDerivatives_with_norm, SobolevSpace.GraphSpace.succOrderAssemblyNormBound") (uses := "sobolev.derivative_word_slice, sobolev.graph_space")
Let $`m>0` and $`U\in W^{m,p}(\Omega)`. Suppose that for every coordinate
$`i` there is a bundled field $`V_i\in W^{m,p}(\Omega)` whose base
coordinate is exactly the stored first derivative $`\partial_iU`. Then there
exists $`W\in W^{m+1,p}(\Omega)` whose base coordinate agrees almost
everywhere with that of $`U`.

For $`p=2`, writing $`\mathcal I_{n,m+1}` for the finite derivative index,
the canonical assembly also satisfies

$$`
  \|W\|_{W^{m+1,2}}
  \leq
  \sqrt{\#\mathcal I_{n,m+1}}
  \left(\|U\|_{W^{m,2}}+\sum_{i=1}^n\|V_i\|_{W^{m,2}}\right).
`

The order-$`m` Sobolev control of every first derivative is a hypothesis,
and the estimate bounds the assembled element in terms of it.
:::

:::proof "sobolev.successor_order_assembly"
For a derivative row of order at most $`m`, use the corresponding row of
$`U`. For a new top-order row, write its canonical derivative word as
$`i::\beta` and use the $`\beta` row of $`V_i`. The hypothesis identifies
the base of $`V_i` with the stored first derivative of $`U`. Compose the
first-derivative identity with the weak-derivative identity for that row of
$`V_i`; the graph-space constructor then assembles the finite family.
:::

The successor-order theorem asks for the first derivatives already bundled in
$`W^{m,p}`. In the passage from $`H^1` to $`H^2` that elliptic regularity
needs, one has only $`L^2` functions $`g_{ij}` with
$`\partial_j(\partial_iU)=g_{ij}` weakly. The $`H^2` constructor takes these
rows directly, without first forming each $`\partial_iU` as an $`H^1`
element.

:::theorem "sobolev.h2_derivative_assembly" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.exists_H2_of_firstDerivatives_haveWeakDerivatives") (uses := "sobolev.graph_space, sobolev.weak_derivative")
Let $`U\in H^1(\Omega)` and suppose that for every ordered pair $`i,j` an
$`L^2` function $`g_{ij}` is supplied with

$$`
  \partial_j(\partial_iU)=g_{ij}
`

weakly on $`\Omega`. Then these rows assemble into an
$`H^2(\Omega)` element with the same base function and the same stored first
derivatives as $`U`. Its squared norm is exactly the finite sum of the
integrals of the selected order-zero, order-one, and canonical order-two
rows.

No equation $`g_{ij}=g_{ji}` is an input to this constructor. The symmetric
derivative index stores one canonical ordering for each second-order row.
On an arbitrary non-open set the redundant ordered representatives need not
agree; on open domains they are identified separately by weak-derivative
uniqueness.
:::

:::proof "sobolev.h2_derivative_assembly"
Use the base and first derivative coordinates of $`U` for words of length
zero and one. For each canonical word $`[i,j]`, use $`g_{ij}` and append the
given weak derivative of $`\partial_iU` to the stored weak derivative of
$`U`. The graph-space constructor supplies the bundled $`H^2` element. Its
norm formula is the definition of the finite-product Hilbert norm after the
coordinate identifications.
:::

The multiplier theorems so far take a smooth $`\zeta`. Variational problems
have coefficients that are merely $`W^{1,\infty}(\Omega)`, and they need more
than membership of $`AU` in $`W^{1,2}`: the map $`U\mapsto AU` must be
bounded, with a constant controlled by $`\|A\|_{W^{1,\infty}}`, because this
is the form in which variational and regularity arguments use the product.
The first-order Leibniz identity
$`\partial_i(AU)=A\,\partial_iU+(\partial_iA)U` remains valid for such $`A`,
and both of its terms are $`L^\infty` times $`L^2` products, which is the
source of the estimate.

:::theorem "sobolev.w1top_w12_product" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.norm_w1TopMultiplierCLM_apply_le, SobolevSpace.GraphSpace.norm_w1TopMultiplierCLM_le, SobolevSpace.GraphSpace.norm_w1TopMultiplicationCLM_le, SobolevSpace.GraphSpace.w1TopMultiplicationCLM, SobolevSpace.GraphSpace.w1TopMultiplierCLM, SobolevSpace.GraphSpace.w1TopMultiplierCLM_base_ae, SobolevSpace.GraphSpace.w1TopMultiplierCLM_singleDeriv_apply_ae") (uses := "sobolev.weak_leibniz, sobolev.graph_space")
Let $`\Omega` be open, let $`A\in W^{1,\infty}(\Omega)`, and let
$`U\in W^{1,2}(\Omega)`. Multiplication is a bounded bilinear map

$$`
  M:W^{1,\infty}(\Omega)\longrightarrow
    \mathcal L\bigl(W^{1,2}(\Omega),W^{1,2}(\Omega)\bigr),
  \qquad M(A)(U)=AU.
`

Write $`\mathcal I_{n,1}` for the finite first-order derivative index and set

$$`
  C_n=2\sqrt{\#\mathcal I_{n,1}}.
`

For the actual finite-product graph norms used by PDEAtlas,

$$`
  \|M(A)(U)\|_{W^{1,2}}
    \leq C_n\|A\|_{W^{1,\infty}}\|U\|_{W^{1,2}},
  \qquad
  \|M(A)\|\leq C_n\|A\|_{W^{1,\infty}},
  \qquad
  \|M\|\leq C_n.
`

The explicit dimension-dependent constant is not sharp in general.
The base coordinate represents the pointwise product $`Au`. More precisely,
if $`u` has weak $`i`-th derivative $`d_i u`, then the $`i`-th derivative
row of $`M(A)(U)` is

$$`
  g_i=A\,d_i u+(\partial_iA)u,
  \qquad
  \|g_i\|_{L^2}
  \leq
  \|A\|_{L^\infty}\|d_i u\|_{L^2}
  +\|\partial_iA\|_{L^\infty}\|u\|_{L^2},
`

and $`\partial_i(Au)=g_i` almost everywhere.
:::

:::proof "sobolev.w1top_w12_product"
The weak Leibniz rule gives the derivative formula. Hölder multiplication
$`L^\infty\cdot L^2\to L^2` and the triangle inequality give the displayed
rowwise bound. Bounding every output coordinate by
$`2\|A\|_{W^{1,\infty}}\|U\|_{W^{1,2}}` and summing their squares yields
$`C_n`. Assemble the coordinate formulas as a continuous linear map on the
ambient finite $`L^2` product. The weak Leibniz identity shows that this map
preserves the closed Sobolev graph subspace. Linearity in both factors and
the quantitative estimate then make the construction the bounded
bilinear map $`M`.
:::

Iterating the first-order multiplier through the Sobolev orders is exactly
what extraction and assembly were built for. Extraction places $`A`, $`U`, and
each of their first derivatives in order $`k`, where the Leibniz rows are
formed and estimated by the order-$`k` product; assembly returns those rows to
order $`k+1`. The recursion defining $`C_{n,k}` records the constants of these
two operations, and uniqueness of weak derivatives makes the resulting product
independent of the choices made along the way.

:::theorem "sobolev.higher_order_multiplier" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm, SobolevSpace.GraphSpace.wkTopMultiplierNormBound, SobolevSpace.GraphSpace.norm_wkTopProduct_le, SobolevSpace.GraphSpace.lowerOrderCLM_wkTopProduct, SobolevSpace.GraphSpace.wkTopProduct_one_eq_w1TopMultiplierCLM, SobolevSpace.GraphSpace.wkTopProduct_firstDeriv_apply_ae, SobolevSpace.GraphSpace.wkTopMultiplierCLM_firstDeriv_apply_ae, SobolevSpace.GraphSpace.wkTopMultiplicationCLM_firstDeriv_apply_ae, SobolevSpace.GraphSpace.norm_wkTopMultiplierCLM_apply_le, SobolevSpace.GraphSpace.norm_wkTopMultiplierCLM_le, SobolevSpace.GraphSpace.norm_wkTopMultiplicationCLM_apply_le, SobolevSpace.GraphSpace.norm_wkTopMultiplicationCLM_le, SobolevSpace.GraphSpace.wkTopMultiplicationCLM, SobolevSpace.GraphSpace.wkTopMultiplierCLM, SobolevSpace.GraphSpace.wkTopMultiplicationCLM_base_ae, SobolevSpace.GraphSpace.WkpSpaceOn.exists_mul_WkTop_WkTwo") (uses := "sobolev.derivative_word_slice, sobolev.w1top_w12_product, sobolev.successor_order_assembly")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "261-262"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open set and for every positive integer $`k`, multiplication is a
bounded bilinear map

$$`
  M_k:W^{k,\infty}(\Omega)\longrightarrow
    \mathcal L\bigl(W^{k,2}(\Omega),W^{k,2}(\Omega)\bigr),
  \qquad M_k(A)(U)=AU.
`

Its base coordinate agrees almost everywhere with the pointwise product, and
the actual graph norms satisfy an explicit recursive estimate. Set

$$`
  C_{n,1}=2\sqrt{\#\mathcal I_{n,1}},
  \qquad
  C_{n,k+1}
  =
  \sqrt{\#\mathcal I_{n,k+1}}\,(1+2n)\,C_{n,k}
  \quad(k\geq1).
`

Then

$$`
  \|M_k(A)(U)\|_{W^{k,2}}
    \leq C_{n,k}\|A\|_{W^{k,\infty}}\|U\|_{W^{k,2}},
  \qquad
  \|M_k(A)\|\leq C_{n,k}\|A\|_{W^{k,\infty}},
  \qquad
  \|M_k\|\leq C_{n,k}.
`

This is stronger than the smooth-cutoff case but remains specific to an
$`L^2` target factor. The displayed constant is elementary, not sharp.

The chosen products are coherent across Sobolev order. If
$`1\leq r\leq k`, then

$$`
  \pi_{k,r}\bigl(M_k(A)(U)\bigr)
  =
  M_r\bigl(\pi_{k,r}A\bigr)\bigl(\pi_{k,r}U\bigr).
`

At $`r=1` this agrees, by graph-space uniqueness, with the dedicated
first-order multiplier. Consequently every first
derivative coordinate of the higher-order operator satisfies

$$`
  \partial_i(AU)
  =A\,\partial_iU+(\partial_iA)U
  \quad\text{almost everywhere}.
`

The existential closure theorem is used only to construct this canonical
operator. Applications use $`M_k` itself, so independently chosen product
witnesses do not leak into elliptic regularity, localization, or pullback
arguments.
:::

:::proof "sobolev.higher_order_multiplier"
The first-order product theorem supplies the base case. At each successor
order, extraction by derivative words places the two factors and every first
derivative in the previous Sobolev order; the Leibniz sums are formed there
and then assembled into the next graph-space bundle. Weak-derivative
uniqueness supplies both compatibility of the assembled rows and uniqueness
of the product from its base coordinate.

Derivative-word extraction is contractive. If the order-$`k` product is
bounded by $`C_{n,k}`, the undifferentiated product row has that bound and
each of the $`n` Leibniz rows has bound
$`2C_{n,k}\|A\|\|U\|`. The quantitative successor-order assembly theorem
therefore gives the displayed recurrence. Choose the unique product and
prove linearity in each factor by comparing base coordinates. The recursive
estimate then makes the linear maps bounded, first for a
fixed coefficient and then as the bilinear operator $`M_k`. Order
restriction preserves the base coordinate, so uniqueness proves the
naturality identity. Restricting to order one and invoking the first-order
coordinate theorem gives the displayed first-row Leibniz formula.
:::

The first-order multiplier takes its coefficient in $`W^{1,\infty}(\Omega)`;
the order-$`k` multiplier requires $`W^{k,\infty}(\Omega)`. A globally
Lipschitz representative of an $`L^\infty(\Omega)` coefficient supplies the
first-order element: its almost-everywhere line derivatives are bounded by
its Lipschitz constant and give the weak derivative rows.

:::definition "sobolev.lipschitz_coefficient_package" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.w1TopOfLipschitzRepresentative, SobolevSpace.GraphSpace.w1TopOfLipschitzRepresentative_base_ae") (uses := "sobolev.coordinate_acl, sobolev.graph_space")
Let $`\Omega` be measurable. Suppose an $`L^\infty(\Omega)` class $`F` has
a globally Lipschitz representative $`f:\mathbb R^n\to\mathbb R` and that
$`F=f` almost everywhere on $`\Omega`. Then the representative and its
Rademacher weak partial derivatives determine a canonical bundled element of
$`W^{1,\infty}(\Omega)` whose base coordinate is $`F`.

The construction accepts the $`L^\infty` class and the globally defined
representative separately. This is useful for elliptic coefficients, where
the variational object is an almost-everywhere class but coefficient
regularity is stated for a concrete Lipschitz function.

The construction uses Rademacher's theorem to obtain almost-everywhere line
derivatives of $`f`; the global Lipschitz constant bounds every coordinate
derivative in $`L^\infty`. Restrict the weak derivative identities to the
measurable domain, replace the base representative by the agreeing class
$`F`, and assemble the base and first derivative rows in graph space.
:::

Inverting a uniformly elliptic coefficient is the first use of this element.
The reciprocal is not globally Lipschitz, but it becomes so once its argument
is clipped at $`\delta`.

:::definition "sobolev.positive_reciprocal_coefficient" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.positiveReciprocal, SobolevSpace.GraphSpace.positiveReciprocal_eq_inv, SobolevSpace.GraphSpace.positiveReciprocalW1Top, SobolevSpace.GraphSpace.positiveReciprocalW1Top_base_ae") (uses := "sobolev.lipschitz_coefficient_package")
For $`\delta>0`, define the globally safe reciprocal

$$`
  R_\delta(t)=\frac1{\max\{\delta,t\}}.
`

This map is bounded and globally Lipschitz. Hence, for every globally
Lipschitz scalar field $`a:\mathbb R^n\to\mathbb R` and every measurable
domain $`\Omega`, $`R_\delta\circ a` has a canonical
$`W^{1,\infty}(\Omega)` element. Its base coordinate agrees almost
everywhere on $`\Omega` with $`R_\delta\circ a`, which equals $`a^{-1}`
at every point where $`a\geq\delta`.

This first-order construction is meant for uniformly elliptic
coefficients, where the singular reciprocal is only needed on $`a\geq\delta`.

The maximum map is one-Lipschitz and keeps its output above $`\delta`; the
identity $`|x^{-1}-y^{-1}|=|x-y|/|xy|` therefore gives the explicit
Lipschitz constant $`\delta^{-2}`. Composition with the Lipschitz coefficient
remains globally Lipschitz and bounded by $`\delta^{-1}`. The preceding
Lipschitz construction applies, and $`\max\{\delta,a\}=a` on the positive
region gives the reciprocal identity.
:::

Higher-order regularity theory needs $`1/a` in $`W^{k,\infty}`, where the
Lipschitz construction no longer suffices and $`a` is assumed $`C^k`. The
two hypotheses offered below, a bounded domain or a coefficient that is
constant outside a compact set, are two ways of guaranteeing that the
classical derivatives of the safe reciprocal of $`a` are bounded through order
$`k`.

:::theorem "sobolev.higher_order_positive_reciprocal" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.WkpSpaceOn.exists_reciprocal_of_contDiff_bounded, SobolevSpace.GraphSpace.WkpSpaceOn.exists_reciprocal_of_contDiff_compactPerturbation") (uses := "sobolev.positive_reciprocal_coefficient, sobolev.graph_space")
Let $`a:\mathbb R^n\to\mathbb R` be globally $`C^k` and satisfy
$`a\geq\delta>0` almost everywhere on $`\Omega`.

* If $`\Omega` is bounded, then the selected reciprocal representative
  $`a^{-1}` is the base coordinate of some
  $`W^{k,\infty}(\Omega)` element.
* On an arbitrary domain, the same conclusion holds if $`a` equals a
  constant outside a compact set.

The theorem asserts existence of this element, without explicit bounds on
its derivatives.
:::

:::proof "sobolev.higher_order_positive_reciprocal"
Compose $`a` with a globally smooth safe inverse agreeing with $`t^{-1}` for
$`t\geq\delta`. On a bounded domain, every continuous classical derivative
through order $`k` is bounded and hence belongs to $`L^\infty`. For the
compact-perturbation variant, subtract the limiting constant: all nonzero
derivatives retain compact support, while the zero-order row is a bounded
compact perturbation of a constant. The classical-to-Sobolev constructor
assembles these rows, and positivity identifies the base with the
reciprocal almost everywhere.
:::

Boundary flattening in the regularity chapters requires the coordinate chain
rule of this section at second order. The Hessian formula below is stated for
a $`C^2` chart with $`C^1` inverse: the first-order rule supplies the gradient
row, and differentiating that row once more brings in both the stored second
derivatives of $`U`, reached through derivative-word extraction, and the
second derivatives of the chart.

The extra chart term is already necessary in one dimension:

$$`
(u\circ E)''
 =u''(E)(E')^2+u'(E)E''.
`

Taking $`u(t)=t` makes the first term zero, while the left side is
$`E''`. Even a linear function acquires a second derivative under a
curved change of coordinates. The second sum in the Hessian formula below
records exactly this effect; it vanishes for affine charts.

:::theorem "sobolev.second_order_coordinate_chain_rule" (parent := "sobolev.calculus") (lean := "SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_firstSobolevPullbackRow, SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_secondSobolevPullbackRow") (uses := "sobolev.coordinate_chain_rule, sobolev.global_approximation, sobolev.derivative_word_slice")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`E` be a $`C^2` coordinate chart with $`C^1` inverse, let $`V` be open,
and suppose $`V\subseteq K\subseteq E.\mathrm{target}` for a compact set $`K`.
For $`U\in H^2(E.\mathrm{target})`, the first weak derivative on the open
pullback $`E^{-1}(V)` is the usual gradient chain-rule row, and the second
weak derivative is the classical Hessian chain-rule row

$$`
  \partial_{ik}(U\circ E)
  =\sum_{j,l}(\partial_{lj}U)\circ E\,
       \partial_iE_l\,\partial_kE_j
   +\sum_j(\partial_jU)\circ E\,\partial_{ik}E_j.
`

No smoothness of $`U` is assumed. The compact set controls localization and
$`L^2` estimates; the distributional identity itself is stated on an open
domain.
:::

:::proof "sobolev.second_order_coordinate_chain_rule"
Approximate $`U` smoothly on the compact target set, apply the classical
second-order chain rule, transport each derivative row through the chart,
and use $`L^2` closedness of weak derivatives to identify the limit with the
canonical graph-space rows of $`U`. Finally restrict the compact-carrier
identity to the open pullback patch.
:::

:::definition "sobolev.localized_h2_pullback" (parent := "sobolev.calculus") (lean := "SobolevSpace.WeakChangeOfVariables.localizedH2Pullback") (uses := "sobolev.second_order_coordinate_chain_rule, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The base, gradient, and Hessian chain-rule rows form one localized
order-two graph-space element on the compact source patch. Because that patch
need not be open, this object records the weak identities required by chart
localization; open-domain uniqueness is not available to make it an intrinsic
$`H^2` function on the patch.

The element is constructed for each $`U` separately, with no continuous
linear map between Sobolev spaces.
:::

The regularity estimates need the size of this element in terms of the
chart.

:::theorem "sobolev.localized_h2_pullback_bound" (parent := "sobolev.calculus") (lean := "SobolevSpace.WeakChangeOfVariables.norm_localizedH2Pullback_sq_le") (uses := "sobolev.localized_h2_pullback")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The squared norm of the localized pullback is bounded by the finite sum of
the explicit base-, gradient-, and Hessian-row chart constants:

$$`
  \left\|\mathcal P^{(2)}_{E,K}U\right\|^2
  \leq \sum_{a\in\mathcal I_{n,2}} C_a(E,K,U)^2.
`

Here $`\mathcal I_{n,2}` indexes all derivative rows of order at most two.
Keeping the finite sum explicit leaves every dimension-dependent coordinate
multiplicity visible rather than hiding it in an unspecified constant. Each
row constant has the form $`C_a(E,K,U)=c_a(E,K)\,\|U\|`, built from the norm
of the localized first-order pullback and the chart coefficient bounds, so the
estimate is uniform and linear:
$`\|\mathcal P^{(2)}_{E,K}U\|\leq C(E,K)\|U\|` with
$`C(E,K)^2=\sum_a c_a(E,K)^2`.
:::

:::proof "sobolev.localized_h2_pullback_bound"
Expand the squared norm of the bundled graph-space element as the finite sum
of the squared $`L^2` norms of its base, gradient, and Hessian rows. The
localized first- and second-order chain rules identify those rows with the
displayed coordinate formulas. Apply the corresponding chart estimate to
each row and sum the inequalities over the finite derivative index set.
:::

# Minors of the weak Jacobian

For a map $`u=(u_1,\dots,u_m)` with components in $`W^{1,p}(\Omega)` and a
choice of $`m` columns $`\sigma(1),\dots,\sigma(m)`, the minor

$$`
M_\sigma(u)=\det\bigl(\partial_{\sigma(j)}u_i\bigr)_{i,j=1}^m
`

is a polynomial of degree $`m` in the weak derivatives. Weak convergence does
not commute with products, so there is no reason in general for
$`M_\sigma(u_k)` to converge weakly when $`u_k` does. It does converge for
exponents above $`m`, because a minor is a divergence. This is the mechanism
behind polyconvex energies and determinant constraints in the calculus of
variations.

:::definition "sobolev.weak_jacobian_minor" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.wkpJacobianMinorLp, SobolevSpace.GraphSpace.wkpSelectedJacobianCLM, SobolevSpace.GraphSpace.wkpSelectedJacobianCLM_apply_ae, SobolevSpace.GraphSpace.coeFn_wkpJacobianMinorLp, SobolevSpace.GraphSpace.wkpJacobianMinorLp_ae_eq_of_contDiffOn, SobolevSpace.GraphSpace.continuous_wkpJacobianMinorLp, SobolevSpace.GraphSpace.isBounded_wkpJacobianMinorLp_range, SobolevSpace.GraphSpace.wkpJacobianDetLp, SobolevSpace.GraphSpace.coeFn_wkpJacobianDetLp") (uses := "sobolev.graph_space, sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n`, $`1\le p`, $`m\ge1` with $`p/m\ge1`, and
$`\sigma:\{1,\dots,m\}\to\{1,\dots,n\}`. For
$`u\in W^{1,p}(\Omega)^m` the selected Jacobian
$`(\partial_{\sigma(j)}u_i)_{i,j}` is a matrix-valued $`L^p` function, and its
determinant $`M_\sigma(u)` is an element of $`L^{p/m}(\Omega)`. It agrees
almost everywhere with the determinant of the weak partial derivatives. If
$`\Omega` is open and the components of $`u` have a common $`C^1`
representative $`f`, then $`M_\sigma(u)` is the corresponding minor of the
Jacobian matrix of $`f`. For $`p<\infty` the map $`u\mapsto M_\sigma(u)` is
continuous from $`W^{1,p}(\Omega)^m` to $`L^{p/m}(\Omega)`, and it sends
bounded sets to bounded sets. The case $`m=n`, $`\sigma=\mathrm{id}` is the
Jacobian determinant $`\det Du\in L^{p/n}(\Omega)`.
:::

The next identity writes a minor of degree $`m+1` as a divergence of
products of one value with minors of degree $`m`. For smooth maps it is the
cofactor expansion together with the Piola identity, which says that the
rows of the cofactor matrix are divergence free.

:::theorem "sobolev.jacobian_minor_divergence" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.testFunctionPairing_wkpJacobianMinorLp, SobolevSpace.integral_det_jacobianMatrix_submatrix_mul_test") (uses := "sobolev.weak_jacobian_minor, sobolev.interior_approximation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open.

1. If $`u\in C^2(\Omega;\mathbb R^m)`, $`A` is the selected square Jacobian
   $`(\partial_{\sigma(j)}u_i)`, $`k` is a row index, and $`\varphi` is a test
   function supported in $`\Omega`, then

   $$`
   \int_\Omega\det A\,\varphi\,dx
     =-\sum_j\int_\Omega u_k\,(\operatorname{adj}A)_{jk}\,
       \partial_{\sigma(j)}\varphi\,dx .
   `

2. Let $`m\ge1`, $`p<\infty`, and let the exponents satisfy
   $`\frac{m+1}{p}=\frac1p+\frac mp` with $`p/m\ge1` and $`p/(m+1)\ge1`. For
   $`U=(U_0,\dots,U_m)\in W^{1,p}(\Omega)^{m+1}` and every test function
   $`\varphi`,

   $$`
   \int_\Omega M_\sigma(U)\,\varphi\,dx
     =-\sum_{j=0}^m(-1)^j\int_\Omega\partial_{\sigma(j)}\varphi\;U_0\;
       M_{\sigma\circ\delta_j}(U_1,\dots,U_m)\,dx,
   `

   where $`\sigma\circ\delta_j` omits the column $`\sigma(j)`.
:::

:::proof "sobolev.jacobian_minor_divergence"
For a $`C^2` map, $`\det A\,\varphi` is the divergence of the flux with
components $`u_k(\operatorname{adj}A)_{jk}\varphi`, up to the term with
$`\partial\varphi`, because the cofactor rows are divergence free: the
mixed second derivatives cancel in pairs. Integrating against a test function
supported in the open set removes the boundary. For Sobolev maps, both sides
of the second identity are continuous in $`U` for the $`W^{1,p}` norm, by
Hölder's inequality and the continuity of minors. Smooth maps are dense in
$`W^{1,p}(\Omega)` on every open set, by the Meyers–Serrin argument built on
{uses "sobolev.interior_approximation"}[], so the identity passes from smooth
maps to all of $`W^{1,p}(\Omega)^{m+1}`. No boundary regularity is used.
:::

The divergence form is what makes weak continuity possible. In the
right-hand side one factor converges strongly and the other weakly, and such
a product does converge in the sense of distributions.

:::theorem "sobolev.jacobian_minor_weak_continuity" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.tendsto_weak_wkpJacobianMinorLp_of_strong_base, SobolevSpace.GraphSpace.tendsto_weak_wkpJacobianMinorLp_one, SobolevSpace.GraphSpace.tendsto_weak_wkpJacobianMinorLp_succ_of_strong_base, SobolevSpace.GraphSpace.tendsto_weak_wkpJacobianMinorLp_of_c1Domain, SobolevSpace.GraphSpace.RellichKondrachov.baseCoordinate_isCompactOperator_of_c1Domain") (uses := "sobolev.jacobian_minor_divergence, sobolev.rellich_full_subcritical")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open, let $`q` be real, and let
$`0<m<q` with $`q/m\ge1`. Suppose $`u_k\rightharpoonup u` weakly in
$`W^{1,q}(\Omega)^m` and each component converges strongly in
$`L^q(\Omega)`. Then

$$`
M_\sigma(u_k)\rightharpoonup M_\sigma(u)\quad\text{weakly in }L^{q/m}(\Omega).
`

If $`n\ge2` and $`\Omega` carries the operational $`C^1` atlas, the strong
convergence is automatic: the map $`W^{1,p}(\Omega)\to L^p(\Omega)` that
forgets the derivatives is compact for every finite $`p\ge1`, so weak
convergence in $`W^{1,q}(\Omega)^m` alone implies weak convergence of every
minor of degree $`m<q`.
:::

:::proof "sobolev.jacobian_minor_weak_continuity"
Induction on $`m`. A minor of degree one is a weak derivative, a continuous
linear function of $`u`, and continuous linear maps preserve weak
convergence. For degree $`m+1`, the divergence identity pairs $`U_0`, which
converges strongly in $`L^q`, with minors of degree $`m`, which converge
weakly in $`L^{q/m}` by induction. Each term of the identity therefore
converges when tested against a fixed $`\varphi`. Weakly convergent sequences
are bounded, so the minors of degree $`m+1` are bounded in
$`L^{q/(m+1)}`. Since $`m+1<q`, that exponent is larger than one and the
space is reflexive. Every subsequence has a weakly convergent subsequence, the
test functions identify its limit as $`M_\sigma(u)`, and so the whole
sequence converges. On a $`C^1` domain a compact operator turns weak
convergence into strong convergence; compactness at every finite exponent,
including $`p\ge n`, comes from compactness below $`n` on the same bounded
domain, as in {uses "sobolev.rellich_full_subcritical"}[].
:::

For $`m=n` this is the theorem used for polyconvex energies. The domain
hypothesis is stated with a bounded $`C^1` graph boundary, from which the
operational atlas is built.

:::theorem "sobolev.jacobian_determinant_weak_continuity" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.tendsto_weak_wkpJacobianDetLp_of_c1GraphBoundary, SobolevSpace.GraphSpace.wkpJacobianDetLift, SobolevSpace.GraphSpace.coeFn_wkpJacobianDetLift, SobolevSpace.GraphSpace.tendsto_weak_wkpJacobianDetLift_of_c1GraphBoundary") (uses := "sobolev.jacobian_minor_weak_continuity, sobolev.extension.atlas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n`, $`n\ge1`, be bounded and open with
$`C^1` graph boundary, and let $`q>n` be real. If
$`u_k\rightharpoonup u` weakly in $`W^{1,q}(\Omega;\mathbb R^n)`, then

$$`
\det Du_k\rightharpoonup\det Du\quad\text{weakly in }L^{q/n}(\Omega).
`

The pair $`(Du,\det Du)`, packed as one function with values in
$`\mathbb R^{n\times n+1}`, lies in $`L^{q/n}(\Omega;\mathbb R^{n\times n+1})`,
and $`(Du_k,\det Du_k)\rightharpoonup(Du,\det Du)` weakly there.
:::

:::proof "sobolev.jacobian_determinant_weak_continuity"
In dimension one the determinant is the derivative itself, which is linear.
Otherwise the bounded $`C^1` graph boundary yields an operational atlas, and
the previous theorem applies with $`m=n` and $`\sigma=\mathrm{id}`. For the
pair, the gradient component is the composition of the gradient with the
inclusion $`L^q\subseteq L^{q/n}` on a set of finite measure, a continuous
linear map, so it converges weakly as well. A pair of weakly convergent
components converges weakly in the product.
:::

The constraint $`\det Du=\rho` is not convex, but the weak continuity makes
it closed under the convergence the direct method produces.

:::theorem "sobolev.jacobian_determinant_fibers" (parent := "sobolev.calculus") (lean := "SobolevSpace.GraphSpace.isSeqClosed_weak_setOf_jacobianDet_eq_ae, SobolevSpace.GraphSpace.isSeqClosed_weak_fiber_wkpJacobianDetLp") (uses := "sobolev.jacobian_determinant_weak_continuity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the hypotheses of the previous theorem, for every
$`\rho\in L^{q/n}(\Omega)` the set

$$`
\{u\in W^{1,q}(\Omega;\mathbb R^n):\det Du=\rho\ \text{a.e.}\}
`

is sequentially closed for the weak topology of $`W^{1,q}(\Omega;\mathbb R^n)`.
:::

:::proof "sobolev.jacobian_determinant_fibers"
If $`u_k` lies in the set and converges weakly to $`u`, then
$`\det Du_k=\rho` for every $`k` and $`\det Du_k\rightharpoonup\det Du`.
Weak limits in $`L^{q/n}` are unique, so $`\det Du=\rho`.
:::
