/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Inequalities.MorreyEmbeddings
import PDE.Elliptic.Variational.PrincipalForms
import PDE.Spaces.Sobolev.Inequalities.Hardy.ChartLocal
import PDE.Spaces.Sobolev.Inequalities.Hardy.Classical
import PDE.Spaces.Sobolev.Inequalities.Hardy.Domain
import PDE.Spaces.Sobolev.Inequalities.Hardy.FiniteExponentCompletion
import PDE.Spaces.Sobolev.Inequalities.Hardy.HalfLine
import PDE.Spaces.Sobolev.Inequalities.Hardy.HalfSpace
import PDE.Spaces.Sobolev.Inequalities.Hardy.HalfSpaceCompletion
import PDE.Spaces.Sobolev.Inequalities.Hardy.Lp
import PDE.Spaces.Sobolev.Inequalities.Hardy.Weighted
import PDE.Spaces.Sobolev.Inequalities.Poincare.BoundedDomain

/-!
# Poincaré and Hardy inequalities

This module proves the bounded-domain Poincaré estimate, the classical $`L^p`
Hardy inequality on smooth and completed zero-trace spaces for the half-line,
the upper half-space and $`C^1` atlas domains, and the iterated weighted
$`p=2` inequality.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Poincaré and Hardy Inequalities" =>

Poincaré and Hardy inequalities both control a lower-order quantity by a
derivative, but they encode different geometry. Poincaré removes the constant
mode through a zero-trace condition on a bounded domain. Hardy controls the
singular quotient $`u(r)/r` through zero-trace closure at the endpoint of the
positive half-line. In the completed theories, division is constructed as a
bounded operator from the compactly supported smooth core. The analytic issue
is integrability near the boundary: forming $`u(r)/r` for $`r>0` is easy,
but proving that it remains in $`L^p` requires the estimate. Changing a
representative on a null set does not remove this issue.

Poincaré holds on $`H^1_0` for arbitrary bounded sets. It also controls the
full $`W^{1,p}_0` graph norm by the weak gradient for every finite
$`p\geq1` on a bounded set in positive dimension.

A power near the endpoint shows what Hardy controls. Let $`p>1` and
$`u(r)=r^\alpha` near zero, with $`\alpha>0`, and smoothly cut it off
away from zero. Both $`u'(r)=\alpha r^{\alpha-1}` and
$`u(r)/r=r^{\alpha-1}` are in $`L^p` near zero exactly when

$$`
p(\alpha-1)>-1,\qquad\text{equivalently}\qquad
\alpha>1-\frac1p.
`

All these powers tend to zero at the endpoint, but the slower ones fail
this integrability condition. A pointwise boundary value of zero is
therefore not enough: the Sobolev derivative bound controls how rapidly
the function may approach that value.

# Poincaré and Hardy estimates

:::theorem "sobolev.poincare" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.exists_poincare_H10") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "289-291"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0` and let $`\Omega\subseteq\mathbb R^n` be any bounded set.
There is $`C\geq0` such that every $`u\in H^1_0(\Omega)` satisfies

$$`
\|u\|_{L^2(\Omega)}
  \leq C\sum_{i=1}^n\|\partial_i u\|_{L^2(\Omega)}.
`

This is the zero-boundary form of the Poincaré inequality. By zero-trace
closure, $`\Omega` is only assumed bounded, with no measurability or boundary
regularity. The norm on the left
is the zeroth coordinate of the bundled $`H^1` graph element, and the terms
on the right are its first weak-derivative coordinates.
:::

:::proof "sobolev.poincare" (uses := "sobolev.poincare_explicit")
Since $`n>0`, one of $`n=1`, $`n=2`, or $`n>2` holds. Choose the
corresponding nonnegative constant from the explicit dimension branches. Each
estimate holds for every $`u\in H^1_0(\Omega)`, so it supplies the required
constant independently of $`u`.
:::

For a quantitative coercivity estimate, the choice of constant matters.

:::theorem "sobolev.poincare_explicit" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.norm_baseCoord_le_poincareConst_mul_sum_derivCoord, SobolevSpace.GraphSpace.norm_baseCoord_le_poincareConstTwo_mul_sum_derivCoord, SobolevSpace.GraphSpace.norm_baseCoord_le_poincareConstOne_mul_sum_derivCoord, SobolevSpace.GraphSpace.poincareConst, SobolevSpace.GraphSpace.poincareConstTwo, SobolevSpace.GraphSpace.poincareConstOne") (uses := "sobolev.h10_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "279-280"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be bounded; no measurability or
regularity of $`\Omega` is assumed. The three dimension branches of
{bpref "sobolev.poincare"}[] are separate theorems with named constants. For
every $`u\in H^1_0(\Omega)`,

$$`
\|u\|_{L^2(\Omega)}
  \leq C\sum_{i=1}^n\|\partial_iu\|_{L^2(\Omega)},
`

where the constant is

- $`C=C_{n,\Omega}` when $`n>2`: Mathlib's constant in
  the Sobolev inequality for $`C^1` functions supported in $`\Omega` at the
  exponents $`p=q=2`;
- $`C=C_{1,2}(\Omega)\,|\Omega|^{1/2}` when $`n=2`,
  where $`C_{1,2}(\Omega)` is the same Mathlib constant for the critical pair
  $`p=1`, $`q=2`;
- $`C=|\Omega|` when $`n=1`.

Here $`|\Omega|` is Lebesgue measure. The left side is the base coordinate
of the bundled element and the right side sums its $`n` first-derivative
coordinates. For $`n>2` the estimate is the case $`q=p=2` of Evans's
$`W^{1,p}_0` estimate on bounded open sets. The two low-dimensional branches
are separate arguments, because $`p=2` is critical in dimension two and
supercritical in dimension one.
:::

:::proof "sobolev.poincare_explicit" (uses := "sobolev.gns")
Each branch is first proved for a test function $`\varphi` supported in
$`\Omega`. For $`n>2`, the Sobolev inequality for functions supported in a
set of finite measure, at $`p=q=2`, bounds $`\|\varphi\|_2` by
$`C_{n,\Omega}` times the sum of the partial-derivative norms. For $`n=2`,
the same inequality at $`p=1`, $`q=2` gives
$`\|\varphi\|_2\leq C_{1,2}(\Omega)\sum_i\|\partial_i\varphi\|_1`, and
Hölder on the bounded support gives
$`\|\partial_i\varphi\|_1\leq|\Omega|^{1/2}\|\partial_i\varphi\|_2`. For
$`n=1`, the fundamental theorem of calculus gives
$`\|\varphi\|_\infty\leq\|\varphi'\|_1`, and two finite-measure
comparisons give $`\|\varphi\|_2\leq|\Omega|^{1/2}\|\varphi\|_\infty` and
$`\|\varphi'\|_1\leq|\Omega|^{1/2}\|\varphi'\|_2`.

In each case the set of $`u\in H^1(\Omega)` satisfying the inequality is
closed, because both sides are continuous in the graph norm, and it contains
the test functions. The closure principle of {uses "sobolev.h10_space"}[]
extends the inequality to all of $`H^1_0(\Omega)`.
:::

A containing coordinate slab gives a simpler computable constant. The
other coordinates need not be bounded, and corners cause no additional
boundary condition.

:::theorem "sobolev.poincare_slab" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.eLpNorm_le_measure_mul_eLpNorm_partialDeriv, SobolevSpace.GraphSpace.norm_baseCoord_le_measure_mul_derivCoord_of_slab, SobolevSpace.GraphSpace.dirichletForm_coercive_bound_of_slab") (uses := "sobolev.h10_space")
Let $`n\geq1` and suppose $`\Omega\subseteq\{x:a\leq x_i\leq b\}`.
With $`\ell=\max(b-a,0)`, every $`u\in H^1_0(\Omega)` satisfies

$$`\|u\|_{L^2(\Omega)}\leq\ell\|\partial_i u\|_{L^2(\Omega)}.`

The full graph norm therefore obeys the explicit Dirichlet coercivity bound

$$`\frac{\|u\|_{H^1}^2}{1+\ell^2}\leq
\int_\Omega |\nabla u|^2.`

In particular, a unit-width slab gives the constant $`1/2`, including
for the three-dimensional unit cube. No smooth boundary or numerical
approximation of a Sobolev constant is needed.
:::

:::proof "sobolev.poincare_slab"
On each coordinate line, the fundamental theorem of calculus bounds the
function by the $`L^1` norm of its derivative. Two applications of Hölder
on $`[a,b]` give the factor $`\ell`. Squaring and integrating over the
remaining coordinates proves the smooth estimate by Fubini. The coordinate
split preserves Euclidean volume.

Both coordinate norms are continuous on $`H^1`, so density carries the
same inequality to $`H^1_0`. Squaring it and using
$`\|\partial_i u\|_2^2\leq\|\nabla u\|_2^2` gives the displayed
bound for $`\|u\|_{H^1}^2=\|u\|_2^2+\|\nabla u\|_2^2`.
:::

Hardy's inequality replaces the zero-trace condition on a bounded domain by
vanishing at the endpoint of the half-line, and it controls the singular
quotient $`u(x)/x` rather than $`u` itself. Every Hardy estimate of the
chapter rests on one integration-by-parts identity on a finite interval in
which only the left endpoint value is assumed to vanish.

:::theorem "sobolev.hardy_lp_interval" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardy_interval_lp_identity, SobolevSpace.Hardy.hardy_interval_lp")
Let $`0<\varepsilon<R`, let $`p>1`, and let $`u:\mathbb R\to\mathbb R` be
$`C^1` with $`u(\varepsilon)=0`. Then

$$`
\int_\varepsilon^R \frac{|u(x)|^p}{x^p}\,dx
\leq
\left(\frac{p}{p-1}\right)^p
\int_\varepsilon^R |u'(x)|^p\,dx.
`

Only the left endpoint is fixed. The exact integration-by-parts identity is

$$`
(p-1)\int_\varepsilon^R\frac{|u(x)|^p}{x^p}\,dx
+ |u(R)|^pR^{1-p}
=
p\int_\varepsilon^R
  |u(x)|^{p-2}u(x)u'(x)x^{1-p}\,dx.
`

The right-endpoint term is nonnegative and may therefore be discarded when
deriving the inequality; no condition $`u(R)=0` is needed.
:::

:::proof "sobolev.hardy_lp_interval"
Differentiate $`|u|^p`, integrate it against $`x^{1-p}`, and retain the
right-endpoint contribution. For $`a,b\geq0` and $`c>0`, scaled Young
inequality gives

$$`
p\,a^{p-1}b
\leq
(p-1)c\,a^p+c^{-(p-1)}b^p.
`

Bound the signed mixed term by its absolute value. Then apply the inequality
pointwise with $`a=|u(x)|/x`, $`b=|u'(x)|`, and
$`c=(p-1)/p`. After integration, the first term is absorbed into the left
side, and $`c^{-p}=(p/(p-1))^p` gives the displayed constant.
:::

Compact support inside $`(0,\infty)` removes the finite interval from the
statement without changing the constant.

:::theorem "sobolev.hardy_lp_smooth_core" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardy_Ioi_lp_of_support_subset_Ioo, SobolevSpace.Hardy.hardy_Ioi_lp_of_hasCompactSupport") (uses := "sobolev.hardy_lp_interval")
Let $`p>1`, and let $`u:\mathbb R\to\mathbb R` be $`C^1` with compact
support contained in $`(0,\infty)`. Then

$$`
\int_0^\infty \frac{|u(x)|^p}{x^p}\,dx
\leq
\left(\frac{p}{p-1}\right)^p
\int_0^\infty |u'(x)|^p\,dx.
`

The support condition keeps both integrands away from the singular endpoint
and from infinity, so the half-line integrals coincide with finite-interval
integrals.
:::

:::proof "sobolev.hardy_lp_smooth_core"
Compactness of the topological support produces
$`0<\varepsilon<R` containing the supports of both $`u` and $`u'`.
Consequently the two half-line integrals equal their restrictions to
$`(\varepsilon,R]`. Apply {uses "sobolev.hardy_lp_interval"}[] on that
interval; compact support supplies $`u(\varepsilon)=0`.
:::

The half-line estimate lifts to the upper half-space by applying it along
each normal line.

:::theorem "sobolev.hardy_lp_half_space_smooth" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardy_upperHalfSpace_lp_of_hasCompactSupport, SobolevSpace.Hardy.hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport") (uses := "sobolev.hardy_lp_smooth_core")
Let

$$`
\mathbb H^{n+1}
  =\{x\in\mathbb R^{n+1}:x_{n+1}>0\},
`

let $`p>1`, and let $`u\in C^1_c(\mathbb H^{n+1})`. Then

$$`
\int_{\mathbb H^{n+1}}
  \frac{|u(x)|^p}
       {\operatorname{dist}(x,\partial\mathbb H^{n+1})^p}\,dx
\leq
\left(\frac{p}{p-1}\right)^p
\int_{\mathbb H^{n+1}}
  |\partial_{n+1}u(x)|^p\,dx.
`

The distance to the boundary is exactly the positive normal coordinate.
The right side therefore needs only the normal derivative; replacing it by
the full gradient gives the customary weaker form.
:::

:::proof "sobolev.hardy_lp_half_space_smooth"
Write $`x=(y,t)` with $`y\in\mathbb R^n` and $`t>0`. For each fixed $`y`,
the normal slice $`t\mapsto u(y,t)` has compact support in $`(0,\infty)`.
Apply {uses "sobolev.hardy_lp_smooth_core"}[] to that slice. The derivative of
the slice is $`\partial_{n+1}u(y,t)`. Integration over $`y` and the
tangential-normal change of variables preserve the same constant. Finally,
$`\operatorname{dist}((y,t),\partial\mathbb H^{n+1})=t`.
:::

Passing from the smooth core to $`W^{1,p}_0(\mathbb H^{n+1})` first requires
saying what division by $`x_{n+1}` means for a general element, since an
arbitrary pointwise representative may be altered on a null set.

:::definition "sobolev.hardy_lp_half_space_quotient" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardyUpperHalfSpaceW1p0Quotient") (uses := "sobolev.graph_space, sobolev.hardy_lp_half_space_smooth")
For $`p>1`, division by the normal coordinate extends uniquely from
$`C^\infty_c(\mathbb H^{n+1})` to a bounded linear operator

$$`
Q_{\mathbb H,p}:
W^{1,p}_0(\mathbb H^{n+1})
\longrightarrow L^p(\mathbb R^{n+1}).
`

On the smooth core, $`Q_{\mathbb H,p}u` is represented by
$`x\mapsto u(x)/x_{n+1}`. Since
$`x_{n+1}=\operatorname{dist}(x,\partial\mathbb H^{n+1})` inside the
half-space, this is the completed distance quotient. On a general Sobolev
element it is the $`L^p` equivalence class given by density. The Lean
constructor takes $`1<p` as an explicit hypothesis.
:::

Extension by density only guarantees a bound in terms of the full graph
norm. The sharper estimate of the smooth core survives the completion.

:::theorem "sobolev.hardy_lp_half_space_completed" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardyUpperHalfSpaceW1p0Quotient_testFunction, SobolevSpace.Hardy.norm_hardyUpperHalfSpaceW1p0Quotient_le_normalDerivative") (uses := "sobolev.hardy_lp_half_space_quotient")
For every $`p>1` and
$`u\in W^{1,p}_0(\mathbb H^{n+1})`,

$$`
\|Q_{\mathbb H,p}u\|_{L^p(\mathbb R^{n+1})}
\leq
\frac{p}{p-1}
\|\partial_{n+1}u\|_{L^p(\mathbb H^{n+1})}.
`

The right side uses only the normal weak-derivative coordinate. Bounding it
by the full gradient gives the standard upper-half-space Hardy inequality
with the same constant. This theorem completes the flat model.
:::

:::proof "sobolev.hardy_lp_half_space_completed"
The smooth estimate bounds the quotient map on the dense compactly supported
core by the full $`W^{1,p}` graph norm, so it has a unique continuous
extension to $`W^{1,p}_0(\mathbb H^{n+1})`. Agreement on test functions
identifies the extension with literal division there. Passing to the closure
preserves the sharper estimate involving only the normal derivative, which
gives the displayed bound.
:::

On a domain carrying a $`C^1` boundary atlas, the flat model is applied one
boundary chart at a time.

:::theorem "sobolev.hardy_lp_boundary_chart" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.exists_eLpNorm_boundaryDistanceQuotient_le_graphNorm") (uses := "sobolev.hardy_lp_half_space_smooth, sobolev.c1_extension")
Let $`\Omega\subset\mathbb R^n` carry the operational $`C^1` boundary atlas
used by the extension theory, and let $`\psi_i` be one boundary partition
function. For every $`p>1`, there is a finite chart-dependent constant $`C_i`
such that every smooth compactly supported $`\varphi` in $`\Omega` satisfies

$$`
\left\|
  \frac{\psi_i\varphi}
       {\operatorname{dist}(\,\cdot\,,\partial\Omega)}
\right\|_{L^p}
\leq C_i\|\varphi\|_{W^{1,p}(\Omega)}.
`

The comparison between flattened height and physical boundary distance is
derived from the atlas, not assumed as an extra atlas field. The constant also
absorbs the inverse Jacobian bound and the norm of the chart-flattening
operator.
:::

:::proof "sobolev.hardy_lp_boundary_chart"
Flatten $`\psi_i\varphi` through the $`i`-th boundary chart. Its transported
support lies strictly inside the upper half-space, so
{uses "sobolev.hardy_lp_half_space_smooth"}[] applies directly to the
transported $`C^1` compactly supported function and controls division by the
flat height using its normal derivative.

On the relevant compact chart support, the atlas geometry supplies a
constant comparing physical boundary distance with flattened height. A
change-of-variables estimate contributes the inverse-Jacobian constant, and
the chart-flattening continuous linear map bounds the transported
normal derivative by the original $`W^{1,p}(\Omega)` graph norm. The product
of these three finite factors is a valid $`C_i`.
:::

Summing the chart estimates over the finite atlas gives the estimate on the
whole domain.

:::theorem "sobolev.hardy_lp_domain_smooth" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.exists_eLpNorm_domainDistanceQuotient_le_graphNorm") (uses := "sobolev.hardy_lp_boundary_chart")
Let $`\Omega\subset\mathbb R^n` carry the bounded operational $`C^1`
boundary atlas, and let $`p>1`. There is a finite constant
$`C_{\Omega,p}` such that every
$`\varphi\in C^\infty_c(\Omega)` satisfies

$$`
\left\|
  \frac{\varphi}
       {\operatorname{dist}(\,\cdot\,,\partial\Omega)}
\right\|_{L^p(\Omega)}
\leq
C_{\Omega,p}\|\varphi\|_{W^{1,p}(\Omega)}.
`

By density the quotient extends to a bounded linear map from
$`W^{1,p}_0(\Omega)` to $`L^p(\Omega)`, agreeing almost everywhere with
division of the Sobolev representative by boundary distance. Poincaré reduces
the bound to the weak gradient alone.
:::

:::proof "sobolev.hardy_lp_domain_smooth"
The atlas partition writes $`\varphi` as one interior piece plus finitely
many boundary pieces. The interior cutoff stays a positive distance from
$`\partial\Omega`, so division by boundary distance is bounded there.
Each boundary piece is controlled by
{uses "sobolev.hardy_lp_boundary_chart"}[]. The finite $`L^p` triangle
inequality and the partition identity combine those estimates into one
domain constant.
:::

Back in one dimension, the completion runs exactly as on the half-space.

:::definition "sobolev.hardy_lp_quotient" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardyW1p0Quotient") (uses := "sobolev.graph_space, sobolev.hardy_lp_smooth_core")
For $`p>1`, let $`W^{1,p}_0(0,\infty)` denote the closure of smooth compactly
supported functions in the positive half-line with respect to the bundled
$`W^{1,p}` graph norm. The Hardy quotient extends uniquely to a bounded
linear operator

$$`
Q_p:W^{1,p}_0(0,\infty)\longrightarrow L^p(\mathbb R).
`

On the smooth core, $`Q_pu` is represented by $`x\mapsto u(x)/x`. On a
general completed-space element, $`Q_pu` is defined by continuity as an
$`L^p` equivalence class. The Lean constructor takes $`1<p` as an explicit
hypothesis.
:::

:::theorem "sobolev.hardy_lp_completed" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardyW1p0Quotient_testFunction, SobolevSpace.Hardy.norm_hardyW1p0Quotient_le_deriv") (uses := "sobolev.hardy_lp_quotient")
For every $`p>1` and every $`u\in W^{1,p}_0(0,\infty)`,

$$`
\|Q_pu\|_{L^p(\mathbb R)}
\leq
\frac{p}{p-1}\,\|u'\|_{L^p(0,\infty)}.
`

The constant is the classical one inherited from the smooth Hardy inequality.
The derivative on the right is the first weak-derivative coordinate of the
bundled Sobolev element.
:::

:::proof "sobolev.hardy_lp_completed"
The smooth estimate gives a bounded linear quotient map on the dense
compactly supported core. Extend that map continuously to the closure
$`W^{1,p}_0(0,\infty)`. Agreement on test functions identifies the extension
with literal division there, and closedness passes the derivative-only bound
to every element of the completion.
:::

The higher-order theory is developed for $`p=2`, where the quotient
operators act between Hilbert spaces. Its starting point is the $`p=2` case
of the interval argument, which differs from the finite-exponent identity
in one respect: the identity here assumes both endpoint values vanish,
so no right-endpoint term has to be discarded, and Cauchy–Schwarz replaces
Young's inequality. The constant $`4` is $`(p/(p-1))^p` at $`p=2`.

:::theorem "sobolev.hardy_classical_core" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.hardy_interval_identity, SobolevSpace.Hardy.hardy_interval, SobolevSpace.Hardy.hardy_Ioi_of_hasCompactSupport")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "296-297"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The one-dimensional $`p=2` Hardy argument starts from integration by parts
on $`[\varepsilon,R]`, followed by Cauchy–Schwarz and passage to the
half-line for $`C^1` functions with compact support contained in $`(0,\infty)`:

$$`
\int_0^\infty \frac{|u(x)|^2}{x^2}\,dx
\le 4\int_0^\infty |u'(x)|^2\,dx.
`

This is the $`p=2` specialization of the finite-exponent inequality, stated
separately because the iterated higher-order construction is built from the
Hilbert-space quotient operators. It uses the same
integration-by-parts mechanism as Hardy's inequality in Evans §5.8.4.
:::

:::proof "sobolev.hardy_classical_core"
On $`[\varepsilon,R]`, integrate $`u^2` against the derivative of
$`-1/x`. The endpoint values remove the boundary terms and give

$$`
\int_\varepsilon^R\frac{u^2}{x^2}
  =2\int_\varepsilon^R\frac{u}{x}u'.
`

Cauchy–Schwarz implies $`X\leq2\sqrt X\sqrt Y`, where $`X` and $`Y` are
the quotient and derivative square integrals, hence $`X\leq4Y`. Compact
support inside the positive half-line supplies suitable endpoints and
identifies these finite-interval integrals with the half-line integrals.
:::

Controlling $`u/x^j` for $`j\geq2` needs more than the unweighted inequality.
The first step must bound $`\int u^2x^{-2j}` by a weighted integral of
$`u'`, namely $`\int u'^2x^{2-2j}`, and the following step must accept that
weighted integrand as its input. The power-weighted inequality does this for
a general exponent $`s>1/2`; at $`s=1` it is the classical interval step.

:::theorem "sobolev.weighted_hardy_interval" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.weighted_hardy_interval, SobolevSpace.Hardy.weighted_hardy_interval_identity")
Let $`0<\varepsilon<R`, let $`s>1/2`, and let $`u:\mathbb R\to\mathbb R` be
$`C^1` with $`u(\varepsilon)=u(R)=0`. Then

$$`
(2s-1)^2\int_\varepsilon^R u(x)^2\,x^{-2s}\,dx
\leq
4\int_\varepsilon^R u'(x)^2\,x^{2-2s}\,dx .
`

The underlying identity needs only $`C^1` regularity and the two endpoint
zeros, with no restriction on $`s`:

$$`
(2s-1)\int_\varepsilon^R u(x)^2\,x^{-2s}\,dx
  =2\int_\varepsilon^R
    \bigl(u(x)\,x^{-s}\bigr)\bigl(u'(x)\,x^{1-s}\bigr)\,dx .
`

At $`s=1` this is the finite-interval step of the classical core. The
inequality is stated multiplied out, without dividing by $`(2s-1)^2`, so
that it can be iterated across weight exponents without case splits. This is
the power-weighted Hardy inequality of Hardy, Littlewood, and Pólya.
:::

:::proof "sobolev.weighted_hardy_interval"
Integrate $`u^2` against the derivative of $`x^{1-2s}`, namely
$`(1-2s)x^{-2s}`, by parts on $`[\varepsilon,R]`. The endpoint zeros remove
the boundary terms and give the identity. Write $`X` and $`Y` for the two
weighted integrals and apply Cauchy–Schwarz to the right side of the
identity, so that $`(2s-1)X\leq2\sqrt X\sqrt Y`. If $`X=0` the inequality
is trivial; otherwise divide by $`\sqrt X` and square, using $`2s-1>0`.
:::

As in the finite-exponent theory, support inside a compact subinterval of
$`(0,\infty)` turns the interval inequality into a half-line inequality
without changing the constant. Since the weight exponent is a free
parameter, the half-line form can be applied to successive derivatives.

:::theorem "sobolev.weighted_hardy_half_line" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.weighted_hardy_Ioi_of_support_subset_Ioo, SobolevSpace.Hardy.weighted_hardy_Ioi_iteratedDeriv_of_support_subset_Ioo, SobolevSpace.Hardy.iterated_weighted_hardy_Ioi_nat, SobolevSpace.Hardy.iterated_weighted_hardy_Ioi_nat_of_hasCompactSupport")
Let $`0<\varepsilon<R` and $`s>1/2`. If $`u` is $`C^1` and $`u` (hence also
$`u'`) is supported in $`(\varepsilon,R)`, then

$$`
(2s-1)^2\int_0^\infty u(x)^2\,x^{-2s}\,dx
\leq
4\int_0^\infty u'(x)^2\,x^{2-2s}\,dx .
`

The same estimate holds with $`u` replaced by the $`m`-th derivative of a
$`C^{m+1}` function $`f` whose derivative of order $`m` (hence also of order $`m+1`) is
supported in $`(\varepsilon,R)`. Iterating it $`j` times with the weight
exponents $`s=j,j-1,\ldots,1` gives the explicit chain: if
$`f\in C^{m+j}` and $`f^{(m+l)}` is supported in $`(\varepsilon,R)` for
every $`l\leq j`, then

$$`
\Bigl(\prod_{l=1}^{j}(2l-1)^2\Bigr)
\int_0^\infty f^{(m)}(x)^2\,x^{-2j}\,dx
\leq
4^j\int_0^\infty f^{(m+j)}(x)^2\,dx .
`

Finally, the chain holds for every $`C^{m+j}` function with compact support
contained in $`(0,\infty)`, with no explicit interval. The support
hypotheses are what allow the half-line integrals to be replaced by
finite-interval integrals, and no decay or endpoint trace is needed. At $`j=0`
the product is empty and the chain reduces to an equality.
:::

:::proof "sobolev.weighted_hardy_half_line" (uses := "sobolev.weighted_hardy_interval")
Support in $`(\varepsilon,R)` forces $`u(\varepsilon)=u(R)=0` and makes each
half-line integrand vanish outside $`(\varepsilon,R)`, so both sides equal
the corresponding finite-interval integrals and
{uses "sobolev.weighted_hardy_interval"}[] applies. The derivative version
is the same statement for $`u=f^{(m)}`, whose derivative is $`f^{(m+1)}`.
The chain is an induction on $`j`: the step at weight $`s=j+1` trades one
factor $`x^{-2}` against one derivative and multiplies the constant by
$`(2j+1)^2` on the left and by $`4` on the right, and the induction
hypothesis at level $`m+1` handles the remaining $`j` steps. For compactly
supported $`f` with support in $`(0,\infty)`, compactness yields one
interval $`[\varepsilon,R]\subset(0,\infty)` containing the support, and
every derivative is supported inside the support of $`f`.
:::

Stating the chain on $`W^{j,2}_0(0,\infty)` requires giving division by
$`r^j` a meaning on the completed space, as in the first-order case.

:::definition "sobolev.iterated_hardy_quotient" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.iteratedHardyWk0Quotient, SobolevSpace.Hardy.iteratedHardyWk0Quotient_testFunction") (uses := "sobolev.graph_space, sobolev.hardy_classical_core")
For every $`j\in\mathbb N`, let $`W^{j,2}_0(0,\infty)` be the closure of
$`C^\infty_c(0,\infty)` in the bundled $`W^{j,2}` graph norm. Literal
division by $`r^j` on the smooth core extends uniquely to a bounded linear
operator

$$`
Q_j:
W^{j,2}_0(0,\infty)\longrightarrow L^2(\mathbb R).
`

For a test function $`\varphi`,

$$`
Q_j\varphi
  = \left[r\mapsto\frac{\varphi(r)}{r^j}\right]_{L^2}.
`

Compact support strictly inside the positive half-line makes the displayed
representative square-integrable. The preliminary estimate
$`\|Q_j\varphi\|_2\leq2^j\|\varphi\|_{W^{j,2}}` supplies the bounded extension.
For a completed Sobolev element, $`Q_j u` is defined by this extension.
:::

With the operator in place, the smooth-core chain at $`m=0` passes to the
completion. Only the top weak-derivative coordinate appears on the right,
whereas the bound used to construct $`Q_j` involved the whole graph norm.

:::theorem "sobolev.iterated_hardy" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Hardy.iterated_weighted_hardy_Wk0") (uses := "sobolev.iterated_hardy_quotient")
For every $`j\in\mathbb N` and every
$`u\in W^{j,2}_0(0,\infty)`,

$$`
\left(\prod_{\ell=1}^{j}(2\ell-1)^2\right)
  \|Q_j u\|_{L^2(\mathbb R)}^2
\leq
4^j\|D^j u\|_{L^2(0,\infty)}^2.
`

Here $`D^j u` is the top weak-derivative coordinate in the bundled
$`W^{j,2}` element. At $`j=0`, the product is empty, $`Q_0` is division by
$`r^0=1`, and the statement is the identity estimate. At $`j=1`, the odd
product is $`1` and the theorem becomes the usual constant-$`4` Hardy
inequality.
:::

:::proof "sobolev.iterated_hardy" (uses := "sobolev.weighted_hardy_half_line")
First work on $`\varphi\in C^\infty_c(0,\infty)`. The weighted
one-dimensional integration-by-parts estimate is iterated at derivative
levels $`0,\ldots,j`. Compact support chooses one interval
$`[\varepsilon,R]\subset(0,\infty)` containing the supports of all those
derivatives. The smooth-core chain gives exactly

$$`
\left(\prod_{\ell=1}^{j}(2\ell-1)^2\right)
 \int_0^\infty\frac{|\varphi(r)|^2}{r^{2j}}\,dr
\leq
4^j\int_0^\infty|D^j\varphi(r)|^2\,dr.
`

The quotient-representative lemma identifies the first integral with
$`\|Q_j\varphi\|_2^2`, and the Sobolev-coordinate lemma identifies the second
with the square of the top bundled derivative coordinate.

The full graph-norm estimate obtained from this core theorem defines $`Q_j`
on the closure. To retain the sharper exact inequality, use the dense range
of the canonical map
$`C^\infty_c(0,\infty)\to W^{j,2}_0(0,\infty)`. The set of completed elements
satisfying the displayed inequality is closed because the quotient operator
and the top-coordinate evaluation are continuous. Dense-range induction
therefore passes the exact odd-weight product and the factor $`4^j` unchanged
to every completed element. The completion step needs no boundary trace for
an intermediate derivative.
:::
