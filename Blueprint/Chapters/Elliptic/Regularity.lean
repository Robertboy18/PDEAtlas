/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.FredholmSpectrum
import PDE.Elliptic.Regularity.Boundary.ConcreteIntervalAtlas
import PDE.Elliptic.Regularity.Boundary.ConcreteUnitBallAtlas
import PDE.Elliptic.Regularity.Boundary.Construction
import PDE.Elliptic.Regularity.Boundary.GlobalGraphChart
import PDE.Elliptic.Regularity.Boundary.H2.ChartPiece
import PDE.Elliptic.Regularity.Global.H2
import PDE.Elliptic.Regularity.Global.HigherOrder
import PDE.Elliptic.Regularity.Global.ShiftedDivergence
import PDE.Elliptic.Regularity.Global.ShiftedDivergenceHigher
import PDE.Elliptic.Regularity.Global.SmoothBoundary
import PDE.Elliptic.Regularity.Interior.H2Compactness
import PDE.Elliptic.Regularity.Interior.H2PartitionPiece
import PDE.Elliptic.Regularity.Interior.LocalHigherOrder
import PDE.Elliptic.Regularity.Localization.HigherOrderCutoffEquation
import PDE.Elliptic.Regularity.OneDimensional.H2Poisson
import PDE.Spaces.Sobolev.Boundary.Atlas.Construction
import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall

/-!
# Elliptic regularity

Interior, boundary, and global Sobolev regularity for divergence-form elliptic equations.
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
#doc (Manual) "Interior and Boundary Regularity" =>

:::group "elliptic.regularity"
Elliptic regularity
:::

Elliptic regularity reconnects the variational and classical theories: a weak
solution produced by Lax–Milgram gains as many Sobolev derivatives as the
coefficients and data permit.

Difference quotients are defined on $`H^1` functions, even when pointwise
derivatives are unavailable, and their product identities separate the
solution, coefficients, and cutoffs. They regularize within the energy space,
with no mollification. Cutoff functions introduce commutator terms, boundary
charts introduce Jacobian factors, and
lower-order coefficients introduce additional forcing.

Evans (2010, Sections 6.3.1–6.3.2, pp. 327–343) proves interior $`H^2`
regularity for arbitrary $`H^1` weak solutions, global boundary regularity
for homogeneous Dirichlet solutions, higher-order Sobolev regularity, and
smoothness under smooth data. We prove Evans's compact-set interior theorem
for arbitrary $`H^1` weak solutions, and also a zero-trace version localized
by an atlas cutoff, which is the form the global Dirichlet assembly uses.

# Operational Boundary Geometry

Boundary regularity needs more than an abstract smooth-boundary label: the
proof differentiates flattening maps, transfers weak derivatives, and sums
localized estimates through a finite partition of unity. The operational
atlases record exactly that data, with concrete instances for the
interval and every positive-dimensional Euclidean unit ball.

This reuses the geometry of
{bpref "sobolev.extension.atlas"}[Sobolev extension], but asks it to do more.
Extension continues a function whose first derivatives are already controlled.
Boundary regularity must obtain an additional derivative from the equation.
Flattening transforms the coefficients as well as the function, and
differentiating that transformed equation requires extra chart derivatives.
We use explicit atlases so that this extra cost is part of the
hypotheses, even on the familiar interval and ball.

:::definition "elliptic.regularity.c2_boundary_atlas" (parent := "elliptic.regularity") (lean := "SobolevSpace.C2BoundaryAtlas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "334-340"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A $`C^2` boundary atlas consists of a finite extension atlas whose flattening
charts and inverse charts are twice continuously differentiable.
:::

The concrete atlases follow Evans's boundary-flattening argument on
pp. 334–340 and start from a finite cover of the boundary.

:::definition "elliptic.regularity.finite_boundary_cover" (parent := "elliptic.regularity") (lean := "SobolevSpace.Boundary.FiniteBoundaryCover, SobolevSpace.Boundary.FiniteBoundaryCover.interiorCutoff, SobolevSpace.Boundary.FiniteBoundaryCover.boundaryCutoff, SobolevSpace.Boundary.FiniteBoundaryCover.interiorCutoff_support, SobolevSpace.Boundary.FiniteBoundaryCover.boundaryCutoff_support, SobolevSpace.Boundary.FiniteBoundaryCover.cutoff_sum_eq_one")
A finite boundary cover consists of bounded open neighborhoods $`U_i` whose
union contains the frontier $`\partial\Omega` of a bounded open domain.
Adding $`\Omega` as the interior member gives a finite open cover of
$`\overline\Omega`. Mathlib's smooth partition-of-unity theorem then
canonically supplies compactly supported interior and boundary test functions
subordinate to those sets and summing to one on $`\Omega`.
:::

A cover alone carries no analytic information about the boundary. The
flattening charts add it: each boundary patch receives a map identifying the
domain locally with the upper half-space, and the differentiability class of
these maps is what distinguishes the $`C^1` extension atlas from the $`C^2`
regularity atlas.

:::definition "elliptic.regularity.flattening_chart_constructor" (parent := "elliptic.regularity") (lean := "SobolevSpace.Boundary.C1FlatteningCharts, SobolevSpace.Boundary.C1FlatteningCharts.toC1ExtensionAtlas, SobolevSpace.Boundary.C2FlatteningCharts, SobolevSpace.Boundary.C2FlatteningCharts.toC2BoundaryAtlas") (uses := "elliptic.regularity.c2_boundary_atlas, elliptic.regularity.finite_boundary_cover")
After the subordinate cutoffs are fixed, one attaches a flattening chart to
each boundary neighborhood. Only the compact support of the corresponding
cutoff must lie in the chart source. Globally represented $`C^1` charts
produce an extension atlas, while $`C^2` charts produce the operational
boundary atlas used by elliptic regularity.
:::

The first instance is the interval. In one dimension the boundary consists
of two points, and affine maps flatten it.

:::definition "elliptic.regularity.concrete_interval_atlas" (parent := "elliptic.regularity") (lean := "SobolevSpace.Boundary.Atlas.Interval.c2BoundaryAtlas") (uses := "elliptic.regularity.flattening_chart_constructor")
For $`\Omega=(-1,1)`, the affine endpoint maps
$`\Phi_-(x)=x+1` and $`\Phi_+(x)=1-x` identify neighborhoods of the two
boundary points with neighborhoods in the upper half-line $`(0,\infty)`.
Both maps are affine with affine inverses, hence smooth to every finite
order. Together with an interior patch and a finite subordinate
partition of unity, they furnish the operational $`C^2` boundary atlas used
by the global elliptic and parabolic regularity theorems.
:::

In higher dimensions the unit ball is the model domain, and its atlas is
assembled in two stages. The first stage is the cover: finitely many signed
coordinate caps containing the sphere, together with a subordinate partition
of unity; each cap is later flattened by a graph chart.

:::definition "elliptic.regularity.unit_ball_boundary_cover" (parent := "elliptic.regularity") (lean := "SobolevSpace.Boundary.Atlas.UnitBall.boundaryCap, SobolevSpace.Boundary.Atlas.UnitBall.boundaryCover, SobolevSpace.Boundary.Atlas.UnitBall.definingFunction_contDiff, SobolevSpace.Boundary.Atlas.UnitBall.definingFunction_pos_iff, SobolevSpace.Boundary.Atlas.UnitBall.radialCovector_ne_zero_of_mem_sphere") (uses := "elliptic.regularity.finite_boundary_cover")
In every positive dimension, the Euclidean unit ball has a finite cover by
$`2n` signed coordinate caps together with a smooth subordinate partition of
unity. The interior and boundary cutoffs have compact support in their
assigned sets and sum exactly to one on the ball. Its global defining
function $`\rho(x)=1-\lVert x\rVert^2` is smooth, is positive exactly in the
ball, and has nonzero radial differential on the unit sphere.

The caps cover the sphere: a point of the unit sphere is nonzero, so at least
one coordinate is either positive or negative, and the identity
$`\sum_j x_j^2=1` shows that the remaining tangential coordinates have
squared norm strictly less than one, placing the point in the corresponding
signed cap. Together with the open ball, these finitely many caps cover the
closed ball. Mathlib's smooth partition-of-unity theorem supplies the cutoffs,
and boundedness of the cover sets makes their supports compact.
:::

On each cap the sphere is the graph of a height function over the tangential
coordinates, and subtracting or adding that height in the normal coordinate
flattens the cap. The constructor requires chart representatives
differentiable on all of $`\mathbb R^n`, so the local height
$`\sqrt{1-\lVert x'\rVert^2}` is replaced by a globally smooth function
agreeing with it on a slightly smaller tangential cylinder.

:::theorem "elliptic.regularity.global_graph_charts" (parent := "elliptic.regularity") (lean := "SobolevSpace.Extension.GraphChart.positiveMap_contDiff, SobolevSpace.Extension.GraphChart.positiveHomeomorph, SobolevSpace.Extension.GraphChart.negativeHomeomorph, SobolevSpace.Extension.GraphChart.negativeMap_contDiff, SobolevSpace.Extension.GraphChart.negativeMapInverse_contDiff, SobolevSpace.Extension.GraphChart.positiveMap_mem_upper_iff, SobolevSpace.Extension.GraphChart.negativeMap_mem_upper_iff, SobolevSpace.Extension.GraphChart.positiveChart, SobolevSpace.Extension.GraphChart.negativeChart, SobolevSpace.Extension.GraphChart.positiveChart_target_bounded, SobolevSpace.Extension.GraphChart.negativeChart_target_bounded, SobolevSpace.Extension.GraphChart.exists_globalSphereHeight_contDiff_eqOn")
For a globally smooth height $`g:\mathbb R^{n-1}\to\mathbb R`, the triangular
maps

$$`
\Psi_+(x',x_n)=(x',g(x')-x_n),\qquad
\Psi_-(x',x_n)=(x',g(x')+x_n)
`

flatten the region below the graph of $`g` and the region above the graph
of $`-g`, respectively, to the standard upper half-space. Their forward and
inverse maps retain every finite differentiability order, and restriction to
a bounded open source gives the bounded partial charts required by the
operational atlas. On every smaller
tangential cylinder of the unit sphere, we also construct a global
$`C^\infty` height agreeing with $`g(x')=\sqrt{1-\lVert x'\rVert^2}`.
:::

:::proof "elliptic.regularity.global_graph_charts"
The flattening maps preserve every tangential coordinate and replace the
normal coordinate by $`g(x')-x_n` or $`g(x')+x_n`. Direct coordinate
calculations give their inverses. The inequalities $`x_n<g(x')` and
$`x_n>-g(x')`, respectively, are equivalent to positivity of the flattened
normal coordinate. Componentwise
calculus proves the required differentiability. Restricting each global
homeomorphism to a bounded open source gives a bounded partial chart because
the image of the compact source closure is bounded. For the sphere, the local
height $`\sqrt{1-\lVert x'\rVert^2}` is smooth on the region where its
radicand is positive; Mathlib's relative smooth-extension theorem produces a
globally smooth function agreeing with it on any strictly smaller closed
tangential cylinder.
:::

Feeding the cap cover and the graph charts into the constructor gives the
concrete $`C^2` atlas on which the global regularity
theorems can be instantiated for the unit ball in every positive dimension.

:::definition "elliptic.regularity.concrete_unit_ball_atlas" (parent := "elliptic.regularity") (lean := "SobolevSpace.Boundary.Atlas.UnitBall.ConcreteAtlas.c2BoundaryAtlas") (uses := "elliptic.regularity.flattening_chart_constructor, elliptic.regularity.unit_ball_boundary_cover, elliptic.regularity.global_graph_charts")
For every $`n\geq1`, quantitative signed caps, coordinate permutations,
globally smooth extensions of
$`x'\mapsto\sqrt{1-\lVert x'\rVert^2}`, and triangular graph-flattening maps
assemble into a finite operational $`C^2` boundary atlas for
$`B^n\subset\mathbb R^n`.
:::

# From Local H² Pieces to Global Regularity

The $`H^2` proof has two analytic pieces. Interior cutoffs permit ordinary
difference quotients, while boundary cutoffs are flattened to the half-space
so tangential derivatives can be estimated and the normal derivative
recovered from the equation. The finite atlas then reassembles those local
representatives into one global Sobolev field.

The difference-quotient bootstrap works as follows. Given a weak solution
$`u\in H^1_0(\Omega)` of $`-\partial_i(a^{ij}\partial_j u)=f`, choose a
direction $`e_k` and form the second-order difference quotient
$`\Delta_h^{-k}\Delta_h^k u` where
$`\Delta_h^k u(x)=(u(x+he_k)-u(x))/h`. Testing the weak equation against
$`\varphi=-\Delta_h^{-k}(\eta^2\Delta_h^k u)` (where $`\eta` is a smooth
interior cutoff) and using the discrete product rule gives

$$`
\alpha\int|\nabla(\eta\Delta_h^k u)|^2
\leq C\bigl(\lVert f\rVert_{L^2}^2+\lVert\nabla u\rVert_{L^2}^2\bigr).
`

The constant hides the cost of localization. For concentric balls
$`\overline{B_r}\subset B_R\subset\Omega`, choose $`\eta=1` on $`B_r`
and supported in $`B_R`, with $`|\nabla\eta|\le C_n/(R-r)`. The product
rule introduces this factor into the estimate. Thus interior regularity
controls derivatives on a smaller region from data on a larger one, and the
bound deteriorates when the gap closes. It requires no boundary trace for
an arbitrary local weak solution; extending the conclusion to the whole
domain requires a separate boundary argument.

Choose sufficiently small nonzero steps $`h_m\to0`. The product rule and
this estimate bound the localized difference quotients of the first
derivatives in $`L^2`. Weak compactness supplies a weak limit along an
ultrafilter containing every tail of the sequence. Discrete integration by
parts identifies each limit as a second weak derivative where $`\eta=1`.
Repeating this in every coordinate gives an $`H^2` representative on that
interior region. Near the boundary the argument is
more delicate: one can only take tangential difference quotients directly,
and the normal second derivative is then recovered algebraically from the
equation using ellipticity of the leading coefficient (Evans, 2010,
pp. 327–340; {Informal.citet "gilbarg-trudinger-2001"}[], Section 8.3).

:::theorem "elliptic.regularity.h2.one_dimensional_poisson" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.exists_oneDimensional_h2_of_weak_poisson_solution") (uses := "elliptic.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "327-331"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open subset of the real line, let $`u\in H^1_0` satisfy the
weak Poisson identity with forcing $`f\in L^2`. (The openness assumption is
carried by the weak Poisson solution predicate.) Then $`u` has a $`W^{2,2}`
representative whose first coordinate derivative agrees with the weak first
derivative of $`u` and whose second weak derivative is $`-f` almost everywhere.
This one-dimensional Dirichlet analogue of the difference-quotient theorem
needs no boundary atlas.
:::

:::proof "elliptic.regularity.h2.one_dimensional_poisson"
The weak Poisson identity says directly that the first weak derivative of
$`u` has weak derivative $`-f`. The second-derivative assembly theorem then
combines the base value, first derivative, and second derivative into one
$`W^{2,2}` representative.
:::

In one dimension the second derivative is read directly from the equation.
For variable principal coefficients the difference-quotient argument is
needed, and it gives regularity on compact subsets of the domain.

:::theorem "elliptic.regularity.h2.local" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.exists_local_h2_open_neighborhood_of_compact") (uses := "elliptic.divergence.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "327-331"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n` be open and let $`u\in H^1(\Omega)` solve

$$`
-\partial_i(a^{ij}\partial_j u)=f
`

weakly against every $`H^1_0(\Omega)` test function. Assume
$`f\in L^2(\Omega)`. The theorem takes a selected coefficient field with
entries in $`L^\infty(\mathbb R^n)` admitting globally Lipschitz
representatives. The selected matrix field is almost-everywhere uniformly
elliptic on all of $`\mathbb R^n` with a positive lower bound.
For every compact $`K\subset\Omega`, there is an open set $`V` with

$$`
K\subset V\subset\Omega
`

such that the restriction of $`u` has an $`H^2(V)` representative. No
boundary condition on $`u` is assumed.
:::

:::proof "elliptic.regularity.h2.local"
Choose an outer cutoff equal to one near $`K`. Its product with $`u` belongs
to $`H^1_0(\Omega)` and satisfies a divergence-form equation whose
commutator forcing lies in $`L^2`. Choose a second cutoff inside the region
where the first equals one and apply the quantitative zero-trace
difference-quotient theorem. On the second cutoff region the localized field
and $`u` agree almost everywhere, so the resulting $`H^2` field represents
the original weak solution near $`K`.
:::

Passing to higher orders requires differentiating the equation, which is done
on localized solutions with zero trace. The cutoff lemma provides those
localized solutions at every Sobolev order in a single statement.

:::theorem "elliptic.regularity.higher.cutoff_localization" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.exists_localized_weakDivergenceSolution_higher") (uses := "elliptic.divergence.weak_solution, sobolev.higher_order_multiplier")
Let $`k>0` and let $`\Omega\subset\mathbb R^n` be open. Suppose
$`a^{ij}\in W^{k+1,\infty}(\Omega)`, $`f\in W^{k,2}(\Omega)`, and
$`u\in W^{k+1,2}(\Omega)` represents an $`H^1_0(\Omega)` weak solution of

$$`
-\partial_i(a^{ij}\partial_j u)=f.
`

For every smooth compactly supported cutoff $`\rho` on $`\mathbb R^n`,
the product $`w=\rho u` has an $`H^1_0(\Omega)` representative and there
is a forcing $`G\in W^{k,2}(\Omega)`, supported where $`\rho` is supported,
such that

$$`
-\partial_i(a^{ij}\partial_j w)=G
`

weakly on $`\Omega`.
:::

:::proof "elliptic.regularity.higher.cutoff_localization"
Apply first-order cutoff localization to obtain the weak equation for
$`\rho u`. Its forcing is the original forcing multiplied by $`\rho`
together with the two coefficient-cutoff commutators. Repeated weak Leibniz
rules, finite derivative-word sums, and the general
$`W^{k,\infty}\times W^{k,2}\to W^{k,2}` multiplier theorem put every term
in $`W^{k,2}`. The cutoff factors also show that the assembled forcing
vanishes almost everywhere off the support of $`\rho`.
:::

Induction on the order combines the $`H^2` theorem with the cutoff lemma. The
coefficient hypotheses grow with the order, since each differentiation of the
equation moves one derivative onto $`a^{ij}`, while the conclusion remains
local and free of boundary conditions.

:::theorem "elliptic.regularity.higher.local" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_local_higherOrder_open_neighborhood_of_compact") (uses := "elliptic.regularity.h2.local, elliptic.regularity.higher.cutoff_localization")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "340-343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`m\geq0`, let $`\Omega\subset\mathbb R^n` be open, and suppose
$`u\in H^1(\Omega)` is a weak solution of

$$`
-\partial_i(a^{ij}\partial_j u)=f.
`

Assume the coefficient matrix has globally Lipschitz representatives for
the $`H^2` base step. More precisely, the theorem takes a coefficient field
with entries in $`L^\infty(\mathbb R^n)`, requires its almost-everywhere ellipticity
hypothesis on all of $`\mathbb R^n`, and requires its restriction to
$`\Omega` to agree with one coherent $`W^{m+1,\infty}(\Omega)` bundle.
If $`f\in W^{m,2}(\Omega)`, then every compact $`K\subset\Omega` has an
open neighborhood $`V` with $`K\subset V\subset\Omega` on which $`u` has
a $`W^{m+2,2}(V)` representative. No trace or boundary condition is
imposed on $`u`.
:::

:::proof "elliptic.regularity.higher.local"
The case $`m=0` is the compact-set $`H^2` theorem. For the successor step,
first apply the induction hypothesis on an intermediate neighborhood of
$`K`, then restrict the weak equation and all Sobolev coefficient and
forcing data to that neighborhood. A cutoff equal to one near $`K`
localizes the equation, with commutator forcing at the required Sobolev
order. Apply the preceding-order regularity theorem to each differentiated
localized field, then assemble those first derivatives to gain one order
for the localized solution. Restricting once more to the cutoff-one region
removes the cutoff and yields the claimed
$`W^{m+3,2}` representative of the original solution.
:::

The global theory takes a different route. Rather than shrinking to compact
subsets, it localizes with the finite partition of unity of an atlas, and the
interior piece is proved with a difference-quotient theorem whose coefficients
live on all of $`\mathbb R^n`. The PDE only provides coefficients on
$`\Omega`, so an extension lemma preserving Lipschitz bounds and ellipticity
is needed first.

:::theorem "elliptic.regularity.coefficient_extension" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_global_ellipticCoefficientExtension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "327-331"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n` be bounded with the operational $`C^1`
extension atlas. If the entries of $`a` are globally $`C^1` and

$$`
\xi^\mathsf{T}a(x)\xi\geq\alpha|\xi|^2
\qquad (x\in\Omega,\ \alpha>0),
`

then there exist one globally defined extension, entrywise Lipschitz
constants, and compatible $`L^\infty(\mathbb R^n)` coefficient classes. The
pointwise field agrees with $`a` on $`\Omega`, each entry is globally
Lipschitz, the $`L^\infty` classes represent those entries almost everywhere,
and the resulting matrix is uniformly elliptic with constant $`\alpha/2`.
:::

:::proof "elliptic.regularity.coefficient_extension"
Continuity extends the ellipticity lower bound from $`\Omega` to its closure
and preserves half of it on an open neighborhood. A smooth cutoff equal to
one on the compact closure glues $`a` there to the scalar matrix
$`(\alpha/2)I` outside that neighborhood. Entrywise compact support of the
deviation from $`(\alpha/2)I` gives global Lipschitz bounds and bounded
$`L^\infty` representatives, while convexity of the quadratic-form lower
bound preserves ellipticity through the transition region.
:::

With the extension in hand, the interior cutoff of the atlas localizes the
weak solution away from the boundary. The resulting statement is a zero-trace
specialization of the compact-set theorem, phrased so that it can be summed
with the boundary pieces.

:::theorem "elliptic.regularity.h2.interior_piece" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_interior_h2_localized_piece") (uses := "elliptic.divergence.weak_solution, elliptic.regularity.coefficient_extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "327-331"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`\Omega` carries an operational bounded $`C^1` extension
atlas and

$$`
-\partial_i(a^{ij}\partial_j u)=f,\qquad
u\in H^1_0(\Omega),\quad f\in L^2(\Omega),
`

where the principal coefficients have global $`C^1` representatives and are
uniformly elliptic on $`\Omega`. If $`\eta_0` is the atlas's interior cutoff,
then $`\eta_0u` has an $`H^2(\Omega)` representative.
:::

:::proof "elliptic.regularity.h2.interior_piece"
A compactly supported cutoff localizes the weak equation away from the
boundary. Difference quotients give a uniform weighted $`L^2` estimate for
the first derivatives, weak compactness produces the second weak
derivatives, and the coordinate derivatives are assembled into the localized
$`H^2` field.
:::

Near the boundary a different mechanism is required, because difference
quotients in the normal direction leave the domain. The $`C^2` charts flatten
each boundary patch to the half-space. Write the transformed equation as
$`-\partial_i(\widetilde a^{ij}\partial_jv)=\widetilde f`, absorbing the
chart Jacobian into the coefficients and load. Tangential difference
quotients control every second derivative with at least one tangential
index. To see how the last derivative is recovered, expand the equation and
isolate the normal direction, indexed here by $`n`:

$$`
\widetilde a^{nn}\partial_{nn}v
=-\widetilde f
-\sum_{(i,j)\ne(n,n)}\widetilde a^{ij}\partial_{ij}v
-\sum_{i,j}(\partial_i\widetilde a^{ij})\partial_jv.
`

Every term on the right is already controlled in $`L^2`. Transformed ellipticity
gives $`\widetilde a^{nn}\ge\widetilde\alpha>0`, so division recovers
$`\partial_{nn}v` in $`L^2`. For a weak solution the expansion is
justified through the normal flux, without assuming the missing derivative
exists. The formula explains both the ellipticity hypothesis and
the coefficient derivatives needed by the boundary theorem.

:::theorem "elliptic.regularity.h2.boundary_piece" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_boundaryChart_h2_localized_piece") (uses := "elliptic.divergence.weak_solution, elliptic.regularity.c2_boundary_atlas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "334-340"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`\Omega` carries the operational $`C^2` boundary atlas, including its
finite charts and partition of unity. For a uniformly elliptic weak equation

$$`
-\partial_i(a^{ij}\partial_j u)=f,\qquad
u\in H^1_0(\Omega),\quad f\in L^2(\Omega),
`

with global $`C^1` coefficient representatives, every boundary cutoff
$`\eta_i` satisfies $`\eta_i u\in H^2(\Omega)` in the representative sense.
:::

:::proof "elliptic.regularity.h2.boundary_piece"
Flatten the boundary chart, transport the weak equation and ellipticity,
estimate tangential difference quotients, recover the normal derivative from
the normal flux, oddly reflect the zero-trace field, pull it back through the
$`C^2` chart, and restrict it to the physical domain.
:::

The interior piece and the finitely many boundary pieces together account for
the whole solution, since the atlas cutoffs sum to one on $`\Omega`. Their sum
is the global $`H^2` representative of the principal problem.

:::theorem "elliptic.regularity.h2.principal" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_global_h2_of_isWeakDivergenceSolution") (uses := "elliptic.regularity.h2.interior_piece, elliptic.regularity.h2.boundary_piece")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "334-340"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a domain carrying the operational $`C^2` boundary atlas,

$$`
-\partial_i(a^{ij}\partial_j u)=f,\qquad
u\in H^1_0(\Omega),\quad f\in L^2(\Omega),\quad
a^{ij}\in W^{1,\infty}(\Omega),
`

with global $`C^1` coefficient representatives and a positive uniform
ellipticity constant, implies $`u\in H^2(\Omega)` in the representative
sense. The representative equals the original weak solution almost
everywhere. This is the principal case $`b=c=0`.
:::

:::proof "elliptic.regularity.h2.principal"
Construct the interior piece and every boundary-chart piece, then assemble
their finite partition of unity in $`H^2`. Equality of each Sobolev base
coordinate with its localized weak solution makes the assembled base
coordinate equal to the original $`H^1_0` function almost everywhere.
:::

Lower-order terms and the Gårding shift do not change the argument at this
level. Because the solution already lies in $`H^1_0(\Omega)` and the
coefficients $`b^i`, $`c` are essentially bounded, the terms $`b^iD_iu`,
$`cu`, and $`\lambda u` can be absorbed into an $`L^2` forcing, reducing the
shifted full-operator problem to the principal case.

:::theorem "elliptic.regularity.h2.global" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_global_h2_of_weak_shifted_full_divergence_solution") (uses := "elliptic.regularity.h2.principal")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "334-340"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same operational atlas, principal-coefficient, and ellipticity
hypotheses, let the first- and zeroth-order coefficients be in $`L^\infty`.
Every $`H^1_0` weak solution of

$$`-\partial_i(a^{ij}\partial_j u)+b^i\partial_i u+cu+\lambda u=f`

with $`f\in L^2(\Omega)` has an $`H^2(\Omega)` representative. Setting
$`\lambda=0` gives the full lower-order operator in Evans Theorem 4.
:::

:::proof "elliptic.regularity.h2.global" (uses := "elliptic.regularity.h2.principal")
Move $`b\cdot Du`, $`cu`, and $`\lambda u` to the right. Since the supplied weak
solution lies in $`H^1_0` and the coefficients are essentially bounded, the
effective forcing remains in $`L^2`. Apply principal-part global $`H^2`
regularity to that equation.
:::

# Higher Orders

Higher regularity differentiates the localized equation and repeatedly uses
the derivatives obtained at the preceding step. The global $`H^2` theorem is
the base case. At each higher order we must control both the differentiated
forcing and the terms created by differentiating the coefficients. The
arbitrary-order theorems record that induction, for the principal operator
and for the full operator; their $`k=1` and $`k=2` specializations give the
traditional $`H^3` and $`H^4` statements.

For $`m\ge1`, suppose $`u\in H^{m+1}` is already known,
$`f\in H^m`, and $`a^{ij}\in W^{m+1,\infty}`. Differentiating once in
coordinate $`k` gives

$$`
-\partial_i(a^{ij}\partial_j(\partial_k u))
=\partial_k f+\sum_{i,j}\partial_i((\partial_k a^{ij})\partial_j u).
`

The right side belongs to $`H^{m-1}` by the Sobolev product rules.
Applying the preceding-order regularity theorem to this equation gives
$`\partial_k u\in H^{m+1}`; assembling the first derivatives yields
$`u\in H^{m+2}`. Interior cutoffs supply the zero-trace conditions needed
for this argument. At a physical boundary, only tangential differentiation
preserves zero trace, so normal-flux recovery and pure-normal assembly are
separate parts of the induction (Evans, 2010, Theorem 5, pp. 340–343).

:::theorem "elliptic.regularity.all_orders" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_global_higherOrder_of_isWeakDivergenceSolution") (uses := "elliptic.regularity.h2.principal")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "340-343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`k\in\mathbb N`, assume $`\Omega` carries the operational
$`C^2` boundary atlas, with forward charts of class $`C^{k+2}` and inverse
charts of class $`C^{k+1}`. Then

$$`
f\in W^{k,2}(\Omega),\quad
a^{ij}\in W^{k+1,\infty}(\Omega),\quad
-\partial_i(a^{ij}\partial_j u)=f
\quad\Longrightarrow\quad
u\in W^{k+2,2}(\Omega),
`

for every $`u\in H^1_0(\Omega)`, provided the coefficients have global
$`C^{k+1}` representatives and are uniformly elliptic on $`\Omega`.
:::

:::proof "elliptic.regularity.all_orders"
Strong induction begins with global $`H^2`. At a successor order, the
previous representative supplies the lower regularity needed to
differentiate the localized equation.  Interior differentiated equations and
flattened boundary equations produce the next localized Sobolev pieces;
tangential derivatives, normal-flux recovery, coefficient reciprocals, and
pure-normal assembly recover all derivative directions.  A finite partition
of unity closes the global step.
:::

:::theorem "elliptic.regularity.full_operator_bootstrap" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.globalHigherRegularity.exists_of_weak_shifted_full_divergence_solution") (uses := "elliptic.regularity.all_orders, elliptic.regularity.h2.global")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "340-343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`k\in\mathbb N`, assume the same operational boundary atlas, with
forward charts of class $`C^{k+2}` and inverse charts of class $`C^{k+1}`.
Let $`a^{ij}\in W^{k+1,\infty}`, let $`b^i,c\in W^{k,\infty}`, and let
$`f\in W^{k,2}`. Then every $`H^1_0` weak solution of

$$`
Lu=-\partial_i(a^{ij}\partial_j u)+b^i\partial_i u+cu+\lambda u=f
`

has a $`W^{k+2,2}(\Omega)` representative, provided the principal
coefficients have global $`C^{k+1}` representatives and satisfy the same
positive uniform ellipticity condition. No regularity above $`H^1_0` is
assumed for the supplied weak solution.
:::

:::proof "elliptic.regularity.full_operator_bootstrap"
Use strong induction on $`k`. The base case is full-operator global $`H^2`
regularity. At a successor order, the induction hypothesis supplies the
preceding Sobolev representative. The higher-order multiplier estimates then
put $`b\cdot Du`, $`cu`, and $`\lambda u` in the required Sobolev space, so
the effective forcing belongs to $`W^{k,2}`. Apply the arbitrary-order
principal theorem to the rewritten divergence equation.
:::

# From Sobolev Regularity to Classical Smoothness

The arbitrary-order bootstrap produces an $`H^{m+2}(\Omega)`
representative for every finite $`m`. These representatives are initially
defined only up to null sets and may depend on $`m`, so this family alone is
not yet one classical function. The supercritical Sobolev–Morrey theory
resolves that coherence problem both in the interior and on the domain
closure.

In every positive dimension, the operational Sobolev theory raises
$`W^{m+n+1,2}(\Omega)` to $`W^{m+1,2n}(\Omega)`. When $`n=1`, this is
simply a restriction from $`W^{m+2,2}` to $`W^{m+1,2}`. In higher
dimensions, the first-order extension and Sobolev iteration raise the
integrability exponent to $`2n`. Since $`2n>n`, the Morrey representatives
are continuous, and their compatible weak derivatives are ordinary Fréchet
derivatives on the open set. Near a boundary point, an operational chart
flattens the closure to a closed half-space. Mathlib's derivative-extension
theorem on a convex half-ball then identifies the same continuous derivative
field as the derivative within $`\overline\Omega`.

:::definition "elliptic.regularity.all_order_data" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.AllOrderPrincipalData")
The all-order principal data fix one pointwise coefficient matrix
and one pointwise forcing function. Every forward and inverse boundary chart
is smooth; the coefficient matrix has a globally smooth representative; for
each $`k`, a $`W^{k+1,\infty}(\Omega)` coefficient bundle represents that
same matrix; and a $`W^{k,2}(\Omega)` forcing bundle represents that same
forcing. Fixing the underlying functions ensures that the Sobolev data at
different orders describe the same coefficients and forcing.
:::

Fixing the data resolves the coherence problem; the analytic content is the
passage from a finite Sobolev order to classical differentiability up to the
boundary. This is a statement about Sobolev fields alone, independent of any
equation.

:::theorem "elliptic.regularity.classical_on_closure_embedding" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_supercriticalSobolevJet_classical_on_closure, SobolevSpace.GraphSpace.BoundaryRegularity.hasClassicalRepresentativesOnClosure") (uses := "sobolev.higher_order_embedding, sobolev.morrey_weak_to_classical_closure")
Let $`n\geq1` and let $`\Omega` carry the operational $`C^2` boundary atlas.
Then every finite-order Sobolev field has a classical representative:

$$`
W^{m+n+1,2}(\Omega)\longrightarrow C^m(\overline\Omega)
`

for every finite $`m`.
:::

:::proof "elliptic.regularity.classical_on_closure_embedding"
For $`n=1`, restrict the derivative order once. For $`n\geq2`, lower the
exponent to one, perform $`n-1` subcritical steps to reach exponent $`n`,
and apply the critical embedding with finite target exponent $`2n`. Since
$`2n>n`, higher-order Morrey embedding supplies continuous representatives
for the weak derivatives. The closure weak-to-classical theorem reconstructs
their Fréchet derivatives within $`\overline\Omega`.
:::

Applied to the all-orders elliptic bootstrap, the embedding yields a $`C^m`
representative for every $`m`. Since all these representatives agree almost
everywhere with the same $`u` and are continuous, they coincide on $`\Omega`,
which produces one smooth function.

:::theorem "elliptic.regularity.interior_smooth" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_allOrderSobolevRepresentatives_of_isWeakDivergenceSolution, SobolevSpace.GraphSpace.BoundaryRegularity.exists_supercriticalSobolevJet, SobolevSpace.GraphSpace.BoundaryRegularity.exists_supercriticalSobolevJet_classical, SobolevSpace.GraphSpace.BoundaryRegularity.exists_interior_smoothRepresentative_of_isWeakDivergenceSolution") (uses := "elliptic.regularity.all_orders, elliptic.regularity.all_order_data, sobolev.higher_order_embedding")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\geq1`. Assume an operationally smooth boundary, coherent principal
coefficients and forcing data at every Sobolev order, and a positive
ellipticity lower bound. Let $`u\in H^1_0(\Omega)` be a homogeneous Dirichlet
weak solution of $`-\partial_i(a^{ij}\partial_j u)=f` with these data. Then
$`u` has a representative $`v` satisfying

$$`
v\in C^\infty(\Omega),
\qquad
v=u\quad\text{almost everywhere on }\Omega.
`
:::

:::proof "elliptic.regularity.interior_smooth"
The all-order elliptic bootstrap supplies a representative in every finite
Sobolev order. For requested classical order $`m`, Sobolev iteration gives a
$`W^{m+1,2n}` representative. Higher-order Morrey embedding produces
continuous representatives for the weak derivatives, and the
weak-to-classical reconstruction theorem identifies adjacent representatives
as Fréchet derivatives on $`\Omega`. Almost-everywhere agreement and
continuity identify the representatives pointwise, so one function belongs
to $`C^m(\Omega)` for every finite $`m`.
:::

The same coincidence argument extends to the closure. The closure-level
embedding provides representatives in $`C^m(\overline\Omega)`, and pointwise
agreement on $`\Omega` between functions continuous on $`\overline\Omega`
persists on $`\overline\Omega`.

:::theorem "elliptic.regularity.smooth_boundary" (parent := "elliptic.regularity") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.exists_smoothRepresentativeOnClosure_of_isWeakDivergenceSolution") (uses := "elliptic.regularity.interior_smooth, elliptic.regularity.classical_on_closure_embedding")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\geq1`. Assume smooth compatible boundary charts, principal coefficients
represented coherently at every Sobolev order, compatible forcing data at
every order, and uniform ellipticity. Let $`u\in H^1_0(\Omega)` be a homogeneous
Dirichlet weak solution of $`-\partial_i(a^{ij}\partial_j u)=f` with these data.
Then $`u` has a single representative $`v` such that

$$`
v\in C^\infty(\overline\Omega),
\qquad
v=u\quad\text{almost everywhere on }\Omega.
`
:::

:::proof "elliptic.regularity.smooth_boundary"
Apply arbitrary-order elliptic regularity at every finite order. The
completed-space embedding theorem gives a $`C^m(\overline\Omega)`
representative for each $`m`. Any two representatives agree almost everywhere
with the same solution; continuity first upgrades this to pointwise equality
on $`\Omega` and then on its closure. One representative therefore has every
finite derivative order on $`\overline\Omega`.
:::
