/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Foundations.TemperedDistributions
import Blueprint.Commands.Figures
import PDE.EnergyMethods.Dirichlet.Ball
import PDE.EnergyMethods.Dirichlet.Box
import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasMeasure
import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasOperator
import PDE.Spaces.Sobolev.Boundary.Trace.C1.MeasureClass
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal
import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Closure
import PDE.Spaces.Sobolev.Boundary.Flux.GreenIdentity
import PDE.Spaces.Sobolev.Boundary.Flux.Rellich.Estimate
import PDE.Elliptic.Semilinear.Pohozaev.Nonexistence

/-!
# Boundary calculus and operational C¹ boundary geometry

Boundary integration at three levels:

* explicit coordinate formulas on closed boxes and rectangles;
* radial formulas on positive-radius Euclidean balls and spheres;
* chartwise normal vectors, tangential Jacobians, a global atlas boundary
  measure on operational `C¹` boundaries, its intrinsic measure class, and
  the induced weighted `Lᵖ` coordinate maps.

The planar Stokes theorem is a coordinate Green formula; there is no
exterior calculus. The `C¹` development glues compatible chart measures into
a global measure with the same null sets as codimension-one Hausdorff surface
measure. The chartwise area formula,
`SobolevSpace.Trace.C1.atlasBoundaryMeasure_eq_surfaceMeasure`, upgrades this
to equality of the two measures.
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
#doc (Manual) "Boundary Calculus and C¹ Boundary Geometry" =>

:::group "foundations.boundary_calculus"
Boundary integration and operational boundary geometry
:::

# Scope, dimensions, and orientation conventions

The box theorem is formulated in dimension $`m+1`. This presentation gives a
nonempty coordinate type without carrying a separate positivity assumption.
The endpoints satisfy the coordinatewise non-strict inequality $`a\le b`.
Consequently, degenerate boxes and degenerate rectangles are included.

The ball theorems are formulated in dimension $`n` with the explicit typeclass
assumption $`n>0`, and the radius hypothesis is strict: $`r>0`. Ball integrals
use the open metric ball. Sphere integrals use the library's sphere measure.

For operational `C¹` domains, every chart sends the physical domain to the
positive side of the flattened last coordinate:

$$`
  x\in\Omega
  \quad\Longleftrightarrow\quad
  (\kappa_i(x))_{\mathrm{last}}>0
`

inside the chart source. Therefore decreasing flattened height points outward.
This sign convention determines the minus sign in the chartwise normal.

# Coordinate boxes

:::definition "foundations.boundary_calculus.box_flux" (parent := "foundations.boundary_calculus") (lean := "Energy.boxFlux")
Let $`F=(F_1,\ldots,F_{m+1})` and let $`[a,b]` be a coordinate box. The
quantity `boxFlux a b F` is the explicit oriented sum of its coordinate-face
integrals:

$$`
  \operatorname{boxFlux}_{[a,b]}(F)
  :=
  \sum_{i=1}^{m+1}
  \left(
    \int_{\{x\in[a,b]:x_i=b_i\}}F_i(x)\,dS_i
    -
    \int_{\{x\in[a,b]:x_i=a_i\}}F_i(x)\,dS_i
  \right).
`

The upper face has normal $`+e_i` and the lower face has normal $`-e_i`.
Each face integral is a Lebesgue integral over the $`m`-dimensional box of the
remaining coordinates.
:::

:::theorem "foundations.boundary_calculus.gauss_box" (parent := "foundations.boundary_calculus") (lean := "Energy.integral_divergence_eq_boxFlux_Icc") (uses := "foundations.operators.divergence, foundations.boundary_calculus.box_flux")
Fix $`a,b\in\mathbb R^{m+1}` with $`a\le b`. Suppose every scalar component
$`F_i:\mathbb R^{m+1}\to\mathbb R` is globally $`C^1`. Then

$$`
  \int_{[a,b]}
    \sum_{i=1}^{m+1}\partial_iF_i(x)\,dx
  =
  \operatorname{boxFlux}_{[a,b]}(F).
`

Integrability of the coordinate divergence follows from continuity on the
compact box and is not a hypothesis.
:::

:::proof "foundations.boundary_calculus.gauss_box"
Identify Euclidean space with Mathlib's finite coordinate-product model by
the canonical continuous linear equivalence. The identification preserves the
coordinate order, so it carries `Set.Icc a b` to the corresponding product
interval. A separate measure-preservation theorem transports Lebesgue volume;
the Euclidean norm and the coordinate-product maximum norm need not agree.

Apply Mathlib's box divergence theorem component by component. Under the
equivalence, the Fréchet derivative in the $`i`th basis direction is exactly
`partialDeriv i`. Transport the volume integral and every oriented face
integral back through the measure-preserving equivalence. The resulting face
sum is definitionally `boxFlux`.
:::

# Green formulas and planar Stokes on rectangles

:::definition "foundations.boundary_calculus.rectangle_circulation" (parent := "foundations.boundary_calculus") (lean := "Energy.rectangleCirculation")
For a planar field $`(P,Q)`, `rectangleCirculation a b P Q` is the
counterclockwise coordinate-face sum

$$`
  \oint_{\partial[a,b]} P\,dx+Q\,dy.
`

Formally it is `boxFlux` applied to the rotated field $`(Q,-P)`. This choice
turns outward flux of the rotated field into positive counterclockwise
circulation of $`(P,Q)`.
:::

Circulation is thus flux in disguise: rotating the field by a quarter turn
exchanges tangential and normal components on every face of the rectangle.

:::definition "foundations.boundary_calculus.rectangle_outward_flux" (parent := "foundations.boundary_calculus") (lean := "Energy.rectangleOutwardFlux") (uses := "foundations.boundary_calculus.box_flux")
For a planar field $`(P,Q)`, `rectangleOutwardFlux a b P Q` is the oriented
face sum representing

$$`
  \oint_{\partial[a,b]}(P,Q)\mathbin{\cdot}\nu\,ds.
`

It is `boxFlux` applied directly to the two coordinate components.
:::

Both planar quantities are box fluxes with $`m+1=2`, so both forms
of Green's theorem reduce to the box Gauss theorem applied to a suitable
two-component field. The circulation form corresponds to the rotated field,
whose coordinate divergence is the scalar curl $`\partial_xQ-\partial_yP`.

:::theorem "foundations.boundary_calculus.green_circulation_rectangle" (parent := "foundations.boundary_calculus") (lean := "Energy.greens_circulation_theorem_Icc") (uses := "foundations.boundary_calculus.gauss_box, foundations.boundary_calculus.rectangle_circulation")
Let $`a,b\in\mathbb R^2` satisfy $`a\le b`, and let
$`P,Q:\mathbb R^2\to\mathbb R` be globally $`C^1`. Then

$$`
  \int_{[a,b]}
    \left(
      \frac{\partial Q}{\partial x}
      -
      \frac{\partial P}{\partial y}
    \right)\,dA
  =
  \operatorname{rectangleCirculation}_{[a,b]}(P,Q).
`
:::

:::proof "foundations.boundary_calculus.green_circulation_rectangle"
Define $`F=(Q,-P)`. Its coordinate divergence is
$`\partial_xQ-\partial_yP`. Global $`C^1` regularity of $`P` and $`Q` gives
global $`C^1` regularity of both components of $`F`, and continuity of the
curl gives integrability on the compact rectangle. Apply the box Gauss
theorem and unfold `rectangleCirculation`.
:::

For a concrete calculation, take $`v(x,y)=(-y,x)` on $`R=[0,2]^2`, with
normal pointing out of the page. Its scalar curl is $`1-(-1)=2`. Each of
the four unit squares therefore contributes $`2`. When we add their
counterclockwise boundary integrals, every shared edge occurs once in each
direction and cancels. Along the outer boundary, the bottom, right, top,
and left edges contribute $`0`, $`4`, $`4`, and $`0`:

$$`
  \oint_{\partial R} -y\,dx+x\,dy
  =0+4+4+0=8
  =\int_R 2\,dA.
`

{leanpde_figure "stokes-circulation"}

The arrows mark the direction of integration. The
{bpref "foundations.boundary_calculus.green_circulation_rectangle"}[rectangle theorem]
justifies the equality for globally $`C^1` components and ordered rectangle
endpoints; the linear components here satisfy those hypotheses.

The same rotation appears in the
{bpref "fluid.euler.rotation"}[Euler calculation], where its nonzero curl
coexists with zero divergence and a quadratic pressure balances its
centripetal acceleration. Its
{bpref "fluid.euler.rotation_zero_strain"}[symmetric gradient also vanishes]:
circulation measures rotation, while the viscous strain measures deformation.

The flux form needs no rotation.

:::theorem "foundations.boundary_calculus.green_flux_rectangle" (parent := "foundations.boundary_calculus") (lean := "Energy.greens_flux_theorem_Icc") (uses := "foundations.boundary_calculus.gauss_box, foundations.boundary_calculus.rectangle_outward_flux")
Under the same hypotheses $`a\le b` and global $`C^1` regularity of $`P,Q`,

$$`
  \int_{[a,b]}
    \left(
      \frac{\partial P}{\partial x}
      +
      \frac{\partial Q}{\partial y}
    \right)\,dA
  =
  \operatorname{rectangleOutwardFlux}_{[a,b]}(P,Q).
`
:::

:::proof "foundations.boundary_calculus.green_flux_rectangle"
Apply the two-dimensional box Gauss theorem directly to $`F=(P,Q)`. The
coordinate divergence is the displayed integrand, and the explicit face sum
is `rectangleOutwardFlux`.
:::

# Euclidean balls and spheres

:::definition "foundations.boundary_calculus.ball_normal_derivative" (parent := "foundations.boundary_calculus") (lean := "Energy.ballOutwardNormalDerivative") (uses := "foundations.operators.gradient")
For a center $`c\in\mathbb R^n`, a scalar function $`v`, and any
$`x\in\mathbb R^n`, define

$$`
  \partial_{\nu_c}v(x)
  :=
  \sum_{i=1}^n
    \partial_i v(x)\,
    \operatorname{normalize}(x-c)_i.
`

On a positive-radius sphere $`\lVert x-c\rVert=r`, this is the derivative in
the outward radial unit direction. The definition remains total at $`x=c`
because Mathlib defines `normalize 0 = 0`.
:::

The definition is written as a coordinate sum so that it matches the
componentwise form of the ball Gauss theorem. Arguments that prefer the
intrinsic gradient use the inner-product form.

:::theorem "foundations.boundary_calculus.ball_normal_derivative_gradient" (parent := "foundations.boundary_calculus") (lean := "Energy.ballOutwardNormalDerivative_eq_inner_gradient") (uses := "foundations.boundary_calculus.ball_normal_derivative")
The coordinate definition agrees everywhere with the Euclidean gradient
pairing:

$$`
  \partial_{\nu_c}v(x)
  =
  \left\langle
    \nabla v(x),
    \operatorname{normalize}(x-c)
  \right\rangle.
`

No differentiability hypothesis is needed for this equality because both
sides use the same totalized Fréchet derivative.
:::

:::proof "foundations.boundary_calculus.ball_normal_derivative_gradient"
Expand the Euclidean-space inner product as the finite sum of coordinate
inner products. Over $`\mathbb R`, each scalar inner product is ordinary
multiplication. Each gradient coordinate is the corresponding partial derivative.
:::

The boundary term of the divergence theorem on a ball is the pairing of the
field with the radial unit vector $`\operatorname{normalize}(x-c)`, the same
vector that appears in the normal derivative. Unlike the box case, a sphere is
not a union of coordinate faces, so the theorem is not a corollary of
Mathlib's box divergence theorem and is proved by a radial differentiation
argument instead.

:::theorem "foundations.boundary_calculus.gauss_ball" (parent := "foundations.boundary_calculus") (lean := "PDE.Analysis.ballIntegral_divergence_eq_sphereIntegral_normal_flux") (uses := "foundations.operators.divergence, foundations.boundary_calculus.ball_normal_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "710-712"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`n>0`, $`r>0`, and let every component
$`F_i:\mathbb R^n\to\mathbb R` be globally $`C^1`. Then

$$`
  \int_{B(c,r)}
    \sum_{i=1}^n\partial_iF_i(x)\,dx
  =
  \int_{\partial B(c,r)}
    \sum_{i=1}^n
      F_i(x)\operatorname{normalize}(x-c)_i\,dS(x).
`

Equivalently, on the sphere where $`x\ne c`,

$$`
  \int_{B(c,r)}\operatorname{div}F\,dx
  =
  \int_{\partial B(c,r)}
    F(x)\mathbin{\cdot}\frac{x-c}{\lVert x-c\rVert}\,dS(x).
`
:::

:::proof "foundations.boundary_calculus.gauss_ball"
Write

$$`
  D(x)=\sum_i\partial_iF_i(x),
  \qquad
  H(x)=\sum_iF_i(x)(x-c)_i.
`

First prove, for positive $`s` near $`r`, the compactly supported weighted
identity

$$`
  \int_{\mathbb R^n}
    \max\!\left(s^2-\lVert x-c\rVert^2,0\right)D(x)\,dx
  =
  2\int_{B(c,s)}H(x)\,dx.
`

This is the integration-by-parts step; the positive-part quadratic cutoff
removes any boundary-at-infinity term.

Differentiate this identity once with respect to $`s`. The derivative of the
left side is $`2s\int_{B(c,s)}D`, while the radial differentiation formula
for the right side gives $`2\int_{\partial B(c,s)}H`. On
$`\partial B(c,r)`, write

$$`
  H(x)
  =
  r\sum_iF_i(x)\operatorname{normalize}(x-c)_i.
`

Substitute this identity and cancel the nonzero factor $`r`. This yields the
normal-flux formula.
:::

# Green identities on balls

:::theorem "foundations.boundary_calculus.green_first_ball" (parent := "foundations.boundary_calculus") (lean := "Energy.greens_first_identity_ball") (uses := "foundations.boundary_calculus.gauss_ball, foundations.boundary_calculus.ball_normal_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "711-712"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`n>0` and $`r>0`. If
$`u:\mathbb R^n\to\mathbb R` is globally $`C^1` and
$`v:\mathbb R^n\to\mathbb R` is globally $`C^2`, then

$$`
  \int_{B(c,r)}u\,\Delta v\,dx
  =
  -\int_{B(c,r)}
    \sum_{i=1}^n\partial_i u\,\partial_i v\,dx
  +
  \int_{\partial B(c,r)}
    u\,\partial_{\nu_c}v\,dS.
`

The gradient pairing is represented in the theorem by its finite coordinate
sum. The regularity is assumed on the whole space, which avoids an extension
theorem.
:::

:::proof "foundations.boundary_calculus.green_first_ball" (uses := "foundations.boundary_calculus.gauss_ball")
Apply the ball Gauss formula to the vector field with components
$`F_i=u\,\partial_i v`. The product rule gives

$$`
  \sum_i\partial_i(u\,\partial_i v)
  =
  \sum_i\partial_i u\,\partial_i v+u\,\Delta v.
`

Global $`C^1` and $`C^2` regularity makes the gradient pairing and Laplacian
term continuous, hence integrable on the bounded ball. The boundary flux
factors as $`u\,\partial_{\nu_c}v`. Split the volume integral and rearrange.
:::

:::theorem "foundations.boundary_calculus.green_second_ball" (parent := "foundations.boundary_calculus") (lean := "Energy.greens_second_identity_ball") (uses := "foundations.boundary_calculus.gauss_ball, foundations.boundary_calculus.ball_normal_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "711-712"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`n>0`, $`r>0`, and let $`u,v:\mathbb R^n\to\mathbb R` be globally
$`C^2`. Then

$$`
  \int_{B(c,r)}
    \left(u\,\Delta v-v\,\Delta u\right)\,dx
  =
  \int_{\partial B(c,r)}
    \left(
      u\,\partial_{\nu_c}v
      -
      v\,\partial_{\nu_c}u
    \right)\,dS.
`
:::

:::proof "foundations.boundary_calculus.green_second_ball" (uses := "foundations.boundary_calculus.gauss_ball")
Apply the ball Gauss theorem to
$`F_i=u\,\partial_i v-v\,\partial_i u`. Expanding its divergence produces
two mixed terms
$`\partial_i u\,\partial_i v` and
$`-\partial_i v\,\partial_i u`, which cancel pointwise. The remaining volume
term is $`u\Delta v-v\Delta u`, and the radial flux is the displayed
antisymmetric combination of normal derivatives.
:::

# Chartwise conormals and outward unit normals

Let $`\Omega\subset\mathbb R^n` carry the finite boundary atlas used for
{bpref "sobolev.extension.atlas"}[Sobolev extension], and assume $`n>0`. Each
chart $`\kappa_i` flattens its boundary piece to a coordinate hyperplane.
The chart map and its inverse map are defined on the ambient space and have
global $`C^1` regularity, but they are inverse to one another only on their
specified chart neighborhoods. All geometric conclusions are restricted to the
chart source.

Extension uses these charts to reflect functions across the boundary. Here
we use their last coordinate to determine which direction points outward.
Differentiating that coordinate gives a conormal; proving that it never
vanishes makes normalization possible. Agreement on overlapping charts then
turns the local directions into one boundary normal.

A graph makes the sign convention visible. Suppose locally that
$`\Omega=\{(y,z):z>h(y)\}` and flatten it by
$`\kappa(y,z)=(y,z-h(y))`. The height $`z-h(y)` increases into the domain.
Its differential sends a displacement $`(v,w)` to
$`w-\nabla h(y)\cdot v`. The *conormal* is this linear measurement of
normal displacement; the Euclidean inner product represents it by
$`(-\nabla h(y),1)`. Consequently the outward unit normal is

$$`
\nu(y,h(y))
=\frac{(\nabla h(y),-1)}{\sqrt{1+|\nabla h(y)|^2}}.
`

For the flat graph $`h=0`, this points straight down, out of the upper
half-space. The general chart construction makes the same choice for charts
of arbitrary form.

:::theorem "foundations.boundary_calculus.chart_height_domain_sign" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartLastCoordinate_pos_iff, SobolevSpace.Trace.C1.chartLastCoordinate_eq_zero_iff")
For $`x` in the source of $`\kappa_i`,

$$`
  (\kappa_i(x))_{\mathrm{last}}>0
  \quad\Longleftrightarrow\quad
  x\in\Omega,
`

and

$$`
  (\kappa_i(x))_{\mathrm{last}}=0
  \quad\Longleftrightarrow\quad
  x\in\partial\Omega.
`

Here $`\partial\Omega` is represented by `frontier Ω`. These equivalences
fix the inward/outward sign convention used in every subsequent normal
definition.
:::

:::proof "foundations.boundary_calculus.chart_height_domain_sign"
The atlas axioms identify the part of $`\Omega` inside the chart source with
the preimage of the upper half-space, and identify the frontier there with the
preimage of its boundary hyperplane. The upper half-space is characterized by
strict positivity of the last coordinate, while its boundary is characterized
by vanishing of that coordinate. Specializing these two identifications at
$`x` gives the claimed equivalences.
:::

Inside a chart source the boundary is the zero level set of the chart height
$`x\mapsto(\kappa_i(x))_{\mathrm{last}}`, so its normal direction at a
boundary point should be the gradient of that height. The height is a scalar
function on $`\mathbb R^n`, its differential is a covector, and the Riesz map
converts the covector into a physical vector.

:::definition "foundations.boundary_calculus.chart_conormal" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartConormal") (uses := "foundations.boundary_calculus.chart_height_domain_sign")
Let $`e_{\mathrm{last}}^*` be last-coordinate projection. The differential
of chart height at $`x` is the continuous linear functional

$$`
  L_i(x)
  :=
  e_{\mathrm{last}}^*\circ D\kappa_i(x).
`

The physical chart conormal is its Riesz representative:

$$`
  c_i(x)
  :=
  \mathcal R^{-1}(L_i(x)).
`

Thus $`L_i(x)[v]=\langle c_i(x),v\rangle` for physical tangent vectors $`v`.
:::

A conormal is useful only if it can be normalized, which requires it to be
nonzero. Invertibility of the chart enters here: differentiating
$`\kappa_i\circ\kappa_i^{-1}=\operatorname{id}` at $`\kappa_i(x)` shows that
$`D\kappa_i(x)` has a right inverse, and composing the nonzero functional
$`e_{\mathrm{last}}^*` with a surjective map cannot give zero.

:::theorem "foundations.boundary_calculus.chart_conormal_nonzero" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartConormal_ne_zero") (uses := "foundations.boundary_calculus.chart_conormal")
If $`x` belongs to the source of chart $`i`, then

$$`
  c_i(x)\ne0.
`
:::

:::proof "foundations.boundary_calculus.chart_conormal_nonzero"
Differentiate the local identity
$`\kappa_i\circ\kappa_i^{-1}=\operatorname{id}` at $`\kappa_i(x)`. Hence
$`D\kappa_i(x)` has a right inverse. Apply this identity to the last basis
vector $`e_{\mathrm{last}}`. If

$$`
  w=D\kappa_i^{-1}(\kappa_i(x))[e_{\mathrm{last}}],
`

then $`L_i(x)[w]=1`. Therefore $`L_i(x)` is not the zero functional, and its
Riesz representative $`c_i(x)` is nonzero.
:::

With nonvanishing established on the chart source, normalization is legitimate
there.

:::definition "foundations.boundary_calculus.chart_outward_normal" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartOutwardUnitNormal") (uses := "foundations.boundary_calculus.chart_conormal")
The chartwise outward unit normal is

$$`
  \nu_i(x)
  :=
  -\lVert c_i(x)\rVert^{-1}c_i(x).
`

The chart models $`\Omega` by positive height. At a boundary point, chart height
is zero, so the negative conormal points toward the exterior side of the
model half-space.
:::

Two facts justify the name outward unit normal: the height differential must
take a negative value on $`\nu_i(x)`, and $`\nu_i(x)` must have norm one. Both
rest on the Riesz identity $`L_i(x)[c_i(x)]=\lVert c_i(x)\rVert^2` together
with $`c_i(x)\ne0`, and the pairing can in fact be computed exactly.

:::theorem "foundations.boundary_calculus.chart_outward_normal_evaluation" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartConormal_apply_outwardUnitNormal") (uses := "foundations.boundary_calculus.chart_conormal_nonzero, foundations.boundary_calculus.chart_outward_normal")
On the source of chart $`i`, the chart-height differential evaluates on the
outward normal as

$$`
  L_i(x)[\nu_i(x)]
  =
  -\lVert c_i(x)\rVert.
`
:::

:::proof "foundations.boundary_calculus.chart_outward_normal_evaluation"
By the Riesz identity,

$$`
  L_i(x)[c_i(x)]
  =
  \langle c_i(x),c_i(x)\rangle
  =
  \lVert c_i(x)\rVert^2.
`

Apply linearity to $`-\lVert c_i(x)\rVert^{-1}c_i(x)` and cancel one norm
factor using $`c_i(x)\ne0`.
:::

At a boundary point, where chart height is zero, the sign of this value
identifies $`\nu_i` as the outward normal to $`\Omega`.

:::theorem "foundations.boundary_calculus.chart_outward_normal_orientation" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartConormal_apply_outwardUnitNormal_neg") (uses := "foundations.boundary_calculus.chart_outward_normal_evaluation, foundations.boundary_calculus.chart_conormal_nonzero")
The chart height decreases strictly in the chartwise outward direction:

$$`
  L_i(x)[\nu_i(x)]<0.
`

:::

:::proof "foundations.boundary_calculus.chart_outward_normal_orientation"
Use
$`L_i(x)[\nu_i(x)]=-\lVert c_i(x)\rVert`. Nonvanishing of $`c_i(x)` gives
$`\lVert c_i(x)\rVert>0`, so its negative is strictly below zero.
:::

Orientation fixes the direction of $`\nu_i(x)`; its length remains. Dividing
by $`\lVert c_i(x)\rVert` is a normalization only where that norm is
nonzero, which again restricts the statement to the chart source.

:::theorem "foundations.boundary_calculus.chart_outward_normal_unit" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.norm_chartOutwardUnitNormal") (uses := "foundations.boundary_calculus.chart_conormal_nonzero, foundations.boundary_calculus.chart_outward_normal")
On the source of chart $`i`,

$$`
  \lVert\nu_i(x)\rVert=1.
`
:::

:::proof "foundations.boundary_calculus.chart_outward_normal_unit"
Norm homogeneity gives

$$`
  \lVert\nu_i(x)\rVert
  =
  \lVert c_i(x)\rVert^{-1}\lVert c_i(x)\rVert.
`

The conormal is nonzero, so its norm is nonzero and the product is one.
:::

Everything so far is relative to one chart. A point of $`\partial\Omega` may
lie in several chart sources, each producing its own conormal, and unless
these agree up to a positive factor no chart-independent normal can be
defined. Agreement of the kernels of the two height differentials gives a
common tangent hyperplane and hence proportionality; the sign of the factor is
where the shared height convention enters.

:::theorem "foundations.boundary_calculus.chart_conormal_compatible" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartConormal_eq_pos_smul") (uses := "foundations.boundary_calculus.chart_conormal_nonzero, foundations.boundary_calculus.chart_height_domain_sign")
Suppose $`x\in\partial\Omega` lies in the sources of charts $`i` and $`j`.
Then there is a strictly positive scalar $`a` such that

$$`
  c_j(x)=a\,c_i(x),
  \qquad a>0.
`

Thus the atlas gives not just a common tangent hyperplane but a coherent
choice of its outward side.
:::

:::proof "foundations.boundary_calculus.chart_conormal_compatible"
First show that the two chart-height differentials vanish on exactly the same
physical vectors. A vector in the kernel of one height differential generates,
to first order, a curve in that chart's flat boundary; chart overlap and the
boundary-characterization theorem force the other height differential to
vanish as well.

Two nonzero linear functionals to $`\mathbb R` with the same kernel are scalar
multiples. To determine the sign, move from the boundary point along the
positive last-coordinate ray in chart $`i`. Its inverse image lies inside
$`\Omega`, so chart $`j` also assigns positive height. Passing to the
right-hand derivative shows that the scalar is nonnegative. Nonvanishing of
both functionals rules out zero, hence the scalar is positive. Transport the
functional equality through the Riesz equivalence.
:::

Positivity of the factor $`a` is exactly what normalization needs: a negative
factor would leave the two unit normals opposite, while a positive one is
cancelled by the norm in the denominator.

:::theorem "foundations.boundary_calculus.chart_outward_normal_compatible" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartOutwardUnitNormal_eq") (uses := "foundations.boundary_calculus.chart_conormal_compatible, foundations.boundary_calculus.chart_outward_normal")
At a common boundary point of two chart sources,

$$`
  \nu_i(x)=\nu_j(x).
`
:::

:::proof "foundations.boundary_calculus.chart_outward_normal_compatible"
Write $`c_j=a\,c_i` with $`a>0`. Then
$`\lVert c_j\rVert=a\lVert c_i\rVert`. The positive factor cancels in

$$`
  -\frac{c_j}{\lVert c_j\rVert}
  =
  -\frac{a c_i}{a\lVert c_i\rVert}.
`
:::

:::definition "foundations.boundary_calculus.outward_unit_normal" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.outwardUnitNormal") (uses := "foundations.boundary_calculus.chart_outward_normal_compatible")
For $`x\in\partial\Omega`, choose a chart source containing $`x` and define

$$`
  \nu(x):=\nu_i(x).
`

The finite atlas covers the frontier, and overlap compatibility proves that
the result does not depend on the chosen chart.
:::

A definition by an arbitrary choice is usable only through a lemma that
replaces the chosen chart by any convenient one.

:::theorem "foundations.boundary_calculus.outward_unit_normal_chart" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.outwardUnitNormal_eq_chart") (uses := "foundations.boundary_calculus.outward_unit_normal")
If chart $`i` contains the boundary point $`x`, then the intrinsic normal
agrees with the chartwise normal:

$$`
  \nu(x)=\nu_i(x).
`
:::

:::proof "foundations.boundary_calculus.outward_unit_normal_chart"
Compare the chart chosen in the definition of $`\nu(x)` with chart $`i` and
apply chartwise overlap compatibility at $`x`.
:::

Once the intrinsic normal can be computed in any chart containing the point,
every chartwise property transfers to it.

:::theorem "foundations.boundary_calculus.outward_unit_normal_unit" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.norm_outwardUnitNormal") (uses := "foundations.boundary_calculus.outward_unit_normal_chart, foundations.boundary_calculus.chart_outward_normal_unit")
For every $`x\in\partial\Omega`,

$$`
  \lVert\nu(x)\rVert=1.
`
:::

:::proof "foundations.boundary_calculus.outward_unit_normal_unit"
Choose a chart containing $`x`, replace the intrinsic normal by its chartwise
representative, and use the chartwise unit-norm theorem.
:::

# Boundary parametrizations

Write the ambient dimension as $`m+1`. The construction also permits $`m=0`,
so it includes one-dimensional domains, whose boundary parameters are
zero-dimensional.

:::definition "foundations.boundary_calculus.chart_boundary_parameter_domain" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryParameterDomain")
Let `flatEmbedding` insert a zero last coordinate. The parameter domain of
chart $`i` is

$$`
  U_i^\partial
  :=
  \left\{
    y\in\mathbb R^m:
    (y,0)\in\operatorname{target}(\kappa_i)
  \right\}.
`
:::

Openness of $`U_i^\partial` is inherited from the chart target through the
continuous flat embedding. It matters later because identities such as
$`\Phi_j\circ\tau_{ij}=\Phi_i` hold only on parameter overlaps, and
differentiating them requires those overlaps to be neighbourhoods of their
points.

:::theorem "foundations.boundary_calculus.chart_boundary_parameter_domain_open" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.isOpen_chartBoundaryParameterDomain") (uses := "foundations.boundary_calculus.chart_boundary_parameter_domain")
The set $`U_i^\partial` is open in $`\mathbb R^m`.
:::

:::proof "foundations.boundary_calculus.chart_boundary_parameter_domain_open"
It is the preimage of the open chart target under the continuous linear
isometric flat embedding $`y\mapsto(y,0)`.
:::

Parameters are turned into physical boundary points by composing the flat
embedding with the inverse chart. This inverts the flattening supplied by the
atlas, restricted to the flat boundary hyperplane.

:::definition "foundations.boundary_calculus.chart_boundary_parametrization" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryParametrization") (uses := "foundations.boundary_calculus.chart_boundary_parameter_domain")
The physical boundary parametrization associated with chart $`i` is

$$`
  \Phi_i(y)
  :=
  \kappa_i^{-1}(y,0).
`

It is defined on all of $`\mathbb R^m` as a Lean function, while its geometric
boundary interpretation is used on $`U_i^\partial`.
:::

Regularity of $`\Phi_i` is global rather than confined to $`U_i^\partial`,
because the atlas supplies inverse charts as globally $`C^1` maps on all of
$`\mathbb R^{m+1}`. This is what allows the tangential derivative to be
defined at every parameter and to depend continuously on it.

:::theorem "foundations.boundary_calculus.chart_boundary_parametrization_regular" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.contDiff_chartBoundaryParametrization") (uses := "foundations.boundary_calculus.chart_boundary_parametrization")
The map $`\Phi_i:\mathbb R^m\to\mathbb R^{m+1}` is globally $`C^1`.
:::

:::proof "foundations.boundary_calculus.chart_boundary_parametrization_regular"
Compose the globally $`C^1` inverse chart with the continuous linear flat
embedding.
:::

Regularity says nothing about what $`\Phi_i` covers. To parametrize the
boundary piece seen by chart $`i` it must be one-to-one on the parameter
domain with image exactly the physical boundary patch, and the sign
characterization of the frontier is what identifies that image.

:::theorem "foundations.boundary_calculus.chart_boundary_parametrization_image" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryParametrization_injOn, SobolevSpace.Trace.C1.image_chartBoundaryParametrization") (uses := "foundations.boundary_calculus.chart_boundary_parametrization, foundations.boundary_calculus.chart_height_domain_sign")
The restriction of $`\Phi_i` to $`U_i^\partial` is injective, and

$$`
  \Phi_i(U_i^\partial)
  =
  \operatorname{source}(\kappa_i)\cap\partial\Omega.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_parametrization_image"
For injectivity, apply $`\kappa_i` to an equality of two parametrized points.
The chart right-inverse identity recovers the two flat embeddings, and the
flat embedding itself is injective.

For the image identity, a parameter in $`U_i^\partial` maps to the chart
source, and its chart image has zero last coordinate, so it lies on the
frontier. Conversely, if $`x` is a boundary point in the chart source, its
chart image has last coordinate zero. Project away that coordinate to obtain
$`y`, re-embed it, and use the chart inverse identity to recover $`x=\Phi_i(y)`.
:::

# Tangential coordinate changes

:::definition "foundations.boundary_calculus.chart_boundary_transition" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryTransitionDomain, SobolevSpace.Trace.C1.chartBoundaryTransition") (uses := "foundations.boundary_calculus.chart_boundary_parametrization")
For two charts, define the overlap parameter domain

$$`
  U_{ij}^\partial
  :=
  \left\{
    y\in U_i^\partial:
    \Phi_i(y)\in\operatorname{source}(\kappa_j)
  \right\}.
`

The tangential coordinate transition is

$$`
  \tau_{ij}(y)
  :=
  \operatorname{flatProjection}
    \left(\kappa_j(\Phi_i(y))\right).
`
:::

Openness makes the overlap measurable and regularity supplies a derivative.
Together with injectivity, these are the hypotheses of the same-dimensional
change-of-variables theorem applied to $`\tau_{ij}`.

:::theorem "foundations.boundary_calculus.chart_boundary_transition_regular" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.isOpen_chartBoundaryTransitionDomain, SobolevSpace.Trace.C1.contDiff_chartBoundaryTransition") (uses := "foundations.boundary_calculus.chart_boundary_transition")
The overlap $`U_{ij}^\partial` is open, and
$`\tau_{ij}:\mathbb R^m\to\mathbb R^m` is globally $`C^1`.
:::

:::proof "foundations.boundary_calculus.chart_boundary_transition_regular"
The overlap is the intersection of the open parameter domain with the
preimage of the open source of chart $`j` under the continuous map $`\Phi_i`.
The transition is a composition of $`\Phi_i`, chart $`\kappa_j`, and the
continuous linear flat projection, all globally $`C^1`.
:::

The transition is designed so that both charts parametrize the same physical
point. Verifying this also shows that $`\tau_{ij}` lands in the parameter
domain of chart $`j`, because a frontier point has zero height in every chart
containing it.

:::theorem "foundations.boundary_calculus.chart_boundary_transition_parametrization" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryTransition_mem_parameterDomain, SobolevSpace.Trace.C1.chartBoundaryParametrization_transition") (uses := "foundations.boundary_calculus.chart_boundary_transition")
For $`y\in U_{ij}^\partial`,

$$`
  \tau_{ij}(y)\in U_j^\partial
`

and

$$`
  \Phi_j(\tau_{ij}(y))=\Phi_i(y).
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_transition_parametrization"
The point $`\Phi_i(y)` lies on the physical frontier. Its image under chart
$`j` therefore has last coordinate zero. Re-embedding its tangential
projection recovers the full flattened point. The chart right-inverse
identity then gives the parametrization equality.
:::

Since $`\Phi_i` is injective on $`U_i^\partial`, the identity
$`\Phi_j\circ\tau_{ij}=\Phi_i` determines $`\tau_{ij}` uniquely, and the
transition in the opposite direction must undo it. Injectivity of the
transition and the exact identification of its image are then formal
consequences.

:::theorem "foundations.boundary_calculus.chart_boundary_transition_inverse" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryTransition_mem_transitionDomain, SobolevSpace.Trace.C1.chartBoundaryTransition_left_inv, SobolevSpace.Trace.C1.chartBoundaryTransition_injOn, SobolevSpace.Trace.C1.image_chartBoundaryTransitionDomain") (uses := "foundations.boundary_calculus.chart_boundary_transition_parametrization")
The transition sends $`U_{ij}^\partial` into $`U_{ji}^\partial`, and the
reverse transition is its inverse there:

$$`
  \tau_{ji}(\tau_{ij}(y))=y
  \qquad(y\in U_{ij}^\partial).
`

Consequently, $`\tau_{ij}` is injective on $`U_{ij}^\partial` and

$$`
  \tau_{ij}(U_{ij}^\partial)=U_{ji}^\partial.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_transition_inverse"
Both $`y` and $`\tau_{ji}(\tau_{ij}(y))` parametrize the same physical
boundary point through $`\Phi_i`. Injectivity of $`\Phi_i` on its parameter
domain proves the inverse identity. That identity gives injectivity.
Applying the same result with $`i` and $`j` exchanged gives surjectivity onto
the reverse overlap.
:::

# Tangential derivatives and Jacobians

Return to the graph parametrization $`\Phi(y)=(y,h(y))`. Its derivative
sends $`v` to $`(v,\nabla h(y)\cdot v)`, so its Gram matrix is
$`I+\nabla h(y)\nabla h(y)^{\mathsf T}`. The square root of its determinant
is

$$`
J_\partial\Phi(y)=\sqrt{1+|\nabla h(y)|^2}.
`

In a planar graph, this is the familiar arc-length factor
$`\sqrt{1+h'(y)^2}`. It measures how much a small patch stretches when
lifted from the parameter plane onto the boundary. The derivative is
rectangular, so an ordinary determinant of $`D\Phi` would not make sense;
the Gram matrix compares lengths and angles in the parameter space.
This is the density used to define the chart measures, and the area formula
identifies the resulting measure with Hausdorff measure on the chart.

:::definition "foundations.boundary_calculus.chart_boundary_tangential_derivative" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryTangentialDerivative") (uses := "foundations.boundary_calculus.chart_boundary_parametrization")
The tangential derivative of $`\Phi_i` is the rectangular continuous linear
map

$$`
  T_i(y)
  :=
  D\kappa_i^{-1}(y,0)
  \circ
  \operatorname{flatEmbedding},
  \qquad
  T_i(y):\mathbb R^m\to\mathbb R^{m+1}.
`
:::

Defining $`T_i` through the derivative of the inverse chart rather than as the
derivative of $`\Phi_i` makes continuity in $`y` visible: it is the continuous
derivative of a $`C^1` map composed with a fixed linear embedding. The chain
rule then identifies it with the Fréchet derivative of $`\Phi_i` at every
point.

:::theorem "foundations.boundary_calculus.chart_boundary_tangential_derivative_formula" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.continuous_chartBoundaryTangentialDerivative, SobolevSpace.Trace.C1.fderiv_chartBoundaryParametrization") (uses := "foundations.boundary_calculus.chart_boundary_tangential_derivative")
The map $`y\mapsto T_i(y)` is continuous, and

$$`
  D\Phi_i(y)=T_i(y)
`

for every $`y\in\mathbb R^m`.
:::

:::proof "foundations.boundary_calculus.chart_boundary_tangential_derivative_formula"
Continuity follows from continuity of the Fréchet derivative of the globally
$`C^1` inverse chart, composed with the flat embedding. The derivative formula
is the Fréchet chain rule for
$`\Phi_i=\kappa_i^{-1}\circ\operatorname{flatEmbedding}`.
:::

An area factor is positive only where the parametrization is nondegenerate, so
injectivity of $`T_i(y)` has to be established before the Jacobian is
introduced. It comes from differentiating
$`\kappa_i\circ\kappa_i^{-1}=\operatorname{id}` at the flat point $`(y,0)`, an
identity valid only when $`(y,0)` lies in the chart target, that is, when
$`y\in U_i^\partial`.

:::theorem "foundations.boundary_calculus.chart_boundary_tangential_derivative_injective" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryTangentialDerivative_injective") (uses := "foundations.boundary_calculus.chart_boundary_tangential_derivative_formula")
For $`y\in U_i^\partial`, the linear map

$$`
  T_i(y):\mathbb R^m\to\mathbb R^{m+1}
`

is injective.
:::

:::proof "foundations.boundary_calculus.chart_boundary_tangential_derivative_injective"
Differentiate
$`\kappa_i\circ\kappa_i^{-1}=\operatorname{id}` at the flat point $`(y,0)`.
The derivative of $`\kappa_i` is a left inverse for the derivative of the
inverse chart. If $`T_i(y)v=T_i(y)w`, apply this left inverse to deduce that
the flat embeddings of $`v` and $`w` agree. Injectivity of the flat embedding
then gives $`v=w`.
:::

:::definition "foundations.boundary_calculus.chart_boundary_jacobian" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryJacobian") (uses := "foundations.boundary_calculus.chart_boundary_tangential_derivative")
The chart surface Jacobian is

$$`
  J_i^\partial(y)
  :=
  \operatorname{normDet}(T_i(y)).
`

Here `LinearMap.normDet` is the generalized determinant norm for the
rectangular map $`\mathbb R^m\to\mathbb R^{m+1}`. Equivalently,

$$`
  \left(J_i^\partial(y)\right)^2
  =
  \det\!\left(
    \bigl[\langle T_i(y)e_p,T_i(y)e_q\rangle\bigr]_{p,q}
  \right).
`
:::

Continuity of the Jacobian is what makes it a usable density: a continuous
function is bounded on the closure of the bounded parameter domain, and this
bound is what later gives the chart measures finite total mass.

:::theorem "foundations.boundary_calculus.chart_boundary_jacobian_continuous" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.continuous_chartBoundaryJacobian") (uses := "foundations.boundary_calculus.chart_boundary_jacobian, foundations.boundary_calculus.chart_boundary_tangential_derivative_formula")
The function $`J_i^\partial:\mathbb R^m\to\mathbb R` is continuous.
:::

:::proof "foundations.boundary_calculus.chart_boundary_jacobian_continuous"
Choose the standard orthonormal basis of $`\mathbb R^m`. Every entry of the
Gram matrix
$`\langle T_i(y)e_p,T_i(y)e_q\rangle` varies continuously with $`y`.
Determinant and square root are continuous, and `normDet` is the nonnegative
square root of the Gram determinant.
:::

Continuity does not exclude zeros. Strict positivity on the parameter domain
is a separate statement, and it is where injectivity of $`T_i(y)` is used.

:::theorem "foundations.boundary_calculus.chart_boundary_jacobian_pos" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryJacobian_pos") (uses := "foundations.boundary_calculus.chart_boundary_jacobian, foundations.boundary_calculus.chart_boundary_tangential_derivative_injective")
For $`y\in U_i^\partial`,

$$`
  J_i^\partial(y)>0.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_jacobian_pos"
Injectivity of $`T_i(y)` says its kernel is trivial. Mathlib's criterion for
`LinearMap.normDet` states that zero norm determinant is equivalent to a
nontrivial kernel in this finite-dimensional setting. Hence the norm
determinant is nonzero. Its general nonnegativity upgrades nonzero to strict
positivity.
:::

# Chart parameter measures and physical chart measures

:::definition "foundations.boundary_calculus.chart_boundary_parameter_measure" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryParameterMeasure") (uses := "foundations.boundary_calculus.chart_boundary_parameter_domain, foundations.boundary_calculus.chart_boundary_jacobian")
The Jacobian-weighted measure on the flat parameter space is

$$`
  \mu_i^\partial
  :=
  \left(
    \mathcal L^m\!\restriction U_i^\partial
  \right)
  \mathbin{\mathrm{withDensity}}
  \operatorname{ofReal}(J_i^\partial).
`

The `ofReal` conversion turns the nonnegative real Jacobian into an
extended-nonnegative density.
:::

Written as a density, the measure is convenient for measure-theoretic
manipulation, but concrete computations want the Jacobian as an integrand. The
two viewpoints agree because $`J_i^\partial` is a nonnegative real number, so
converting it to an extended-nonnegative density and back loses nothing.

:::theorem "foundations.boundary_calculus.chart_boundary_parameter_integral" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.integral_chartBoundaryParameterMeasure") (uses := "foundations.boundary_calculus.chart_boundary_parameter_measure")
For a function $`g:\mathbb R^m\to E` into a real normed vector space,

$$`
  \int_{\mathbb R^m}g(y)\,d\mu_i^\partial(y)
  =
  \int_{U_i^\partial}
    J_i^\partial(y)\,g(y)\,dy.
`

In Lean, multiplication of the real Jacobian with a vector-valued integrand
is scalar multiplication.
:::

:::proof "foundations.boundary_calculus.chart_boundary_parameter_integral"
Unfold the restricted measure and `withDensity`. The Bochner integral against
an extended-nonnegative density uses its real value. Since `normDet` is
nonnegative, `toReal (ofReal J_i^\partial)=J_i^\partial`, yielding the stated
weighted set integral.
:::

The parameter measure lives on the flat space $`\mathbb R^m`. Transporting it
along $`\Phi_i` produces a measure on physical space which, by construction,
is the parametrized area of the boundary piece seen by chart $`i`.

:::definition "foundations.boundary_calculus.chart_boundary_measure" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryMeasure") (uses := "foundations.boundary_calculus.chart_boundary_parameter_measure, foundations.boundary_calculus.chart_boundary_parametrization")
The physical surface measure contributed by chart $`i` is the pushforward

$$`
  \sigma_i^\partial
  :=
  (\Phi_i)_\#\mu_i^\partial.
`

This measure is concentrated on the physical chart boundary piece
$`\operatorname{source}(\kappa_i)\cap\partial\Omega`: almost every point
belongs to that piece. Its topological support can also contain limit points
outside the open chart source.
:::

For a pushforward measure the Bochner integral formula needs measurability
only with respect to the pushforward itself, which is weaker than strong
measurability of $`f` on all of $`\mathbb R^{m+1}`.

:::theorem "foundations.boundary_calculus.chart_boundary_integral" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.integral_chartBoundaryMeasure") (uses := "foundations.boundary_calculus.chart_boundary_measure, foundations.boundary_calculus.chart_boundary_parameter_integral")
Let $`E` be a real normed vector space and let
$`f:\mathbb R^{m+1}\to E`. If $`f` is almost everywhere strongly measurable
with respect to the specific chart measure $`\sigma_i^\partial`, then

$$`
  \int_{\mathbb R^{m+1}}f(x)\,d\sigma_i^\partial(x)
  =
  \int_{U_i^\partial}
    J_i^\partial(y)\,
    f(\Phi_i(y))\,dy.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_integral"
Use the Bochner integral formula for a mapped measure to pull the integral
back through $`\Phi_i`. Then apply the parameter-measure integral formula to
$`g=f\circ\Phi_i`.
:::

# Compatibility of chart measures

:::theorem "foundations.boundary_calculus.chart_boundary_transition_integral" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.lintegral_chartBoundaryTransition") (uses := "foundations.boundary_calculus.chart_boundary_transition_inverse, foundations.boundary_calculus.chart_boundary_jacobian")
For any extended-nonnegative integrand
$`g:\mathbb R^{m+1}\to[0,\infty]`,

$$`
  \int_{U_{ji}^\partial}
    J_j^\partial(z)\,
    g(\Phi_j(z))\,dz
  =
  \int_{U_{ij}^\partial}
    J_i^\partial(y)\,
    g(\Phi_i(y))\,dy.
`

The formal statement uses `ENNReal.ofReal` on each Jacobian and `lintegral`,
so it does not need an integrability assumption.
:::

:::proof "foundations.boundary_calculus.chart_boundary_transition_integral"
Apply the same-dimensional change-of-variables theorem to the injective
$`C^1` map

$$`
  \tau_{ij}:U_{ij}^\partial\to U_{ji}^\partial.
`

The image theorem identifies its image exactly with the reverse overlap.
The chain rule and
$`\Phi_j\circ\tau_{ij}=\Phi_i` identify the derivative of the composite.
Multiplicativity of `normDet` converts the transition Jacobian times
$`J_j^\partial` into $`J_i^\partial`. Substitute these identities into the
change-of-variables formula.
:::

The transition identity compares two Jacobian-weighted parameter integrals. To
turn it into a statement about the physical measures $`\sigma_i^\partial` and
$`\sigma_j^\partial`, each side must first be recognized as an integral
against one chart measure restricted to the other chart's source.

:::theorem "foundations.boundary_calculus.chart_boundary_restricted_integral" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.lintegral_chartBoundaryMeasure_restrict_source") (uses := "foundations.boundary_calculus.chart_boundary_measure, foundations.boundary_calculus.chart_boundary_transition")
If $`g:\mathbb R^{m+1}\to[0,\infty]` is measurable, then restricting chart
$`i`'s physical measure to chart $`j`'s source gives

$$`
  \int g(x)\,
    d\!\left(
      \sigma_i^\partial
      \restriction\operatorname{source}(\kappa_j)
    \right)(x)
  =
  \int_{U_{ij}^\partial}
    J_i^\partial(y)\,
    g(\Phi_i(y))\,dy.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_restricted_integral"
Unfold the pushforward measure and pull the restricted `lintegral` back
through $`\Phi_i`. The preimage of chart $`j`'s source inside
$`U_i^\partial` is precisely $`U_{ij}^\partial`. Unfold the parameter
measure's Jacobian density to obtain the right-hand side.
:::

Combining the two formulas, the restriction
$`\sigma_i^\partial\restriction\operatorname{source}(\kappa_j)` integrates
$`g` over $`U_{ij}^\partial`, its mirror image integrates over
$`U_{ji}^\partial`, and the transition identity equates the two. Applied to
indicator functions, this is equality of measures.

:::theorem "foundations.boundary_calculus.chart_boundary_measure_compatible" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryMeasure_restrict_source") (uses := "foundations.boundary_calculus.chart_boundary_transition_integral, foundations.boundary_calculus.chart_boundary_restricted_integral")
The two chart measures agree on their common physical patch:

$$`
  \sigma_i^\partial
    \restriction\operatorname{source}(\kappa_j)
  =
  \sigma_j^\partial
    \restriction\operatorname{source}(\kappa_i).
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_measure_compatible"
Use measure extensionality. For a measurable set $`A`, represent its measure
as the `lintegral` of the indicator of $`A`. Rewrite each restricted chart
measure by its parameter-overlap formula. The transition integral theorem
identifies the two Jacobian-weighted parameter integrals.
:::

# Local measure class

Two measures have the same *measure class* when they have the same null
sets. For example, $`\sigma` and $`2\sigma` agree on which functions are
equal almost everywhere, but
$`\int f\,d(2\sigma)=2\int f\,d\sigma` and, for finite $`p`,
$`\|f\|_{L^p(2\sigma)}=2^{1/p}\|f\|_{L^p(\sigma)}`.
Thus agreement of null sets is enough to compare representatives, while
transporting integrals and norms requires a density. Keeping these two
tasks distinct matters for the trace operators.

:::definition "foundations.boundary_calculus.chart_boundary_reference_measure" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryReferenceMeasure") (uses := "foundations.boundary_calculus.chart_boundary_parameter_domain, foundations.boundary_calculus.chart_boundary_parametrization")
The unweighted parametrized reference measure of chart $`i` is

$$`
  \nu_i^\partial
  :=
  (\Phi_i)_\#
  \left(
    \mathcal L^m\restriction U_i^\partial
  \right).
`

It separates the geometric transport through $`\Phi_i` from the positive
Jacobian density used to define $`\sigma_i^\partial`.
:::

Because $`J_i^\partial` is positive on $`U_i^\partial`, the weighted and
unweighted parameter measures have the same null sets, and hence so do
$`\sigma_i^\partial` and $`\nu_i^\partial`. Comparison with intrinsic
Hausdorff measure can therefore be carried out for the unweighted measure,
where only Lipschitz transport of null sets is needed.

:::theorem "foundations.boundary_calculus.chart_boundary_measure_ac_surface" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryMeasure_absolutelyContinuous_surfaceMeasure") (uses := "foundations.boundary_calculus.chart_boundary_reference_measure, foundations.boundary_calculus.chart_boundary_jacobian_pos")
The Jacobian-weighted chart measure is absolutely continuous with respect to
intrinsic surface measure:

$$`
  \sigma_i^\partial
  \ll
  \mathcal H^m\restriction\partial\Omega.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_measure_ac_surface"
The positive Jacobian density makes $`\sigma_i^\partial` absolutely
continuous with respect to $`\nu_i^\partial`. On the bounded physical chart
patch, the forward chart is Lipschitz. Its codimension-one Hausdorff
distortion estimate sends intrinsic surface-null sets to flat null sets,
which are exactly the parameter-null sets defining $`\nu_i^\partial`.
:::

Absolute continuity in the opposite direction cannot hold globally, since
$`\sigma_i^\partial` sees only the boundary patch of chart $`i`. Restricted to
that patch, however, the same Lipschitz argument applies with the roles of
chart and inverse chart exchanged.

:::theorem "foundations.boundary_calculus.surface_patch_ac_chart_boundary_measure" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasure_restrict_chartBoundaryPatch_absolutelyContinuous_boundaryMeasure") (uses := "foundations.boundary_calculus.chart_boundary_reference_measure, foundations.boundary_calculus.chart_boundary_jacobian_pos")
On the physical patch covered by chart $`i`, intrinsic surface measure is
absolutely continuous with respect to the chart measure:

$$`
  \left(
    \mathcal H^m\restriction\partial\Omega
  \right)
  \restriction
  \left(
    \operatorname{source}(\kappa_i)\cap\partial\Omega
  \right)
  \ll
  \sigma_i^\partial.
`
:::

:::proof "foundations.boundary_calculus.surface_patch_ac_chart_boundary_measure"
Strict positivity of $`J_i^\partial` shows that weighted and unweighted
parameter measures have the same null sets. The inverse chart is Lipschitz on
its bounded target, so flat parameter-null sets map to intrinsic
Hausdorff-null subsets of the physical boundary patch.
:::

# Global atlas boundary measure

Compatibility on overlaps says that the chart measures could be glued, but it
does not by itself produce a single measure: adding the $`\sigma_i^\partial`
would count overlaps several times. The remedy is to disjointify the chart
patches along the order of the finite atlas, so that each boundary point is
charged to exactly one chart.

:::definition "foundations.boundary_calculus.chart_boundary_cell" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.chartBoundaryCell") (uses := "foundations.boundary_calculus.chart_boundary_measure")
Fix the order already carried by the finite atlas. The cell assigned to chart
$`i` is

$$`
  C_i
  :=
  \left(
    \operatorname{source}(\kappa_i)\cap\partial\Omega
  \right)
  \setminus
  \bigcup_{j<i}
  \left(
    \operatorname{source}(\kappa_j)\cap\partial\Omega
  \right).
`
:::

Restricting a measure to a set is well behaved only for measurable sets, so
measurability of the cells is the first thing to check. It holds because each
cell is a finite Boolean combination of open chart sources and the closed
frontier.

:::theorem "foundations.boundary_calculus.chart_boundary_cell_measurable" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.measurableSet_chartBoundaryCell") (uses := "foundations.boundary_calculus.chart_boundary_cell")
Every cell $`C_i` is measurable.
:::

:::proof "foundations.boundary_calculus.chart_boundary_cell_measurable"
Each physical chart patch is the intersection of an open chart source with
the closed frontier. A cell is obtained from that measurable patch by
subtracting finitely many earlier measurable patches.
:::

Disjointness and covering are the two properties that make the cells a
partition of $`\partial\Omega`. Disjointness is built into the construction:
of two distinct indices, the larger has had the patch of the smaller removed.

:::theorem "foundations.boundary_calculus.chart_boundary_cells_disjoint" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.pairwise_disjoint_chartBoundaryCell") (uses := "foundations.boundary_calculus.chart_boundary_cell")
If $`i\ne j`, then $`C_i\cap C_j=\varnothing`.
:::

:::proof "foundations.boundary_calculus.chart_boundary_cells_disjoint"
If $`i<j`, the definition of $`C_j` removes the entire patch assigned to
chart $`i`, and $`C_i` is a subset of that patch. The opposite ordering is
symmetric.
:::

Removing earlier patches loses no points, since a point removed from the patch
of chart $`j` lies in the patch of an earlier chart. Covering the frontier
therefore reduces to the fact that the chart sources cover it.

:::theorem "foundations.boundary_calculus.chart_boundary_cells_cover" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.iUnion_chartBoundaryCell") (uses := "foundations.boundary_calculus.chart_boundary_cell")
The cells cover the whole frontier:

$$`
  \bigsqcup_i C_i=\partial\Omega.
`
:::

:::proof "foundations.boundary_calculus.chart_boundary_cells_cover"
Disjointization preserves the union of the original finite family. Every
chart patch lies in the frontier, and the boundary partition of unity proves
that every frontier point belongs to at least one chart source.
:::

With a measurable partition of the frontier in hand, the gluing is a finite
sum in which each cell is charged with the measure of its chart.
On a set contained in two chart sources the two chart measures agree by
compatibility, so which chart is charged for such a set does not affect its
mass.

:::definition "foundations.boundary_calculus.atlas_boundary_measure" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure") (uses := "foundations.boundary_calculus.chart_boundary_cell, foundations.boundary_calculus.chart_boundary_measure")
The global boundary measure associated with the operational atlas is

$$`
  \sigma_{\mathcal A}
  :=
  \sum_i
  \left(
    \sigma_i^\partial\restriction C_i
  \right).
`
:::

Finiteness of $`\sigma_{\mathcal A}` is inherited from the charts. Each chart
target is bounded by the atlas axioms, so each parameter domain is bounded and
the continuous Jacobian is integrable over it, and a finite sum of finite
pushforward measures is finite.

:::theorem "foundations.boundary_calculus.atlas_boundary_measure_finite" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_univ_lt_top") (uses := "foundations.boundary_calculus.atlas_boundary_measure")
The operational atlas measure has finite total mass:

$$`
  \sigma_{\mathcal A}\!\left(\mathbb R^{m+1}\right)<\infty.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_measure_finite"
For each chart, boundedness of the physical chart target and the isometric
flat embedding imply that the tangential parameter domain is bounded. The
continuous tangential Jacobian is bounded on the compact closure of that
domain, so its integral against Lebesgue measure is finite. Mapping this
finite parameter measure into physical space preserves its total mass.
Finally, the atlas contains only finitely many restricted chart measures, and
a finite sum of finite masses is finite.
:::

The intrinsic surface measure is finite for a parallel reason, with Lipschitz
transport of Hausdorff measure replacing the Jacobian bound. Its finiteness is
needed later because the Radon–Nikodym density of the intrinsic measure is
known to be finite almost everywhere only for a sigma-finite measure.

:::theorem "foundations.boundary_calculus.intrinsic_surface_measure_finite" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasure_lt_top_of_isC1ExtensionAtlas")
Intrinsic codimension-one Hausdorff surface measure has finite total mass on
the boundary of a bounded operational `C¹` domain:

$$`
  \left(
    \mathcal H^m\restriction\partial\Omega
  \right)
  \left(\mathbb R^{m+1}\right)
  <\infty.
`
:::

:::proof "foundations.boundary_calculus.intrinsic_surface_measure_finite"
Each bounded chart target intersects the flat boundary in a bounded
measurable set of finite flat Hausdorff measure. The inverse chart is
Lipschitz on its target, so its physical boundary patch also has finite
Hausdorff measure. The finite chart family covers the frontier.
:::

Integrals against a finite sum of restricted measures decompose accordingly.
For nonnegative extended-valued integrands the decomposition needs no
hypothesis at all, so global boundary integrals can be computed cell by
cell.

:::theorem "foundations.boundary_calculus.atlas_boundary_lintegral_cells" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.lintegral_atlasBoundaryMeasure_eq_sum_cells") (uses := "foundations.boundary_calculus.atlas_boundary_measure")
For every $`f:\mathbb R^{m+1}\to[0,\infty]`,

$$`
  \int_{\mathbb R^{m+1}}^- f\,d\sigma_{\mathcal A}
  =
  \sum_i
  \int_{C_i}^- f\,d\sigma_i^\partial.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_lintegral_cells"
Unfold $`\sigma_{\mathcal A}`. The Lebesgue integral of a nonnegative
function against a sum of measures is the sum of its integrals against the
individual measures. The atlas index type is finite, so the resulting
infinite sum is the displayed finite sum.
:::

For vector-valued integrands the same decomposition holds, but Bochner
integrability against $`\sigma_{\mathcal A}` must be assumed so that every
cell integral is defined and the finite sum is legitimate.

:::theorem "foundations.boundary_calculus.atlas_boundary_integral_cells" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.integral_atlasBoundaryMeasure_eq_sum_cells") (uses := "foundations.boundary_calculus.atlas_boundary_measure")
If $`f:\mathbb R^{m+1}\to E` is Bochner integrable with respect to
$`\sigma_{\mathcal A}`, then

$$`
  \int_{\mathbb R^{m+1}} f\,d\sigma_{\mathcal A}
  =
  \sum_i
  \int_{C_i} f\,d\sigma_i^\partial.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_integral_cells"
The Bochner integral of an integrable function against a countable sum of
measures is the sum of the component integrals. Unfold the atlas measure and
use finiteness of the chart index type.
:::

Two structural properties of $`\sigma_{\mathcal A}` follow from the
definition. The first is that it lives on the frontier, because every summand
is already restricted to a cell inside $`\partial\Omega`.

:::theorem "foundations.boundary_calculus.atlas_boundary_measure_supported" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_restrict_frontier") (uses := "foundations.boundary_calculus.atlas_boundary_measure, foundations.boundary_calculus.chart_boundary_cells_cover")
The global atlas measure is concentrated on the frontier:

$$`
  \sigma_{\mathcal A}\restriction\partial\Omega
  =
  \sigma_{\mathcal A}.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_measure_supported"
Every summand in the definition is restricted to a cell
$`C_i\subseteq\partial\Omega`. Restricting the finite measure sum to the
frontier therefore leaves every summand unchanged.
:::

The second property is the one that justifies calling $`\sigma_{\mathcal A}` a
gluing of the chart measures. Restricting the global measure to a chart source
must return that chart's measure in full, not only its own cell contribution,
and this is where compatibility on overlaps is used: the cells of other charts
that meet the source carry measures agreeing with $`\sigma_i^\partial` there.

:::theorem "foundations.boundary_calculus.atlas_boundary_measure_local" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_restrict_chartSource") (uses := "foundations.boundary_calculus.atlas_boundary_measure, foundations.boundary_calculus.chart_boundary_measure_compatible")
On every chart source, the global measure recovers the full measure of that
chart:

$$`
  \sigma_{\mathcal A}
    \restriction\operatorname{source}(\kappa_i)
  =
  \sigma_i^\partial.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_measure_local"
Restrict the defining sum to the source of chart $`i`. For each cell $`C_j`,
commute the two restrictions and use compatibility of the chart measures on
the $`i,j` overlap. The resulting sum is

$$`
  \sum_j \sigma_i^\partial\restriction C_j.
`

Pairwise disjointness and $`\bigsqcup_jC_j=\partial\Omega` identify this sum
with $`\sigma_i^\partial\restriction\partial\Omega`. The chart measure is
already concentrated on its physical boundary patch, so the final
restriction changes nothing.
:::

Frontier support and the local restriction property together characterize
$`\sigma_{\mathcal A}`. Any measure with both properties agrees with it on
every cell, and a measure concentrated on the frontier is determined by its
restrictions to a partition of the frontier.

:::theorem "foundations.boundary_calculus.atlas_boundary_measure_unique" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.eq_atlasBoundaryMeasure_of_restrict_chartSource") (uses := "foundations.boundary_calculus.atlas_boundary_measure_local")
Let $`\mu` be a measure concentrated on $`\partial\Omega`. If

$$`
  \mu\restriction\operatorname{source}(\kappa_i)
  =
  \sigma_i^\partial
`

for every boundary chart $`i`, then
$`\mu=\sigma_{\mathcal A}`.
:::

:::proof "foundations.boundary_calculus.atlas_boundary_measure_unique"
Restrict both measures to every disjoint cell $`C_i`. Since
$`C_i\subseteq\operatorname{source}(\kappa_i)`, the assumed chart equality
and the local theorem give equal cell restrictions. Glue those equalities
over the disjoint cell cover and use that both measures are concentrated on
the frontier.
:::

Uniqueness turns the question of whether $`\sigma_{\mathcal A}` is the
intrinsic surface measure into a local one. Since
$`\mathcal H^m\restriction\partial\Omega` is concentrated on the frontier by
definition, it equals the atlas measure exactly when it satisfies the chart
restriction property, which is the local area formula in each chart.

:::theorem "foundations.boundary_calculus.atlas_boundary_measure_surface_measure_iff" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_eq_surfaceMeasure_iff") (uses := "foundations.boundary_calculus.atlas_boundary_measure_local, foundations.boundary_calculus.atlas_boundary_measure_unique")
The atlas measure equals intrinsic codimension-one Euclidean Hausdorff
surface measure exactly when the equality holds in every chart:

$$`
  \sigma_{\mathcal A}
  =
  \mathcal H^m\restriction\partial\Omega
  \quad\Longleftrightarrow\quad
  \forall i,\;
  \left(
    \mathcal H^m\restriction\partial\Omega
  \right)
  \restriction\operatorname{source}(\kappa_i)
  =
  \sigma_i^\partial.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_measure_surface_measure_iff"
The forward implication follows by restricting the global equality to each
chart source and applying the local theorem. Conversely, intrinsic surface
measure is concentrated on the frontier by definition, so the uniqueness
theorem applies to the family of assumed local equalities.
:::

Without the local area formula one still gets that the two measures have the
same null sets. The first half is that intrinsically null sets are
$`\sigma_{\mathcal A}`-null: each cell contribution is a restriction of a
chart measure, for which this was shown locally.

:::theorem "foundations.boundary_calculus.atlas_boundary_measure_ac_surface" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure") (uses := "foundations.boundary_calculus.atlas_boundary_measure, foundations.boundary_calculus.chart_boundary_measure_ac_surface")
The assembled atlas measure is absolutely continuous with respect to
intrinsic surface measure:

$$`
  \sigma_{\mathcal A}
  \ll
  \mathcal H^m\restriction\partial\Omega.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_measure_ac_surface"
Every cell contribution is a restriction of a chart measure, hence is
absolutely continuous with respect to intrinsic surface measure by the local
result. Absolute continuity is preserved by the finite sum defining
$`\sigma_{\mathcal A}`.
:::

The reverse direction, that $`\sigma_{\mathcal A}`-null sets are intrinsically
null, cannot be read off from the chart measures one at a time, because the
local statement only controls the intrinsic measure of subsets of a single
patch. The cells resolve this: they partition the frontier, and on each cell
the corresponding chart contribution is one summand of the atlas measure.

:::theorem "foundations.boundary_calculus.surface_measure_ac_atlas_boundary" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure") (uses := "foundations.boundary_calculus.surface_patch_ac_chart_boundary_measure, foundations.boundary_calculus.chart_boundary_cells_cover")
Intrinsic surface measure is absolutely continuous with respect to the
assembled atlas measure:

$$`
  \mathcal H^m\restriction\partial\Omega
  \ll
  \sigma_{\mathcal A}.
`
:::

:::proof "foundations.boundary_calculus.surface_measure_ac_atlas_boundary"
Restrict the local reverse absolute-continuity theorem to each disjoint cell
$`C_i`. The corresponding chart contribution is one summand of the atlas
measure. Summing the restricted intrinsic measures over the disjoint cell
cover recovers all intrinsic surface measure.
:::

Mutual absolute continuity is the same as having identical null sets, so the
two directions combine into a single equivalence.

:::theorem "foundations.boundary_calculus.atlas_surface_same_null_sets" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_apply_eq_zero_iff_surfaceMeasure") (uses := "foundations.boundary_calculus.atlas_boundary_measure_ac_surface, foundations.boundary_calculus.surface_measure_ac_atlas_boundary")
The atlas and intrinsic surface measures have exactly the same null sets:

$$`
  \sigma_{\mathcal A}(A)=0
  \quad\Longleftrightarrow\quad
  \left(
    \mathcal H^m\restriction\partial\Omega
  \right)(A)=0.
`
:::

:::proof "foundations.boundary_calculus.atlas_surface_same_null_sets"
Apply the two absolute-continuity directions to the set $`A`.
:::

Almost-everywhere equality of two functions is a statement about a single set,
the set where they differ. Identical null sets therefore transfer
almost-everywhere equality between the two measures, for functions with values
in an arbitrary type.

:::theorem "foundations.boundary_calculus.atlas_surface_same_ae_equality" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.ae_eq_atlasBoundaryMeasure_iff_surfaceMeasure") (uses := "foundations.boundary_calculus.atlas_surface_same_null_sets")
For arbitrary functions $`f,g:\mathbb R^{m+1}\to X`,

$$`
  f=g\quad\sigma_{\mathcal A}\text{-a.e.}
  \quad\Longleftrightarrow\quad
  f=g\quad
  \left(
    \mathcal H^m\restriction\partial\Omega
  \right)\text{-a.e.}
`
:::

:::proof "foundations.boundary_calculus.atlas_surface_same_ae_equality"
The exceptional set $`\{x:f(x)\ne g(x)\}` is null for one measure exactly
when it is null for the other.
:::

Absolute continuity is the hypothesis of the Radon–Nikodym theorem, and it
holds in both directions. The density of intrinsic surface measure
with respect to $`\sigma_{\mathcal A}` is the more important of the two, since
it converts atlas-coordinate integrals into intrinsic ones.

:::definition "foundations.boundary_calculus.surface_measure_density" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasureDensity") (uses := "foundations.boundary_calculus.surface_measure_ac_atlas_boundary")
The intrinsic surface-measure density relative to the operational atlas
measure is the Radon–Nikodym derivative

$$`
  \rho_{\mathcal A}
  :=
  \frac{
    d\left(\mathcal H^m\restriction\partial\Omega\right)
  }{
    d\sigma_{\mathcal A}
  }.
`
:::

The opposite density describes the atlas measure in intrinsic terms. Mathlib's
`rnDeriv` is defined for any pair of measures, so both densities exist as
measurable functions; absolute continuity is what makes them reconstruct the
measures.

:::definition "foundations.boundary_calculus.atlas_boundary_measure_density" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasureDensity") (uses := "foundations.boundary_calculus.atlas_boundary_measure_ac_surface")
The reverse Radon–Nikodym density is

$$`
  \eta_{\mathcal A}
  :=
  \frac{
    d\sigma_{\mathcal A}
  }{
    d\left(\mathcal H^m\restriction\partial\Omega\right)
  }.
`
:::

The reconstruction statement for $`\rho_{\mathcal A}` uses
$`\mathcal H^m\restriction\partial\Omega\ll\sigma_{\mathcal A}`, the direction
that required the cell decomposition. The area formula identifies the two
measures, so $`\rho_{\mathcal A}=1` almost everywhere.

:::theorem "foundations.boundary_calculus.atlas_weighted_by_surface_density" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasBoundaryMeasure_withDensity_surfaceMeasureDensity") (uses := "foundations.boundary_calculus.surface_measure_density")
Weighting the operational atlas measure by
$`\rho_{\mathcal A}` recovers intrinsic surface measure exactly:

$$`
  \rho_{\mathcal A}\,\sigma_{\mathcal A}
  =
  \mathcal H^m\restriction\partial\Omega.
`
:::

:::proof "foundations.boundary_calculus.atlas_weighted_by_surface_density"
Apply the Radon–Nikodym reconstruction theorem to the already proved
absolute continuity
$`\mathcal H^m\restriction\partial\Omega\ll\sigma_{\mathcal A}`.
:::

For the density to be invertible it must avoid both zero and infinity almost
everywhere. Positivity holds intrinsically almost everywhere for the
Radon–Nikodym derivative of an absolutely continuous measure, and transfers to
$`\sigma_{\mathcal A}` because the null sets coincide.

:::theorem "foundations.boundary_calculus.surface_density_positive" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasureDensity_pos_ae") (uses := "foundations.boundary_calculus.surface_measure_density, foundations.boundary_calculus.atlas_boundary_measure_ac_surface")
The density $`\rho_{\mathcal A}` is strictly positive
$`\sigma_{\mathcal A}`-almost everywhere.
:::

:::proof "foundations.boundary_calculus.surface_density_positive"
The Radon–Nikodym derivative is positive almost everywhere for intrinsic
surface measure. Mutual absolute continuity transfers that statement to the
atlas measure.
:::

Finiteness is where finiteness of the intrinsic surface measure enters. The
Radon–Nikodym derivative of a sigma-finite measure is finite almost everywhere
for the reference measure, here $`\sigma_{\mathcal A}`.

:::theorem "foundations.boundary_calculus.surface_density_finite" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasureDensity_lt_top_ae") (uses := "foundations.boundary_calculus.surface_measure_density, foundations.boundary_calculus.intrinsic_surface_measure_finite")
The density $`\rho_{\mathcal A}` is finite
$`\sigma_{\mathcal A}`-almost everywhere.
:::

:::proof "foundations.boundary_calculus.surface_density_finite"
Intrinsic surface measure is finite on a bounded operational `C¹` domain and
therefore sigma-finite. The Radon–Nikodym derivative of a sigma-finite
measure is finite almost everywhere for its reference measure.
:::

Positive and finite almost everywhere, $`\rho_{\mathcal A}` has an
almost-everywhere reciprocal, and that reciprocal is the opposite density
$`\eta_{\mathcal A}`. This is the sense in which the two densities carry the
same information.

:::theorem "foundations.boundary_calculus.atlas_surface_densities_reciprocal" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceMeasureDensity_inv_ae") (uses := "foundations.boundary_calculus.surface_measure_density, foundations.boundary_calculus.atlas_boundary_measure_density")
The two densities are reciprocal
$`\sigma_{\mathcal A}`-almost everywhere:

$$`
  \rho_{\mathcal A}^{-1}
  =
  \eta_{\mathcal A}.
`
:::

:::proof "foundations.boundary_calculus.atlas_surface_densities_reciprocal"
Apply the reciprocal Radon–Nikodym theorem and transfer its exceptional set
between the mutually absolutely continuous measures.
:::

Reconstruction of the measure gives change-of-measure formulas for integrals.
For nonnegative integrands only almost-everywhere measurability with respect
to $`\sigma_{\mathcal A}` is required, and the density simply multiplies the
integrand.

:::theorem "foundations.boundary_calculus.surface_lintegral_as_weighted_atlas_lintegral" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.lintegral_surfaceMeasureDensity_mul") (uses := "foundations.boundary_calculus.atlas_weighted_by_surface_density")
For every nonnegative almost everywhere measurable $`f`,

$$`
  \int_{\partial\Omega}^{-} f\,
    d\left(\mathcal H^m\restriction\partial\Omega\right)
  =
  \int_{\partial\Omega}^{-}
    \rho_{\mathcal A} f\,d\sigma_{\mathcal A}.
`
:::

:::proof "foundations.boundary_calculus.surface_lintegral_as_weighted_atlas_lintegral"
Use the nonnegative integral formula for a measure reconstructed from its
Radon–Nikodym density.
:::

The Bochner version needs no integrability hypothesis in its statement. Its
weight is the real value of the extended-nonnegative density, and
almost-everywhere finiteness means the real value loses nothing.

:::theorem "foundations.boundary_calculus.surface_integral_as_weighted_atlas_integral" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.integral_surfaceMeasureDensity_smul") (uses := "foundations.boundary_calculus.atlas_weighted_by_surface_density")
For every function $`f` into a normed real vector space, Bochner integration
against intrinsic surface measure is weighted Bochner integration against the
atlas measure:

$$`
  \int_{\partial\Omega} f\,
    d\left(\mathcal H^m\restriction\partial\Omega\right)
  =
  \int_{\partial\Omega}
    \rho_{\mathcal A} f\,d\sigma_{\mathcal A}.
`
:::

:::proof "foundations.boundary_calculus.surface_integral_as_weighted_atlas_integral"
Apply the Bochner integral change-of-measure theorem for the
Radon–Nikodym derivative. In Lean the scalar weight is the real value of the
almost everywhere finite extended-nonnegative density.
:::

Change of measure with a density $`\rho` preserves $`L^p` norms once the
integrand is rescaled by $`\rho^{1/p}`: the $`p`-th power of $`\rho^{1/p}f`
integrated against $`\sigma_{\mathcal A}` is $`\rho\,\lvert f\rvert^p` against
$`\sigma_{\mathcal A}`, which is $`\lvert f\rvert^p` against intrinsic surface
measure. Positivity and finiteness of the density are what make this rescaling
invertible.

:::definition "foundations.boundary_calculus.surface_atlas_lp_equiv" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceLpEquivAtlasLp") (uses := "foundations.boundary_calculus.atlas_weighted_by_surface_density, foundations.boundary_calculus.surface_density_positive, foundations.boundary_calculus.surface_density_finite")
For a finite real exponent $`p\ge 1`, density-root rescaling gives the
canonical linear isometric equivalence

$$`
  T_p:
  L^p(
    \mathcal H^m\restriction\partial\Omega
  )
  \simeq_{\mathrm{iso}}
  L^p(\sigma_{\mathcal A}).
`

Its forward map and inverse change representatives by

$$`
  T_p f=\rho_{\mathcal A}^{1/p}f,
  \qquad
  T_p^{-1}g=\rho_{\mathcal A}^{-1/p}g
`
almost everywhere with respect to the corresponding measures. In
particular, $`\lVert T_p f\rVert_{L^p(\sigma_{\mathcal A})}` equals the
intrinsic surface `Lᵖ` norm of $`f`.
:::

Elements of $`L^p` are equivalence classes, so describing $`T_p` by a formula
is a statement about representatives and holds almost everywhere for the
target measure. For the forward map the target measure is
$`\sigma_{\mathcal A}`.

:::theorem "foundations.boundary_calculus.surface_atlas_lp_equiv_apply_ae" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceLpEquivAtlasLp_apply_ae") (uses := "foundations.boundary_calculus.surface_atlas_lp_equiv")
The atlas-measure representative of $`T_p f` is
$`\rho_{\mathcal A}^{1/p}f` almost everywhere.
:::

:::proof "foundations.boundary_calculus.surface_atlas_lp_equiv_apply_ae"
Apply the finite-exponent density-root change-of-measure equivalence with
$`\sigma_{\mathcal A}` as the reference measure and
$`\rho_{\mathcal A}\sigma_{\mathcal A}` as intrinsic surface measure.
:::

The inverse is described the same way, this time almost everywhere for intrinsic
surface measure, and its formula is the reciprocal density root. This is where
almost-everywhere positivity and finiteness of $`\rho_{\mathcal A}` are both
used.

:::theorem "foundations.boundary_calculus.surface_atlas_lp_equiv_symm_apply_ae" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.surfaceLpEquivAtlasLp_symm_apply_ae") (uses := "foundations.boundary_calculus.surface_atlas_lp_equiv")
The intrinsic-surface representative of $`T_p^{-1}g` is
$`\rho_{\mathcal A}^{-1/p}g` almost everywhere.
:::

:::proof "foundations.boundary_calculus.surface_atlas_lp_equiv_symm_apply_ae"
Use positivity and almost everywhere finiteness of the density to multiply
by the reciprocal density root.
:::

The finite-exponent trace operator `traceLp` takes values in $`L^p` of
intrinsic surface measure. Composing it with $`T_p` produces a trace whose
values are $`L^p` classes for $`\sigma_{\mathcal A}`, the measure for which
chartwise integral formulas are available, for every $`1\le p<\infty`.

:::definition "foundations.boundary_calculus.atlas_trace_lp" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.atlasTraceLp") (uses := "foundations.boundary_calculus.surface_atlas_lp_equiv")
For $`1\le p`, the finite-exponent boundary trace in operational atlas
coordinates is

$$`
  \operatorname{Tr}_{\mathcal A,p}
  :=
  T_p\circ\operatorname{Tr}_p.
`

Its representatives are expressed against the atlas measure used by the
chartwise boundary calculus.
:::

Because $`T_p` is a linear isometry, composition with it changes
representatives but not norms, so every quantitative bound on the intrinsic
trace transfers to atlas coordinates unchanged.

:::theorem "foundations.boundary_calculus.atlas_trace_lp_norm" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.norm_atlasTraceLp") (uses := "foundations.boundary_calculus.atlas_trace_lp, foundations.boundary_calculus.surface_atlas_lp_equiv")
For every Sobolev input $`u`,

$$`
  \lVert
    \operatorname{Tr}_{\mathcal A,p}u
  \rVert_{L^p(\sigma_{\mathcal A})}
  =
  \lVert
    \operatorname{Tr}_p u
  \rVert_{
    L^p(\mathcal H^m\restriction\partial\Omega)
  }.
`
:::

:::proof "foundations.boundary_calculus.atlas_trace_lp_norm"
The atlas trace is the intrinsic trace followed by the density-root linear
isometry, so its norm is preserved definitionally by the isometry API.
:::

The purpose of moving to atlas coordinates is to compute. On a chart source
the global measure is the chart measure, so the Bochner integral formula for
$`\sigma_i^\partial` becomes a formula for $`\sigma_{\mathcal A}` itself, with
the Jacobian-weighted parameter integral on the right.

:::theorem "foundations.boundary_calculus.atlas_boundary_integral_local" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.integral_atlasBoundaryMeasure_restrict_chartSource") (uses := "foundations.boundary_calculus.atlas_boundary_measure_local, foundations.boundary_calculus.chart_boundary_integral")
For a real normed vector space $`E`, let
$`f:\mathbb R^{m+1}\to E` be almost everywhere strongly measurable with respect
to the restriction of $`\sigma_{\mathcal A}` to the source of $`\kappa_i`.
Then

$$`
  \int_{\operatorname{source}(\kappa_i)}
    f(x)\,d\sigma_{\mathcal A}(x)
  =
  \int_{U_i^\partial}
    J_i^\partial(y)\,
    f(\Phi_i(y))\,dy.
`
:::

:::proof "foundations.boundary_calculus.atlas_boundary_integral_local"
Replace the restriction of $`\sigma_{\mathcal A}` to the chart source by
$`\sigma_i^\partial` using the local restriction theorem. The result is
exactly the Bochner integral formula for the physical chart measure.
:::

# The divergence theorem on C¹ graph domains

Boxes and balls are special because their boundaries have explicit
parametrizations. A general bounded domain is handled through local graphs:
near each boundary point, after a linear change of coordinates, the domain is
the region above the graph of a $`C^1` function. This is the hypothesis most
analysis texts place on a domain when they state the Gauss–Green theorem, and
{Informal.citet "evans-2010"}[] states the theorem for such domains in
Appendix C.2. Every integral in the theorem is taken against intrinsic
Hausdorff surface measure, and the chart and atlas measures enter only in the
proof.

{leanpde_figure "boundary-chart-normal"}

The figure shows both halves of the statement. On the left the divergence of
the plotted field is identically one, so its integral is an area, and the
flux of the same field through the outward normals reproduces that area. On
the right is the local picture in which the normal and the surface element
are computed.

:::definition "foundations.boundary_calculus.c1_graph_boundary" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Boundary.HasC1GraphBoundary, SobolevSpace.Trace.C1.normalFlux") (uses := "foundations.boundary_calculus.outward_unit_normal")
A set $`\Omega\subseteq\mathbb R^n` has *$`C^1` graph boundary* if for each
$`x\in\partial\Omega` there are a linear isomorphism
$`e:\mathbb R^n\to\mathbb R^{n-1}\times\mathbb R` and a function
$`\gamma:\mathbb R^{n-1}\to\mathbb R`, $`C^1` near the first component of
$`e(x)`, such that $`e(x)` lies on the graph of $`\gamma` and, for $`y` near
$`x`,

$$`
y\in\Omega\iff \gamma\bigl(e(y)_1\bigr)<e(y)_2 .
`

The isomorphism need not be orthogonal. For a vector field $`F` on a domain
with a $`C^1` boundary atlas, the *normal flux* is
$`\langle F(x),\nu(x)\rangle` at boundary points, with $`\nu` the outward
unit normal, and zero elsewhere.
:::

Extending the flux by zero off the boundary costs nothing, because it is only
ever integrated against surface measure, which lives on $`\partial\Omega`.

:::theorem "foundations.boundary_calculus.gauss_green_c1" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Boundary.Flux.gaussGreen_of_raw_graph, SobolevSpace.Boundary.Flux.gaussGreen_of_contDiffUpToBoundary, SobolevSpace.Boundary.Flux.integral_divergence_eq_normalFlux") (uses := "foundations.boundary_calculus.c1_graph_boundary, foundations.operators.divergence, foundations.boundary_calculus.atlas_boundary_measure_surface_measure_iff, foundations.boundary_calculus.intrinsic_surface_measure_finite")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      citation := "Appendix C.2"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 41, endLine := 61 }
    }
  ]
}
%%%
Let $`\Omega\subseteq\mathbb R^{m+1}` be bounded and open with $`C^1`
graph boundary, and write $`\sigma` for the $`m`-dimensional Hausdorff
measure on $`\partial\Omega`. Let $`F:\mathbb R^{m+1}\to\mathbb R^{m+1}` be
continuous on $`\overline\Omega`, with each component $`C^1` on $`\Omega`
and with the component and its first partial derivatives uniformly
continuous on $`\Omega`. Then $`\operatorname{div}F` is integrable on
$`\Omega`, the normal flux is $`\sigma`-integrable, and

$$`
\int_\Omega\operatorname{div}F\,dx=\int_{\partial\Omega}F\cdot\nu\,d\sigma .
`

The graph hypothesis alone builds the boundary atlas that defines $`\nu`.
A second form takes the atlas as given, and a third assumes $`F` is
$`C^1` on all of $`\mathbb R^{m+1}`.
:::

:::proof "foundations.boundary_calculus.gauss_green_c1"
First let $`F` be globally $`C^1` and treat one component and one direction
at a time. Cover $`\overline\Omega` by finitely many graph charts and one
open set compactly inside $`\Omega`, and split the component with a smooth
partition of unity subordinate to that cover. The interior piece has compact
support in $`\Omega`, so the integral of its derivative vanishes. On a graph
piece, integrate first along the vertical coordinate of the chart; the
fundamental theorem of calculus leaves the value on the graph, and the
factor produced by the change to graph coordinates is exactly the
chart surface element times the corresponding component of $`\nu`.
Summing the pieces gives
$`\int_\Omega\partial_iF_i=\int_{\partial\Omega}F_i\nu_i\,d\sigma`, and
summing over $`i` gives the vector identity.

For a field that is only regular up to the boundary, uniform continuity of
the derivatives and the graph structure give a globally $`C^1` field $`U`
equal to $`F` on $`\overline\Omega`. The divergences agree on the open set
$`\Omega` and the normal fluxes agree on $`\partial\Omega`, so the identity
for $`U` is the identity for $`F`. Integrability comes from the same
extension: $`\operatorname{div}U` is continuous on a compact set, and the
flux is bounded on a boundary of finite surface measure.
:::

Continuity of $`F` on the closure is a separate hypothesis because the
boundary side of the formula evaluates $`F` itself on $`\partial\Omega`.
Uniform continuity on $`\Omega` gives a continuous extension to the closure,
and the hypothesis says that $`F` equals it.

Applying the theorem to $`u\nabla v` gives Green's identities. The gradient of
$`v` on the boundary is the continuous extension of the interior gradient,
since $`v` is only assumed regular up to the boundary.

:::theorem "foundations.boundary_calculus.green_first_c1" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Boundary.Flux.green_first_identity_of_contDiffUpToBoundary") (uses := "foundations.boundary_calculus.gauss_green_c1, foundations.operators.gradient, foundations.operators.laplacian, foundations.boundary_calculus.green_first_ball")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      citation := "Appendix C.2"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 41, endLine := 61 }
    }
  ]
}
%%%
Let $`\Omega` be as in the divergence theorem, with its boundary atlas. Let
$`u` be $`C^1` up to the boundary and continuous on $`\overline\Omega`, and
let $`v` be $`C^2` up to the boundary, with continuously extended gradient
$`\overline{\nabla v}`. Then $`u\,\Delta v` and
$`\langle\nabla u,\nabla v\rangle` are integrable on $`\Omega`,
$`u\,\partial_\nu v` is $`\sigma`-integrable, and

$$`
\int_\Omega u\,\Delta v\,dx+\int_\Omega\nabla u\cdot\nabla v\,dx
=\int_{\partial\Omega}u\,\overline{\nabla v}\cdot\nu\,d\sigma .
`
:::

:::proof "foundations.boundary_calculus.green_first_c1"
Extend $`u` to a globally $`C^1` function and $`\nabla v` to a globally
$`C^1` field, both agreeing with the originals on the closure. Their product
is a globally $`C^1` field whose divergence on $`\Omega` is
$`\langle\nabla u,\nabla v\rangle+u\,\Delta v`. The divergence theorem for
globally $`C^1` fields turns its integral into the flux of
$`u\,\overline{\nabla v}`.
:::

:::theorem "foundations.boundary_calculus.green_second_c1" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Boundary.Flux.green_second_identity_of_contDiffUpToBoundary") (uses := "foundations.boundary_calculus.green_first_c1, foundations.boundary_calculus.green_second_ball")
If $`u` and $`v` are both $`C^2` up to the boundary and continuous on
$`\overline\Omega`, then

$$`
\int_\Omega\bigl(u\,\Delta v-v\,\Delta u\bigr)\,dx
=\int_{\partial\Omega}\bigl(u\,\overline{\nabla v}\cdot\nu
 -v\,\overline{\nabla u}\cdot\nu\bigr)\,d\sigma ,
`

with both integrands integrable.
:::

:::proof "foundations.boundary_calculus.green_second_c1"
Apply the first identity to $`(u,v)` and to $`(v,u)` and subtract. The
gradient terms cancel by symmetry of the inner product.
:::

Neither identity asks $`u` or $`v` to vanish on the boundary. The
{bpref "foundations.boundary_calculus.green_first_ball"}[ball versions] are the
case of a sphere, with a direct radial proof.

# Rellich and Pohozaev identities on bounded domains

The {bpref "foundations.distributions.rellich_compact"}[compact-support dilation identities]
have no boundary terms. On a bounded domain the multiplier
$`(x-c)\cdot\nabla u` does not vanish at the boundary even when $`u` does,
and the divergence theorem produces a boundary integral. What makes the
bounded-domain identity useful is that this boundary integral can be
computed exactly when $`u=0` on $`\partial\Omega`. The gradient is then
normal to the boundary, and the flux reduces to
$`\tfrac12\lvert\nabla u\rvert^2(x-c)\cdot\nu`. Its sign is the sign of
$`(x-c)\cdot\nu`, which is nonnegative when $`\overline\Omega` is star-shaped
about $`c`.

:::definition "foundations.boundary_calculus.rellich_field" (parent := "foundations.boundary_calculus") (lean := "PDE.Analysis.rellichField, PDE.Analysis.rellichMultiplierField, PDE.Analysis.divergence_rellichField, PDE.Analysis.divergence_rellichField_of_gradient, PDE.Analysis.inner_rellichField_of_normal") (uses := "foundations.operators.divergence, foundations.operators.gradient")
For a vector field $`X` and a vector field $`G` on $`\mathbb R^n`, the
*Rellich field* is

$$`
R_X(G)=(X\cdot G)\,G-\tfrac12\lvert G\rvert^2X ,
`

and $`R_c(G)` denotes the case $`X(x)=x-c`. If $`G` agrees with
$`\nabla u` near $`x` for a function $`u` that is $`C^2` at $`x`, then

$$`
\operatorname{div}R_c(G)(x)
=\bigl((x-c)\cdot G(x)\bigr)\,\Delta u(x)
+\Bigl(1-\frac n2\Bigr)\lvert G(x)\rvert^2 .
`

If $`G(x)` is a multiple of a unit vector $`\nu`, then
$`R_c(G)(x)\cdot\nu=\tfrac12\lvert G(x)\rvert^2\,(x-c)\cdot\nu`.
:::

For a general differentiable $`G`, the Lean divergence formula has two more
terms, $`(x-c)\cdot DG\,G-G\cdot DG\,(x-c)`. They cancel when $`DG` is
symmetric, which is the case for a gradient by equality of mixed partials.
The divergence of $`x-c` is $`n`, and that is where the dimension enters.
The Rellich field is the stress tensor of the Dirichlet energy contracted
with $`X`.

:::theorem "foundations.boundary_calculus.rellich_boundary" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Boundary.Flux.rellich_identity_of_contDiffUpToBoundary, SobolevSpace.Boundary.Flux.rellich_identity_of_raw_graph") (uses := "foundations.boundary_calculus.rellich_field, foundations.boundary_calculus.gauss_green_c1, foundations.distributions.rellich_compact")
Let $`\Omega\subseteq\mathbb R^{m+1}` be bounded and open with $`C^1` graph
boundary, let $`u` be $`C^2` up to the boundary and continuous on
$`\overline\Omega` with $`u=0` on $`\partial\Omega`, and let $`c` be any
point. Write $`n=m+1` and $`\overline{\nabla u}` for the continuous
extension of the gradient to $`\overline\Omega`. Then
$`\lvert\nabla u\rvert^2` and $`((x-c)\cdot\nabla u)\,\Delta u` are
integrable on $`\Omega`, the boundary integrand is $`\sigma`-integrable, and

$$`
\int_\Omega\bigl((x-c)\cdot\nabla u\bigr)\,\Delta u\,dx
+\Bigl(1-\frac n2\Bigr)\int_\Omega\lvert\nabla u\rvert^2\,dx
=\frac12\int_{\partial\Omega}\lvert\overline{\nabla u}\rvert^2\,(x-c)\cdot\nu\,d\sigma .
`
:::

:::proof "foundations.boundary_calculus.rellich_boundary"
The regularity of $`u` up to the boundary gives a $`C^1` vector field
$`G` on all of $`\mathbb R^{m+1}` that equals $`\nabla u` in $`\Omega` and
$`\overline{\nabla u}` on the closure. Apply the divergence theorem to
$`R_c(G)`. Inside $`\Omega`, $`G` is the gradient of $`u` near every
point, so the divergence formula of the Rellich field turns the volume side
into the left side. On the boundary, $`u` vanishes identically, so all
tangential derivatives vanish and $`\overline{\nabla u}` is a multiple of
$`\nu`. The normal component of $`R_c(G)` is then
$`\tfrac12\lvert\overline{\nabla u}\rvert^2\,(x-c)\cdot\nu`.
:::

Because the boundary is only $`C^1`, $`u` is $`C^2` up to the boundary rather
than on a neighbourhood of $`\overline\Omega`. Extending the gradient as a
$`C^1` field in its own right, rather than extending $`u` as a $`C^2`
function, is what lets the argument run with $`C^1` charts.

Replacing $`x-c` by a $`C^1` field $`X` that points strictly outward along
the boundary turns the same identity into an estimate for the normal
derivative.

:::theorem "foundations.boundary_calculus.rellich_transverse" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Boundary.Flux.exists_normalFlux_sq_integral_bound, SobolevSpace.Boundary.Flux.normalFlux_sq_integral_le_of_transverse, SobolevSpace.Boundary.Flux.normalFlux_sq_integral_le_of_raw_graph_transverse, SobolevSpace.Boundary.Flux.rellich_multiplier_identity_of_contDiffUpToBoundary") (uses := "foundations.boundary_calculus.rellich_boundary")
Let $`\Omega` be bounded and open with $`C^1` graph boundary. There is a
constant $`C>0` such that every $`u` that is $`C^2` up to the boundary,
continuous on $`\overline\Omega` and zero on $`\partial\Omega` satisfies

$$`
\int_{\partial\Omega}(\partial_\nu u)^2\,d\sigma
\le C\Bigl(\int_\Omega(\Delta u)^2\,dx+\int_\Omega\lvert\nabla u\rvert^2\,dx\Bigr).
`

More precisely, if $`X` is $`C^1` with $`X\cdot\nu\ge\delta>0` on
$`\partial\Omega`, and $`\lvert X\rvert\le M`,
$`\lVert DX\rVert\le K` and $`\lvert\operatorname{div}X\rvert\le D` in
$`\Omega`, one may take the constant $`\delta^{-1}` in front of
$`\int(\Delta u)^2+(M^2+2K+D)\int\lvert\nabla u\rvert^2`.
:::

:::proof "foundations.boundary_calculus.rellich_transverse"
The divergence theorem for $`R_X(G)`, with $`G` the $`C^1` extension of
the gradient, gives

$$`
\int_\Omega\Bigl((X\cdot\nabla u)\Delta u+DX\,\nabla u\cdot\nabla u
-\tfrac12\lvert\nabla u\rvert^2\operatorname{div}X\Bigr)dx
=\frac12\int_{\partial\Omega}(\partial_\nu u)^2\,X\cdot\nu\,d\sigma .
`

The right side is at least $`\tfrac\delta2\int(\partial_\nu u)^2`. On the
left, $`2\lvert(X\cdot\nabla u)\Delta u\rvert\le(\Delta u)^2+M^2\lvert\nabla u\rvert^2`,
and the other two terms are bounded by $`K` and $`D/2` times
$`\lvert\nabla u\rvert^2`. For the constant, the graph structure provides a
smooth field $`X` with $`X\cdot\nu\ge\tfrac12` on the boundary, built before
$`u` is chosen.
:::

Star-shapedness enters only through the sign of the boundary term.

:::theorem "foundations.boundary_calculus.star_shaped_flux" (parent := "foundations.boundary_calculus") (lean := "SobolevSpace.Trace.C1.inner_sub_outwardUnitNormal_nonneg_of_starConvex_closure, SobolevSpace.Trace.C1.normalFlux_smul_sub_nonneg_of_starConvex_closure, SobolevSpace.Trace.C1.integral_normalFlux_smul_sub_nonneg_of_starConvex_closure") (uses := "foundations.boundary_calculus.c1_graph_boundary, foundations.boundary_calculus.outward_unit_normal")
If $`\overline\Omega` is star-shaped about $`c`, then
$`(x-c)\cdot\nu(x)\ge0` at every boundary point. Consequently
$`\int_{\partial\Omega}w\,(x-c)\cdot\nu\,d\sigma\ge0` for every weight $`w`
that is nonnegative on $`\partial\Omega`.
:::

:::proof "foundations.boundary_calculus.star_shaped_flux"
The segment from $`x\in\partial\Omega` to $`c` lies in $`\overline\Omega`.
In a boundary chart at $`x`, the flattened height coordinate is positive in
$`\Omega` and zero on the boundary, so on $`\overline\Omega` it has a local
minimum at $`x`. Its derivative in the direction $`c-x` of the segment is
therefore nonnegative. The gradient of the height is a positive multiple of
$`-\nu(x)`, so $`(c-x)\cdot\nu(x)\le0`.
:::

Only the closure is required to be star-shaped, and $`c` may lie on the
boundary. The inequality can be an equality on part of the boundary.

The Pohozaev identity on a bounded domain combines the Rellich identity with
two more consequences of the divergence theorem. For $`-\Delta u=V'(u)`
with $`u=0` on $`\partial\Omega`, the chain rule gives
$`((x-c)\cdot\nabla u)\,V'(u)=(x-c)\cdot\nabla(V\circ u)`, whose integral is
$`-n\int V(u)` because $`V(u)=V(0)=0` on the boundary. Green's first
identity gives the energy identity.

:::theorem "foundations.boundary_calculus.pohozaev_boundary" (parent := "foundations.boundary_calculus") (lean := "PDE.Elliptic.Semilinear.pohozaev_identity_of_zero_boundary, SobolevSpace.Boundary.Flux.integral_radial_gradient_mul_deriv_potential") (uses := "foundations.boundary_calculus.rellich_boundary, foundations.boundary_calculus.green_first_c1, foundations.distributions.pohozaev_compact")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.4.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n`, $`n=m+1`, be bounded and open with
$`C^1` graph boundary, and let $`V:\mathbb R\to\mathbb R` be $`C^1` with
$`V(0)=0`. Let $`u` be $`C^2` up to the boundary, continuous on
$`\overline\Omega`, zero on $`\partial\Omega`, with $`-\Delta u=V'(u)` in
$`\Omega`. Then for every $`c`, all integrands in the two identities are
integrable, and

$$`
\int_\Omega\lvert\nabla u\rvert^2\,dx=\int_\Omega u\,V'(u)\,dx,
`

$$`
\frac{n-2}2\int_\Omega\lvert\nabla u\rvert^2\,dx
+\frac12\int_{\partial\Omega}\lvert\overline{\nabla u}\rvert^2\,(x-c)\cdot\nu\,d\sigma
=n\int_\Omega V(u)\,dx .
`
:::

:::proof "foundations.boundary_calculus.pohozaev_boundary"
Green's first identity with $`u=0` on the boundary gives
$`\int u\,\Delta u=-\int\lvert\nabla u\rvert^2`, and the equation turns
this into the energy identity. For the second identity, extend $`u` to a
$`C^1` function on $`\mathbb R^n` and apply the divergence theorem to
$`V(u)\,(x-c)`. Its flux vanishes because $`V(u)=0` on $`\partial\Omega`,
and its divergence is $`nV(u)+((x-c)\cdot\nabla u)V'(u)`, so
$`\int((x-c)\cdot\nabla u)V'(u)=-n\int V(u)`. By the equation the left side
is $`-\int((x-c)\cdot\nabla u)\Delta u`. Substituting into the Rellich
identity gives the result.
:::

With a power nonlinearity the two identities contradict each other unless
$`u=0`.

:::theorem "foundations.boundary_calculus.supercritical_nonexistence" (parent := "foundations.boundary_calculus") (lean := "PDE.Elliptic.Semilinear.eq_zero_on_closure_of_supercritical_power") (uses := "foundations.boundary_calculus.pohozaev_boundary, foundations.boundary_calculus.star_shaped_flux")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.4.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge3` and $`p>(n+2)/(n-2)`. Let $`\Omega\subseteq\mathbb R^n` be
bounded and open with $`C^1` graph boundary, with $`\overline\Omega`
star-shaped about some point. If $`u` is $`C^2` up to the boundary,
continuous on $`\overline\Omega`, zero on $`\partial\Omega`, and

$$`
-\Delta u=\lvert u\rvert^{p-1}u\quad\text{in }\Omega ,
`

then $`u=0` on $`\overline\Omega`.
:::

:::proof "foundations.boundary_calculus.supercritical_nonexistence"
Take $`V(s)=\lvert s\rvert^{p+1}/(p+1)`, which is $`C^1` with
$`V'(s)=\lvert s\rvert^{p-1}s` because $`p\ge1`. Write
$`P=\int_\Omega\lvert u\rvert^{p+1}`. The energy identity gives
$`\int\lvert\nabla u\rvert^2=P`, and by star-shapedness the boundary term of
the Pohozaev identity is nonnegative, so

$$`
\Bigl(\frac{n-2}2-\frac n{p+1}\Bigr)P\le0 .
`

The bracket is positive exactly when $`p+1>2n/(n-2)`, that is,
$`p>(n+2)/(n-2)`. Hence $`P=0`, so $`u=0` almost everywhere in
$`\Omega`, everywhere in $`\Omega` by continuity, and on the closure
by continuity again.
:::

The solution may change sign, and the closure need not be strictly
star-shaped. The exponent is strictly supercritical: at $`p=(n+2)/(n-2)` the
bracket vanishes, and the argument would need the boundary term to be strictly
positive somewhere. The boundary is a $`C^1` graph, and the two derivatives
are asked of $`u` up to the boundary, not of the boundary itself.

# Scope of the boundary calculus

The finite compatible chart family assembles into a unique frontier-supported
measure $`\sigma_{\mathcal A}` with the same null sets as intrinsic Hausdorff
surface measure. Density-root rescaling identifies the finite-exponent `Lᵖ`
spaces of the two measures isometrically, and for finite $`p\ge1` the
intrinsic trace has a norm-preserving atlas-coordinate form.

Mathlib supplies the same-dimensional Jacobian change of variables used for
chart transitions, Hausdorff-measure transport under isometries, and Lipschitz
null-set transport. The nonlinear codimension-one area formula, which
identifies $`\sigma_{\mathcal A}` with Hausdorff surface measure, is proved in
the trace development.
