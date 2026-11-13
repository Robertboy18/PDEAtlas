/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Foundations.PDEProblems
import PDE.Analysis.Integration.Polar
import PDE.Common.Euclidean.SpaceTime
import PDE.CoordinateSystems.Polar
import PDE.CoordinateSystems.Radial
import PDE.FDeriv.SpaceTime.Gradient.Basic
import PDE.FDeriv.Euclidean.Laplacian
import PDE.FDeriv.Polar.Laplacian
import PDE.FDeriv.SpaceTime

/-!
# Coordinate systems

Spacetime coordinates, radial and polar Laplacians, and integration in polar coordinates.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Euclidean, polar, and spherical coordinates" =>

PDE arguments repeatedly move between three coordinate languages. Evolution
equations use a canonical point of $`\mathbb R^{n+1}` with time stored in
coordinate zero. Radial differential identities replace
$`x\mapsto f(\lVert x\rVert)` by a one-variable profile. Polar integration
replaces Euclidean volume by an angular measure and a radial measure carrying
the Jacobian. These are different transformations with different hypotheses,
so each has its own interface.

The spacetime convention is shared by the heat, wave, transport,
conservation-law, Hamilton–Jacobi, and fluid equations.
If $`z\in\mathbb R^{n+1}`, then

$$`
  t=z_0,\qquad x_i=z_{i+1}.
`

The canonical vector therefore looks like $`(t,x)` at the coordinate level.
However, many analytic APIs curry a field as $`u(x,t)` or use the product
$`\mathbb R^n\times\mathbb R`. Explicit round trips convert between the
orders. In particular,
`splitSpaceTime` returns $`(x,t)`, `joinSpaceTime` accepts $`(x,t)`, and the
separate `timeSpaceContinuousLinearEquiv` exposes the order $`(t,x)`.

For derivatives, the central statement identifies the Euclidean Laplacian of
a radial field with
$`f''(r)+(n-1)f'(r)/r` away from the origin. The logarithmic and power
profiles then supply the calculations used by Laplace and Poisson fundamental
solutions.

For integration, the formal route is measure theoretic. A
measure-preserving equivalence gives the coordinate change, and Fubini turns
it into the familiar iterated polar formula with the Jacobian already encoded
in the radial measure.
The radial Jacobian decides whether a singularity is integrable. In positive
dimension, a shell of radius $`r` and thickness $`dr` has volume
$`|S^{n-1}|r^{n-1}\,dr`. Thus, for the nonnegative radial function
$`|x|^{-\alpha}` on the unit ball,

$$`
\int_{B_1}|x|^{-\alpha}\,dx
=|S^{n-1}|\int_0^1 r^{n-1-\alpha}\,dr.
`

This is finite exactly when $`\alpha<n`; in that case its value is
$`|S^{n-1}|/(n-\alpha)`. At $`\alpha=n` the radial integral is
$`\int_0^1dr/r`, which diverges logarithmically. The value assigned at the
single point $`x=0` does not change the integral. This power count determines whether a singular fundamental solution is
locally integrable at its source.

:::group "foundations.coordinates"
Coordinate systems
:::

# Canonical Euclidean spacetime

We fix one spacetime type rather than accept whichever presentation of
$`\mathbb R^{n+1}` a lemma arrives in. `EuclideanSpace ℝ (Fin n)` is
`WithLp 2 (Fin n → ℝ)`, and the `WithLp` structure keeps it distinct from the
function type `Fin n → ℝ` with its maximum norm; `PiLp.continuousLinearEquiv`
converts between them. The Zulip discussion
[thoughts on gradient](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/thoughts.20on.20gradient.html)
gives background on these normed-space instance choices. We pin the
Euclidean type and convert at the boundary, so the projections land in
Euclidean coordinates rather than in a function space.

:::definition "foundations.coordinates.bundled_projections" (parent := "foundations.coordinates") (lean := "PDE.Common.timeCLM, PDE.Common.timeCLM_apply, PDE.Common.spatialPartCLM_apply, PDE.Common.spatialPartCLM_timeSpaceCons, PDE.Common.timeSpaceCons_spatialPartCLM, PDE.Common.embedWithTimeZeroCLM, PDE.Common.embedWithTimeZeroCLM_zero, PDE.Common.embedWithTimeZeroCLM_succ") (uses := "foundations.euclidean_space.time, foundations.euclidean_space.spatial_projection")
The coordinate functions are bundled as continuous linear maps

$$`
  \pi_t\in\mathcal L(\mathbb R^{n+1},\mathbb R),
  \qquad
  \pi_x\in\mathcal L(\mathbb R^{n+1},\mathbb R^n),
`

with exact coordinate laws

$$`
  \pi_t(z)=z_0,
  \qquad
  \pi_x(z)_i=z_{i+1}.
`

The bundled spatial projection has the same coordinate values as the plain
projection.

The map

$$`
  \iota_x\in\mathcal L(\mathbb R^n,\mathbb R^{n+1}),
  \qquad
  \iota_x(v)=(0,v),
`

is the derivative of every fixed-time embedding
$`x\mapsto(t,x)`. Its coordinate laws are
$`(\iota_xv)_0=0` and $`(\iota_xv)_{i+1}=v_i`.

*Construction.*
The time map is Mathlib's continuous-linear coordinate projection at
$`0:\operatorname{Fin}(n+1)`. For the spatial map, take the family of
coordinate projections indexed by $`i:\operatorname{Fin}(n)`, using
$`i+1` in spacetime, assemble the family into a continuous linear map to a
function space, and transport it through the continuous-linear equivalence
between that function space and Euclidean $`\ell^2` coordinates. Extensional
equality with `spatialPart` follows by evaluating both sides at every $`i`.
The embedding is verified in coordinate zero and in every successor
coordinate.
:::

The bundled projections combine into an explicit equivalence between canonical
spacetime and the product $`\mathbb R^n\times\mathbb R`. Both directions are
given by formulas, so round-trip identities are available for rewriting.

:::definition "foundations.coordinates.product_split" (parent := "foundations.coordinates") (lean := "PDE.Common.splitSpaceTime, PDE.Common.joinSpaceTime, PDE.Common.split_joinSpaceTime, PDE.Common.join_splitSpaceTime, PDE.Common.spaceTimeContinuousLinearEquiv, PDE.Common.timeSpaceContinuousLinearEquiv") (uses := "foundations.coordinates.bundled_projections")
Canonical spacetime has two explicit product views:

$$`
  \begin{aligned}
  \operatorname{split}(z)&=(\pi_xz,\pi_tz)
      \in\mathbb R^n\times\mathbb R,\\
  \operatorname{join}(x,t)&=(t,x)
      \in\mathbb R^{n+1}.
  \end{aligned}
`

They are inverse:

$$`
  \operatorname{split}(\operatorname{join}(x,t))=(x,t),
  \qquad
  \operatorname{join}(\operatorname{split}z)=z.
`

Both directions are continuous linear maps, and together they define

$$`
  \mathbb R^{n+1}
  \xrightarrow[\sim]{\text{continuous linear}}
  \mathbb R^n\times\mathbb R.
`

Composing with the product swap gives the equally useful equivalence

$$`
  \mathbb R^{n+1}
  \xrightarrow[\sim]{\text{continuous linear}}
  \mathbb R\times\mathbb R^n.
`

The names encode the order: `spaceTimeContinuousLinearEquiv` returns
$`(x,t)`, while `timeSpaceContinuousLinearEquiv` returns $`(t,x)`, so one
pair is never read in both orders.

*Verification.*
For the first round trip, compare the spatial and time components:
`spatialPart (timeSpaceCons t x) = x` and the zeroth coordinate of
`timeSpaceCons t x` is $`t`. For the reverse round trip, use coordinate
extensionality. Coordinate zero is reconstructed from $`z_0`; every successor
coordinate is reconstructed from the corresponding entry of `spatialPart z`.

The bundled equivalence is a composite of four Mathlib equivalences: Euclidean
coordinates to plain functions, splitting coordinate zero off the tail,
returning the tail to Euclidean coordinates, and swapping the two factors.
Its forward and inverse maps unfold to the split and join maps by
definition, and the time-first equivalence adds one more swap.
:::

At the level of functions on spacetime, the same coordinate round trip converts
between curried fields $`u(x)(t)` and fields on $`\mathbb R^{n+1}`.

:::definition "foundations.coordinates.curry_uncurry" (parent := "foundations.coordinates") (lean := "PDE.Common.spaceTimeUncurry, PDE.Common.spaceTimeCurry, PDE.Common.spaceTimeCurry_uncurry, PDE.Common.spaceTimeUncurry_curry") (uses := "foundations.coordinates.product_split")
For any codomain type $`E`, with no topology or algebraic structure required,
the coordinate round trip induces

$$`
  (\mathbb R^n\to\mathbb R\to E)
  \;\longleftrightarrow\;
  (\mathbb R^{n+1}\to E).
`

Explicitly,

$$`
  \begin{aligned}
  \operatorname{uncurry}(u)(z)
    &=u(\pi_xz)(\pi_tz),\\
  \operatorname{curry}(U)(x)(t)
    &=U(t,x).
  \end{aligned}
`

Both composites are identity functions. Since this is a coordinate
reindexing, scalar fields, vector fields, predicates, solution records, and
symbolic objects can all use the same interface.

*Verification.*
For a curried $`u`, evaluate at arbitrary $`x,t` and use the two projection
laws for $`(t,x)`. For a spacetime field $`U`, evaluate at arbitrary $`z` and
use the reconstruction identity
$`(\pi_tz,\pi_xz)=z`. Function extensionality then gives both global
equalities.
:::

Because the coordinate equivalence is continuous linear, it is $`C^\infty`, and
composing with it preserves every order of differentiability. Smoothness can
therefore be checked in whichever of the two coordinate presentations is
convenient.

:::theorem "foundations.coordinates.smoothness_transport" (parent := "foundations.coordinates") (lean := "PDE.Common.contDiff_comp_joinSpaceTime_iff, PDE.Common.contDiff_spaceTimeUncurry_iff") (uses := "foundations.coordinates.product_split, foundations.coordinates.curry_uncurry")
Let $`E` be a real normed vector space and let $`m\in\mathbb N_\infty`.
Smoothness is invariant under the spacetime coordinate equivalence:

$$`
  U:\mathbb R^{n+1}\to E\text{ is }C^m
  \quad\Longleftrightarrow\quad
  ((x,t)\mapsto U(t,x))\text{ is }C^m.
`

Equivalently, a curried field $`u(x)(t)` is jointly $`C^m` after
`spaceTimeUncurry` exactly when the ordinary product function
$`(x,t)\mapsto u(x)(t)` is $`C^m`. This is joint regularity; it is stronger
than assuming separate smoothness in $`x` and $`t`.
:::

:::proof "foundations.coordinates.smoothness_transport"
Both directions are composition with one side of the continuous-linear
equivalence
$`\mathbb R^{n+1}\cong\mathbb R^n\times\mathbb R`. Continuous linear maps
are $`C^\infty`, so composition preserves every requested order $`m`.
The inverse laws identify the resulting composites with the original fields.
The curried statement is the same theorem after unfolding `spaceTimeUncurry`.
:::

The first differential operator adapted to the spacetime convention is the
spatial gradient, which drops the time component of the full gradient. It is the
operator appearing in the heat and transport equations, where the time
derivative is treated separately.

:::definition "foundations.coordinates.spatial_gradient" (parent := "foundations.coordinates") (lean := "PDE.spatialGradient, PDE.spatialGradient_apply") (uses := "foundations.coordinates.bundled_projections, foundations.operators.gradient")
For a scalar spacetime field $`u:\mathbb R^{n+1}\to\mathbb R`, the spatial
gradient discards the time component of the full Euclidean gradient:

$$`
  \nabla_xu(z):=\pi_x(\nabla u(z)).
`

Its exact component formula is

$$`
  (\nabla_xu(z))_i=\partial_{i+1}u(z).
`

Coordinate zero never appears. As with the full gradient and
`partialDeriv`, this is an equality of totalized expressions; interpreting
the components as classical derivatives requires differentiability of $`u`
at the point.

*Verification.*
Evaluate the spatial projection at $`i`, which selects coordinate $`i+1` of
the full gradient. The gradient-coordinate theorem attached to the gradient
definition identifies that coordinate with $`\partial_{i+1}u`.
:::

Evolution equations differentiate a field in time at fixed $`x` and in space at
fixed $`t`. The slice derivative theorems express both as the joint Fréchet
derivative evaluated on a coordinate direction, under differentiability of the
joint field at the point.

:::theorem "foundations.coordinates.slice_derivatives" (parent := "foundations.coordinates") (lean := "PDE.deriv_prod_timeSlice, PDE.partialDeriv_prod_spaceSlice, PDE.partialDeriv_timeSpaceCons_spatial, PDE.hasDerivAt_timeSpaceCons, PDE.partialDeriv_timeSpaceCons_eq_deriv, PDE.fderiv_timeSpaceCons_time, PDE.fderiv_joinSpaceTime_time, PDE.fderiv_joinSpaceTime_spatial") (uses := "foundations.coordinates.product_split, foundations.derivatives.partial")
Let $`E` be a real normed vector space. At a point where the joint field is
differentiable, derivatives of fixed-space and fixed-time slices are the
corresponding joint directional derivatives.

For a product field $`F:\mathbb R^n\times\mathbb R\to E`,

$$`
  \frac d{ds}F(x,s)\bigg|_{s=t}
  =DF(x,t)[(0,1)]
`

and

$$`
  \partial_i\bigl(y\mapsto F(y,t)\bigr)(x)
  =DF(x,t)[(e_i,0)].
`

For a canonical spacetime field $`U:\mathbb R^{n+1}\to E`,

$$`
  \begin{aligned}
  \partial_i\bigl(y\mapsto U(t,y)\bigr)(x)
    &=\partial_{i+1}U(t,x),\\
  \frac d{ds}U(s,x)\bigg|_{s=t}
    &=\partial_0U(t,x).
  \end{aligned}
`

The same facts are also stated after pulling $`U` back through
`joinSpaceTime`: the product direction $`(0,1)` becomes spacetime coordinate
$`0`, and $`(e_i,0)` becomes coordinate $`i+1`.
:::

:::proof "foundations.coordinates.slice_derivatives"
Apply the Fréchet chain rule to the affine inclusions
$`s\mapsto(x,s)` and $`y\mapsto(y,t)`. Their derivatives are respectively
$`a\mapsto(0,a)` and $`v\mapsto(v,0)`. Evaluating at $`1` or $`e_i` gives
the two product formulas.

For canonical spacetime, the fixed-time embedding has derivative
$`\iota_x:v\mapsto(0,v)`, and
$`\iota_x(e_i)=e_{i+1}`. The fixed-space time curve has velocity $`e_0`.
Substitution into the same chain rule yields the coordinate formulas.
Finally, `joinSpaceTime` is the inverse continuous linear map from
$`(x,t)` coordinates, so the pullback statements are these identities in the
product representation.
:::

Once slice derivatives are written as `fderiv` on a constant direction, the
regularity of a slice derivative follows from that of the derivative field,
which has one order less than the field. Each statement fixes which variable is
allowed to move, and none of them upgrades a fixed-time result to a joint one.

:::theorem "foundations.coordinates.slice_regularity" (parent := "foundations.coordinates") (lean := "PDE.contDiff_deriv_prod_timeSlice, PDE.contDiff_partialDeriv_prod_spaceSlice, PDE.contDiff_partialDeriv_timeTrace, PDE.contDiff_secondPartialDeriv_timeTrace, PDE.differentiableAt_time_slice_of_contDiffOn") (uses := "foundations.coordinates.slice_derivatives")
The slice operations use exactly the expected number of derivatives.
If $`F:\mathbb R^n\times\mathbb R\to E` is globally $`C^{m+1}`, then:

* for every fixed $`t`, the map
  $`x\mapsto \frac d{ds}F(x,s)|_{s=t}` is $`C^m`;
* the jointly varying spatial derivative
  $`(x,t)\mapsto\partial_i^xF(x,t)` is $`C^m`;
* consequently, for every fixed $`x`, the time trace

$$`
  t\longmapsto
  \partial_i\bigl(y\mapsto F(y,t)\bigr)(x)
`

  is $`C^m`.

If $`F` is $`C^{m+2}`, then a fixed-point time trace of two spatial
derivatives is $`C^m`. These are the exact variable dependencies of the Lean
theorems.

There is also a local cylinder statement. If $`I\subseteq\mathbb R` is open
and $`F` is jointly $`C^1` on $`\mathbb R^n\times I`, then every curve
$`t\mapsto F(x,t)` is differentiable at every $`t\in I`. Thus a classical
solution predicate that already stores joint $`C^1` regularity should not
store time differentiability again as independent data.
:::

:::proof "foundations.coordinates.slice_regularity"
Rewrite each slice derivative using the preceding slice chain rules as
`fderiv` of $`F` evaluated on a constant direction. The derivative field of
a $`C^{m+1}` map is $`C^m`; evaluation of a continuous-linear map on a
constant vector preserves that regularity. Composing with the smooth paths
$`x\mapsto(x,t)` or $`t\mapsto(x,t)` gives the trace statements. Iterate the
argument for two spatial derivatives. On an open cylinder, joint `ContDiffOn`
upgrades to `ContDiffAt` at each interior point, after which the fixed-space
chain rule supplies differentiability of the time curve.
:::

Commuting a time derivative with spatial derivatives is the slice form of the
symmetry of mixed partials, and needs the corresponding global $`C^2` or $`C^3`
regularity.

:::theorem "foundations.coordinates.mixed_time_space" (parent := "foundations.coordinates") (lean := "PDE.deriv_partialDeriv_timeSlice_comm, PDE.deriv_secondPartialDeriv_timeSlice_comm") (uses := "foundations.coordinates.slice_regularity, foundations.derivatives.mixed_commutation")
For a globally $`C^2` field
$`F:\mathbb R^n\times\mathbb R\to E`, one spatial derivative commutes with
the derivative of a fixed-space time trace:

$$`
  \frac d{dt}\,\partial_i^xF(x,t)
  =\partial_i^x\frac d{dt}F(x,t).
`

For a globally $`C^3` field, the same is true after two spatial derivatives:

$$`
  \frac d{dt}\,\partial_i^x\partial_j^xF(x,t)
  =\partial_i^x\partial_j^x\frac d{dt}F(x,t).
`

The codomain $`E` is any real normed space. After slice derivatives are rewritten as
joint derivatives, the $`C^2` and $`C^3` hypotheses provide the symmetric
second differentials of the field and of its spatial derivatives that move time past one or
two spatial directions.
:::

:::proof "foundations.coordinates.mixed_time_space"
Represent the left side using the constant spatial direction $`(e_i,0)` and
the time direction $`(0,1)`. Both directions are constant, so differentiating
again gives the second differential on the pair, and its symmetry exchanges
their order, proving the $`C^2` identity. For two spatial derivatives, first
view the inner spatial derivative as a new $`C^2` field; one derivative has
already been spent from the original $`C^3` hypothesis. Apply the first
commutation theorem and then commute time past the remaining spatial
direction.
:::

The last spacetime statement is topological rather than differential: a
continuous field is bounded on every compact cylinder
$`[a,b]\times\overline B(c,r)`. Bounds of this kind feed the integrability and
dominated-convergence arguments of the evolution chapters.

:::theorem "foundations.coordinates.compact_cylinder_bound" (parent := "foundations.coordinates") (lean := "PDE.Common.exists_norm_le_on_timeSpaceCylinder") (uses := "foundations.coordinates.product_split")
Let $`f:\mathbb R^{n+1}\to E` be continuous, where $`E` is a normed additive
group. For every closed time interval $`[a,b]` and closed spatial ball
$`\overline B(c,r)`, there is a nonnegative $`C` such that

$$`
  \lVert f(t,x)\rVert\le C
  \qquad
  (t\in[a,b],\ x\in\overline B(c,r)).
`

No assumption that $`a\le b` or $`r\ge0` is needed. If either set is empty,
the conclusion is vacuous; otherwise it is the ordinary compact-cylinder
bound.
:::

:::proof "foundations.coordinates.compact_cylinder_bound"
Compose $`f` with the jointly smooth assembly map
$`(t,x)\mapsto(t,x)`. The product of a closed interval and a closed ball in
finite-dimensional Euclidean space is compact. A continuous norm-valued
function is bounded on that compact set. Replacing the resulting bound by
its maximum with zero gives the stated nonnegative constant.
:::

# Radial and planar differential coordinates

:::definition "foundations.coordinates.radial_laplacian" (parent := "foundations.coordinates") (lean := "PDE.CoordinateSystems.radialLaplacian") (uses := "foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In dimension $`n`, the radial expression is
$`f''(r) + (n-1)f'(r)/r`. It specializes to the familiar polar and spherical formulas in
dimensions two and three. Real division is total in Lean, so the definition itself also has a
value at zero; analytic theorems interpreting it as a coordinate Laplacian assume that the
radius is positive or nonzero.

By the {bpref "foundations.operators.laplacian_radial"}[radial Laplacian theorem],
this expression is the Cartesian Laplacian of $`x\mapsto f(\lVert x\rVert)` at
$`x\ne0`, provided the profile is twice continuously differentiable at that radius.
:::

The two profiles that matter for fundamental solutions are the logarithm in
dimension two and powers of the radius in higher dimensions. For the logarithm
the two terms of the two-dimensional radial Laplacian cancel exactly.

:::theorem "foundations.coordinates.polar_log" (parent := "foundations.coordinates") (lean := "PDE.CoordinateSystems.radialLaplacian_log") (uses := "foundations.coordinates.radial_laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-22"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On the positive radial branch,

$$`
  \left(\frac{d^2}{dr^2}+\frac1r\frac d{dr}\right)\log r=0
  \qquad(r>0).
`

This one-variable identity underlies the two-dimensional logarithmic
fundamental solution away from its singularity.
:::

:::proof "foundations.coordinates.polar_log"
Differentiate on the positive half-line: $`(\log r)'=1/r` and
$`(\log r)''=-1/r^2`. Substitution into the two-dimensional radial
Laplacian gives $`-1/r^2+(1/r)(1/r)=0`.
:::

For a power profile the radial Laplacian is again a power, with a coefficient
quadratic in the exponent. Its zeros $`p=0` and $`p=2-n` identify the constant
and the inverse-power harmonic profiles.

:::theorem "foundations.coordinates.radial_power" (parent := "foundations.coordinates") (lean := "PDE.CoordinateSystems.radialLaplacian_rpow") (uses := "foundations.coordinates.radial_laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At every positive radius, the dimension-$`n` radial Laplacian sends the power profile $`r^p` to
$`p(p+n-2)r^{p-2}`. For $`n>2`, the choice $`p=2-n` gives the harmonic
inverse-power profile. In dimension two this choice gives only the constant
profile; the nonconstant logarithmic profile is covered by the preceding theorem.
:::

:::proof "foundations.coordinates.radial_power"
On $`r>0`, the first two derivatives of $`r^p` are
$`pr^{p-1}` and $`p(p-1)r^{p-2}`. Adding the radial correction
$`(n-1)r^{-1}pr^{p-1}` and collecting coefficients yields
$`p(p+n-2)r^{p-2}`.
:::

# Compactified radial modes

A decaying radial profile can be written in a bounded angular variable as
$`u(\beta)=\cos\beta\,f(\beta)`. Factoring out the cosine turns the
weighted derivative into a simple operator on $`f`.

:::theorem "foundations.coordinates.compactified_radial_modes" (parent := "foundations.coordinates") (lean := "PDE.CoordinateSystems.compactifiedRadialCompletion, PDE.CoordinateSystems.cos_mul_compactifiedRadialCompletion, PDE.CoordinateSystems.compactifiedRadialCompletion_sum, PDE.CoordinateSystems.compactifiedRadialCompletion_const_mul, PDE.CoordinateSystems.compactifiedRadialCompletion_sin, PDE.CoordinateSystems.compactifiedRadialCompletion_cos, PDE.CoordinateSystems.compactifiedRadialCompletion_sum_sin, PDE.CoordinateSystems.compactifiedRadialCompletion_sum_cos")
Define

$$`
\mathcal Df=(1+\cos^2\beta)f
  +\sin\beta\cos\beta\,f'.
`

At each point where $`f` is differentiable,

$$`
\begin{aligned}
\cos\beta\,\mathcal Df
  & = \sin\beta\cos\beta\,u' + 2u,\\
u&=\cos\beta\,f.
\end{aligned}
`

For either $`m_k(\beta)=\sin(k\beta)` or $`m_k(\beta)=\cos(k\beta)`,
with any real frequency $`k`,

$$`
\begin{aligned}
\mathcal Dm_k
  &=\frac32m_k+\frac{k+1}{4}m_{k+2}\\
  &\quad+\frac{1-k}{4}m_{k-2}.
\end{aligned}
`

The identity extends termwise to any finite expansion with real coefficients
and frequencies. It gives an exact transformation of the radial coefficients;
the finite index set, its coefficients, and its frequencies are arbitrary. A spherical
divergence-free reconstruction also needs the angular basis and the physical
coordinate change, which are separate from this one-variable identity.
:::

:::proof "foundations.coordinates.compactified_radial_modes"
Differentiate $`\cos\beta\,f` by the product rule and use
$`\sin^2\beta+\cos^2\beta=1` to obtain the weighted-derivative identity.
CAS checks the derivatives of the sine and cosine modes. Double-angle and
addition formulas then give the two neighboring frequencies. Finite-sum
differentiation and linearity yield the expansion formula.
:::

# Homogeneous planar profiles

In two dimensions the angular variable can be kept explicit by adding the
angular term $`r^{-2}\partial_\beta^2` to the radial operator.

:::theorem "foundations.coordinates.planar_polar_homogeneous" (parent := "foundations.coordinates") (lean := "PDE.CoordinateSystems.radialLaplacian_mul, PDE.CoordinateSystems.planarPolarPoint, PDE.CoordinateSystems.planarPolarMap, PDE.CoordinateSystems.planarPolarLaplacian, PDE.CoordinateSystems.planarPolarLaplacian_radial_mul, PDE.CoordinateSystems.planarPolarLaplacian_rpow_mul, PDE.CoordinateSystems.planarPolarLaplacian_cutoff_rpow_mul, PDE.CoordinateSystems.neg_planarPolarLaplacian_rpow_add_two_mul, PDE.CoordinateSystems.neg_planarPolarLaplacian_rpow_add_two_mul_eq, PDE.CoordinateSystems.neg_planarPolarLaplacian_cutoff_rpow_mul_eq, EuclideanLaplacian.planarPolarLaplacianParam, EuclideanLaplacian.planarPolarLaplacianParam_comp_planarPolarMap, EuclideanLaplacian.planarPolarLaplacianParam_uncurry, EuclideanLaplacian.laplacian_eq_planarPolarLaplacian_of_pullback") (uses := "foundations.coordinates.radial_power, foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a two-variable profile $`u(r,\beta)`, define the polar differential
expression

$$`
\Delta_{\mathrm{pol}}u
  =\partial_r^2u+\frac1r\partial_ru+\frac1{r^2}\partial_\beta^2u.
`

At every $`r>0`, a homogeneous angular mode satisfies

$$`
-\Delta_{\mathrm{pol}}\bigl(r^{2+\alpha}f(\beta)\bigr)
=r^\alpha\left(-f''(\beta)-(2+\alpha)^2f(\beta)\right).
`

Consequently, the angular equation
$`(-\partial_\beta^2-(2+\alpha)^2)f=g` produces the polar source
$`r^\alpha g(\beta)`. More generally, if
$`(-\partial_\beta^2-m^2)f=g` and $`\chi` is a radial $`C^2` cutoff,
Lean proves the product rule with every cutoff error explicit:

$$`
-\Delta_{\mathrm{pol}}(\chi r^m f)
=\chi r^{m-2}g-r^m f\,\Delta_{\mathrm{rad}}\chi
  -2m r^{m-1}\chi'f.
`

For a Cartesian $`C^2` field $`U`, Lean additionally proves, at every
$`r\ne0`,

$$`
\Delta U\bigl(r\cos\beta,r\sin\beta\bigr)
=\Delta_{\mathrm{pol}}(U\circ\Phi)(r,\beta),
\qquad \Phi(r,\beta)=(r\cos\beta,r\sin\beta).
`

The parameter-plane operator is proved equal to the curried operator
$`\Delta_{\mathrm{pol}}`, and a germ-local theorem permits replacing
$`U\circ\Phi` by a locally equal polar profile. Thus the homogeneous and cutoff calculations become Euclidean
Laplacian identities once their $`C^2` pullback hypotheses hold.
:::

:::proof "foundations.coordinates.planar_polar_homogeneous"
The radial-power formula with dimension two gives
$`(\partial_r^2+r^{-1}\partial_r)r^m=m^2r^{m-2}`. The angular derivative
contributes $`r^{m-2}f''(\beta)`. Set $`m=2+\alpha`, negate, and collect the
common factor $`r^\alpha`. The radial product rule then expands
$`\Delta_{\mathrm{pol}}(\chi r^m f)` and isolates the two terms containing
$`\chi'` or $`\chi''`. For the coordinate bridge, apply the second-order
chain rule to $`U\circ\Phi`; the first-order terms cancel, the mixed Hessian
terms cancel, and $`\sin^2\beta+\cos^2\beta=1` leaves the Cartesian trace.
:::

# Integration in polar coordinates

:::theorem "foundations.coordinates.euclidean_sum_volume" (parent := "foundations.coordinates") (lean := "PDE.Analysis.euclideanSumMeasurableEquiv_measurePreserving") (uses := "foundations.euclidean_space.type")
Orthogonally splitting $`\mathbb R^{m+n}` into its first $`m` and last $`n`
coordinates preserves the canonically normalized Euclidean volume measure.
This is a measure-theoretic coordinate change, so Fubini's theorem applies
to it.
:::

:::proof "foundations.coordinates.euclidean_sum_volume"
First split the coordinates into the two blocks equipped with the
$`\ell^2` product norm, represented in Lean by `WithLp 2`. This is a linear
isometry and preserves canonically normalized Euclidean volume. Forgetting
the `WithLp` structure also preserves product volume, by a separate
measure-preservation theorem. The composite therefore gives the required
product measure, although the ordinary product carries the maximum norm
and the composite need not be an isometry.
:::

Polar coordinates are handled in the same way, as a measure-preserving
equivalence rather than a Jacobian computation.

:::theorem "foundations.coordinates.polar_integral" (parent := "foundations.coordinates") (lean := "PDE.Analysis.integral_polar_addHaar") (uses := "foundations.euclidean_space.type")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "712-713"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a positive-dimensional real normed space of finite dimension carrying an
additive Haar measure, a whole-space Bochner integral equals its
angular-times-radial pullback. The
radial measure already contains the Jacobian $`r^{n-1}`, and the origin is
discarded as a null set before the measure-preserving equivalence is applied.
:::

:::proof "foundations.coordinates.polar_integral"
Remove the origin, which has Haar measure zero, and integrate over its
complement. The polar homeomorphism identifies that complement with the unit
sphere times the positive radii and is measure preserving for the sphere
measure times `volumeIoiPow`. Pulling the integrand across this equivalence
gives the formula; the radial measure already contains the Jacobian.
:::

Only the iterated form needs integrability, which Fubini's theorem requires;
the measure-preserving formula holds without it.

:::theorem "foundations.coordinates.polar_integral_iterated" (parent := "foundations.coordinates") (lean := "PDE.Analysis.integral_polar_addHaar_iterated") (uses := "foundations.coordinates.polar_integral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "712-713"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On the same positive-dimensional space, for every integrable Banach-valued
function, Fubini exposes the familiar iterated formula

$$`
\int_E g(x)\,d\mu(x)
=\int_0^\infty r^{\dim E-1}
  \left(\int_{S(E)} g(r\omega)\,d\mu_S(\omega)\right)dr.
`

Here $`\mu_S` is the canonical sphere measure induced by the chosen additive
Haar measure $`\mu`.
:::

:::proof "foundations.coordinates.polar_integral_iterated"
Start from the measure-preserving polar-coordinate formula. Fubini's theorem
then separates the product integral into an angular integral followed by a
radial integral. Expanding the radial measure contributes the density
$`r^{\dim E-1}` and gives the displayed iterated expression.
:::
