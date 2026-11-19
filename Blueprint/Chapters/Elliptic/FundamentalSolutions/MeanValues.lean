/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.FundamentalSolutions.Kernel
import Blueprint.Commands.Figures
import PDE.Elliptic.Classical.MeanValue.Formulas
import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue
import PDE.Elliptic.Classical.MeanValue.MeanValueToPDE

/-!
# Mean-value formulas for harmonic functions

Sphere and ball integrals, the coarea formula on balls,
and the implication from harmonicity to the spherical and ball mean-value
properties.
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
#doc (Manual) "Mean-Value Formulas" =>

# Sphere and ball mean values

A harmonic function equals the average of its values over every sphere, and over
every ball, centered at a point of the domain and contained in it. Stating this
requires the sphere and ball integrals themselves, whose normalizations are
fixed in terms of $`\alpha(n)` and $`|S^{n-1}|=n\alpha(n)`.

:::definition "elliptic.mean_value.integrals" (parent := "elliptic.representation") (lean := "PDE.Analysis.sphereIntegral, PDE.Analysis.ballIntegral, PDE.Analysis.sphereAverage, PDE.Analysis.ballAverage") (uses := "elliptic.geometry.ball_volume_scaling, elliptic.geometry.unit_sphere_area")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "25-26"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "712-713"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
Sphere integrals are defined by pulling the Euclidean surface measure on the
unit sphere through $`\omega\mapsto x+r\omega` and including the Jacobian
$`|r|^{n-1}`. Ball integrals are ordinary restricted Lebesgue integrals.
Division by the corresponding surface area or volume gives the normalized
averages at positive radius; at radius zero both averages are totalized to
$`u(x)`. The mean-value theorems therefore assume a positive radius.
:::

{leanpde_figure "mean-value"}

The picture returns to the cubic harmonic polynomial checked by CAS in the
Elliptic introduction. There, cancellation of second derivatives gave a
pointwise equation. The
{bpref "elliptic.mean_value.from_harmonicity"}[mean-value theorem] turns that
equation, together with smoothness, into an identity on every contained
circle. The plotted averages illustrate one instance; the theorem explains
why changing the center or radius preserves the identity.

The spherical mean-value property states the sphere identity as a predicate on
functions, with no differentiability attached. Keeping it separate from
harmonicity is what allows the two implications between them to be stated and
proved independently, and it lets the
{bpref "elliptic.mean_value.boundary_principle"}[mean-value boundary principle]
apply to functions that are only continuous.

:::definition "elliptic.mean_value.sphere_property" (parent := "elliptic.representation") (lean := "LaplacianEquation.HasSphereMeanValueProperty") (uses := "elliptic.mean_value.integrals")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The spherical mean-value property on $`U` requires

$$`u(x)=\frac{1}{|\partial B(x,r)|}
  \int_{\partial B(x,r)}u\,dS`

for every $`x\in U`, every $`r>0`, and every closed ball
$`\overline{B(x,r)}\subseteq U`. The closed-ball containment is essential:
the spherical integral evaluates the function on the boundary itself.
:::

Passing from sphere averages to ball averages means integrating sphere integrals
over the radius. The coarea formula on balls is the exact identity that permits
this.

:::theorem "elliptic.geometry.coarea_balls" (parent := "elliptic.representation") (lean := "PDE.Analysis.coarea_formula_ball, PDE.Analysis.coarea_formula_annulus") (uses := "elliptic.mean_value.integrals")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "712-713"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`u` is integrable on $`B(x,r)` and $`r\ge 0`,
then

$$`\int_{B(x,r)}u(y)\,dy
  =\int_0^r\left(\int_{\partial B(x,\rho)}u\,dS\right)d\rho.`

Subtracting two ball formulas gives the corresponding identity on a
concentric annulus, with radial integrability stated explicitly. These are
the radial specialization of Evans's polar-coordinate/coarea theorem.
:::

:::proof "elliptic.geometry.coarea_balls"
Translate the center to zero, apply Mathlib's polar integration formula with
the radial Jacobian measure, identify the inner integral with the defined
sphere integral, and translate back. The annulus formula follows by subtracting
the nested ball integrals and splitting the radial interval.
:::

Harmonicity enters through the ball Dirichlet problem. A function harmonic on a
set containing a closed ball is the Poisson extension of its own boundary trace,
and at the center of the ball the Poisson kernel is the constant
$`1/|\partial B(x,r)|`, so evaluating the Poisson integral at the center gives
exactly the spherical average. The uniqueness theorem that justifies the
identification follows from the weak maximum
principle.

:::theorem "elliptic.mean_value.from_harmonicity" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.hasSphereMeanValueProperty") (uses := "elliptic.harmonicity, elliptic.mean_value.sphere_property")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`u\in C^2(U)` and $`\Delta u=0` on $`U`, then
every closed ball $`\overline{B(x,r)}\subseteq U` with $`r>0` satisfies

$$`u(x)=\frac{1}{|\partial B(x,r)|}
  \int_{\partial B(x,r)}u(y)\,dS(y).`
:::

:::proof "elliptic.mean_value.from_harmonicity" (uses := "elliptic.poisson.ball.uniqueness")
For an admissible ball, translate its center to the origin, extend the
continuous boundary trace, solve the ball Dirichlet problem by the Poisson
kernel, and use the maximum-principle uniqueness theorem to identify the
original function with the Poisson solution.  Evaluation at the center gives
the spherical average.
:::

The converse implication needs a maximum principle that assumes only the
mean-value property, since a function with the mean-value property is not
assumed differentiable. The boundary principle supplies it, with mean-value
rigidity replacing the second-derivative test used for harmonic functions.

:::theorem "elliptic.mean_value.boundary_principle" (parent := "elliptic.representation") (lean := "LaplacianEquation.HasSphereMeanValueProperty.le_of_boundary_le, LaplacianEquation.HasSphereMeanValueProperty.ge_of_boundary_ge") (uses := "elliptic.mean_value.sphere_property")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "26-28"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`u` be continuous on $`\overline{B(c,r)}` and
have the spherical mean-value property in $`B(c,r)`, where $`r>0`. An upper
or lower bound for $`u` on the boundary sphere holds throughout the closed
ball.
:::

:::proof "elliptic.mean_value.boundary_principle"
Compactness gives a maximizer on the closed ball.  If it lies on the boundary,
the conclusion is immediate.  If it lies in the interior, mean-value rigidity
makes the function constant on the ball and continuity extends that equality
to the boundary.  The minimum statement follows by applying the maximum
statement to $`-u`.
:::

:::theorem "elliptic.mean_value.to_harmonicity" (parent := "elliptic.representation") (lean := "LaplacianEquation.HasSphereMeanValueProperty.isHarmonicPDE") (uses := "elliptic.harmonicity, elliptic.mean_value.sphere_property, elliptic.mean_value.boundary_principle, elliptic.poisson.ball.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-27"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Conversely, in positive dimension, let $`U\subseteq\mathbb R^n` be open.
If $`u` is continuous on $`U` and has the spherical mean-value property on
every closed ball contained in $`U`, then $`u` is $`C^2` on $`U` and
satisfies $`\Delta u=0` there. Together with the
{bpref "elliptic.mean_value.from_harmonicity"}[forward implication], this
characterizes classical harmonic functions by their spherical averages.
:::

:::proof "elliptic.mean_value.to_harmonicity" (uses := "elliptic.poisson.ball.solution, elliptic.mean_value.boundary_principle")
Openness of $`U` gives a small closed ball around each point. Continuously
extend the boundary trace and form its Poisson solution. The difference from
$`u` has the mean-value property and zero boundary values, so the mean-value
boundary principle makes it vanish throughout the ball. Local equality with
the smooth Poisson
solution supplies both $`C^2` regularity and the vanishing Laplacian.
:::

Evans proves the mean-value formula by differentiating the sphere average in the
radius and showing, through the divergence theorem, that the derivative is
proportional to the flux of $`Du` through the sphere, which vanishes for
harmonic $`u`. The theorem is the differentiation step of that argument, for
globally $`C^1` fields; the two characterization theorems rest on the Poisson
construction.

:::theorem "elliptic.mean_value.radial_derivative" (parent := "elliptic.representation") (lean := "PDE.Analysis.sphereAverage_eq_unitSphereAverage, LaplacianEquation.hasDerivAt_sphereAverage, LaplacianEquation.deriv_sphereAverage") (uses := "elliptic.mean_value.integrals")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension and at positive radii, the normalized geometric sphere
average equals the average over the fixed unit sphere, because the radial
Jacobian cancels the surface-area scaling. If
$`u:\mathbb R^n\to\mathbb R` is globally $`C^1`, then differentiation under
this fixed finite measure gives

$$`
\frac{d}{dr}\left(
  \frac{1}{|\partial B(x,r)|}\int_{\partial B(x,r)}u\,dS
\right)
=\frac1{|\partial B(0,1)|}
  \int_{\partial B(0,1)}Du(x+r\omega)\,\omega\,dS(\omega).
`

For a function defined only on an open domain, the formula applies after a
$`C^1` extension from a neighborhood of the closed ball.
:::

:::proof "elliptic.mean_value.radial_derivative"
Rewrite the normalized sphere average on radius $`r` as an integral over the
fixed unit sphere; the Jacobian and surface-area factors cancel. Global
$`C^1` regularity permits differentiation under this finite measure, and the
chain rule differentiates $`u(x+r\omega)` to $`Du(x+r\omega)\,\omega`.
:::

Ball averages follow from sphere averages by integrating in the radius. If
$`u(x)` equals the sphere average at every radius $`\rho\le r`, then multiplying
by the area of $`\partial B(x,\rho)` and integrating from $`0` to $`r` gives
$`u(x)|B(x,r)|` on one side and, by the coarea formula, the ball integral on the
other. Integrability of $`u` on the ball is the hypothesis the coarea formula
needs.

:::theorem "elliptic.mean_value.sphere_and_ball" (parent := "elliptic.representation") (lean := "LaplacianEquation.HasSphereMeanValueProperty.eq_ballAverage") (uses := "elliptic.mean_value.sphere_property, elliptic.geometry.coarea_balls")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`u` has the spherical mean-value property,
$`x\in U`, $`r>0`, $`\overline{B(x,r)}\subseteq U`, and $`u` is integrable
on $`B(x,r)`, then

$$`u(x)=\frac{1}{|B(x,r)|}\int_{B(x,r)}u(y)\,dy.`
:::

:::proof "elliptic.mean_value.sphere_and_ball" (uses := "elliptic.geometry.coarea_balls")
The spherical identity is the defining property.  The ball identity follows
by the coarea formula: substitute the spherical identity at every intermediate
radius and integrate the surface areas from $`0` to $`r`.
:::
