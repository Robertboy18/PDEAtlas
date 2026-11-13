/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Foundations.DifferentialOperators
import Blueprint.Commands.Figures
import PDE.Elliptic.Classical.Harmonic.Definitions
import PDE.Elliptic.Classical.Laplace.Equation
import PDE.Elliptic.Classical.Poisson.Equation
import PDE.Elliptic.PotentialTheory.FundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.FluxNormalization
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# The Laplace fundamental solution

The Laplace and Poisson equation records, the Euclidean geometric
normalizations, the canonical Laplace fundamental solution, its
local integrability and smoothness away from the pole, and its normalized
radial flux.
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
#doc (Manual) "The Laplace Fundamental Solution" =>

# Fundamental solution and flux normalization

:::group "elliptic.representation"
Fundamental solutions and mean values
:::

Evans opens Section 2.2 with Laplace's equation $`\Delta u=0` and Poisson's
equation $`-\Delta u=f`. We state both as second-order linear PDE
records on all of $`\mathbb R^n`. The records use the totalized
{bpref "foundations.operators.laplacian"}[coordinate Laplacian], which agrees
with the canonical Laplacian on $`C^2` fields. The kernel, the mean values, and
the derivative estimates below are all stated for this one Laplacian.

:::definition "elliptic.laplace_equation" (parent := "elliptic.representation") (lean := "PDE.laplaceEquation") (uses := "foundations.pde_problems.linear_class, foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every dimension $`n`, the Laplace equation is the order-two linear PDE
record with operator $`u\mapsto\Delta u`, right-hand side $`0`, and domain
$`\mathbb R^n`, representing

$$`
\Delta u=\sum_{i=1}^n\partial_i^2u=0\qquad\text{on }\mathbb R^n.
`

Additivity is the sum rule for the iterated coordinate derivatives of two
fields that are $`C^2` at the point, homogeneity is the scalar rule and needs
no regularity, and the second-order locality law demanded by the record is
proved for $`C^2` fields by identifying the coordinate Laplacian with the
second Fréchet derivative evaluated on the coordinate vectors.
For $`n=0` the coordinate sum is empty and the operator vanishes
identically, so analytic applications assume $`0<n`.
:::

The Poisson record differs from the Laplace record in the sign of its operator
and in carrying a source term. With $`f=0` the two residuals differ only by a
sign, so the Laplace equation is the homogeneous Poisson equation up to the
textbook normalization.

:::definition "elliptic.poisson_equation" (parent := "elliptic.representation") (lean := "PoissonEquation.poissonEquation") (uses := "foundations.pde_problems.linear_class, foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a source term $`f:\mathbb R^n\to\mathbb R`, the Poisson equation is the
order-two linear PDE record with operator $`u\mapsto-\Delta u`, right-hand
side $`f`, and domain $`\mathbb R^n`, representing

$$`
-\Delta u=f\qquad\text{on }\mathbb R^n.
`

The minus sign is the textbook convention; it matches the normalization
$`-\Delta\Phi_n=\delta_0` of the fundamental solution below. The record is
built from the same coordinate Laplacian and the same locality proof as the
Laplace record.
:::

Solving either record means making its residual vanish. The characterization
below unfolds the
residuals to pointwise expressions, so that vanishing of the Poisson residual on
the domain is literally the equation $`-\Delta u=f`.

:::theorem "elliptic.poisson_equation.residual" (parent := "elliptic.representation") (lean := "PoissonEquation.poissonEquation_residual_eq_zero_iff, PoissonEquation.poissonEquation_residual, PoissonEquation.poissonEquation_residual_zero_iff, PDE.laplaceEquation_residual") (uses := "elliptic.poisson_equation, elliptic.laplace_equation")
For every field $`u:\mathbb R^n\to\mathbb R` and every point $`x`, the
residuals unfold to the pointwise coordinate expressions

$$`
\mathcal R_{\mathrm{Poisson}}(u)(x)=-\Delta u(x)-f(x),
\qquad
\mathcal R_{\mathrm{Laplace}}(u)(x)=\Delta u(x).
`

Hence the Poisson residual vanishes at $`x` exactly when
$`-\Delta u(x)=f(x)`, and it vanishes at every point of the domain exactly
when $`-\Delta u=f` holds on all of $`\mathbb R^n`.
:::

:::proof "elliptic.poisson_equation.residual"
The residual of a linear PDE record is the operator value minus the
right-hand side, so both identities are the definitions of the records
unfolded at $`x`. A difference vanishes exactly when its two terms agree,
which gives the pointwise characterization. The domain of the Poisson record
is all of $`\mathbb R^n`, so quantifying over domain points is quantifying
over every $`x`, which gives the global form.
:::

A vanishing residual carries no regularity, since the totalized Laplacian is
defined for every field, so the residual characterization alone does not single
out classical solutions. The harmonicity predicate adds the missing $`C^2`
hypothesis; it is the notion over which the mean-value theorems, maximum
principles, and derivative estimates below quantify.

:::definition "elliptic.harmonicity" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE") (uses := "foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-22"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A scalar function is harmonic on $`U\subseteq\mathbb R^n` when it is $`C^2`
on $`U` and its Euclidean Laplacian vanishes at every point of $`U`.
:::

Every explicit constant in this section, from the coefficient of $`\Phi_n` to
the normalizations of the sphere and ball averages and of the Poisson kernels,
is expressed through the volume $`\alpha(n)` of the unit ball. The constant is
fixed by a closed formula, and the identities following it relate that formula
to Lebesgue measure and to the area of the unit sphere.

:::definition "elliptic.geometry.unit_ball_volume" (parent := "elliptic.representation") (lean := "PDE.Analysis.unitBallVolume")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The constant $`\alpha(n)` is the Euclidean volume of the unit ball in
$`\mathbb R^n`. The Lean definition is the exact real expression
$`(\sqrt{\pi})^n/\Gamma(n/2+1)`, which is the usual
$`\pi^{n/2}/\Gamma(n/2+1)` formula.
:::

Since $`\alpha(n)` occurs in denominators throughout, positivity is the first
property required of it.

:::theorem "elliptic.geometry.unit_ball_volume_positive" (parent := "elliptic.representation") (lean := "PDE.Analysis.unitBallVolume_pos") (uses := "elliptic.geometry.unit_ball_volume")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every natural-number dimension $`n`, $`\alpha(n)>0`.
:::

:::proof "elliptic.geometry.unit_ball_volume_positive"
Both $`(\sqrt{\pi})^n` and $`\Gamma(n/2+1)` are strictly positive. Their quotient is therefore
positive, which proves positivity of the explicit volume normalization.
:::

Positivity concerns the closed-form expression alone. The scaling identity is
what ties that expression to geometry: it identifies $`\alpha(n)` with Mathlib's
Lebesgue measure of the unit ball and, by dilation, gives the volume of every
ball $`B(0,r)`.

:::theorem "elliptic.geometry.ball_volume_scaling" (parent := "elliptic.representation") (lean := "PDE.Analysis.ballVolume_eq_unitBallVolume_mul_pow") (uses := "elliptic.geometry.unit_ball_volume_positive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for $`r\ge0`, the Lebesgue volume of $`B(0,r)` is
$`\alpha(n)r^n`.
:::

:::proof "elliptic.geometry.ball_volume_scaling"
For $`r>0`, dilation by $`r` carries the unit ball to $`B(0,r)` and
scales Lebesgue measure by $`r^n`. At $`r=0`, both sides vanish because
$`n>0`. The formal proof specializes Mathlib's Euclidean-ball volume formula
and converts the measure to a real number.
:::

Differentiating $`\alpha(n)r^n` in the radius suggests that the sphere of radius
$`r` has area $`n\alpha(n)r^{n-1}`. Our proof of the unit-sphere identity
does not differentiate: Mathlib's sphere measure has total mass
$`n` times the volume of the unit ball, and the volume identity at radius one
converts this to $`n\alpha(n)`.

:::theorem "elliptic.geometry.unit_sphere_area" (parent := "elliptic.representation") (lean := "PDE.Analysis.unitSphereArea_eq") (uses := "elliptic.geometry.ball_volume_scaling")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Mathlib-induced area of the Euclidean unit sphere is $`n\alpha(n)`. This
identity connects radial derivatives to the surface normalization used in
Evans's punctured-ball calculations.
:::

:::proof "elliptic.geometry.unit_sphere_area"
Mathlib's sphere-area identity identifies the total
mass of the induced sphere measure with $`n` times the real volume of the unit ball. The
ball-volume theorem at radius one identifies that real volume with
$`\alpha(n)`, yielding $`|S^{n-1}|=n\alpha(n)`.
:::

{leanpde_figure "fundamental-solution"}

With $`\alpha(n)` and $`|S^{n-1}|=n\alpha(n)` available, the coefficient of the
Newtonian kernel can be chosen so that its outward radial flux through every
sphere about the pole is exactly $`-1`. That normalization is what qualifies the
kernel below as the candidate for $`-\Delta\Phi_n=\delta_0`.

The figure reports the flux of the negative gradient, so its positive unit
flux uses the same normalization with the sign moved into the field.
The two plots show different singular profiles with the same flux
normalization. Shrinking the sphere does not remove the source: the growing
radial derivative compensates for the shrinking surface area. The
{bpref "symbolic.fundamental_solution_examples"}[symbolic radial examples]
identify these logarithmic and inverse-distance formulas with the analytic
kernels and verify harmonicity away from the pole. Local integrability and
the flux calculation are what let the distributional argument account for
the pole itself.

:::definition "elliptic.fundamental_solution" (parent := "elliptic.representation") (lean := "PotentialTheory.fundamentalSolution") (uses := "elliptic.geometry.unit_ball_volume")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
With $`\alpha(n)=|B(0,1)\subset\mathbb R^n|`, the total kernel is

$$`
\Phi_n(x)=
\begin{cases}
-\frac12|x|, & n=1,\\
-\frac{1}{2\pi}\log |x|, & n=2,\\
\frac{1}{(n-2)n\alpha(n)|x|^{n-2}}, & n\ge3,
\end{cases}
`

The coefficients give outward radial flux $`-1`, the normalization required
for $`-\Delta\Phi_n=\delta_0`. The Lean function sets $`\Phi_n(0)=0`;
a single point is irrelevant for almost-everywhere and distributional
statements.
:::

The kernel is singular at the origin, so before it can act on test functions it
must be shown locally integrable. This is the property that lets $`\Phi_n`
define a regular distribution, the object in which the point-source identity is
stated in every positive dimension.

:::theorem "elliptic.fundamental_solution.local_integrability" (parent := "elliptic.representation") (lean := "PotentialTheory.locallyIntegrable_fundamentalSolution") (uses := "elliptic.fundamental_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`n\ge1`,

$$`\Phi_n\in L^1_{\mathrm{loc}}(\mathbb R^n).`
:::

:::proof "elliptic.fundamental_solution.local_integrability"
The proof treats neighborhoods away from the origin by continuity.  Near the
origin, the logarithmic kernel in dimension two is bounded by a multiple of
$`|x|^{-1}`, while in higher dimensions the kernel is a multiple of
$`|x|^{-(n-2)}`. Mathlib's radial-power estimates apply because $`1<2` and
$`n-2<n`, respectively.
:::

Away from the pole the singularity is absent and $`\Phi_n` is a smooth function
of the norm. Smoothness there is what makes the second derivatives in the
harmonicity statement classical.

:::theorem "elliptic.fundamental_solution.smooth_off_pole" (parent := "elliptic.representation") (lean := "PotentialTheory.contDiffAt_fundamentalSolution") (uses := "elliptic.fundamental_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`n\ge1` and $`x\ne0`, the fundamental solution is smooth at
$`x`:

$$`\Phi_n\in C^\infty(\mathbb R^n\setminus\{0\}).`
:::

:::proof "elliptic.fundamental_solution.smooth_off_pole"
On a neighborhood avoiding the origin, the norm is smooth and strictly
positive. The one-dimensional profiles $`r\mapsto r`, $`\log r`, and the
relevant real powers are smooth on positive radii. Composing the appropriate
profile with the norm proves smoothness of every dimensional branch.
:::

Harmonicity away from the pole is the regular half of $`-\Delta\Phi_n=\delta_0`;
the singular half is carried entirely by the flux through spheres about the
pole.

:::theorem "elliptic.fundamental_solution.harmonic_off_pole" (parent := "elliptic.representation") (lean := "PotentialTheory.laplacian_fundamentalSolution_eq_zero") (uses := "elliptic.fundamental_solution.smooth_off_pole")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-22"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`n\ge1` and every $`x\in\mathbb R^n\setminus\{0\}`,

$$`\Delta\Phi_n(x)=0.`
:::

:::proof "elliptic.fundamental_solution.harmonic_off_pole" (uses := "elliptic.fundamental_solution.smooth_off_pole")
The two-dimensional logarithmic branch and the power-law branches are reduced
to the radial Laplacian formula.  Smoothness away from the pole justifies the
second derivatives, and the radial first- and second-derivative terms cancel
with the dimension coefficient.
:::

Harmonicity off the pole does not distinguish $`\Phi_n` from the zero function;
the distinction is the total flux through a sphere about the pole. Because
$`\Phi_n` is radial, that flux is the radial derivative times the surface area,
and the radial derivative comes first. The restriction to $`n\ge2` reflects the
sphere-measure formulation; the one-dimensional kernel is treated separately.

:::theorem "elliptic.fundamental_solution.radial_derivative" (parent := "elliptic.representation") (lean := "PotentialTheory.deriv_fundamentalSolution_smul") (uses := "elliptic.fundamental_solution, elliptic.geometry.unit_sphere_area")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In dimension $`n\ge2`, along every unit ray and at every radius $`r>0`,

$$`\frac{d}{d\rho}\Phi_n(\rho\omega)\big|_{\rho=r}
=-\frac{1}{r^{n-1}|S^{n-1}|}.`

The right-hand side is independent of the chosen unit direction.
:::

:::proof "elliptic.fundamental_solution.radial_derivative"
Substitute $`\lVert\rho\omega\rVert=\rho` for a unit vector and differentiate
the logarithmic branch when $`n=2` and the Newtonian power branch when
$`n\geq3`. In both cases the coefficient simplifies using
$`|S^{n-1}|=n\alpha(n)`, giving
$`-1/(r^{n-1}|S^{n-1}|)`.
:::

Multiplying the constant radial derivative by the area $`r^{n-1}|S^{n-1}|`
of the radius-$`r` sphere gives the total outward flux.

:::theorem "elliptic.fundamental_solution.surface_flux" (parent := "elliptic.representation") (lean := "PotentialTheory.deriv_fundamentalSolution_smul_mul_surfaceArea") (uses := "elliptic.fundamental_solution.radial_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`n\ge2`, $`r>0`, and every unit vector $`\omega`, the radial derivative
$`\frac{d}{d\rho}\Phi_n(\rho\omega)\big|_{\rho=r}` times the area of the
radius-$`r` sphere equals $`-1`. This is the pointwise normalization from which
the integrated flux identity follows.
:::

:::proof "elliptic.fundamental_solution.surface_flux"
The sphere of radius $`r` has area
$`r^{n-1}|S^{n-1}|`. Multiplying this by the radial derivative
$`-1/(r^{n-1}|S^{n-1}|)` cancels both positive factors and leaves $`-1`.
:::

Integrating the constant radial derivative over the unit sphere and transporting
the result to radius $`r` gives the integrated version of the same cancellation.
The value $`-1` is the boundary coefficient in Evans's punctured-ball
integration by parts and the reason the point mass in $`-\Delta\Phi_n=\delta_0`
has unit strength. The distributional identity is proved separately: by direct
arguments in dimensions one and two, and by spherical means and radial
integration in higher dimensions.

:::theorem "elliptic.fundamental_solution.flux_normalization" (parent := "elliptic.representation") (lean := "PotentialTheory.integral_deriv_fundamentalSolution_smul") (uses := "elliptic.fundamental_solution.surface_flux, elliptic.geometry.unit_sphere_area")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "22-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every dimension $`n\geq2`, the total outward radial flux of $`\Phi_n` through
every sphere centered at the pole is $`-1`. More precisely, for $`r>0`,

$$`r^{n-1}\int_{S^{n-1}}
  \frac{d}{d\rho}\Phi_n(\rho\omega)\big|_{\rho=r}\,dS(\omega)=-1.`

Here $`dS` is Mathlib's measure on the unit sphere; the factor $`r^{n-1}`
transports it to the sphere of radius $`r`.
:::

:::proof "elliptic.fundamental_solution.flux_normalization"
On a unit ray, the logarithmic branch in dimension two and the Newtonian
power-law branch in dimensions at least three are differentiated separately.
The resulting radial derivative is
$`-1/(r^{n-1}|S^{n-1}|)`. The identity
$`|S^{n-1}|=n\alpha_n` and integration of this constant over the unit sphere
give the asserted flux.
:::
