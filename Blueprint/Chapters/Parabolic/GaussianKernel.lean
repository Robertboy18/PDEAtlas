/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Parabolic.Equation
import Blueprint.Commands.Figures
import PDE.Parabolic.Heat.Kernel.Basic
import PDE.Parabolic.Heat.Kernel.Equation
import PDE.Parabolic.Heat.Kernel.Integrability
import PDE.Parabolic.Heat.MeanValue
import Verso
import VersoBlueprint
import VersoManual

/-!
# Gaussian heat kernel

The Gaussian kernel and the classical heat-flow results built from it.
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
#doc (Manual) "The Gaussian Heat Kernel" =>

# The Gaussian Kernel

The Gaussian heat kernel is the canonical positive, mass-one solution used to
construct heat flows on Euclidean space. Under the usual regularity and growth
hypotheses, convolution with this kernel produces the corresponding heat
evolution, and uniqueness theorems identify that evolution with the prescribed
solution. Its exponential decay drives positive-time smoothing, while
preservation of unit mass expresses conservation of total heat.

{leanpde_figure "heat-kernel"}

The decreasing peak and increasing width must be read together: the total
mass stays one as the profile spreads. Verifying the differential equation
at positive time is a separate step from proving the mass normalization or
the initial limit. The
{bpref "symbolic.gaussian_heat_symbolic_bridge"}[planar Gaussian CAS example]
handles the first step by the same differentiation and cancellation used for
the polynomial and sine heat solutions. Positive time supplies its denominator
conditions; the kernel estimates supply the integral information.

Convolution with the heat kernel evolves initial data, much as convolution
with a fundamental solution of the Laplacian solves a stationary Poisson problem.
Evans (2010, pp. 44–59) develops the kernel and its convolution consequences
under explicit analytic hypotheses.

## Example: Verifying the Heat Equation

For $`n=1` and $`t>0`, the kernel is

$$`\Gamma_1(x,t)=\frac{1}{\sqrt{4\pi t}}\exp\!\left(-\frac{x^2}{4t}\right).`

To verify $`\partial_t\Gamma_1=\partial_{xx}\Gamma_1` by hand, compute each
side. Write $`\Gamma_1=C t^{-1/2}e^{-x^2/(4t)}` with $`C=(4\pi)^{-1/2}`.
Then

$$`\partial_t\Gamma_1
  =\Gamma_1\!\left(-\frac{1}{2t}+\frac{x^2}{4t^2}\right),`

$$`\partial_x\Gamma_1
  =\Gamma_1\!\left(-\frac{x}{2t}\right),`

$$`\partial_{xx}\Gamma_1
  =\Gamma_1\!\left(\frac{x^2}{4t^2}-\frac{1}{2t}\right).`

The two expressions coincide term by term. Heat scaling determines the
quadratic exponent $`-x^2/(4t)` and the mass-preserving prefactor; their time
and spatial derivatives then cancel in exactly the displayed combination.

Physically, the spreading width $`\sigma(t)=\sqrt{2t}` grows as the square
root of time. This is the diffusive scaling: doubling the observation time
increases the spread by a factor of $`\sqrt2`, not $`2`. Strict positivity
of the Gaussian makes the solution from nonnegative, nonzero continuous data
positive everywhere at every positive time
({bpref "parabolic.infinite_propagation"}[]), while the influence at distance
$`L\gg\sigma(t)` is exponentially small in $`L^2/t`. This gives the
parabolic equation infinite propagation speed with exponentially small
far-field influence.

:::definition "parabolic.heat_kernel" (parent := "parabolic.classical") (lean := "HeatEquation.fundamentalSolutionHeat")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "45-46"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`x \in \mathbb R^n` and $`t>0`, the heat kernel is

$$`\Gamma_n(x,t)=(4\pi t)^{-n/2}\exp\!\left(-\frac{\lVert x\rVert^2}{4t}\right).`

The Lean function is total: it is defined to be zero when $`t \leq 0`.
The differential identities for it assume $`t>0`.
:::

The worked one-dimensional computation is the case $`n=1` of the general
identity. In dimension $`n` the prefactor $`(4\pi t)^{-n/2}` contributes
$`-n/(2t)` to the logarithmic time derivative, and the $`n` diagonal entries
of the Gaussian Hessian each contribute $`-1/(2t)` to the Laplacian, so the
two sides agree in every dimension with no change to the exponent.

:::theorem "parabolic.heat_kernel_equation" (parent := "parabolic.classical") (lean := "HeatEquation.fundamentalSolutionHeat_satisfies_equation") (uses := "parabolic.heat_kernel, parabolic.heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "45-46"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At every positive time, the Gaussian satisfies the homogeneous heat equation
pointwise:

$$`\partial_t\Gamma_n(x,t)-\Delta_x\Gamma_n(x,t)=0.`

The identity holds in every finite spatial dimension $`n`.
:::

:::proof "parabolic.heat_kernel_equation"
Differentiate the Gaussian time factor and exponential factor, compute each
spatial second derivative, and sum the diagonal Hessian entries. Both sides
reduce to
$`(\lVert x\rVert^2/(4t^2)-n/(2t))\Gamma_n(x,t)`.
:::

The differential identity verifies the Gaussian formula but does not fix its
multiplicative constant: every constant multiple also solves the heat equation. The prefactor is chosen so that the spatial integral equals one, and
it is this normalization, not the equation, that the convolution estimates
for the initial-value problem depend on.

:::theorem "parabolic.heat_kernel_mass" (parent := "parabolic.classical") (lean := "HeatEquation.fundamentalSolutionHeat_integral") (uses := "parabolic.heat_kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "46"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`t>0`, the heat kernel has unit spatial mass:

$$`\int_{\mathbb R^n}\Gamma_n(x,t)\,dx=1.`

This is the normalization needed for preservation of constants and for the
approximate-identity argument.
:::

:::proof "parabolic.heat_kernel_mass"
Apply Mathlib's Gaussian integral with coefficient $`1/(4t)`. The spatial
integral of the exponential is $`(4\pi t)^{n/2}`; multiplying by the
prefactor $`(4\pi t)^{-n/2}` gives one.
:::

# Heat-ball mean values

:::definition "parabolic.heat_ball" (parent := "parabolic.classical") (lean := "HeatEquation.heatBall, HeatEquation.heatBallWeight") (uses := "parabolic.heat_kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-51"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a pole $`(x,t)` and radius parameter $`r>0`, the backward heat ball is

$$`
E(x,t;r)=
\left\{(y,s):
  \Gamma_n(x-y,t-s)>r^{-n}\right\},
`

and Watson's mean-value weight is

$$`
W_{x,t}(y,s)=\frac{\lVert x-y\rVert^2}{(t-s)^2}.
`

Every point of a positive-radius heat ball lies strictly before its pole in
time, so the denominator is nonzero on the integration domain.
:::

The level set defining $`E(x,t;r)` uses the kernel itself, rather than a
Euclidean distance, to measure closeness to the pole. Watson's weight
replaces the uniform density of the elliptic mean-value formula. For $`n>0`,
applying the identity to $`u\equiv1` shows that its total mass over a heat
ball with radius parameter $`r>0` is $`4r^n`, the normalizing constant.

:::theorem "parabolic.heat_ball_mean_value" (parent := "parabolic.classical") (lean := "HeatEquation.heatBall_meanValue") (uses := "parabolic.heat_ball, parabolic.heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-51"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0`, $`r>0`, and let $`u\in C^2(\mathbb R^{n+1})` satisfy
$`u_t-\Delta u=0` on $`E(x,t;r)`. Then

$$`
u(x,t)=\frac1{4r^n}
\int_{E(x,t;r)}
  u(y,s)\frac{\lVert x-y\rVert^2}{(t-s)^2}\,dy\,ds.
`

The Lean statement assumes only continuous first derivatives, continuous second spatial derivatives, and caloricity on the displayed heat ball.
:::

:::proof "parabolic.heat_ball_mean_value"
Parabolically scale the domain to the unit heat ball and differentiate the
weighted integral with respect to the scale. On each backward-time slice,
Watson's transport identity converts that derivative into a spatial flux.
The boundary flux and both singular endpoint contributions vanish. Fubini
and the fundamental theorem of calculus therefore make the weighted integral
constant in scale, and its zero-scale value is
$`4u(x,t)`. Scaling back contributes the factor $`r^n`.
:::

For the kernel solution $`u(\cdot,t)=\Gamma_n(\cdot,t)*g` with
$`g\in L^1(\mathbb R^n)` and $`\int g=M`, Fubini and unit kernel mass give
$`\int u(\cdot,t)=M` for all $`t>0`. This is conservation of total heat.
In probability, the kernel is the transition density of Brownian motion with
covariance $`2tI`, whose generator is $`\Delta`. Unit mass says the particle
is somewhere with probability one.
For broad classes of uniformly parabolic equations, Aronson's estimates
instead compare their fundamental solutions above and below with Gaussian
profiles under suitable coefficient hypotheses ({Informal.citet "aronson-1967"}[]).
