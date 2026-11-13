/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Elliptic.FundamentalSolutions.Newtonian
import Blueprint.Chapters.Elliptic.MovingPlanes
import Blueprint.Commands.Figures
import PDE.Analysis.Integration.ConvolutionDerivative
import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianL2
import PDE.Elliptic.Classical.Poisson.FundamentalSolution
import PDE.Elliptic.Classical.Poisson.FundamentalSolutionConvolution
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Dirichlet.Uniqueness
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.GreenKernel
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.InteriorRegularity
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.KernelLaplacian
import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Reciprocity
import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Representation
import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Uniqueness
import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Dirichlet
import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Symmetry
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.BoundaryConvergence
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Differentiation

/-!
# Green kernels and Poisson representation

Green and Poisson kernels on the ball and the half-space, the ball Dirichlet problem, and
fundamental-solution convolution.
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
#doc (Manual) "Green Kernels and Poisson Representation" =>

:::group "elliptic.green_kernels"
Green and Poisson kernels
:::

Green's functions convert Dirichlet problems into integral representations.
Given boundary data $`g` on $`\partial\Omega` and interior forcing $`f`, the
solution of $`-\Delta u=f` in $`\Omega`, $`u=g` on $`\partial\Omega`, is
formally represented by

$$`
u(x)=\int_\Omega G(x,y)f(y)\,dy
      -\int_{\partial\Omega}\frac{\partial G}{\partial\nu_y}(x,y)g(y)\,dS(y).
`

Evans (2010, pp. 33–41) derives this representation and symmetry for bounded
$`C^1` domains, then computes explicit kernels on the half-space and ball.
{Informal.citet "gilbarg-trudinger-2001"}[] (Chapter 2) give a more classical treatment
emphasizing the potential-theoretic perspective. We follow the explicit
model-domain route first: construct the kernels, prove their off-pole
properties, and solve the Dirichlet problem on the ball. The representation
and symmetry theorems on general bounded $`C^1` domains come after the ball.

# The Ball Kernel and Dirichlet Problem

Kelvin inversion places an image pole outside the ball, so subtracting the
image fundamental solution produces a kernel that is harmonic away from the
physical pole and vanishes on the sphere. The negative outward normal
derivative $`-\partial_{\nu_y}G_B(x,y)` is the Poisson kernel, and the
associated Poisson extension is regular, harmonic, recovers its boundary
values, and is the unique such solution.

To make the construction concrete, consider the three-dimensional unit ball.
The fundamental solution is $`\Phi_3(x)=1/(4\pi|x|)`. For an interior pole
$`x\in B(0,1)` with $`x\ne0`, the Kelvin image is $`x^*=x/|x|^2`, which lies
outside the ball since $`|x^*|=1/|x|>1`. The Green's function is then

$$`
G_B(x,y)=\frac{1}{4\pi|y-x|}-\frac{1}{4\pi|x|\,|y-x^*|}.
`

On the boundary sphere $`|y|=1`, the identity $`|y-x|=|x|\,|y-x^*|` makes
the two terms cancel, confirming $`G_B(x,y)=0`. The outward normal derivative
of $`G_B` is negative; its negative gives the Poisson kernel

$$`
K_1(x,y)=\frac{1-|x|^2}{4\pi|x-y|^3}\qquad(|y|=1).
`

This explicit formula shows that the Poisson kernel is positive, singular as
$`x\to y\in\partial B`, and has mass one over the sphere. For the ball of
radius $`r`, scaling replaces $`|x|^2` by $`|x|^2/r^2` and introduces the
appropriate dimensional normalization (Evans, 2010, pp. 40–41;
{Informal.citet "gilbarg-trudinger-2001"}[], Theorem 2.6).

:::definition "elliptic.green.ball.kernel" (parent := "elliptic.green_kernels") (lean := "GreenFunction.ballGreenFunction") (uses := "elliptic.fundamental_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "39-40"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, write $`x^*=x/\lVert x\rVert^2` when $`x\ne0`.
The unit-ball Green kernel is the total function

$$`
G_B(x,y)=
\begin{cases}
\dfrac{(1-\max\{x_0,y_0\})(1+\min\{x_0,y_0\})}{2},&n=1,\\[4pt]
\Phi_n(y-x)-\Phi_n\!\left(\lVert x\rVert(y-x^*)\right),&n\geq2,\ x\ne0,
\end{cases}
`

with the continuous $`x=0` branch written explicitly in Lean. The first
variable is the physical pole and the second is the field point; in the
one-dimensional branch, $`x_0` and $`y_0` denote their sole coordinates. For
$`n\geq2` the kernel is the Kelvin construction of Evans §2.2.4; for $`n=1` it
is the Dirichlet kernel of $`-d^2/dx^2` on $`(-1,1)`.
:::

The defining property of a Green kernel is that it vanishes when the field point
reaches the boundary. For the Kelvin construction this is the inversion identity
$`\lVert y-x\rVert=\lVert x\rVert\,\lVert y-x^*\rVert` on the unit sphere, which
gives the two fundamental-solution terms arguments of equal norm.

:::theorem "elliptic.green.ball.boundary" (parent := "elliptic.green_kernels") (lean := "GreenFunction.ballGreenFunction_boundary") (uses := "elliptic.green.ball.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "39-40"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`n\geq2`, an interior pole and a boundary field point satisfy

$$`
\lVert x\rVert<1,\quad \lVert y\rVert=1
\quad\Longrightarrow\quad G_B(x,y)=0.
`
:::

:::proof "elliptic.green.ball.boundary"
Write $`x^*=x/\lVert x\rVert^2` for the Kelvin image of a nonzero pole.
For $`\lVert y\rVert=1`, the inversion identity gives

$$`
\lVert y-x\rVert
  =\lVert x\rVert\,\lVert y-x^*\rVert
  =\bigl\|\lVert x\rVert(y-x^*)\bigr\|.
`

Thus the physical and image arguments of the fundamental solution have the
same norm, so the two terms in the Green kernel cancel. The proof treats
dimension two and dimensions at least three separately because the
fundamental solution is logarithmic in the former and a negative power in the
latter. If $`x=0`, both formulas reduce directly using
$`\lVert y\rVert=1`.
:::

Boundary vanishing concerns the sphere; harmonicity concerns the interior. For a
nonzero interior pole the image $`x^*` lies outside the closed ball, so both
fundamental-solution terms are harmonic in $`y` throughout
$`B(0,1)\setminus\{x\}`. Harmonicity off the pole together with vanishing on
the sphere makes $`G_B` a Green kernel.

:::theorem "elliptic.green.ball.harmonic" (parent := "elliptic.green_kernels") (lean := "GreenFunction.ballGreenFunction_harmonic") (uses := "elliptic.green.ball.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "39-40"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`n\geq2`, $`x,y\in B(0,1)`, and $`y\ne x`, the field-variable
Laplacian vanishes:

$$`\Delta_yG_B(x,y)=0.`
:::

:::proof "elliptic.green.ball.harmonic" (uses := "elliptic.fundamental_solution.harmonic_off_pole")
Expand the Kelvin-inversion formula.  Each fundamental-solution term is
harmonic away from its pole, and the geometric hypotheses keep both relevant
poles outside the point where the field-variable Laplacian is evaluated.
:::

The Poisson kernel is the negative outward normal derivative
$`-\partial_{\nu_y}G_B(x,y)` on the sphere, in which the two
fundamental-solution terms combine into a single closed expression. We take
that closed form, scaled to a ball of radius $`r`, as the definition of the
kernel, following Evans's computation of $`-\partial_{\nu_y}G_B`; the theorems
about the Poisson extension work from the formula directly.

:::definition "elliptic.poisson.ball.kernel" (parent := "elliptic.green_kernels") (lean := "GreenFunction.ballPoissonKernel") (uses := "elliptic.green.ball.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a positive radius $`r`, the ball Poisson kernel is

$$`K_r(x,y)=\frac{r^2-\lVert x\rVert^2}
  {n\alpha(n)r\lVert x-y\rVert^n}.`

Its boundary-value interpretation uses $`x\in B(0,r)` and
$`y\in\partial B(0,r)`; the Lean definition is total.
:::

Integrating the kernel against boundary data over the sphere gives the Poisson
extension. The definition pulls the $`y`-independent prefactor
$`(r^2-\lVert x\rVert^2)/(n\alpha(n)r)` outside the integral, leaving
$`g(y)/\lVert x-y\rVert^n` as the integrand; this is the form in which the
extension is differentiated.

:::definition "elliptic.poisson.ball.extension" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonBallExtension") (uses := "elliptic.poisson.ball.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Poisson extension integrates the prescribed boundary datum over the
radius-$`r` sphere with the normalization used by the ball Poisson kernel.
Analytic theorems about this total function supply positivity of $`r`,
continuity of the data, and the appropriate interior or boundary hypotheses.
:::

The prefactor form and the kernel form of the extension are equal as total
functions, with no hypotheses on $`r`, $`g`, or $`x`, so later theorems may pass
between them freely.

:::theorem "elliptic.poisson.ball.kernel_integral" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonBallExtension_eq_sphereIntegral_ballPoissonKernel") (uses := "elliptic.poisson.ball.kernel, elliptic.poisson.ball.extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The prefactor form of the ball extension is algebraically equal to the sphere
integral of $`K_r(x,y)g(y)`.
:::

:::proof "elliptic.poisson.ball.kernel_integral"
Insert the explicit formula for $`K_r(x,y)` into the sphere integral. The
factor $`(r^2-\lVert x\rVert^2)/(n\alpha(n)r)` is independent of $`y` and
can be pulled outside, leaving exactly the prefactor definition of the
Poisson extension.
:::

The Poisson extension is meaningful only inside the ball. The Dirichlet
candidate glues it to the datum on the sphere and outside, and attaching the
data definitionally rather than through a limit is what lets boundary equality
be exact and uniqueness be stated as an equation on the closed ball.

:::definition "elliptic.poisson.ball.solution" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonBallDirichletSolution") (uses := "elliptic.poisson.ball.extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The boundary-attached Dirichlet candidate is the total function

$$`
u_{r,g}(x)=
\begin{cases}
\displaystyle\int_{\partial B(0,r)}K_r(x,y)g(y)\,dS(y),
  &\lVert x\rVert<r,\\[6pt]
g(x),&\lVert x\rVert\geq r.
\end{cases}
`

Thus it is the Poisson extension in the open ball and agrees definitionally
with the prescribed ambient datum outside it.
:::

Classical harmonicity requires two derivatives, but the same kernel gives every
derivative order in the interior. Near a fixed interior point, a smooth cutoff
removes the inverse-distance singularity without changing the sphere integral.
Mathlib's convolution regularity theorem then gives smoothness.

:::theorem "elliptic.poisson.ball.interior_regular" (parent := "elliptic.green_kernels") (lean := "GreenFunction.contDiffOn_poissonBallExtension, GreenFunction.contDiffAt_poissonBallExtension") (uses := "elliptic.poisson.ball.extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for a positive radius and a continuous ambient
representative of the boundary datum, differentiation under the sphere
integral gives a $`C^\infty` extension on the open ball. The linked theorems
allow every regularity order $`m\in\mathbb N\cup\{\infty\}`, both at individual
interior points and throughout the ball. The choice $`m=2` supplies the
regularity needed by the classical Laplacian statement.
:::

:::proof "elliptic.poisson.ball.interior_regular"
Fix an interior point and choose a smaller neighborhood whose distance from
the boundary sphere is positive. The differences between points in this
neighborhood and points on the sphere lie in a compact annulus away from zero.
Replace the inverse-distance kernel by a smooth compactly supported kernel
that agrees on this annulus. Its convolution with the boundary datum is
smooth and agrees locally with the original potential. Multiplying by the
smooth Poisson prefactor preserves every derivative order.
:::

Given the two derivatives, the Laplacian of the extension is the sphere integral
of $`\Delta_xK_r(x,y)`, and for $`\lVert y\rVert=r` the kernel is harmonic in
$`x`. The theorem carries this pointwise cancellation through the integral.

:::theorem "elliptic.poisson.ball.laplacian" (parent := "elliptic.green_kernels") (lean := "GreenFunction.laplacian_poissonBallExtension_eq_zero") (uses := "elliptic.poisson.ball.interior_regular, foundations.operators.laplacian_norm_sq")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`r>0`, $`g:\mathbb R^n\to\mathbb R` is
continuous, and $`x\in B(0,r)`, then the coordinate Laplacian of the Poisson
extension vanishes:

$$`\Delta\!\left(P_rg\right)(x)=0.`

The proof differentiates the kernel twice, uses the common norm-square
identities, and performs the resulting sphere-integral cancellation.
:::

:::proof "elliptic.poisson.ball.laplacian"
Use the two derivative formulas justified by interior regularity and sum their
diagonal terms. After writing all denominators over
$`\lVert x-y\rVert^{n+4}`, the norm-square identities for boundary points
$`\lVert y\rVert=r` make the numerator cancel. Integrating the zero kernel
Laplacian yields $`\Delta(P_rg)(x)=0`.
:::

Interior regularity and the vanishing Laplacian are exactly the two clauses of
the harmonicity predicate. Combining them for the boundary-attached candidate,
which agrees with $`P_rg` on the open ball, gives the existence half of the
Dirichlet theorem at the $`C^2` level.

:::theorem "elliptic.poisson.ball.harmonic" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonBallDirichletSolution_isHarmonicPDE") (uses := "elliptic.poisson.ball.solution, elliptic.poisson.ball.interior_regular, elliptic.poisson.ball.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for $`r>0` and continuous ambient data $`g`, the
boundary-attached solution satisfies

$$`
u_{r,g}\in C^2\!\left(B(0,r)\right),
\qquad \Delta u_{r,g}=0\quad\text{in }B(0,r).
`

Interior $`C^\infty` regularity holds as well, by the
{bpref "elliptic.poisson.ball.interior_regular"}[smoothness theorem].
:::

:::proof "elliptic.poisson.ball.harmonic"
Inside the ball, the boundary-attached solution is definitionally the Poisson
extension. Apply its interior $`C^2` theorem and its pointwise Laplacian-zero
theorem; together these are exactly the classical harmonicity predicate on
$`B(0,r)`.
:::

Harmonicity inside the ball settles nothing about the boundary condition.
Boundary recovery rests on the kernel being positive with mass one and
concentrating at $`x_0` as $`x\to x_0\in\partial B(0,r)`, so that the Poisson
integral of continuous data converges to $`g(x_0)`.

:::theorem "elliptic.poisson.ball.continuous_up_to_boundary" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonBallExtension_tendsto_g_on_sphere, GreenFunction.poissonBallDirichletSolution_eq_boundary, GreenFunction.continuousOn_poissonBallDirichletSolution") (uses := "elliptic.poisson.ball.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`r>0` and $`g` is continuous, then

$$`
u_{r,g}\in C\!\left(\overline{B(0,r)}\right),\qquad
u_{r,g}|_{\partial B(0,r)}=g|_{\partial B(0,r)}.
`

The proof first shows
$`P_rg(x)\to g(x_0)` as $`x\to x_0` through $`B(0,r)` for every
$`x_0\in\partial B(0,r)`; the attached total solution then gives exact
boundary equality.
:::

:::proof "elliptic.poisson.ball.continuous_up_to_boundary"
Subtract $`g(x_0)` inside the Poisson integral and use that the kernel has
mass one. Continuity makes this difference uniformly small near $`x_0`,
while positivity and concentration of the kernel control the complementary
part. This proves the interior limit; the piecewise definition supplies exact
boundary values and glues the two continuous pieces on the closed ball.
:::

Uniqueness comes from the maximum principle. The difference of two solutions
is harmonic in the ball, continuous on its closure, and zero on the sphere, and
two applications of the weak maximum principle force it to vanish. The
mean-value property and the derivative estimates use this theorem to identify
a harmonic function with its Poisson extension.

:::theorem "elliptic.poisson.ball.uniqueness" (parent := "elliptic.green_kernels") (lean := "GreenFunction.eq_poissonBallDirichletSolution_of_isHarmonicPDE") (uses := "elliptic.poisson.ball.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "27-28"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "40-41"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
In positive dimension, let $`r>0`, let $`g` be continuous, and let
$`u\in C^2(B(0,r))`. If

$$`
\Delta u=0\ \text{in }B(0,r),\qquad
u\in C\!\left(\overline{B(0,r)}\right),\qquad
u=g\ \text{on }\partial B(0,r),
`

then

$$`u(x)=u_{r,g}(x)\qquad(x\in\overline{B(0,r)}).`
:::

:::proof "elliptic.poisson.ball.uniqueness" (uses := "elliptic.maximum.weak_ball, elliptic.poisson.ball.harmonic, elliptic.poisson.ball.continuous_up_to_boundary")
Subtract the two harmonic functions.  Their difference is continuous up to
the boundary and vanishes there, so the weak maximum principle applied to the
difference and its negative forces it to vanish on the ball.
:::

Evans states these properties of $`P_rg` together as Poisson's formula for the
ball.

:::theorem "elliptic.poisson.ball.formula" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poisson_formula_ball")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "40-41"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for $`r>0` and continuous $`g`, the Poisson formula
gives a field $`P_rg` such that

$$`
P_rg\in C^2(B(0,r)),\qquad
\Delta(P_rg)=0\ \text{in }B(0,r),\qquad
\lim_{\substack{x\to x_0\\x\in B(0,r)}}P_rg(x)=g(x_0)
`

for every $`x_0\in\partial B(0,r)`.
:::

:::proof "elliptic.poisson.ball.formula" (uses := "elliptic.poisson.ball.harmonic, elliptic.poisson.ball.continuous_up_to_boundary")
The three clauses are the interior Laplacian identity, interior $`C^2`
regularity, and pointwise boundary convergence of the Poisson integral.
:::

With uniqueness, the Poisson formula gives the only solution of the ball
Dirichlet problem with continuous data.
For model domains with explicit geometry, the classical and
potential-theoretic routes therefore give the same answer.
For general domains, uniqueness instead follows from the maximum principle
alone, without an explicit representation
({Informal.citet "gilbarg-trudinger-2001"}[], Theorem 2.5).

# Green Functions on General Domains

On a general domain the Green function is built the same way, but the
corrector has no formula. For a pole $`x\in\Omega` it is the harmonic function
$`\phi^x` with $`\phi^x(y)=\Phi(y-x)` on $`\partial\Omega`, and

$$`G(x,y)=\Phi(y-x)-\phi^x(y).`

The representation formula and the symmetry $`G(x,y)=G(y,x)` follow
{Informal.citet "evans-2010"}[] §2.2.4. A weak construction of the corrector uses the
Dirichlet solver in
$`H^1`, and the barrier theorem for $`C^1` domains makes it continuous on the
closure. Symmetry needs nothing more. The representation formula also needs
the normal derivative of $`\phi^x` on the boundary. The construction of that derivative
assumes a $`C^{n+3}` boundary, where the boundary regularity theory gives
$`\phi^x\in C^2(\overline\Omega)`.

:::definition "elliptic.green.domain.kernel" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.GreenFunction.Domain.greenKernel, PotentialTheory.GreenFunction.Domain.greenKernelGradient") (uses := "elliptic.fundamental_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a pole $`x` and a function $`\phi`, the domain Green kernel is

$$`G_\phi(x,y)=\Phi_n(y-x)-\phi(y).`

Its gradient field is $`\nabla_y\Phi_n(y-x)` minus the continuous extension of
$`\nabla\phi` to $`\overline\Omega`, so the same field gives the interior
gradient and the boundary flux. The definition imposes no conditions on
$`\phi`; each theorem states the ones it uses.
:::

:::theorem "elliptic.green.domain.corrector" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.GreenFunction.Domain.exists_unique_harmonic_corrector_of_local_graph, PotentialTheory.GreenFunction.Domain.exists_harmonic_corrector_of_local_graph") (uses := "elliptic.green.domain.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge2` and let $`\Omega\subset\mathbb R^n` be a bounded open set with
$`C^1` boundary, given by local graphs. For every $`x\in\Omega` there is a
function $`\phi^x` that is harmonic in $`\Omega`, continuous on
$`\overline\Omega`, equal to $`\Phi_n(\cdot-x)` on $`\partial\Omega`, and
a.e. equal to an $`H^1(\Omega)` field whose gradient is orthogonal to the
gradients of $`H^1_0(\Omega)`. Any other function harmonic in $`\Omega`,
continuous on $`\overline\Omega`, with the same boundary values equals
$`\phi^x` on $`\overline\Omega`.

The domain need not be connected, and $`n=2`, with its logarithmic kernel, is
included.
:::

:::proof "elliptic.green.domain.corrector" (uses := "elliptic.green.domain.kernel")
Change $`\Phi_n(\cdot-x)` inside a small ball around the pole to get a smooth
compactly supported function $`A` with the right boundary values. Solve the
Dirichlet problem with data $`A` in $`H^1`: its solution $`U` is weakly
harmonic, has a harmonic representative, and the barrier theorem for $`C^1`
domains shows that this representative is continuous up to the boundary with
the values of $`A`. Uniqueness is the weak maximum principle on
$`\overline\Omega`, applied to the difference of two such functions.
:::

:::theorem "elliptic.green.domain.representation" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.GreenFunction.Domain.dirichlet_representation, PotentialTheory.GreenFunction.Domain.representation_of_corrector, PotentialTheory.GreenFunction.Domain.exists_corrector_dirichlet_representation_of_higher_graph") (uses := "elliptic.green.domain.kernel, elliptic.green.domain.corrector")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge2` and let $`\Omega` be a bounded open set with $`C^1` boundary.
Let $`u\in C^2(\overline\Omega)` solve $`-\Delta u=f` in $`\Omega` with
$`u=g` on $`\partial\Omega`, and let $`x\in\Omega`. If $`\phi` is harmonic in
$`\Omega`, lies in $`C^2(\overline\Omega)`, and equals $`\Phi_n(\cdot-x)` on
$`\partial\Omega`, then $`f\,G_\phi(x,\cdot)` is integrable on $`\Omega`,
$`g\,\partial_\nu G_\phi(x,\cdot)` is integrable on $`\partial\Omega`, and

$$`
u(x)=-\int_{\partial\Omega}g(y)\,\frac{\partial G_\phi}{\partial\nu_y}(x,y)\,dS(y)
  +\int_\Omega f(y)\,G_\phi(x,y)\,dy.
`

If the boundary is $`C^{n+3}`, a corrector with these properties exists, and
the formula holds with it.
:::

:::proof "elliptic.green.domain.representation" (uses := "elliptic.green.domain.corrector")
Green's second identity on $`\Omega` minus a small ball around $`x`, applied
to $`u` and $`\Phi_n(\cdot-x)`, gives the Newton representation of $`u(x)`,
which still contains $`\partial_\nu u` on the boundary. The same identity for
$`u` and the harmonic $`\phi`, which has no pole, has no interior point term.
Subtracting it cancels $`\partial_\nu u`, because $`\phi=\Phi_n(\cdot-x)` on
$`\partial\Omega`. On a $`C^{n+3}` boundary the
{bpref "elliptic.green.domain.corrector"}[constructed corrector] is
$`C^2` up to the boundary by the boundary regularity theory, and the formula
applies to it.
:::

Symmetry has a weak proof, and so holds on every bounded $`C^1` domain with
the constructed correctors. Regularize the two poles in disjoint small balls.
Each corrector minus its regularized pole lies in $`H^1_0`, so each can be
used as a test field in the other's weak equation. The Dirichlet form is
symmetric, and evaluating the regularized poles gives $`G(x,y)=G(y,x)`.

:::theorem "elliptic.green.domain.symmetry" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.GreenFunction.Domain.green_eq_swap_of_classical_correctors, PotentialTheory.GreenFunction.Domain.exists_reciprocal_harmonic_correctors_of_local_graph, PotentialTheory.GreenFunction.Domain.green_eq_swap_of_native_correctors, PotentialTheory.GreenFunction.Domain.symmetry_of_correctors, PotentialTheory.GreenFunction.Domain.symmetry_of_raw_graph") (uses := "elliptic.green.domain.corrector")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge2` and let $`\Omega` be a bounded open set with $`C^1` boundary.
If $`\phi^x` and $`\phi^y` are harmonic in $`\Omega`, continuous on
$`\overline\Omega`, and equal to $`\Phi_n(\cdot-x)` and $`\Phi_n(\cdot-y)` on
$`\partial\Omega`, then

$$`\Phi_n(y-x)-\phi^x(y)=\Phi_n(x-y)-\phi^y(x),`

that is, $`G(x,y)=G(y,x)`. When the correctors are also $`C^2` up to the
boundary, a second proof goes through Green's identity, as in Evans.
:::

:::proof "elliptic.green.domain.symmetry" (uses := "elliptic.green.domain.corrector")
By uniqueness, $`\phi^x` and $`\phi^y` are the constructed correctors, which
come with $`H^1` representatives, and the weak argument with regularized poles
applies. For
$`C^2` correctors the second proof writes the Green representation of each
corrector at the other pole. The two expressions differ by a boundary flux of
the antisymmetric pairing of $`\Phi_n(\cdot-x)` and $`\Phi_n(\cdot-y)`, and
by Green's identity for the two regular correctors. Both integrals vanish.
:::

{leanpde_figure "green-disc"}

The disc shows everything at once. For $`n=2` the corrector is
$`\Phi\big(|x|(y-x^*)\big)`, a fundamental solution placed at the reflected
point $`x^*=x/|x|^2`, so here the corrector has a formula. The left panel shows
the level curves of $`G(x,\cdot)`, which close up on the circle where $`G=0`.
The right panel shows the Poisson kernel $`-\partial_\nu G` for poles at
several distances from the centre. Each kernel has total mass one, and they
concentrate as the pole approaches the circle.

# The Half-Space Kernel

Reflection across the boundary hyperplane gives the half-space analogue of
Kelvin inversion. The kernel identities, the normalization, and boundary
recovery hold in every positive dimension. The half-space Green's function is
important both as a model and as the local building block in parametrix
constructions for general domains.

:::definition "elliptic.green.half_space.kernel" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpaceGreenFunction") (uses := "elliptic.fundamental_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "36-37"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`R(x',x_n)=(x',-x_n)` be reflection across the
boundary hyperplane. The upper-half-space Green kernel is

$$`G_{\mathbb H}(x,y)=\Phi_n(y-x)-\Phi_n(y-Rx).`

The first pole is physical; the reflected image pole lies outside
$`\mathbb H=\{z:z_n>0\}` whenever $`x\in\mathbb H`.
:::

Reflection is an isometry fixing the boundary hyperplane and exchanging the two
half-spaces, so for $`x\in\mathbb H` the image pole $`Rx` has negative last
coordinate and never meets $`\mathbb H`. Away from the physical pole both terms
are therefore smooth and harmonic in $`y\in\mathbb H`, in every positive
dimension.

:::theorem "elliptic.green.half_space.harmonic" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpaceGreenFunction_harmonic, GreenFunction.halfSpaceGreenFunction_isHarmonicPDE") (uses := "elliptic.green.half_space.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "36-38"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for $`x\in\mathbb H`, the field
$`y\mapsto G_{\mathbb H}(x,y)` is $`C^2` on
$`\mathbb H\setminus\{x\}` and satisfies

$$`\Delta_yG_{\mathbb H}(x,y)=0
\qquad(y\in\mathbb H\setminus\{x\}).`
:::

:::proof "elliptic.green.half_space.harmonic" (uses := "elliptic.fundamental_solution.smooth_off_pole, elliptic.fundamental_solution.harmonic_off_pole")
Both image terms are smooth and harmonic away from their poles.  Reflection
places the image pole outside the upper half-space, while the physical pole is
removed from the asserted domain.
:::

On the boundary itself, where $`y_n=0`, the point $`y` is equidistant from $`x`
and $`Rx`, and radiality of $`\Phi_n` makes the two terms equal. Unlike the ball
case, no restriction to $`n\ge2` is needed, because the reflection formula does
not depend on the Kelvin branch of the kernel.

:::theorem "elliptic.green.half_space.boundary" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpaceGreenFunction_boundary") (uses := "elliptic.green.half_space.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "36-37"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for every pole $`x` and every boundary point
$`y=(y',0)`,

$$`G_{\mathbb H}(x,y)=0.`

The pole $`x` is arbitrary; the cancellation uses only
$`\lVert y-x\rVert=\lVert y-Rx\rVert`.
:::

:::proof "elliptic.green.half_space.boundary"
Reflection fixes every boundary point $`y=(y',0)` and changes only the sign
of the pole's normal coordinate. Hence $`\lVert y-x\rVert=\lVert y-Rx\rVert`.
The fundamental solution is radial, so the two image terms agree and their
difference is zero.
:::

Integrating the kernel against a source over the half-space gives the Green
potential, the volume term of the representation formula. The integrability
predicate is kept separate from the integral because Mathlib's Bochner integral
is total: the identities that follow are meaningful only where the integrand is
integrable.

:::definition "elliptic.green.half_space.potential" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpaceGreenPotential, GreenFunction.HasIntegrableHalfSpaceGreenPotential") (uses := "elliptic.green.half_space.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "35-38"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for a source $`f`, the method-of-images Green
potential is

$$`
\mathcal G_{\mathbb R^n_+}f(x)
  =\int_{\mathbb R^n_+}G_{\mathbb H}(y,x)f(y)\,dy.
`

The argument order follows the Lean kernel: $`y` is the pole and $`x` is the
field point. The integral is a total Mathlib definition, while
the Green-potential integrability condition records the analytic domain condition
that the displayed integrand is integrable for every $`x`.
:::

Two consequences follow from the kernel identities alone: the potential vanishes
at boundary points because the kernel does, and a tangential reflection that
flips the sign of $`f` flips the sign of the potential. Neither uses
differentiability of $`f`.

:::theorem "elliptic.green.half_space.potential_geometry" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpaceGreenPotential_boundary, GreenFunction.halfSpaceGreenFunction_coordinateReflection, GreenFunction.halfSpaceGreenPotential_coordinateReflection_of_odd") (uses := "elliptic.green.half_space.boundary, elliptic.green.half_space.potential")
In positive dimension, for every boundary point $`x`, the potential satisfies
$`\mathcal G_{\mathbb R^n_+}f(x)=0`. Let $`R_i` reflect a tangential coordinate.
If $`f(R_i y)=-f(y)` for $`y` in the upper half-space and the Green
integrand is integrable at one field point $`x`, then it is also integrable
at $`R_i x` and

$$`
\mathcal G_{\mathbb R^n_+}f(R_i x)
  =-\mathcal G_{\mathbb R^n_+}f(x).
`
:::

:::proof "elliptic.green.half_space.potential_geometry"
Boundary vanishing follows pointwise from the image-kernel cancellation. For
parity, change variables $`y=R_i z`. Tangential reflection preserves the upper
half-space and Lebesgue measure, the Green kernel is invariant when both
arguments are reflected, and oddness of $`f` supplies the remaining minus
sign.
:::

For the potential to solve $`-\Delta u=f` it is compared with the whole-space
convolution $`\Phi_2*f`. When $`f` is odd under the boundary reflection, folding
the lower half-plane onto the upper one turns the convolution into the
method-of-images integral, provided the convolution integrand is integrable in
the first place. The logarithmic growth of $`\Phi_2` makes this a condition on
the tails of $`f`, met for instance by continuous $`L^1` data with a finite logarithmic
moment.

:::theorem "elliptic.green.half_space.planar_images_integrable" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.integrable_fundamentalSolution_mul_of_integrable_log_weight, GreenFunction.hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable, GreenFunction.halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable, GreenFunction.hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable_log_weight, GreenFunction.halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable_log_weight") (uses := "elliptic.green.half_space.potential_geometry, elliptic.fundamental_solution.distributional_planar")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "35-38"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f:\mathbb R^2\to\mathbb R` be odd under reflection across the horizontal
boundary. Suppose that, for every field point $`x`,

$$`
y\longmapsto \Phi_2(x-y)f(y)
`

is integrable on $`\mathbb R^2`. Then the method-of-images integrand is
integrable on the upper half-plane and

$$`
\mathcal G_{\mathbb R^2_+}f(x)=(\Phi_2*f)(x).
`

No compact support is assumed; the hypothesis is the tail condition for the
logarithmic kernel. A concrete sufficient condition is that
$`f` be continuous and

$$`
f\in L^1(\mathbb R^2),\qquad
\log(1+|\cdot|)f\in L^1(\mathbb R^2).
`

These assumptions make the displayed convolution integrable at every $`x`,
so odd data in this class have a well-defined
half-space Green potential equal to $`\Phi_2*f`.
:::

:::proof "elliptic.green.half_space.planar_images_integrable"
Split the whole-space integral into the upper and lower half-planes; their
common boundary has Lebesgue measure zero. Reflect the lower integral into the
upper half-plane. Reflection preserves Lebesgue measure, while oddness of
$`f` changes its sign. The reflected lower term is therefore exactly the
negative image term in the half-space Green kernel. For the sufficient
logarithmic-moment criterion, continuity controls the locally integrable pole.
Outside $`|y|\le |x|+1`, use

$$`
|\log|x-y||
\le (1+\log(1+|x|))(1+\log(1+|y|))
`

and dominate by the two $`L^1` hypotheses.
:::

Compactly supported $`C^2` sources satisfy the tail condition trivially, and for
them the {bpref "elliptic.poisson.planar_convolution_solution"}[planar convolution theorem]
gives $`-\Delta(\Phi_2*f)=f`. The identification
$`\mathcal G_{\mathbb R^2_+}f=\Phi_2*f` transports this equation to the
half-plane Green potential.

:::theorem "elliptic.green.half_space.planar_inversion" (parent := "elliptic.green_kernels") (lean := "GreenFunction.hasIntegrableHalfSpaceGreenPotential_of_odd, GreenFunction.halfSpaceGreenPotential_eq_fundamentalSolutionConvolution_of_odd, GreenFunction.negative_laplacian_halfSpaceGreenPotential_of_odd") (uses := "elliptic.green.half_space.planar_images_integrable, elliptic.poisson.planar_convolution_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "35-38"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f\in C_c^2(\mathbb R^2)` be odd under reflection across the horizontal
boundary, so its restriction to $`\mathbb R^2_+` is represented by an odd
whole-space extension. Then the method-of-images integral is integrable at
every field point and

$$`
\mathcal G_{\mathbb R^2_+}f=\Phi_2*f,
\qquad
-\Delta\mathcal G_{\mathbb R^2_+}f=f.
`

Together with boundary cancellation, this is a classical Dirichlet Poisson
solution for this source class.
:::

:::proof "elliptic.green.half_space.planar_inversion"
Split the whole-space convolution into upper- and lower-half-plane integrals;
the separating boundary hyperplane is Lebesgue null. Reflect the lower-half
integral into the upper half-plane. Measure preservation and oddness of $`f`
turn it into the negative image term, giving exactly the Green potential.
The planar whole-space convolution theorem then supplies the equation
$`-\Delta u=f`.
:::

Boundary data enter through the Poisson kernel, the negative outward normal
derivative of $`G_{\mathbb H}` at a boundary point: differentiating
$`\Phi_n(y-x)-\Phi_n(y-Rx)` in $`y_n` at $`y_n=0` gives
$`2x_n/(n\alpha(n)\lVert x-y\rVert^n)`. As for the ball, we take the closed
form as the definition.

:::definition "elliptic.poisson.half_space.kernel" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpacePoissonKernel") (uses := "elliptic.green.half_space.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a positive-dimensional upper half-space, the Poisson kernel is

$$`K(x,y)=\frac{2x_n}{n\alpha(n)\lVert x-y\rVert^n}.`

The definition is total in the field and boundary variables; its analytic
interpretation requires an interior field point and a boundary point.
:::

The boundary of the half-space is a copy of $`\mathbb R^{n-1}`, and integrating
over it requires a measure on the hyperplane inside $`\mathbb R^n`. Pushing
Lebesgue measure forward through the embedding $`\iota(y')=(y',0)` is the
measure-theoretic form of the surface element $`dS` on the flat boundary.

:::definition "elliptic.poisson.half_space.boundary_measure" (parent := "elliptic.green_kernels") (lean := "GreenFunction.halfSpaceBoundaryMeasure")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Lebesgue measure on $`\mathbb R^{n-1}` is pushed forward through the canonical
embedding into the boundary hyperplane. This measure realizes the boundary
integral in Evans's formula.
:::

With kernel and boundary measure available, the Poisson extension is their
pairing with the boundary datum. As for the ball, the definition pulls the
prefactor $`2x_n/(n\alpha(n))` outside, leaving the inverse distance power
$`\lVert x-\iota(y')\rVert^{-n}` as the kernel.

:::definition "elliptic.poisson.half_space.extension" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonHalfSpaceExtension") (uses := "elliptic.poisson.half_space.kernel, elliptic.poisson.half_space.boundary_measure")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Writing $`\iota(y')=(y',0)` for the boundary embedding, the half-space
Poisson extension is

$$`
(P_{\mathbb H}g)(x)
=\frac{2x_n}{n\alpha(n)}
  \int_{\mathbb R^{n-1}}
  \frac{g(\iota(y'))}{\lVert x-\iota(y')\rVert^n}\,dy'.
`

In Lean this is first defined against the pushforward of Lebesgue measure
under $`\iota`; the displayed formula is its coordinate realization.
:::

Unlike the sphere, the boundary hyperplane is unbounded, so decay of the
integrand at infinity matters. At an interior point the distance to $`\iota(y')`
grows like $`\lVert y'\rVert`, and $`\lVert y'\rVert^{-n}` is integrable at
infinity on $`\mathbb R^{n-1}` because $`n>n-1`; this is what makes the
extension of bounded data well defined.

:::theorem "elliptic.poisson.half_space.integrability" (parent := "elliptic.green_kernels") (lean := "GreenFunction.integrable_inv_distance_pow") (uses := "elliptic.poisson.half_space.kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every interior point $`x\in\mathbb R^n_+`, the boundary-coordinate
function

$$`y'\longmapsto\lVert x-\iota(y')\rVert^{-n}`

is integrable on $`\mathbb R^{n-1}`. Consequently, bounded measurable
boundary data give an integrable Poisson integrand.
:::

:::proof "elliptic.poisson.half_space.integrability"
Let $`t=x_n>0` and let $`a` be the tangential projection of $`x`. Both $`t`
and $`\lVert y'-a\rVert` are bounded by
$`d=\lVert x-\iota(y')\rVert`, hence

$$`1+\lVert y'-a\rVert\leq(1+t^{-1})d.`

After taking $`n`th powers and reciprocals, the inverse-distance kernel is
dominated by a constant multiple of the translated integrable weight
$`(1+\lVert y'-a\rVert)^{-n}`.
:::

The coordinate formula for the extension is a rewrite of the pushforward
integral rather than an analytic statement. It is the form in which the
differentiation, normalization, and trace arguments are carried out.

:::theorem "elliptic.poisson.half_space.integral" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonHalfSpaceExtension_eq_integral") (uses := "elliptic.poisson.half_space.extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every positive dimension, for measurable ambient data $`g` and every field
point $`x\in\mathbb R^n`, the half-space Poisson extension equals the
coordinate integral
$`\frac{2x_n}{n\alpha(n)}\int_{\mathbb R^{n-1}}g(\iota(y'))\,\lVert x-\iota(y')\rVert^{-n}\,dy'`.
:::

:::proof "elliptic.poisson.half_space.integral"
Unfold the boundary measure as the pushforward of Lebesgue measure under the
canonical embedding $`\iota(y')=(y',0)`. The pushforward integration formula
turns the boundary integral into an integral over $`\mathbb R^{n-1}`;
expanding the Poisson kernel produces the displayed constant and denominator.
:::

Interior differentiability follows by differentiating under the integral. On a
ball about $`x_0` of radius $`(x_0)_n/2`, the gradient of
$`\lVert x-\iota(y')\rVert^{-n}` is dominated by a multiple of
$`\lVert x_0-\iota(y')\rVert^{-(n+1)}`, which decays one power faster than the
kernel and is again integrable; boundedness of $`g` on the hyperplane keeps the
product integrable.

:::theorem "elliptic.poisson.half_space.differentiability" (parent := "elliptic.green_kernels") (lean := "GreenFunction.differentiableOn_poissonHalfSpaceExtension") (uses := "elliptic.poisson.half_space.integrability, elliptic.poisson.half_space.integral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every positive dimension, if $`g:\mathbb R^n\to\mathbb R` is measurable
and uniformly bounded on the boundary hyperplane, then its half-space Poisson
extension is Fréchet differentiable at every point of $`\mathbb R^n_+`.
:::

:::proof "elliptic.poisson.half_space.differentiability"
At an interior point $`x_0`, the ball of radius $`(x_0)_n/2` remains inside
the upper half-space. On this ball, differentiating
$`\lVert x-\iota(y')\rVert^{-n}` produces a norm bounded by a constant times
$`\lVert x_0-\iota(y')\rVert^{-(n+1)}`. This boundary-coordinate majorant is
integrable, so parametric dominated differentiation applies. The scalar
prefactor $`2x_n/(n\alpha_n)` is differentiable by the coordinate projection
rule, and the product rule gives the result.
:::

The exact mass of the kernel is the half-space analogue of the ball kernel's
mass one, and it means that the extension reproduces constants.

:::theorem "elliptic.poisson.half_space.normalization" (parent := "elliptic.green_kernels") (lean := "GreenFunction.poissonHalfSpaceExtension_one_eq_one") (uses := "elliptic.poisson.half_space.integral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-38"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every positive dimension, each point $`x` of the upper half-space
$`\mathbb R^n_+` satisfies

$$`(P_{\mathbb H}1)(x)=1.`

Equivalently, the half-space Poisson kernel has boundary mass one.
:::

:::proof "elliptic.poisson.half_space.normalization"
Translation and positive scaling reduce the boundary-distance integral to
unit height. For $`n\geq2`, polar coordinates and the substitution $`u=r^2`
turn its radial part into
$`\frac12 B((n-1)/2,1/2)`. The Beta–Gamma identity, the sphere-area formula,
and $`\Gamma(1/2)=\sqrt\pi` give exactly $`n\alpha_n/2`, which cancels the
kernel constant. The case $`n=1` is the integral over the zero-dimensional
boundary.
:::

Mass one converts boundary recovery into an approximate-identity argument.
Rescaling the boundary variable by the height $`t` turns the extension into the
integral of $`g(\iota(a+tz))` against a fixed integrable kernel; dominated
convergence sends this to the integral of the constant $`g(\iota(a))` against
the kernel, and mass one identifies that with $`g(\iota(a))`. The theorem
holds $`a` fixed and lets the height decrease to zero.

:::theorem "elliptic.poisson.half_space.vertical_trace" (parent := "elliptic.green_kernels") (lean := "GreenFunction.tendsto_poissonHalfSpaceExtension_vertical") (uses := "elliptic.poisson.half_space.normalization, elliptic.poisson.half_space.integrability")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "37-39"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every positive dimension, let $`g:\mathbb R^n\to\mathbb R` be continuous
and bounded on the boundary hyperplane. For each
$`a\in\mathbb R^{n-1}`,

$$`
\lim_{t\downarrow0}
(P_{\mathbb H}g)(\iota(a)+t e_n)=g(\iota(a)),
`

where $`\iota(a)=(a,0)`. The linked theorem expresses $`t\downarrow0` through
the positive-height neighborhood filter.
:::

:::proof "elliptic.poisson.half_space.vertical_trace"
Translate and rescale the boundary variable by $`y=a+tz`. The extension then
has a fixed integrable kernel
$`K_n(z)=|e_n-\iota(z)|^{-n}`. Continuity gives pointwise convergence of the
rescaled boundary data, while boundedness supplies a constant multiple of
$`K_n` as an integrable dominator. Dominated convergence and the exact kernel
mass from the normalization calculation give the stated limit.
:::

The boundary limit also holds when the tangential position varies with the
height. The boundary convergence theorem proves
convergence along every approach from the upper half-space. It requires a
measurable ambient datum, a uniform bound on the boundary hyperplane, and
continuity of the boundary restriction at the limiting point. There is no
bound on the ratio of horizontal displacement to height: after rescaling,
the sampled boundary points still approach the same point, and the same
integrable kernel dominates the data.

For measurable ambient data uniformly bounded on the boundary, the extension
is also $`C^2` and harmonic in the interior, by
the interior regularity theorem and
the harmonicity theorem.

# Fundamental-Solution Convolution

The representation-formula approach to existence starts here: given
$`f\in C_c^2(\mathbb R^n)`, the convolution $`u=\Phi_n*f` is the natural
whole-space candidate for $`-\Delta u=f`. The proof has two steps. The
derivative-transfer identity $`\Delta(\Phi_n*f)=\Phi_n*(\Delta f)` uses only
local integrability of $`\Phi_n` and the two continuous derivatives and
compact support of $`f`. The second step identifies $`\Phi_n*(\Delta f)` with
$`-f` through the distributional identity $`-\Delta\Phi_n=\delta_0`, which
needs singular-kernel analysis and holds in every positive dimension. Together
the two steps give classical inversion for every $`n\ge2` and every
$`f\in C_c^2(\mathbb R^n)` (Evans, 2010, Theorem 1, pp. 23–25).

:::definition "elliptic.poisson.fundamental_solution_convolution" (parent := "elliptic.green_kernels") (lean := "PoissonEquation.fundamentalSolutionConvolution") (uses := "elliptic.fundamental_solution, elliptic.fundamental_solution.local_integrability")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a bundled test function $`f\in C_c^2(\mathbb R^n)`, the classical
whole-space candidate is

$$`
(\Phi_n*f)(x)
=\int_{\mathbb R^n}\Phi_n(y)f(x-y)\,dy.
`
:::

Differentiating the convolution is legitimate because the derivative can be
moved onto the compactly supported smooth factor, whose translates stay in a
fixed compact set as the field point varies locally; local integrability of
$`\Phi_n` then supplies the dominator. The transfer theorem records this for
iterated coordinate derivatives of arbitrary finite order.

:::theorem "elliptic.poisson.convolution_derivative_transfer" (parent := "elliptic.green_kernels") (lean := "PDE.Analysis.convolution_iteratedPartialDeriv_right") (uses := "elliptic.poisson.fundamental_solution_convolution, elliptic.fundamental_solution.local_integrability")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a locally integrable left factor and a right factor in
$`C_c^\infty(\mathbb R^n)`, every finite iterated coordinate derivative
transfers to the right factor. For the datum $`f\in C_c^2(\mathbb R^n)` used
in the Poisson construction, the separate one- and two-derivative transfer
lemmas give the required identities without assuming infinite smoothness.
:::

:::proof "elliptic.poisson.convolution_derivative_transfer"
Compact support confines every translated derivative of the right factor to
a fixed compact set locally in the field variable. Local integrability of
the left factor supplies an integrable dominator there. Differentiation under
the integral transfers one coordinate derivative to the right factor, and
induction repeats this for any finite derivative list.
:::

## Five-dimensional potentials in L²

The same derivative transfer gives estimates on an unbounded domain. The
near and far parts of the Newtonian kernel need different bounds.

:::theorem "elliptic.poisson.five_dimensional_l2" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.memLp_fundamentalSolution_five_convolution, PotentialTheory.fundamentalSolution_five_convolution_iteratedPartialDeriv_two_memLp, PotentialTheory.fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two, PotentialTheory.ae_convolutionExistsAt_fundamentalSolution_five_of_integrable, PotentialTheory.memLp_fundamentalSolution_five_convolution_of_integrable, PotentialTheory.memLp_fundamentalSolution_five_convolution_of_ae_compact_support") (uses := "elliptic.poisson.convolution_derivative_transfer, elliptic.fundamental_solution.local_integrability")
In dimension five, let $`f\in L^1(\mathbb R^5)\cap L^2(\mathbb R^5)` and
$`u=\Phi_5*f`. The defining integral converges absolutely for almost every field
point, and $`u\in L^2(\mathbb R^5)`. This also applies to any $`L^2` source that
vanishes almost everywhere outside a compact set. No continuity or radial symmetry
is needed. If $`f\in C_c^2(\mathbb R^5)`, each Cartesian Hessian entry is also in
$`L^2`. If $`f\in C_c^\infty(\mathbb R^5)`, then for every finite word $`\alpha`
of coordinate directions, including the empty word,

$$`
\partial^\alpha u=\Phi_5*(\partial^\alpha f)\in L^2(\mathbb R^5).
`

The linked theorems prove the $`L^2` membership; the identity itself is the
{bpref "elliptic.poisson.convolution_derivative_transfer"}[derivative transfer]
for a locally integrable kernel.
:::

:::proof "elliptic.poisson.five_dimensional_l2"
Split $`\Phi_5` at unit radius. Its near part is in $`L^1` by local
integrability of the kernel. Its far part decays as $`\lVert X\rVert^{-3}`
and belongs to $`L^2`: five-dimensional shells have volume proportional to
$`r^4\,dr`, so

$$`
\int_1^\infty r^4(r^{-3})^2\,dr
=\int_1^\infty r^{-2}\,dr<\infty.
`

Convolution of an $`L^1` kernel with an $`L^2` function belongs to $`L^2` and
converges absolutely almost everywhere. Apply this first to the near kernel and
$`f\in L^2`, then to $`f\in L^1` and the far kernel, swapping the convolution
variables in the second term. Adding the two absolutely convergent integrals
recovers $`\Phi_5*f` and proves its $`L^2` membership. If an $`L^2` source
vanishes almost everywhere outside a compact set, Cauchy–Schwarz and finite volume
give $`f\in L^1`. Continuous compact sources satisfy both hypotheses as well.

Transfer the derivatives onto $`f` and apply the same estimate to each
continuous compactly supported source derivative.
:::

:::theorem "elliptic.poisson.five_dimensional_hessian_energy" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.fundamentalSolution_five_convolution_solves_poisson, PotentialTheory.fundamentalSolution_five_convolution_hessian_energy, PotentialTheory.fundamentalSolution_five_convolution_axial_mixed_l2_le_half") (uses := "elliptic.poisson.five_dimensional_l2")
Let $`f\in C_c^\infty(\mathbb R^5)` and $`u=\Phi_5*f`. Then $`-\Delta u=f`, and
global integration by parts gives

$$`
\begin{aligned}
\sum_{i,j=1}^5\int_{\mathbb R^5}|\partial_i\partial_j u|^2
  &=\int_{\mathbb R^5}|f|^2,\\
\left(\sum_{a=1}^4\int_{\mathbb R^5}
  |\partial_{y_a}\partial_z u|^2\right)^{1/2}
  &\le\tfrac12\lVert f\rVert_{L^2(\mathbb R^5)}.
\end{aligned}
`

The full Hessian sum counts both orders of each mixed derivative. The second
sum contains just the four axial/transverse entries. These estimates use ordinary
five-dimensional volume and the full classical Hessian, including its diagonal
local term.
:::

:::proof "elliptic.poisson.five_dimensional_hessian_energy"
Derivatives through order three are in $`L^2`, so Cauchy–Schwarz makes every
product in the two global integrations by parts integrable. Commuting derivatives gives
$`\int(\partial_i\partial_j u)^2=\int(\partial_i^2u)(\partial_j^2u)`.
Summing over $`i,j` yields the squared Laplacian norm. The proved Poisson equation
$`-\Delta u=f` identifies that norm with the source norm. No compact support of
$`u` or separately prescribed flux at infinity is needed.

For the half constant, put $`a=\Delta_yu`, $`b=\partial_z^2u`, and let $`M`
be the sum of the four axial/transverse squared $`L^2` norms. The same integration
by parts gives $`M=\int ab`. Since $`a+b=\Delta u`,

$$`
4M=\int_{\mathbb R^5}(a+b)^2-\int_{\mathbb R^5}(a-b)^2
\le\int_{\mathbb R^5}|f|^2.
`

Taking square roots gives the factor $`1/2` in norm.
:::

:::theorem "elliptic.poisson.newtonian_hessian_l2" (parent := "elliptic.green_kernels") (lean := "PotentialTheory.exists_newtonianHessianL2, PotentialTheory.hasWeakDerivativeOn_newtonianHessianL2_of_ae_compact_support, PotentialTheory.newtonianHessianL2_apply_ae_eq_of_contDiff_two") (uses := "elliptic.poisson.five_dimensional_hessian_energy")
By density, the full classical Hessian extends uniquely to bounded linear maps on
all of $`L^2(\mathbb R^5)`, retaining the energy identity and mixed $`1/2` bound.
For an $`L^2` source vanishing almost everywhere outside a compact set, the
extended entry $`T_{ij}f` is the weak derivative $`\partial_i\partial_j` of
$`\Phi_5*f`. For a $`C^2_c` source it agrees almost everywhere with the
classical Hessian entry.
:::

:::proof "elliptic.poisson.newtonian_hessian_l2"
Smooth compactly supported sources are dense in $`L^2(\mathbb R^5)`.
The energy identity bounds every Hessian component by the source norm, so
each component extends continuously to the completion. The full energy
identity and the mixed bound pass to the limit. Two such continuous maps
agree on the dense class and therefore on every $`L^2` source.

For the weak-derivative identification, approximate a compactly carried
$`L^2` source by smooth sources supported in a fixed compact set. The
potentials converge in $`L^2`, the extended Hessian entries converge in
$`L^2`, and the integration-by-parts identity against each test function
passes to the limit. A $`C^2_c` source has a $`C^2` potential, whose classical
Hessian is also a weak derivative, so uniqueness of weak derivatives gives the
almost-everywhere agreement.
:::

For a source radial in the four transverse coordinates, integrating out
their angles turns five-dimensional volume into a constant times
$`r^3\,dr\,dz`. The resulting radial Laplacian
$`\partial_r^2+3r^{-1}\partial_r+\partial_z^2` also appears in the
{bpref "fluid.axisymmetric.streamfunction_identities"}[axisymmetric streamfunction calculation].
Applying the Hessian bounds in those coordinates requires identifying the
source and derivatives with their radial lifts.

## Returning to the Poisson equation

Moving two coordinate derivatives onto $`f` in each direction gives the second
derivatives of $`\Phi_n*f`, whose continuity follows from the same domination,
and summing the pure second derivatives under the integral moves the Laplacian
onto $`f`.

:::theorem "elliptic.poisson.convolution_laplacian_transfer" (parent := "elliptic.green_kernels") (lean := "PoissonEquation.contDiff_two_fundamentalSolutionConvolution, PoissonEquation.laplacian_fundamentalSolutionConvolution") (uses := "elliptic.poisson.convolution_derivative_transfer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, for $`f\in C_c^2(\mathbb R^n)`, the convolution
candidate is globally $`C^2` and

$$`
\Delta(\Phi_n*f)(x)
=\bigl(\Phi_n*(\Delta f)\bigr)(x)
\qquad(x\in\mathbb R^n).
`
:::

:::proof "elliptic.poisson.convolution_laplacian_transfer"
Mathlib's convolution regularity theorem gives global $`C^2` regularity
from local integrability of $`\Phi_n` and the compactly supported $`C^2`
datum. Apply the two-derivative transfer lemma in each coordinate and sum
the pure second derivatives under the integral to obtain
$`\Phi_n*(\Delta f)`.
:::

:::theorem "elliptic.poisson.planar_convolution_solution" (parent := "elliptic.green_kernels") (lean := "PoissonEquation.negative_laplacian_fundamentalSolutionConvolution_two, PoissonEquation.fundamentalSolutionConvolution_two_isSolution") (uses := "elliptic.poisson.convolution_laplacian_transfer, elliptic.fundamental_solution.distributional_planar")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`f\in C_c^2(\mathbb R^2)`, the logarithmic fundamental-solution
convolution is a classical solution of the planar Poisson equation:

$$`
u=\Phi_2*f
\quad\Longrightarrow\quad
u\in C^2(\mathbb R^2),
\qquad -\Delta u=f.
`

Equivalently, the residual of the
{bpref "elliptic.poisson_equation"}[Poisson equation record] vanishes at $`u`
on all of $`\mathbb R^2`.
:::

:::proof "elliptic.poisson.planar_convolution_solution"
Transfer the Laplacian to the compactly supported factor. Reflect the
convolution variable so the resulting integral is the planar test-function
pairing $`\int\Phi_2\Delta\varphi`. The distributional pole identity evaluates
that pairing as $`-f(x)`, and negating gives
$`-\Delta(\Phi_2*f)(x)=f(x)`.
:::

:::theorem "elliptic.poisson.convolution_solution" (parent := "elliptic.green_kernels") (lean := "PoissonEquation.negative_laplacian_fundamentalSolutionConvolution, PoissonEquation.fundamentalSolutionConvolution_isSolution") (uses := "elliptic.poisson.convolution_laplacian_transfer, elliptic.poisson.planar_convolution_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge2` and $`f\in C_c^2(\mathbb R^n)`. The fundamental-solution
convolution is a classical solution of the Poisson equation on
$`\mathbb R^n`:

$$`
u=\Phi_n*f
\quad\Longrightarrow\quad
u\in C^2(\mathbb R^n),
\qquad -\Delta u(x)=f(x)\quad(x\in\mathbb R^n).
`

Equivalently, the residual of the
{bpref "elliptic.poisson_equation"}[Poisson equation record] vanishes at $`u`
on all of $`\mathbb R^n`.
:::

:::proof "elliptic.poisson.convolution_solution" (uses := "elliptic.fundamental_solution.distributional_newtonian")
For $`n=2` this is the
{bpref "elliptic.poisson.planar_convolution_solution"}[planar theorem]. For
$`n\ge3`, fix $`x` and apply the Newtonian pole identity
$`\int\Phi_n\Delta\varphi=-\varphi(0)` to the translated datum
$`\varphi(y)=f(x+y)`. Reflecting the integration variable and using
$`\Phi_n(-y)=\Phi_n(y)` identify this integral with
$`\bigl(\Phi_n*(\Delta f)\bigr)(x)`, so the Laplacian transfer gives
$`\Delta(\Phi_n*f)(x)=-f(x)`. Global $`C^2` regularity is part of the
transfer theorem.
:::
