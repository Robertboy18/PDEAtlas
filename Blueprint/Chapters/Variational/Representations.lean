/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.Asymptotics
import Blueprint.Chapters.Variational.Representations.Hodograph
import Blueprint.Chapters.Variational.Representations.Splines

/-!
# Explicit representations and transform methods

Separation of variables, similarity and traveling-wave reductions,
Cole–Hopf, Fourier and Laplace reconstruction, analytic models, asymptotic
limits, local hodograph and Legendre transformations, and spline collocation.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Explicit Representations and Transform Methods" =>

# Exact Reductions

For a product $`u(t,x)=T(t)X(x)`, the heat equation becomes

$$`
T'(t)X(x)-T(t)X''(x)=0.
`

After division by $`T(t)X(x)` on the region where it is nonzero, the quotient
$`T'/T` depends only on $`t` and the quotient $`X''/X` only on $`x`, so both
equal a common separation constant. Boundary conditions then select the
spatial eigenfunctions, and the time equation determines their decay. On an
interval, this produces sine modes and the familiar spectral heat series. We
prove the product residual and the boundary-value modes, and convergence and
truncation estimates for an arbitrary Hilbert basis.

Traveling and self-similar substitutions change the independent variables. For
$`u(t,x)=U(x-ct)`, the PDE reduces to an ODE for $`U`; for
$`u(t,x)=t^{-\alpha}U(xt^{-\beta})`, every derivative carries a power of
$`t` determined by scaling. The chain-rule theorems are therefore the reusable
core. Transport, heat, Burgers, and singularity models use the same derivative
identities with different profile equations.
The KdV example constructs a localized $`\operatorname{sech}^2` wave by
balancing nonlinear transport and dispersion. The porous-medium example
constructs the Barenblatt profile with any prescribed positive mass, proves
the weak PDE across its free boundary, and identifies its Dirac initial trace.

Cole–Hopf is more delicate because it divides by the transformed heat profile:

$$`
u=-2\nu\,\frac{\partial_x v}{v}.
`

The nonvanishing domain belongs in the statement. On that domain, the heat
residual of $`v` cancels the nonlinear Burgers residual of $`u`. For bounded
continuous initial velocity and positive viscosity,
{bpref "methods.cole_hopf.cauchy"}[] constructs the heat profile itself:
the Gaussian integral of the exponential primitive is integrable and positive,
and its logarithmic derivative attains the velocity in a joint space-time limit.

A hodograph transform uses the unknown velocity as a new coordinate.
A local Legendre transform does the same with the gradient of a scalar
solution. In both cases, an invertible Jacobian supplies the change of
coordinates. Following its inverse through the equation turns nonlinear
planar flow and minimal-surface equations into linear equations on the
new coordinate domain.

# Spectral and Analytic Reconstruction

With the convention $`\widehat f(\xi)=\int e^{-2\pi ix\xi}f(x)\,dx`,
Fourier analysis converts a constant-coefficient operator
$`P(\partial_x)` into multiplication by its symbol $`P(2\pi i\xi)`. For the shifted
elliptic equation

$$`
-u''+\lambda u=f,\qquad \lambda>0,
`

the transformed equation is

$$`
((2\pi\xi)^2+\lambda)\widehat u(\xi)=\widehat f(\xi).
`

Positivity gives the pointwise frequency bound
$`|\widehat u(\xi)|\leq\lambda^{-1}|\widehat f(\xi)|`. The transformed
equation and the bound are proved for Schwartz $`u` and $`f`, at each
frequency.

For heat and one-dimensional waves, the inverse Fourier formulas
are identified with the Gaussian convolution and d'Alembert solution.
Those identities carry the analytic PDE and initial traces back to physical
space. One-sided Laplace inversion similarly reconstructs a boundary-driven
transport solution from a smooth compactly supported causal signal; the
operational rule keeps the initial term $`L(f')=sLf-f(0)` visible.
For Schwartz initial data in any spatial dimension, we also differentiate
the inverse Fourier integral directly. The resulting wave is jointly
$`C^2`, solves the wave equation, and attains both initial data.

Power-series methods reconstruct a local solution from coefficient recurrences
and require convergence together with a noncharacteristic initial surface.
Asymptotic methods ask a different question: how does an integral or profile
behave as a parameter becomes large or small? Gaussian identities, Laplace
concentration, oscillatory cancellation, and periodic averaging quantify the
dominant contribution in such limits.

Spline collocation is the finite-dimensional counterpart of these
expansions. On a carrier where a nonnegative B-spline family sums to one,
coefficient bounds become pointwise bounds. The strict Schoenberg–Whitney
inequalities give a sufficient condition for sampling to determine the
coefficients. We prove the recursion and this sufficient condition, and give the
exact factorization certificate that a validated backend can use to prove a
collocation matrix nonsingular.

{include 0 Blueprint.Chapters.Variational.Representations.Separation}
{include 0 Blueprint.Chapters.Variational.Representations.Similarity}
{include 0 Blueprint.Chapters.Variational.Representations.ColeHopf}
{include 0 Blueprint.Chapters.Variational.Representations.Hodograph}
{include 0 Blueprint.Chapters.Variational.Representations.Fourier}
{include 0 Blueprint.Chapters.Variational.Representations.AnalyticModels}
{include 0 Blueprint.Chapters.Variational.Representations.Asymptotics}
{include 0 Blueprint.Chapters.Variational.Representations.Splines}
