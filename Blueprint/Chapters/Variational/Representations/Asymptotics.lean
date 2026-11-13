/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.AnalyticModels
import PDE.Analysis.Asymptotics.LaplaceMethod.Euclidean
import PDE.Analysis.Asymptotics.LaplaceMethod.Limit
import PDE.Analysis.Asymptotics.NonstationaryPhase.Decay
import PDE.Analysis.Asymptotics.NonstationaryPhase.Euclidean
import PDE.Analysis.Asymptotics.OscillatoryIntegral
import PDE.Analysis.Asymptotics.PeriodicAveraging
import PDE.Elliptic.OneDimensional.BoundaryLayer.Asymptotics
import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Expansion
import PDE.Hyperbolic.GeometricOptics.Limit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Asymptotic model identities

Gaussian model identities and Laplace limits with the actual Hessian,
nonstationary phase in Euclidean space, exact WKB residuals and their eikonal
limit, variable-coefficient boundary-layer matching, and periodic rescaling.
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
#doc (Manual) "Asymptotic Model Identities" =>

Gaussian integrals supply exactly evaluable models for Laplace's method and
stationary phase, in which a large parameter concentrates or oscillates the
integrand. In a differential equation the parameter also enters through
derivatives. A rapidly oscillating wave has an exact residual whose leading
terms determine the eikonal and transport equations, and a boundary layer
repairs a trace lost by the reduced equation.

:::theorem "methods.asymptotics.gaussian_integrals" (parent := "methods.representations") (lean := "integral_gaussian, integral_gaussian_complex")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "216-228"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The exact real and damped complex Gaussian integrals provide the normalization
identities

$$`
\int_{\mathbb R}e^{-b x^2}\,dx=\sqrt{\frac{\pi}{b}}
\quad(b>0),
\qquad
\int_{\mathbb R}e^{-\beta x^2}\,dx
=\left(\frac{\pi}{\beta}\right)^{1/2}
\quad(\operatorname{Re}\beta>0).
`

Both are Mathlib theorems, used by the model Laplace and stationary-phase
calculations.
:::

:::proof "methods.asymptotics.gaussian_integrals"
For real $`b>0`, substitute $`y=\sqrt b\,x` in the standard Gaussian
integral $`\int_{\mathbb R}e^{-y^2}\,dy=\sqrt\pi`. For complex $`\beta`
with positive real part, the damped Gaussian is absolutely integrable and
the standard complex Gaussian theorem evaluates it using the principal square
root.
:::

Laplace's method concerns $`\int g(x)e^{-\lambda\phi(x)}\,dx` as
$`\lambda\to\infty`, where the integral concentrates near the minimum of
$`\phi`. In the model case $`\phi(x)=x^2` with constant amplitude, the real
Gaussian formula evaluates the integral exactly.

:::theorem "methods.asymptotics.laplace_exact" (parent := "methods.representations") (lean := "PDE.Analysis.Asymptotics.laplaceConstantAmplitudeIntegral_eq, PDE.Analysis.Asymptotics.laplaceConstantAmplitudeIntegral") (uses := "methods.asymptotics.gaussian_integrals")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "216-218"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every positive parameter $`\lambda`, the normalized constant-amplitude
Gaussian integral is exactly $`\sqrt\pi c`:

$$`
\sqrt{\lambda}\int_{\mathbb R}c\,e^{-\lambda x^2}\,dx
=\sqrt{\pi}\,c.
`

The variable-phase {bpref "methods.asymptotics.laplace_limit"}[Laplace limit]
uses this Gaussian normalization after rescaling about the minimum.
:::

:::proof "methods.asymptotics.laplace_exact"
Pull the constant amplitude outside the integral and substitute
$`y=\sqrt\lambda\,x`. The Jacobian contributes $`\lambda^{-1/2}`, while the
Gaussian integral contributes $`\sqrt\pi`. Multiplication by the normalizing
factor $`\sqrt\lambda` leaves exactly $`\sqrt\pi\,c`.
:::

A nonlinear phase has the same leading Gaussian behavior when its quadratic
Taylor term controls concentration. Writing the large parameter as
$`\lambda=\varepsilon^{-2}` makes the relevant spatial scale explicit:
substitute $`y=\varepsilon x` and the normalization cancels the Jacobian.

:::theorem "methods.asymptotics.laplace_limit" (parent := "methods.representations") (lean := "PDE.Analysis.Asymptotics.tendsto_rescaled_stationary_phase, PDE.Analysis.Asymptotics.tendsto_laplace_integral") (uses := "methods.asymptotics.gaussian_integrals")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, Laplace's method"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\phi\in C^2(\mathbb R)` satisfy $`\phi(0)=\phi'(0)=0` and the
global lower bound $`\phi(y)\ge\delta y^2` for some $`\delta>0`.
Let $`a:\mathbb R\to E` be bounded and continuous, where $`E` is a real
Banach space. Then

$$`
\lim_{\varepsilon\downarrow0}\varepsilon^{-1}
\int_{\mathbb R}e^{-\phi(y)/\varepsilon^2}a(y)\,dy
=\sqrt{\frac{\pi}{\phi''(0)/2}}\,a(0).
`

The coefficient uses the actual second derivative of the phase. On a compact
integration set, the
{bpref "methods.asymptotics.laplace_euclidean"}[Euclidean version] derives
the required lower bound from a strict minimum and a positive Hessian, in
every finite dimension.
:::

:::proof "methods.asymptotics.laplace_limit"
After $`y=\varepsilon x`, Taylor's theorem gives
$`\phi(\varepsilon x)/\varepsilon^2\to\phi''(0)x^2/2` for each fixed
$`x`, and continuity gives $`a(\varepsilon x)\to a(0)`. If
$`\|a\|\le M`, the norm of the rescaled integrand is bounded by
$`M e^{-\delta x^2}`, independently of positive $`\varepsilon`.
This Gaussian is integrable. Dominated convergence passes the pointwise
limit through the Bochner integral, and the real Gaussian formula evaluates
the resulting integral. Thus the local Taylor coefficient and the global
tail bound supply different parts of the argument.
:::

The quadratic term in several variables is an ellipsoid rather than a
single coefficient. Its principal widths determine the Gaussian integral:
each positive Hessian eigenvalue contributes an inverse square root, and
their product is the inverse square root of the determinant.

:::theorem "methods.asymptotics.laplace_euclidean" (parent := "methods.representations") (lean := "PDE.Analysis.Asymptotics.tendsto_laplace_integral_compact, PDE.Analysis.Asymptotics.tendsto_laplace_integral_compact_atTop, PDE.Analysis.Asymptotics.tendsto_normalized_laplace_integral_compact, PDE.Analysis.Asymptotics.tendsto_normalized_laplace_integral_of_hasCompactSupport") (uses := "methods.asymptotics.gaussian_integrals, methods.asymptotics.laplace_limit")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, Laplace's method"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`K\subseteq\mathbb R^n` be compact and $`x_0\in\operatorname{int}K`.
Suppose $`\phi` is continuous on $`K`, is $`C^2` near $`x_0`, and
$`\phi(x)>\phi(x_0)` for every $`x\in K\setminus\{x_0\}`. Let
$`H=D^2\phi(x_0)` be its actual Hessian and assume
$`H[v,v]>0` for every nonzero $`v`. For an amplitude
$`a:\mathbb R^n\to E` continuous on $`K`, with $`E` a real Banach space,

$$`
\lim_{\varepsilon\downarrow0}\varepsilon^{-n}
\int_K e^{-(\phi(x)-\phi(x_0))/\varepsilon^2}a(x)\,dx
=\frac{(2\pi)^{n/2}}{\sqrt{\det H}}\,a(x_0).
`

Equivalently, the two large-parameter normalizations have the same limit:

$$`
\lim_{\lambda\to\infty}\lambda^{n/2}
\int_K e^{-\lambda(\phi(x)-\phi(x_0))}a(x)\,dx
=
\lim_{\lambda\to\infty}\lambda^{n/2}e^{\lambda\phi(x_0)}
\int_K e^{-\lambda\phi(x)}a(x)\,dx
=\frac{(2\pi)^{n/2}}{\sqrt{\det H}}\,a(x_0).
`

Stationarity at the interior minimum, symmetry of the Hessian, and the
quadratic lower bound used in the proof are derived from these hypotheses.
The result includes $`n=0`, where
the empty determinant and the Gaussian factor are one.

There is also a whole-space version for continuous compactly supported
$`a:\mathbb R^n\to E`. In that version, assume $`C^2` regularity near
$`x_0`, $`D\phi(x_0)=0`, positive Hessian, continuity of $`\phi` on
the topological support of $`a`, and
$`\phi(x)>\phi(x_0)` on that support away from $`x_0`.
The same exponentially normalized limit holds with $`\int_{\mathbb R^n}`.
The minimum need not belong to the support. In either version,
$`a(x_0)=0` is allowed and gives a zero limit.
:::

:::proof "methods.asymptotics.laplace_euclidean"
An interior minimum has zero first derivative. The $`C^2` Taylor estimate
and positivity of $`H` give
$`\phi(x)-\phi(x_0)\ge c_0|x-x_0|^2` near $`x_0`, for some $`c_0>0`.
Outside a smaller ball, compactness and strict minimality give a positive
gap above $`\phi(x_0)`. Since $`K` is bounded, this gap extends the
quadratic lower bound to all of $`K`, with a possibly smaller constant
$`c>0`.

Substitute $`x=x_0+\varepsilon z`. For fixed $`z`, the rescaled domain
eventually contains $`z` because $`x_0` is interior, and Taylor's theorem gives
$`(\phi(x_0+\varepsilon z)-\phi(x_0))/\varepsilon^2\to H[z,z]/2`.
The amplitude is bounded on $`K`, so the rescaled integrand, extended by
zero, is dominated by $`M e^{-c|z|^2}`. Dominated convergence leaves
$`a(x_0)\int_{\mathbb R^n}e^{-H[z,z]/2}\,dz`. Orthogonal
diagonalization evaluates this integral as
$`(2\pi)^{n/2}/\sqrt{\det H}`. Setting
$`\varepsilon=\lambda^{-1/2}` gives the large-parameter forms.

For the compact-amplitude version, adjoin a small closed ball about
$`x_0` to the support and apply the compact-domain theorem. Explicit
stationarity and Hessian positivity make $`x_0` a strict minimum on
that ball. The integral outside the support is zero.
:::

Oscillatory integrals are the counterpart in which the exponent is
imaginary, so cancellation rather than concentration is the mechanism. The
basic instance is the pure phase $`e^{i\omega t}`, whose antiderivative
$`e^{i\omega t}/(i\omega)` has modulus $`1/|\omega|`, giving a bound that
does not depend on the length of the interval.

:::theorem "methods.asymptotics.pure_oscillation" (parent := "methods.representations") (lean := "PDE.Analysis.norm_intervalIntegral_osc_le")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "218-228"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every nonzero real frequency, the complex phase
$`e^{i\omega t}` has interval integral bounded by $`2/|\omega|`, independently
of the interval length. The estimate is the elementary nonstationary
cancellation mechanism behind more elaborate high-frequency arguments.
:::

:::proof "methods.asymptotics.pure_oscillation"
Use the antiderivative $`e^{i\omega t}/(i\omega)`. The interval integral is
$`(e^{i\omega b}-e^{i\omega a})/(i\omega)`. Both endpoint exponentials have
norm one, so the triangle inequality bounds the numerator by two and gives
$`2/|\omega|`.
:::

Inserting a slowly varying amplitude $`f` costs one integration by parts:
the phase is integrated and the derivative moves onto $`f`. Values in a
complex Banach space are allowed because only the scalar phase is integrated
exactly.

:::theorem "methods.asymptotics.oscillatory_integration_by_parts" (parent := "methods.representations") (lean := "PDE.Analysis.norm_intervalIntegral_osc_smul_le_of_hasDerivAt, PDE.Analysis.norm_integral_osc_comp_smul_le, PDE.Analysis.exists_norm_integral_osc_comp_smul_le_pow, PDE.Analysis.NonstationaryPhase.exists_norm_integral_osc_smul_le_pow") (uses := "methods.asymptotics.pure_oscillation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "218-228"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\omega\ne0` and let $`f` take values in a complex Banach space. If
$`\|f(t)\|\le M` and $`\|f'(t)\|\le M'` on the unordered closed interval
with endpoints $`a,b`, integration by parts gives the explicit estimate

$$`
\left\|\int_a^b e^{i\omega t}f(t)\,dt\right\|
\le \frac{2M+|b-a|M'}{|\omega|}.
`

The theorem assumes pointwise differentiability on the unordered closed
interval and interval integrability of the derivative.

More generally, let $`\phi` be a real phase with two pointwise derivatives
on that closed interval, with $`\phi''` continuous there. If $`f'` is
continuous there and

$$`
|\phi'|\ge\delta>0,\quad |\phi''|\le K,\quad
\|f\|\le M,\quad \|f'\|\le M',
`

then the nonlinear-phase bound is

$$`
\left\|\int_a^b e^{i\omega\phi(t)}f(t)\,dt\right\|
\le
\frac{2M/\delta+|b-a|(M'/\delta+KM/\delta^2)}{|\omega|}.
`

The two endpoints contribute $`2M/\delta`; the amplitude need not vanish
there. For every-order decay, assume instead that $`\phi` and $`f` are
globally smooth, $`\phi'` is nowhere zero on $`\mathbb R`, and the
topological support of $`f` lies inside $`(a,b)`. For each $`k\in\mathbb N`
there is $`C_k\ge0`, independent of nonzero $`\omega`, such that

$$`
\left\|\int_a^b e^{i\omega\phi(t)}f(t)\,dt\right\|
\le C_k|\omega|^{-k}.
`

The whole-space theorem extends rapid decay to every $`n\in\mathbb N`:
let $`\phi:\mathbb R^n\to\mathbb R` be smooth, let
$`f:\mathbb R^n\to E` be smooth and compactly supported, with $`E` a complex
Banach space, and assume
$`d\phi(x)\ne0` on the topological support of $`f`. For each
$`k\in\mathbb N` there is $`C_k\ge0` such that

$$`
\left\|\int_{\mathbb R^n}e^{i\omega\phi(x)}f(x)\,dx\right\|
\le C_k|\omega|^{-k}\qquad(\omega\ne0).
`

Critical points of $`\phi` outside the support of $`f` are allowed.
:::

:::proof "methods.asymptotics.oscillatory_integration_by_parts"
Write $`e^{i\omega t}=(i\omega)^{-1}(e^{i\omega t})'` and integrate by
parts. The two boundary terms have total norm at most $`2M/|\omega|`.
The remaining integral is bounded by
$`|\omega|^{-1}\int_{\min(a,b)}^{\max(a,b)}\|f'(t)\|\,dt`, which is at most
$`|b-a|M'/|\omega|`. Adding the estimates proves the displayed bound.

For a nonlinear phase, use
$`(e^{i\omega\phi})'=i\omega\phi'e^{i\omega\phi}` and transfer the
derivative to $`g=f/\phi'`. The quotient rule gives
$`g'=f'/\phi'-\phi''f/(\phi')^2`, hence
$`\|g\|\le M/\delta` and
$`\|g'\|\le M'/\delta+KM/\delta^2`. The same integration-by-parts
estimate now proves the explicit bound.

For every-order decay, repeat the operation $`f\mapsto(f/\phi')'`.
Global smoothness and nonvanishing make every transferred amplitude smooth.
Division and differentiation preserve support inside the interval, so every
boundary term vanishes. Each integration by parts gains $`|\omega|^{-1}`;
a compact-interval integral bound at the last step supplies $`C_k`.

In Euclidean space the corresponding transfer is

$$`
Tf=\sum_j\partial_j\left(
\frac{\partial_j\phi}{|\nabla\phi|^2}f\right).
`

On the support of $`f`, nonstationarity makes the denominator nonzero.
Off that closed support the product is locally zero, even where the phase
is critical. Thus each normalized product is smooth everywhere, and taking
its divergence preserves smoothness and keeps its support inside the
original compact set. Coordinate integration by parts gives

$$`
i\omega\int e^{i\omega\phi}f=-\int e^{i\omega\phi}Tf.
`

The compact support removes boundary terms and justifies the finite
sum of integrals. Iterate this identity: each step gains
$`|\omega|^{-1}`, and the final amplitude's $`L^1` norm bounds the
remaining integral. This constructs the decay constants from the amplitude.
:::

Stationary phase replaces the real exponent $`-\lambda x^2` by the imaginary
one $`i\lambda x^2`, whose critical point $`x=0` is where the phase is
stationary. A damping $`-\varepsilon x^2` with $`\varepsilon>0` makes the
integrand absolutely integrable, and the complex Gaussian formula with
$`\beta=\varepsilon-i\lambda`, whose real part is $`\varepsilon`, evaluates
the damped integral exactly.

For $`\varepsilon>0` and $`\lambda\in\mathbb R`, this gives

$$`
\int_{\mathbb R}
\exp\!\left(-(\varepsilon-i\lambda)x^2\right)\,dx
=\left(\frac{\pi}{\varepsilon-i\lambda}\right)^{1/2}.
`

The square root is the principal complex square root.

The same oscillatory exponential appears in geometric optics, now inside
a differential equation. Write spacetime as $`z=(t,x)\in\mathbb R^{n+1}`
and use the wave operator $`\Box=\partial_t^2-\Delta_x`. For real
amplitude $`a` and real phase $`p`, the complex ansatz is
$`U_\varepsilon=a e^{ip/\varepsilon}`. Differentiating the phase once
costs $`\varepsilon^{-1}`; differentiating twice separates the wave
residual into three orders.

:::theorem "methods.asymptotics.wkb_residual" (parent := "methods.representations") (lean := "WaveEquation.GeometricOptics.waveOperator_wavePacket_frequency, WaveEquation.GeometricOptics.scaled_waveOperator_wavePacket, WaveEquation.GeometricOptics.waveOperator_wavePacket_eq_zero_iff")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.5.3, Example 3, geometric optics"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose $`a,p` are $`C^2` near the point of evaluation and
$`\varepsilon\ne0`. Define the eikonal defect and transport expression by

$$`
E(p)=p_t^2-|\nabla_xp|^2,\qquad
T(a,p)=a\Box p+2(p_ta_t-\nabla_xp\cdot\nabla_xa).
`

The actual complex wave residual is

$$`
\Box U_\varepsilon
=e^{ip/\varepsilon}
\left(\Box a+\frac{i}{\varepsilon}T(a,p)
-\frac{a}{\varepsilon^2}E(p)\right).
`

Equivalently,
$`\varepsilon^2\Box U_\varepsilon
=e^{ip/\varepsilon}(\varepsilon^2\Box a-aE(p)+i\varepsilon T(a,p))`.
Since the exponential never vanishes and the two coefficients are real,

$$`
\Box U_\varepsilon=0
\quad\Longleftrightarrow\quad
aE(p)=\varepsilon^2\Box a
\quad\hbox{and}\quad T(a,p)=0.
`

The equivalence holds whether or not $`a` vanishes.
:::

:::proof "methods.asymptotics.wkb_residual"
For any time or space coordinate $`j`, the product and chain rules give

$$`
\partial_j^2(ae^{ip/\varepsilon})
=e^{ip/\varepsilon}
\left(\partial_j^2a+
\frac{i}{\varepsilon}(a\,\partial_j^2p+2\partial_jp\,\partial_ja)
-\frac{a}{\varepsilon^2}(\partial_jp)^2\right).
`

Subtract the spatial terms from the time term. Multiplication by
$`\varepsilon^2` removes the negative powers, and taking real and
imaginary parts after cancelling the exponential gives the equivalence.
The derivatives here are those of the displayed ansatz.
:::

:::theorem "methods.asymptotics.wkb_eikonal_limit" (parent := "methods.representations") (lean := "WaveEquation.GeometricOptics.squared_eikonal_of_wavePacket_family") (uses := "methods.asymptotics.wkb_residual")
Fix a spacetime point $`z`. Let $`a_\varepsilon,p_\varepsilon` be real
families which are $`C^2` near $`z` and satisfy the actual equation
$`\Box(a_\varepsilon e^{ip_\varepsilon/\varepsilon})(z)=0` for all
sufficiently small positive $`\varepsilon`. Suppose, as
$`\varepsilon\downarrow0`,

$$`
a_\varepsilon(z)\longrightarrow a_0\ne0,\qquad
\partial_jp_\varepsilon(z)\longrightarrow\partial_jp_0(z)
\quad(0\le j\le n),\qquad
\varepsilon^2\Box a_\varepsilon(z)\longrightarrow0,
`

where $`p_0` is differentiable at $`z`. Then the limiting phase satisfies
the squared eikonal equation

$$`
(\partial_tp_0(z))^2=|\nabla_xp_0(z)|^2.
`

The result is pointwise and chooses no sign for $`\partial_tp_0`.
:::

:::proof "methods.asymptotics.wkb_eikonal_limit"
The exact residual equivalence gives
$`a_\varepsilon(z)E(p_\varepsilon)(z)
=\varepsilon^2\Box a_\varepsilon(z)`.
Finite sums and products preserve the stated limits, so
$`a_0 E(p_0)(z)=0`. Cancelling the nonzero number $`a_0` gives the
conclusion. The scaled amplitude residual is a hypothesis in this
argument; the full wave residual is zero because the family solves the PDE.
:::

Cancelling the eikonal and transport terms alone leaves $`\Box a`.
For $`a(t,x,y)=y^2` and $`p(t,x,y)=t-x`, both $`E(p)` and $`T(a,p)`
vanish, but

$$`
\Box\!\left(y^2e^{i(t-x)/\varepsilon}\right)
=-2e^{i(t-x)/\varepsilon},\qquad
\left|\Box\!\left(y^2e^{i(t-x)/\varepsilon}\right)\right|=2.
`

Thus the unscaled residual does not tend to zero, although
$`\varepsilon^2\Box a=-2\varepsilon^2\to0`. At $`(0,0,1)` the
amplitude is one and the residual is always $`-2`, so the distinction
persists at a nonzero amplitude. This family does not solve the wave
equation, so the eikonal limit theorem does not apply to it.

The phase has $`p_t=1`, $`p_x=-1`, $`p_y=0` and zero second
derivatives. The amplitude has $`a_t=a_x=0` and $`a_{yy}=2`.
Substitution into the exact residual identity gives the formula; the
complex exponential has norm one. The calculation and failure of convergence
are checked in `PDE/Examples/Hyperbolic/GeometricOptics.lean`.

When a small parameter multiplies the highest derivative of an equation,
setting it to zero can remove a boundary condition. The discrepancy need
not be small near that boundary. An explicit convection-diffusion problem
shows both the failure of uniform outer convergence and the correction
that restores it.

:::theorem "methods.asymptotics.boundary_layer" (parent := "methods.representations") (lean := "PDE.Elliptic.BoundaryLayer.solution_contDiff, PDE.Elliptic.BoundaryLayer.solution_equation, PDE.Elliptic.BoundaryLayer.solution_zero, PDE.Elliptic.BoundaryLayer.solution_right, PDE.Elliptic.BoundaryLayer.outer_equation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4, §4.5.1, boundary layers"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\varepsilon,b,L>0` and $`A,B,f\in\mathbb R`. Define the
outer solution and its left boundary mismatch by

$$`
v(x)=B+\frac fb(x-L),\qquad D=A-v(0).
`

The smooth function

$$`
u_\varepsilon(x)=v(x)+D\,
\frac{e^{-bx/\varepsilon}-e^{-bL/\varepsilon}}
{1-e^{-bL/\varepsilon}}
`

satisfies the actual differential equation
$`\varepsilon u_\varepsilon''+bu_\varepsilon'=f`, with
$`u_\varepsilon(0)=A` and $`u_\varepsilon(L)=B`.
The reduced function satisfies $`bv'=f` and $`v(L)=B`.
:::

:::proof "methods.asymptotics.boundary_layer"
Positive $`b,L,\varepsilon` make the denominator strictly positive.
At zero the normalized exponential correction is one; at $`L` it is
zero. The two endpoint conditions follow. Differentiate the constructed
function twice. The exponential terms in
$`\varepsilon u_\varepsilon''+bu_\varepsilon'` cancel, leaving
$`bv'=f`.
:::

:::theorem "methods.asymptotics.boundary_layer_matching" (parent := "methods.representations") (lean := "PDE.Elliptic.BoundaryLayer.interior_error_le, PDE.Elliptic.BoundaryLayer.solution_tendstoUniformlyOn, PDE.Elliptic.BoundaryLayer.composite_error_le, PDE.Elliptic.BoundaryLayer.composite_remainder_tendstoUniformlyOn, PDE.Elliptic.BoundaryLayer.not_solution_tendstoUniformlyOn, PDE.Elliptic.BoundaryLayer.solution_stretched_tendsto, PDE.Elliptic.BoundaryLayer.inner_matching_tendsto") (uses := "methods.asymptotics.boundary_layer")
Under the same assumptions, for every fixed $`\delta>0` and
$`x\in[\delta,L]`,

$$`
|u_\varepsilon(x)-v(x)|
\le \frac{|D|e^{-b\delta/\varepsilon}}{1-e^{-bL/\varepsilon}}.
`

Thus $`u_\varepsilon\to v` uniformly away from the left endpoint as
$`\varepsilon\downarrow0`. If $`D\ne0`, uniform convergence to $`v`
on $`[0,L]` fails: the error at zero is always $`|D|`.
The composite approximation $`w_\varepsilon(x)=v(x)+De^{-bx/\varepsilon}`
instead satisfies, throughout $`[0,L]`,

$$`
|u_\varepsilon(x)-w_\varepsilon(x)|
\le\frac{|D|e^{-bL/\varepsilon}}{1-e^{-bL/\varepsilon}},
`

and this remainder tends uniformly to zero. At each fixed stretched
coordinate $`y`,
$`u_\varepsilon(\varepsilon y)\to v(0)+De^{-by}`.
For $`y\ge0` this is the physical left layer, whose limit as
$`y\to\infty` matches $`v(0)`.
:::

:::proof "methods.asymptotics.boundary_layer_matching"
The exponential decreases with $`x`, so the exact correction is bounded
by its value at $`\delta`, divided by the positive normalization.
Subtracting the unnormalized layer from the exact correction leaves
$`De^{-bL/\varepsilon}(e^{-bx/\varepsilon}-1)/(1-e^{-bL/\varepsilon})`.
On $`[0,L]`, the absolute value of the parenthesized term is at most one.
These bounds tend to zero independently of position on the stated sets.
The fixed nonzero endpoint discrepancy rules out uniform outer convergence.
Finally substitute $`x=\varepsilon y`; the left exponential becomes
$`e^{-by}`, while the right-end tail vanishes and $`v(\varepsilon y)\to v(0)`.
Letting $`y\to\infty` proves matching.
:::

For variable drift, the reduced equation still determines a solution from
the right endpoint. Its curvature creates a new error: substituting the
outer solution into the full equation leaves $`\varepsilon v''`.
A homogeneous correction repairs the left trace exactly; comparison
controls the remaining curvature term.

:::theorem "methods.asymptotics.variable_boundary_layer" (parent := "methods.representations") (lean := "PDE.Elliptic.BoundaryLayer.Variable.exists_expansion, PDE.Elliptic.BoundaryLayer.Variable.Expansion.equation, PDE.Elliptic.BoundaryLayer.Variable.Expansion.exact_error, PDE.Elliptic.BoundaryLayer.Variable.Expansion.composite_error_with_tail, PDE.Elliptic.BoundaryLayer.Variable.Expansion.composite_error") (uses := "methods.asymptotics.boundary_layer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.5.1, boundary layers"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`L,\alpha>0`, let $`a,f` be $`C^1` on an open neighborhood of
$`[0,L]`, and assume $`a(x)\ge\alpha` throughout that interval.
For arbitrary real boundary values $`A,B`, the construction supplies a
family of classical solutions, for every $`\varepsilon>0`, with

$$`
\varepsilon u_\varepsilon''+a(x)u_\varepsilon'=f(x),\qquad
u_\varepsilon(0)=A,\quad u_\varepsilon(L)=B.
`

The solutions have $`C^2` extensions and satisfy the equation on the
closed interval. Define

$$`
v(x)=B-\int_x^L\frac{f(s)}{a(s)}\,ds,\qquad
D=A-v(0),\qquad b=a(0),\qquad \mu=\alpha/2.
`

The construction, not the statement, fixes constants $`M,K\ge0`, independent of
$`\varepsilon`, with $`|(f/a)'|\le M` and
$`|a(x)-a(0)|\le Kx` on $`[0,L]`, and it puts $`C=bK/\mu^3`.
The constructed homogeneous correction $`H_\varepsilon` satisfies
$`\varepsilon H_\varepsilon''+aH_\varepsilon'=0`,
$`H_\varepsilon(0)=1`, $`H_\varepsilon(L)=0`, and
$`0\le H_\varepsilon(x)\le e^{-\alpha x/\varepsilon}`. For
$`x\in[0,L]`,

$$`
|u_\varepsilon(x)-v(x)-D H_\varepsilon(x)|
\le\frac{\varepsilon M(L-x)}{\alpha},
\qquad
|H_\varepsilon(x)-e^{-bx/\varepsilon}|
\le C\varepsilon e^{-\mu x/\varepsilon}+e^{-bL/\varepsilon}.
`

Consequently the frozen composite
$`w_\varepsilon(x)=v(x)+De^{-bx/\varepsilon}` obeys

$$`
\begin{aligned}
|u_\varepsilon(x)-w_\varepsilon(x)|
&\le\frac{\varepsilon M(L-x)}{\alpha}
 +|D|\left(C\varepsilon e^{-\mu x/\varepsilon}+e^{-bL/\varepsilon}\right)\\
&\le\varepsilon\left(\frac{ML}{\alpha}
 +|D|\left(C+\frac{1}{bL}\right)\right).
\end{aligned}
`

The finite-interval tail $`e^{-bL/\varepsilon}` is present even when
$`K=0`: at $`x=L`, the difference between $`H_\varepsilon` and the
frozen exponential is exactly $`e^{-bL/\varepsilon}`.
:::

:::proof "methods.asymptotics.variable_boundary_layer"
An integrating factor constructs the classical solutions and the
homogeneous correction with both traces. The reduced function satisfies
$`av'=f` and $`v''=(f/a)'` in the interior. Therefore
$`r_\varepsilon=u_\varepsilon-v-DH_\varepsilon` has zero boundary
values and solves
$`\varepsilon r_\varepsilon''+ar_\varepsilon'=-\varepsilon v''`.
The affine barriers $`\pm\varepsilon M(L-x)/\alpha` bound this
remainder by scalar comparison.

Freezing the coefficient produces the residual
$`b(b-a(x))e^{-bx/\varepsilon}/\varepsilon`.
The variation bound and exponential decay control it by a multiple of
$`e^{-\mu x/\varepsilon}`. Adding and subtracting
$`C\varepsilon e^{-\mu x/\varepsilon}+e^{-bL/\varepsilon}`
from $`e^{-bx/\varepsilon}` gives comparison barriers for
$`H_\varepsilon`. The constant tail supplies the right boundary
inequality. Adding the two error bounds proves the composite estimate,
and $`e^{-bL/\varepsilon}\le\varepsilon/(bL)` gives its uniform
linear bound.
:::

:::theorem "methods.asymptotics.variable_boundary_matching" (parent := "methods.representations") (lean := "PDE.Elliptic.BoundaryLayer.Variable.Expansion.outer_convergence, PDE.Elliptic.BoundaryLayer.Variable.Expansion.outer_convergence_of_match, PDE.Elliptic.BoundaryLayer.Variable.Expansion.not_outer_convergence, PDE.Elliptic.BoundaryLayer.Variable.Expansion.exact_remainder_convergence, PDE.Elliptic.BoundaryLayer.Variable.Expansion.composite_convergence, PDE.Elliptic.BoundaryLayer.Variable.Expansion.inner_convergence, PDE.Elliptic.BoundaryLayer.Variable.Expansion.matching, PDE.Elliptic.BoundaryLayer.Variable.Expansion.inner_nonconstant") (uses := "methods.asymptotics.variable_boundary_layer")
For the constructed family, $`u_\varepsilon\to v` uniformly on every
$`[\delta,L]` with $`\delta>0`, as $`\varepsilon\downarrow0`.
Convergence is uniform on $`[0,L]` exactly when $`D=0`.
Both the exact-correction remainder
$`u_\varepsilon-v-DH_\varepsilon` and the frozen composite remainder
$`u_\varepsilon-w_\varepsilon` tend uniformly to zero on $`[0,L]`.

At each fixed physical stretched coordinate $`y\ge0`,

$$`
u_\varepsilon(\varepsilon y)\longrightarrow
v(0)+De^{-by}.
`

This inner profile tends to $`v(0)` as $`y\to\infty` and is
nonconstant if $`D\ne0`.
:::

:::proof "methods.asymptotics.variable_boundary_matching"
The outer error is bounded by
$`|D|e^{-\alpha x/\varepsilon}+\varepsilon M(L-x)/\alpha`.
On $`[\delta,L]`, both terms tend to zero uniformly; when $`D=0`,
the same bound works on the whole interval. When $`D\ne0`, the error
at zero is always $`|D|`, which rules out uniform outer convergence.
The remainder estimates already hold uniformly up to both endpoints.
For fixed $`y\ge0`, the point $`\varepsilon y` eventually lies in
$`[0,L]`. Evaluate the composite estimate there and use
$`v(\varepsilon y)\to v(0)`. The frozen exponential becomes
$`e^{-by}`; positivity of $`b` gives matching as $`y\to\infty`.
:::

Periodic averaging is asymptotics of a different kind: the small parameter
is the period $`\varepsilon=1/N` of an oscillating coefficient
$`a(x/\varepsilon)`, and the leading behaviour is governed by the mean of
$`a` over one cell. The elementary fact behind this is a Mathlib theorem,
used here with unit period.

:::theorem "methods.asymptotics.periodic_cell_integral" (parent := "methods.representations") (lean := "Function.Periodic.intervalIntegral_add_zsmul_eq")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "229-232"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The integral of a locally integrable periodic function over an integer number
of cells is that integer times its one-cell integral. If $`a(x+1)=a(x)` and
$`a` is integrable on $`[0,1]`, then

$$`
\int_0^N a(x)\,dx=N\int_0^1a(x)\,dx
\qquad(N\in\mathbb N).
`
:::

:::proof "methods.asymptotics.periodic_cell_integral"
Partition $`[0,N]` into the unit intervals $`[k,k+1]`. Translation by the
integer $`k` and one-periodicity give integrability on each cell and identify
its integral with $`\int_0^1a`. Additivity of the interval integral then gives $`N` identical
summands.
:::

A change of variables and the cell identity show that the rescaled
coefficient has the same mean at every integer frequency, which is the exact
form of the statement that rapid oscillation does not change the average.

:::theorem "methods.asymptotics.periodic_average" (parent := "methods.representations") (lean := "PDE.Analysis.Asymptotics.periodicCellAverage_integerRescaling") (uses := "methods.asymptotics.periodic_cell_integral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "229-232"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a one-periodic interval-integrable function, positive-integer rescaling
preserves the average over one cell:

$$`
\int_0^1a((N+1)x)\,dx=\int_0^1a(x)\,dx
\qquad(N\in\mathbb N).
`

This is an exact identity used in the elementary algebra of periodic
homogenization.
:::

:::proof "methods.asymptotics.periodic_average"
Substitute $`y=(N+1)x`; the left side becomes
$`(N+1)^{-1}\int_0^{N+1}a(y)\,dy`. The periodic-cell identity evaluates the
last integral as $`(N+1)\int_0^1a`, and cancellation of the positive integer
factor proves the claim.
:::
