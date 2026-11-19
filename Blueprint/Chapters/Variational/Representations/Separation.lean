/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Fluid
import PDE.Analysis.Spectral.HilbertBasis
import PDE.Hyperbolic.Models.Wave.SeparationOfVariables
import PDE.Examples.Hyperbolic.Symbolic.Wave.SeparationOfVariables
import PDE.Parabolic.Heat.SeparationOfVariables
import PDE.Parabolic.Symbolic.Heat.SeparationOfVariables
import PDE.Representations.SeparationOfVariables

/-!
# Separation of variables and spectral expansions

Product calculations, explicit heat and wave modes, and the Hilbert-basis
convergence and truncation estimates behind spectral expansions.
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
#doc (Manual) "Separation of Variables and Spectral Expansions" =>

:::group "methods.representations"
Representation methods
:::

# Separation of variables

The two product calculations are identities for totalized derivative
residuals: their only hypotheses are the displayed derivative identities.
The interval modes are built from the Dirichlet eigenfunctions of
$`-d^2/dx^2` on the unit interval.

:::definition "methods.separation.dirichlet_sine_mode" (parent := "methods.representations") (lean := "PDE.Representations.intervalDirichletSineMode, PDE.Representations.intervalDirichletEigenvalue")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "168-169"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`n\in\mathbb N`, the $`n`th unit-interval Dirichlet sine mode and its
eigenvalue are

$$`
w_n(x)=\sin\bigl((n+1)\pi x\bigr),\qquad
\lambda_n=\bigl((n+1)\pi\bigr)^2.
`

Indexing starts at zero, so every mode has a positive frequency. These are
the one-dimensional instance of the Dirichlet eigenfunctions
$`-\Delta w=\lambda w` in $`U`, $`w=0` on $`\partial U`, in which Evans's
separation of variables expands the solution.
:::

:::theorem "methods.separation.dirichlet_sine_mode_eigenfunction" (parent := "methods.representations") (lean := "PDE.Representations.intervalDirichletSineMode_second_deriv, PDE.Representations.intervalDirichletSineMode_zero, PDE.Representations.intervalDirichletSineMode_one, PDE.Representations.intervalDirichletSineMode_nontrivial") (uses := "methods.separation.dirichlet_sine_mode")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "168-169"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Each sine mode is a nontrivial Dirichlet eigenfunction on the unit interval:
for every $`x\in\mathbb R`,

$$`
w_n''(x)=-\lambda_n\,w_n(x),
`

together with the endpoint traces $`w_n(0)=w_n(1)=0` and
$`w_n\not\equiv0`.
:::

:::proof "methods.separation.dirichlet_sine_mode_eigenfunction"
Set $`a=(n+1)\pi`. Differentiating $`x\mapsto\sin(ax)` twice with the chain
rule gives $`-a^2\sin(ax)`, which is $`-\lambda_nw_n(x)`. The traces follow
from $`\sin0=0` and $`\sin((n+1)\pi)=0`. Evaluating at
$`x=1/(2(n+1))` gives $`\sin(\pi/2)=1\neq0`, so the mode is nontrivial.
:::

Separation of variables reverses the order of this reasoning. Instead of
starting from a known eigenfunction, it assumes only that a spatial factor
$`X` and a time factor $`T` satisfy ordinary differential equations with a
common constant $`\lambda`, and asks what the product $`X(x)T(t)` then
satisfies. For the heat equation the time equation is first order,
$`T'=-\lambda T`, because $`u_t` differentiates $`T` once.

:::theorem "methods.separation.heat.product" (parent := "methods.representations") (lean := "HeatEquation.separated_heat_residual_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "168-170"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If

$$`
X''=-\lambda X,\qquad T'=-\lambda T,
`

then $`u(t,x)=X(x)T(t)` satisfies

$$`
u_t-u_{xx}=0.
`
:::

:::proof "methods.separation.heat.product"
The constant-multiple rule gives $`u_t=XT'` and $`u_{xx}=X''T`. Substituting
$`T'=-\lambda T` and $`X''=-\lambda X` makes both expressions equal to
$`-\lambda XT`, so their difference is zero.
:::

Taking $`X=w_n` and $`T(t)=e^{-\lambda_nt}` in the product calculation gives
the residual identity for the interval heat mode: the eigenfunction theorem
supplies $`X''=-\lambda_nX`, and the exponential supplies $`T'=-\lambda_nT`.

:::theorem "methods.separation.heat.interval" (parent := "methods.representations") (lean := "HeatEquation.intervalHeatMode_satisfies_heat_dirichlet_ivp") (uses := "methods.separation.dirichlet_sine_mode")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "168-170"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every positive Dirichlet sine frequency on the unit interval, the
mode

$$`
u_n(t,x)=\sin((n+1)\pi x)
\exp\!\left(-((n+1)\pi)^2t\right)
`

is jointly $`C^2` and satisfies $`u_t-u_{xx}=0`, $`u_n(t,0)=u_n(t,1)=0`,
and $`u_n(0,x)=\sin((n+1)\pi x)`.
:::

:::proof "methods.separation.heat.interval" (uses := "methods.separation.heat.product, methods.separation.dirichlet_sine_mode_eigenfunction")
The sine eigenfunction and exponential time factor satisfy the two separated
ordinary differential equations. The product calculation gives the heat
residual, while direct evaluation gives the two boundary traces and initial
trace. The product of a sine and an exponential is smooth, hence jointly
$`C^2`.
:::

The wave equation differentiates twice in time, so the same product ansatz
reduces to a pair of oscillator equations with one constant:
$`X''=-\lambda X` for the spatial factor and $`T''=-\lambda T` for the
time factor. Only the time equation changes between the heat and wave
calculations.

:::theorem "methods.separation.wave.product" (parent := "methods.representations") (lean := "WaveEquation.separated_wave_residual_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If

$$`
X''=-\lambda X,\qquad T''=-\lambda T,
`

then $`u(t,x)=X(x)T(t)` satisfies $`u_{tt}-u_{xx}=0`. For positive
$`\lambda` the time factor oscillates, where the heat time factor decays.
:::

:::proof "methods.separation.wave.product"
Differentiate the product twice in each variable:
$`u_{tt}=XT''` and $`u_{xx}=X''T`. The two oscillator equations identify
both with $`-\lambda XT`, hence $`u_{tt}-u_{xx}=0`.
:::

For the interval wave mode the time factor is $`\sin((n+1)\pi t)`, the same
function as the spatial mode $`w_n`, so it satisfies $`T''=-\lambda_nT` by
the eigenfunction theorem already proved. Since $`T(0)=0` and
$`T'(0)=(n+1)\pi`, this mode carries zero initial displacement and a nonzero
initial velocity; a cosine time factor would exchange those two roles.

:::theorem "methods.separation.wave.interval" (parent := "methods.representations") (lean := "WaveEquation.intervalWaveMode_satisfies_wave_dirichlet_ivp") (uses := "methods.separation.dirichlet_sine_mode")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The interval mode

$$`
u_n(t,x)=\sin((n+1)\pi x)\sin((n+1)\pi t)
`

is jointly $`C^2` and satisfies $`u_{tt}-u_{xx}=0`, homogeneous Dirichlet
boundary conditions, $`u_n(0,x)=0`, and
$`\partial_tu_n(0,x)=(n+1)\pi\sin((n+1)\pi x)`. It is a concrete wave
analogue of the separated boundary-value calculations in Evans §4.1.
:::

:::proof "methods.separation.wave.interval" (uses := "methods.separation.wave.product, methods.separation.dirichlet_sine_mode_eigenfunction")
The sine factors solve oscillator equations with the same eigenvalue. The
product calculation supplies the wave residual, and the boundary and initial
conditions follow from sine identities and a derivative at time zero. The product of two
sines is smooth, hence jointly $`C^2`.
:::

The modes $`e^{-t}\sin x` and $`\sin t\sin x` are the $`\lambda=1` instances
of the two product calculations, with $`X=\sin x` and $`T=e^{-t}` or
$`T=\sin t`, taken on all of $`\mathbb R^2` with no boundary condition
attached. They are proved differently: a verified symbolic
differentiator computes the closed-form residual, and a bridge theorem
identifies the symbolic derivatives with Euclidean partial derivatives, so
the analytic residual vanishes as well.

:::theorem "methods.separation.heat.symbolic_mode" (parent := "methods.representations") (lean := "HeatEquation.Symbolic.Space1.separatedHeatMode1D_analytic_residual_eq_zero") (uses := "methods.separation.heat.product")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "168-170"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The explicit mode

$$`u(t,x)=e^{-t}\sin x`

has zero analytic heat residual on all of one-dimensional spacetime.
:::

:::proof "methods.separation.heat.symbolic_mode"
The verified differentiator computes $`u_t=-e^{-t}\sin x` and
$`u_{xx}=-e^{-t}\sin x`; normalization therefore proves the symbolic
residual is zero. The analytic bridge proves that these symbolic derivatives
equal the corresponding Euclidean partial derivatives everywhere, so the
ordinary heat residual also vanishes.
:::

The wave example replaces the exponential time factor by $`\sin t`:

$$`u(t,x)=\sin t\sin x`

Symbolic differentiation gives $`u_{tt}=-\sin t\sin x` and
$`u_{xx}=-\sin t\sin x`. The verified normalizer cancels the two expressions,
and the derivative bridge transports that exact symbolic identity to the
analytic wave residual. This is an instance of the
{bpref "methods.separation.wave.product"}[product calculation].

## Abstract spectral expansions

A single separated mode solves the equation but matches only its own initial
datum. Representing general data requires expanding in the whole family
$`(e_i)`. Here that family is an arbitrary Hilbert basis of an inner
product space $`H` over $`\mathbb R` or $`\mathbb C`.

:::theorem "methods.spectral.expansion" (parent := "methods.representations") (lean := "HilbertBasis.hasSum_repr")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For any Hilbert basis $`(e_i)` and any vector $`u`, the Fourier coefficients
$`\langle e_i,u\rangle` reconstruct `u`: the net of finite sums
$`\sum_i\langle e_i,u\rangle e_i` converges to `u` in the Hilbert norm. This
is Mathlib's basis theorem behind Evans's eigenfunction-series method.
:::

:::proof "methods.spectral.expansion"
Mathlib defines a Hilbert basis by its coefficient map, a linear isometric
equivalence onto the square-summable sequences; it sends $`u` to the sequence
of its coefficients. Such a sequence is the sum, in the sequence norm, of its
single-entry pieces. The inverse isometry is continuous and maps each piece to
the coefficient times the basis vector in $`H`, so the expansion converges to $`u`.
:::

The expansion converges as a net indexed by finite subsets of the index set.
Spectral methods truncate an $`\mathbb N`-indexed basis to the initial
segments $`\{0,\dots,N-1\}`, and this unconditional convergence covers them in
particular.

:::theorem "methods.spectral.partial_sums" (parent := "methods.representations") (lean := "HasSum.tendsto_sum_nat") (uses := "methods.spectral.expansion")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a basis indexed by the natural numbers, the conventional first-`N`
partial sums converge in norm:

$$`
\sum_{n=0}^{N-1}\langle e_n,u\rangle e_n
\longrightarrow u.
`
:::

:::proof "methods.spectral.partial_sums"
The basis expansion gives convergence of the net over all finite index sets.
The initial segments $`\{0,\dots,N-1\}` eventually contain every fixed finite
set. Restricting the convergent net to these initial segments gives
$`\sum_{n<N}\langle e_n,u\rangle e_n\to u` in norm.
:::

Norm convergence of the expansion is the qualitative statement; Parseval's
identity is its quantitative counterpart, obtained by taking the squared norm
on both sides and using orthonormality to remove the cross terms. The
coefficients are written $`\langle e_n,u\rangle` with the basis vector in the
first slot, following Mathlib's convention for which argument is
conjugate-linear.

:::theorem "methods.spectral.parseval" (parent := "methods.representations") (lean := "PDE.Analysis.Spectral.hilbertBasis_parseval_norm_sq") (uses := "methods.spectral.expansion")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The squared Hilbert norm is exactly the sum of the squared norms of the
Hilbert-basis coefficients:

$$`
\sum_{n=0}^{\infty}
\left\lVert\langle e_n,u\rangle\right\rVert^2
=\lVert u\rVert^2.
`
:::

:::proof "methods.spectral.parseval"
Mathlib's coefficient map is a linear isometry onto the square-summable
sequences, and the coefficient of each index is the inner product with that
basis vector. The squared norm of a square-summable sequence is the sum of the
squared norms of its entries. Applying this to the coefficient sequence and
using that the isometry preserves norms yields Parseval's identity.
:::

Subtracting the first $`N` terms from $`u` leaves a vector whose nonzero
coefficients are exactly the omitted ones, so Parseval applied to that
difference converts the truncation error into a coefficient sum.

:::theorem "methods.spectral.tail_identity" (parent := "methods.representations") (lean := "PDE.Analysis.Spectral.hilbertBasis_spectralResidual_norm_sq_eq_tsum_tail") (uses := "methods.spectral.partial_sums, methods.spectral.parseval")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The squared error of the first-`N` approximation is exactly the sum of the
squared omitted coefficients:

$$`
\left\lVert
u-\sum_{n=0}^{N-1}\langle e_n,u\rangle e_n
\right\rVert^2
=\sum_{k=0}^{\infty}
\left\lVert\langle e_{k+N},u\rangle\right\rVert^2.
`

This is the quantitative identity behind
spectral truncation and Galerkin approximation estimates.
:::

:::proof "methods.spectral.tail_identity"
Split the series of squared coefficient norms after its first $`N` terms; the
tail is indexed by $`k+N`. Orthonormality makes the squared truncation error
equal to the squared norm minus the retained squared coefficients, and Parseval
identifies the squared norm with the full series. Hence, with $`k\in\mathbb N`,
the error equals the tail, which is the displayed formula.
:::

The tail identity by itself gives no rate, since it only rearranges the
coefficients. A rate appears once the coefficients are known to decay: if
$`\sum_n(n+1)^q\lVert\langle e_n,u\rangle\rVert^2` is finite, then every
omitted index satisfies $`k+N\ge N`, so the monotone weight $`(N+1)^q` can be
pulled out of the tail and compared termwise with the weighted energy. For
eigenfunction expansions such weighted summability is a regularity statement
about $`u`, expressed spectrally.

:::theorem "methods.spectral.polynomial_rate" (parent := "methods.representations") (lean := "PDE.Analysis.Spectral.hilbertBasis_spectralResidual_norm_sq_le_polynomial") (uses := "methods.spectral.tail_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "167-172"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`q\in\mathbb N`, if the coefficient energy weighted by $`(n+1)^q` is summable, then the
first-`N` squared truncation error is bounded by that weighted energy divided
by $`(N+1)^q`.
:::

:::proof "methods.spectral.polynomial_rate" (uses := "methods.spectral.tail_identity")
Multiply the exact omitted tail by the monotone weight at index `N`, compare
it termwise with the weighted tail, and divide by the strictly positive
quantity $`(N+1)^q`.
:::
