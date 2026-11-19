/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.AutomaticDifferentiation
import PDE.Elliptic.Symbolic.Radial.Logarithmic
import PDE.Elliptic.Symbolic.Radial.Newtonian
import PDE.Elliptic.Symbolic.VariationalIntegrands
import PDE.Examples.Hyperbolic.Models.Transport.RightMovingSine
import PDE.Examples.Hyperbolic.Symbolic.Transport.Integrand
import PDE.Examples.Hyperbolic.Symbolic.Wave.TravelingSine
import PDE.Parabolic.Heat.Gaussian
import PDE.Parabolic.Symbolic.Heat.Gaussian
import PDE.Parabolic.Symbolic.Heat.Polynomial

/-!
## Symbolic PDE examples

Theorem-facing symbolic computations for representative PDE solutions.
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
#doc (Manual) "Symbolic PDE Theorem API" =>

:::group "symbolic.theorem_api"
Symbolic PDE proofs
:::

To check a proposed heat profile, we hold space fixed while differentiating
in time, then hold time fixed while taking the spatial Laplacian. In the
library's spacetime coordinates $`p=(t,x,y)`, time is coordinate zero, so the
calculation is

$$`\partial_0u-\partial_1^2u-\partial_2^2u=0.`

For the Gaussian the domain matters, since its formula contains $`1/t`; the
polynomial $`x^2+y^2+4t` has no such restriction. In both cases `cas`
computes the coordinate residual, and the slice-Laplacian theorem identifies
the spatial sum with the Laplacian of $`(x,y)\mapsto u(t,x,y)`. This is how
the calculation enters the ordinary heat-equation predicate.

The remaining examples ask different questions of the same calculus.
Harmonic kernels require a punctured domain and a normalization; transport
adds prescribed values at time zero; rigid rotation tests a symmetric
gradient rather than a scalar Laplacian. Each theorem states which of these
properties has been proved.

The field itself can remain abstract. In
`PDE/Examples/Symbolic/CAS/FluxDerivatives.lean`, if $`u` is differentiable at
$`x`, $`u(x)\ne0`, and $`v` is a fixed vector, the reciprocal-flux example
proves $`\nabla\cdot(u^{-1}v)(x)=-Du(x)[v]/u(x)^2`.
Here `cas` differentiates the scalar reciprocal at $`u(x)`, and the general
divergence chain rule supplies the dependence on $`u`. Only the stated
pointwise hypotheses are needed.

:::theorem "symbolic.gaussian_heat_symbolic_bridge" (parent := "symbolic.theorem_api") (uses := "parabolic.heat_kernel") (lean := "HeatEquation.Symbolic.Space2.heatKernel2D_spacetime_coordinate_residual_zero_of_time_pos")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "45-47"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The symbolically represented planar Gaussian ansatz, interpreted as an ordinary
spacetime function, has zero heat residual in spacetime coordinates at positive
time, and the CAS proves it. With

$$`\Phi(t,x,y)=\frac{\exp\!\left(-(x^2+y^2)/(4t)\right)}{4\pi t},`

the linked Lean theorem states

$$`t>0\quad\Longrightarrow\quad
  \partial_t\Phi-\partial_x^2\Phi-\partial_y^2\Phi=0`

at $`(t,x,y)`. The slice-Laplacian identity turns this into the residual
predicate
$`\operatorname{SatisfiesPDEProblem}(\operatorname{heatEquation}(\{t>0\}),\Phi)`.
For the analytic kernel that predicate is the
{bpref "symbolic.gaussian_heat_example"}[Gaussian heat theorem]; for the
symbolic expression the Lean module derives it in an example.
:::

:::proof "symbolic.gaussian_heat_symbolic_bridge"
Write $`\xi=(x,y)` and $`r^2=x^2+y^2`. Differentiating the prefactor
$`1/(4\pi t)` and the exponential gives

$$`
\begin{aligned}
\Phi_t&=\left(\frac{r^2}{4t^2}-\frac1t\right)\Phi,\\
\Phi_{xx}&=\left(\frac{x^2}{4t^2}-\frac1{2t}\right)\Phi,\qquad
\Phi_{yy}=\left(\frac{y^2}{4t^2}-\frac1{2t}\right)\Phi.
\end{aligned}
`

Adding the two spatial derivatives recovers the time derivative. The CAS
checks this cancellation. The assumption $`t>0` discharges its time
denominators and the validity conditions needed to interpret both rounds of
differentiation; $`\pi\ne0` handles the constant denominator. The residual
bridge then gives the displayed equation for the coordinate partial
derivatives.

Positive time also selects the branch on which this formula agrees with
the analytic heat kernel, whose definition is zero for $`t\le0`. At the
spatial origin the positive-time value is $`1/(4\pi t)`, which grows without
bound as $`t\downarrow0`. Thus substituting the definition's value at time
zero cannot establish an initial-trace theorem.
:::

:::theorem "symbolic.gaussian_heat_example" (parent := "symbolic.theorem_api") (uses := "parabolic.heat_kernel") (lean := "HeatEquation.Space2.gaussianHeatKernel_satisfies_heatResidual_on")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "45-47"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The two-dimensional Gaussian heat kernel satisfies the analytic heat equation
on a domain where time is positive. The theorem statement uses the ordinary
heat-equation predicate defined in the parabolic API. Its proof comes from
the analytic heat-kernel theorem; the CAS computation of the same identity in
spacetime coordinates is the
{bpref "symbolic.gaussian_heat_symbolic_bridge"}[symbolic Gaussian bridge].

For every $`\Omega\subseteq\mathbb R^3`,

$$`\left(\forall p\in\Omega,\ 0<\operatorname{time}(p)\right)
  \quad\Longrightarrow\quad
  \operatorname{SatisfiesPDEProblem}
    (\operatorname{heatEquation}(\Omega),\Phi).`
:::

:::proof "symbolic.gaussian_heat_example"
The positive-time assumption supplies the nonzero and positivity conditions
needed when differentiating the Gaussian factor. The heat-kernel calculation
then identifies its time derivative with its spatial Laplacian. Rewriting the
heat residual by that identity gives zero at every point of the stated domain,
which is the `SatisfiesPDEProblem` conclusion.
:::

:::theorem "symbolic.polynomial_heat_example" (parent := "symbolic.theorem_api") (lean := "HeatEquation.Symbolic.Space2.polynomialHeat2D_satisfiesPDEProblem_univ") (uses := "parabolic.heat_problem")
The polynomial profile

$$`u(t,x,y)=x^2+y^2+4t`

has zero residual for the ordinary two-dimensional heat-equation problem on
all spacetime; the linked `SatisfiesPDEProblem` theorem is exactly that
residual property.
:::

:::proof "symbolic.polynomial_heat_example" (uses := "symbolic.residual_bridge")
Here $`u_t=4`, $`u_{xx}=2`, and $`u_{yy}=2`, so the checked residual is
$`4-2-2=0`. Polynomial evaluation and its derivatives are valid everywhere;
the coordinate and fixed-time slice bridges therefore apply on all
spacetime.
:::

:::theorem "symbolic.fundamental_solution_examples" (parent := "symbolic.theorem_api") (uses := "elliptic.fundamental_solution, foundations.operators.laplacian") (lean := "LaplacianEquation.Symbolic.laplaceFundamental2DSymbolic_eval_eq_fundamentalSolution, LaplacianEquation.Symbolic.laplacian_laplaceFundamental2DSymbolic_of_ne_zero, LaplacianEquation.Symbolic.fundamentalSolution_three_eq_scaled_newtonianCore3D, LaplacianEquation.Symbolic.laplacian_newtonianCore3D_of_ne_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The linked value bridges identify the logarithmic planar expression with the
normalized two-dimensional fundamental solution and the three-dimensional
fundamental solution with a constant multiple of the Newtonian core. The
symbolic profiles are checked to be harmonic away from the pole, with domain
hypotheses kept explicit.

For the Poisson-normalized kernels

$$`\Phi_2(x)=-\frac1{2\pi}\log\|x\|,
\qquad
\Phi_3(x)=\frac1{4\pi\|x\|},`

the linked theorems prove

$$`x\neq0\quad\Longrightarrow\quad
  \Delta\Phi_2(x)=0
  \quad\text{and}\quad
  \Delta\Phi_3(x)=0.`
:::

:::proof "symbolic.fundamental_solution_examples"
For the planar logarithmic expression, {uses "symbolic.residual_bridge"}[]
transports the checked CAS residual to the analytic Laplacian. The Newtonian
core instead reuses the general radial-Laplacian identity: the coefficient
$`k(k+2-n)` vanishes at $`k=1`, $`n=3`. Its value bridge identifies the
reflected expression with the inverse norm; constant scaling gives the
normalized fundamental solution.
:::

Harmonicity away from the pole cannot determine the normalization: every
constant multiple of a harmonic profile is still harmonic there. In three
dimensions the unit-source normalization is visible in the flux through a
sphere of radius $`r>0`:

$$`
-\int_{\partial B_r}\nabla\Phi_3\cdot n\,dS
=-\left(-\frac{1}{4\pi r^2}\right)4\pi r^2=1.
`

This calculation explains why the coefficient $`1/(4\pi)` matters. A
distributional identity $`-\Delta\Phi_3=\delta_0` must account for that
flux at the excluded pole, which the pointwise zero-residual theorem does not
see.

# One profile, two equations
%%%
tag := "symbolic-sine-example"
%%%
The profile $`u(t,x)=\sin(x-t)` solves two different equations. We use it as
a small example of the {bpref "hyperbolic.wave.ivp"}[wave] and
{bpref "hyperbolic.transport.ivp"}[transport] interfaces:

$$`\partial_t^2u-\partial_x^2u=0,
\qquad
\partial_tu+\partial_xu=0,
\qquad
u(0,x)=\sin x.`

The checked examples live in `PDE/Examples/Hyperbolic`. The wave theorem
records the zero residual on all spacetime; the transport theorem also
checks the assigned value $`u(0,x)=\sin x` by substitution. That part of
its proof is a slice equality, with no limiting argument. The derivative
calculation is short:
$`u_t=-\cos(x-t)` and $`u_x=\cos(x-t)` cancel, while
$`u_{tt}=u_{xx}=-\sin(x-t)`.

For the wave calculation, the
{bpref "symbolic.residual_bridge"}[derivative bridge] transfers the symbolic
identity to ordinary derivatives. The transport example applies the checked
derivative tactic directly to the ordinary function. Both calculations then
feed the library's PDE predicates.

We can also integrate the residual. For this profile, the symbolic residual
equals the ordinary advective derivative at every point, so their integrals
agree on every set and both vanish.

Writing $`R_{\mathrm{sym}}` for the reflected residual and
$`D_bu=\partial_tu+\partial_xu`, the example proves

$$`R_{\mathrm{sym}}(p)=D_bu(p),\qquad
  \int_\Omega R_{\mathrm{sym}}\,dp
    =\int_\Omega D_bu\,dp,\qquad
  \int_\Omega D_bu\,dp=0`

for every $`p\in\mathbb R^2` and every set $`\Omega\subseteq\mathbb R^2`.
A conservation-law weak formulation needs more, including test functions
and the initial or boundary terms.

# Rigid rotation

:::theorem "symbolic.rigid_rotation_energy" (parent := "symbolic.theorem_api") (lean := "VariationalEquation.Symbolic.rigid_rotation_sym_energy_density_integral_zero")
For the planar rigid rotation $`u(x,y)=(-y,x)`, every entry of the symmetric
gradient vanishes. Consequently its small-strain energy density integrates to
zero on every domain. The public theorem is an ordinary integral identity;
the symbolic engine is used only to calculate the coordinate derivatives and
close the pointwise algebra.
:::

:::proof "symbolic.rigid_rotation_energy" (uses := "symbolic.residual_bridge")
The checked derivative bridge computes the four coordinate derivatives of
$`(-y,x)` as $`0,-1,1,0`. Each symmetric-gradient entry therefore vanishes,
so the sum of their squares is pointwise zero. Integral congruence gives
the result on every set.
:::
