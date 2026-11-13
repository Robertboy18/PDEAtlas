/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.WeakProblems.Dirichlet
import Blueprint.Chapters.Fluid.Equations
import Blueprint.CodeExamples
import PDE.Elliptic.Symbolic.VariationalIntegrands
import PDE.Fluid.Euler.PotentialFlow
import PDE.Fluid.Euler.ZeroSolutions.Weak
import PDE.Fluid.Euler.ZeroSolutions.Classical
import PDE.Fluid.Incompressible.EnergyIdentities
import PDE.Fluid.Incompressible.Pressure
import PDE.Fluid.Incompressible.VorticityEvolution
import PDE.Fluid.NavierStokes.Symbolic.SpacetimeRotation
import PDE.Fluid.NavierStokes.Symbolic.Stationary.Rotation

/-!
# Incompressible Euler flow

The inviscid equation, its classical and weak solutions, the pressure
constraint, vorticity transport, Bernoulli's law, time-dependent potential
flow, and exact solid rotation.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Incompressible Euler Flow" =>

:::group "fluid.euler"
Incompressible Euler flow
:::

Removing viscosity from the momentum law leaves the incompressible Euler
equations:

$$`
\partial_tu+(u\mathbin\cdot\nabla)u+\nabla p=f,
\qquad \nabla\mathbin\cdot u=0.
`

The equation describes an ideal fluid with no viscous dissipation. Its
nonlinearity is the vector analogue of Burgers self-transport, while pressure
couples all components through incompressibility.

:::definition "fluid.euler.residual" (parent := "fluid.euler") (lean := "IncompressibleFlow.eulerMomentumResidual") (uses := "fluid.equations.material_decomposition")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The Euler momentum residual is the vector field

$$`R_E=D_t^u u+\nabla p-f.`

The pointwise momentum balance is the equation $`R_E=0`.
:::

:::theorem "fluid.euler.residual_eq_zero" (parent := "fluid.euler") (lean := "IncompressibleFlow.eulerMomentumResidual_eq_zero_iff") (uses := "fluid.euler.residual")
The residual vanishes exactly when

$$`D_t^u u+\nabla p=f.`
:::

:::proof "fluid.euler.residual_eq_zero"
Move the force term across the equality. This is an identity in the additive
group of velocity vectors.
:::

# Initial-value and classical solutions

:::definition "fluid.euler.classical_solutions" (parent := "fluid.euler") (lean := "IncompressibleFlow.InitialValueData, Euler.PointwiseResidualSolution, Euler.PointwiseResidualSolution.momentumResidual_eq_zero, Euler.SmoothSolution, Euler.GlobalPointwiseResidualSolution, Euler.GlobalPointwiseResidualSolution.momentumResidual_eq_zero, Euler.GlobalSmoothSolution") (uses := "fluid.euler.residual, fluid.equations.kinematics")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
Initial-value data consist of a force $`f`, a prescribed velocity $`u_0`, and
distributional incompressibility of $`u_0`. A finite-time residual solution
stores $`u`, $`p`, a positive horizon $`T`, the Euler momentum equation and
pointwise incompressibility on $`(0,T)\times\mathbb R^n`, and the exact value
$`u(0,x)=u_0(x)`.

A residual solution carries no differentiability. A smooth solution also
requires ambient smoothness at every positive-time
point and one-sided continuity of velocity at $`t=0`. A global smooth solution
has these properties at all positive times and relative smoothness on
$`[0,\infty)\times\mathbb R^n`. Every global smooth solution restricts, with
the same fields and data, to every positive finite horizon. Smoothness alone
on the whole space does not imply the $`L^2` bounds, decay, and spacetime
integrability required by a weak solution, so a smooth solution is weak only
once those bounds are proved.
:::

:::theorem "fluid.euler.zero_classical" (parent := "fluid.euler") (lean := "Euler.exists_zero_globalSmoothSolution, Euler.exists_zero_smoothSolution_on, Euler.zeroGlobalSmoothSolution, Euler.zeroSmoothSolution") (uses := "fluid.euler.classical_solutions")
For zero initial velocity and zero forcing, $`u=0` and $`p=0` give a smooth
Euler solution globally and on every positive finite horizon.
:::

:::proof "fluid.euler.zero_classical"
Every time derivative, convective term, pressure gradient, and divergence is
zero. Constant zero fields are smooth on the closed physical half-space, and
their initial value is the prescribed zero datum. Restricting the global
solution gives the finite-time result.
:::

# Weak solutions

:::definition "fluid.euler.weak_solutions" (parent := "fluid.euler") (lean := "Euler.weakMomentumIntegrand, Euler.WeakMomentumIntegrableOn, Euler.WeakSolution, Euler.WeakSolution.weak_momentum_eq, Euler.WeakSolution.weakDivergencePairing_eq_zero") (uses := "fluid.euler.residual, fluid.euler.classical_solutions, fluid.equations.weak_test_data")
%%%
source := {
  document := "wiedemann-euler-weak"
  spans := #[{
    page := "Equation (3)"
    text := some { path := "Blueprint/Sources/WiedemannEulerWeak.md", startLine := 1, endLine := 14 }
  }]
}
%%%
A weak Euler solution on $`[0,T]\times\mathbb R^n` consists of velocity
$`u`, pressure $`p`, and a positive horizon $`T`. For every smooth compactly
supported vector field $`\varphi` that vanishes at $`t=T`, it satisfies

$$`
\int_0^T\!\int_{\mathbb R^n}
\left[-u\cdot\partial_t\varphi
      -(u\otimes u):\nabla\varphi
      -p\,\nabla\cdot\varphi
      -f\cdot\varphi\right]dx\,dt
=\int_{\mathbb R^n}u_0\cdot\varphi(0)\,dx.
`

At every $`t\in[0,T]`, the velocity slice is distributionally divergence-free,
and the velocity, pressure, and forcing slices belong to spatial $`L^2`.
The prescribed initial velocity also belongs to $`L^2`. The definition requires
spatial integrability of the combined momentum integrand at every such time
and time integrability of its spatial integral. The initial pairing is
integrable by the $`L^2` datum and the compactly supported smooth test. It
specifies the initial condition through the weak equation, without requiring
$`u(0,\cdot)=u_0` for the chosen representative.

The definition is posed on a whole-space finite slab, allows general tests,
keeps the pressure, and uses the initial-boundary and convection signs of
Wiedemann's formulation.
:::

For a smooth incompressible field,
$`(u\cdot\nabla)u=\nabla\cdot(u\otimes u)`. Testing momentum and
integrating by parts, when the integrations are justified, moves the
derivatives onto $`\varphi`; the initial term comes from the lower endpoint of
the time integral. This explains both the minus signs and why the weak
formulation can make sense without pointwise derivatives of $`u`.
Divergence-free tests also remove $`p\,\nabla\cdot\varphi`, which gives the
pressure-free formulation on the solenoidal space.

:::theorem "fluid.euler.zero_weak" (parent := "fluid.euler") (lean := "Euler.exists_zero_weakSolution_on, Euler.zeroWeakSolution") (uses := "fluid.euler.weak_solutions")
For zero force and zero initial velocity, $`u=0` and $`p=0` form a weak Euler
solution on every positive finite time slab.
:::

:::proof "fluid.euler.zero_weak"
All four terms in the momentum integrand vanish pointwise, hence their space
and time integrals are integrals of zero. The initial pairing is zero,
every zero velocity slice belongs to $`L^2`, and its distributional divergence
is zero.
:::

# Pressure as an elliptic constraint

Pressure has no separate evolution equation. Taking the divergence of Euler
and using $`\nabla\cdot u=0` gives

$$`
-\Delta p
=\nabla\mathbin\cdot\bigl((u\mathbin\cdot\nabla)u\bigr)
 -\nabla\mathbin\cdot f.
`

Thus pressure is determined nonlocally at each time, up to the boundary
conditions and the usual additive constant. Hyperbolic transport and elliptic
pressure recovery are already coupled before viscosity enters.

One way to read this constraint is to start with the acceleration
$`a=f-(u\cdot\nabla)u`. Momentum asks for
$`\partial_tu=a-\nabla p`, but an incompressible evolution must also have
$`\nabla\cdot\partial_tu=0`. Thus $`\Delta p=\nabla\cdot a`: the pressure
gradient corrects the acceleration so that it stays tangent to the
divergence-free constraint. Solving that elliptic problem is the nonlocal
step; knowing $`u` at one point does not determine its pressure correction
there.

On a bounded domain with homogeneous Dirichlet data, the
{bpref "elliptic.poisson.distributional_exists_unique"}[weak Poisson theorem]
of the elliptic chapter gives a variational existence-and-uniqueness model for
this elliptic step.
Fluid pressure more often comes with periodic, whole-space, or Neumann data
and an additive normalization, so that theorem supplies the analytic pattern
rather than a direct pressure solver for every fluid domain.

:::definition "fluid.euler.pressure_poisson" (parent := "fluid.euler") (lean := "IncompressibleFlow.pressurePoissonSource, IncompressibleFlow.pressurePoissonResidual") (uses := "fluid.euler.residual")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The pressure Poisson source and residual are

$$`
S_p=\nabla_x\cdot((u\cdot\nabla_x)u)-\nabla_x\cdot f,
\qquad R_p=-\Delta_xp-S_p.
`

The spatial subscript distinguishes these operators from derivatives in the
time coordinate.
:::

:::theorem "fluid.euler.pressure_recovery" (parent := "fluid.euler") (lean := "IncompressibleFlow.pressurePoissonResidual_eq_zero_of_divergence_balance, IncompressibleFlow.pressurePoissonResidual_eq_zero_iff") (uses := "fluid.euler.pressure_poisson")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
If the spatial divergence of the differentiated Euler momentum balance holds
and $`\nabla_x\cdot\partial_tu=0`, then

$$`
-\Delta_xp
=\nabla_x\cdot((u\cdot\nabla_x)u)-\nabla_x\cdot f.
`
:::

:::proof "fluid.euler.pressure_recovery"
Taking spatial divergence gives
$`\nabla_x\cdot\partial_tu+\nabla_x\cdot((u\cdot\nabla_x)u)
+\Delta_xp=\nabla_x\cdot f`. The first term vanishes for a sufficiently
regular divergence-free flow. Rearranging the remaining scalar identity gives
the stated Poisson equation.
:::

# Vorticity

For a three-dimensional velocity field, set $`\omega=\nabla\times u`.
Taking the curl of the unforced Euler equation yields

$$`
\partial_t\omega+(u\cdot\nabla)\omega
  =(\omega\cdot\nabla)u.
`

The right-hand side stretches and tilts vortex lines. In two dimensions
vorticity is scalar and this term disappears:

$$`\partial_t\omega+u\cdot\nabla\omega=0.`

This difference is one reason two-dimensional incompressible flow is more
regular than its three-dimensional counterpart.

:::definition "fluid.euler.vorticity" (parent := "fluid.euler") (lean := "IncompressibleFlow.vorticityTensor, IncompressibleFlow.spacetimePlanarVorticity") (uses := "fluid.equations.operators")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapters 1-2"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
For a flow in $`n` space dimensions, define the antisymmetric
velocity-gradient components

$$`
\Omega_{ij}=\partial_j u_i-\partial_i u_j.
`

For a planar spacetime field, scalar vorticity is
$`\omega=\Omega_{21}=\partial_xu_2-\partial_yu_1`.
:::

Antisymmetry is what makes the planar case scalar. An antisymmetric $`2\times2`
matrix has a single independent entry, so in two dimensions the whole tensor is
determined by $`\omega=\Omega_{21}`, while in three dimensions its three
independent entries are, up to sign, the components of $`\nabla\times u`.

:::theorem "fluid.euler.vorticity_antisymmetric" (parent := "fluid.euler") (lean := "IncompressibleFlow.vorticityTensor_apply, IncompressibleFlow.vorticityTensor_apply_self, IncompressibleFlow.vorticityTensor_apply_swap") (uses := "fluid.euler.vorticity")
The vorticity tensor is antisymmetric:

$$`\Omega_{ii}=0,\qquad \Omega_{ji}=-\Omega_{ij}.`
:::

:::proof "fluid.euler.vorticity_antisymmetric"
On the diagonal the two derivatives are identical and cancel. Exchanging
$`i` and $`j` reverses the order of the same difference, hence changes its
sign.
:::

With vorticity scalar in the plane, the stretching term $`(\omega\cdot\nabla)u`
of the three-dimensional equation has no counterpart: the vorticity vector is
normal to the plane of motion and the velocity does not vary in that direction.
What remains is pure transport, and its residual is the material derivative of
the scalar $`\omega`.

:::definition "fluid.euler.vorticity_transport" (parent := "fluid.euler") (lean := "IncompressibleFlow.spacetimePlanarVorticityTransportResidual") (uses := "fluid.euler.vorticity, fluid.equations.material_decomposition")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapters 1-2"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
For planar flow, the vorticity-transport residual is

$$`
R_\omega
=\partial_t\omega+u\cdot\nabla\omega.
`

For unforced planar Euler flow, the vorticity equation is
$`R_\omega=0`.
:::

The residual is a definition; the content is that for solutions of the momentum
equation it equals the curl of the force, hence vanishes in the unforced case.
Taking the planar curl of $`\partial_tu+(u\cdot\nabla)u+\nabla p=f` eliminates
the pressure, because the curl of a gradient is zero, and incompressibility
converts the curl of the convective term into transport of $`\omega`. Since the
derivation differentiates the momentum equation, it needs that equation on an
open neighborhood rather than at a single point.

:::theorem "fluid.euler.vorticity_from_momentum" (parent := "fluid.euler") (lean := "IncompressibleFlow.spatialPlanarVorticity_equation_of_momentum, IncompressibleFlow.spatialPlanarVorticity_advectiveDerivative_eq, IncompressibleFlow.spatialPlanarVorticity_gradient_eq_zero, IncompressibleFlow.spatialPlanarClockwiseVorticity_equation_of_momentum, IncompressibleFlow.spatialPlanarClockwiseVorticity_advectiveDerivative_eq, IncompressibleFlow.spatialPlanarClockwiseVorticity_gradient_eq_zero") (uses := "fluid.euler.vorticity_transport, fluid.euler.residual")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapters 1-2"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
Let $`u` be jointly $`C^2` in space and time, let the pressure slice be
$`C^2`, and let the force slice be $`C^1`. Suppose the momentum equation and
$`\nabla\cdot u=0` hold on an open spatial neighborhood of $`x`. For standard
counterclockwise vorticity $`\omega=\partial_xu_2-\partial_yu_1`,

$$`
\partial_t\omega+u\cdot\nabla\omega
  =\partial_x f_2-\partial_y f_1.
`

The clockwise-sign counterpart
$`\omega_{\mathrm{cw}}=\partial_yu_1-\partial_xu_2=-\omega`, used by the
Boussinesq system, satisfies the same identity with the clockwise curl of the
force on the right; the two statements differ by an overall sign, and the
auxiliary commutation identities are proved in both conventions. In
particular, either right-hand side vanishes for unforced planar Euler flow.
:::

:::proof "fluid.euler.vorticity_from_momentum"
Differentiate the two momentum components in the transverse spatial
directions and subtract. Joint $`C^2` regularity commutes the time and spatial
derivatives. The pressure contribution vanishes because mixed derivatives
commute. For a divergence-free planar velocity, the clockwise curl of
$`(u\cdot\nabla)u` is $`u\cdot\nabla\omega_{\mathrm{cw}}`. What remains is exactly
the clockwise curl of the force. Lean proves the clockwise form first;
negating it gives the counterclockwise statement.
:::

In three dimensions the curl of the convective term is not pure transport: the
additional term $`(\omega\cdot\nabla)u` survives and is responsible for vortex
stretching. The general residual keeps that term and includes a viscous term,
so Euler and Navier–Stokes flow share it.

:::definition "fluid.euler.vorticity_stretching_residual" (parent := "fluid.euler") (lean := "IncompressibleFlow.vorticityTransportResidual, IncompressibleFlow.vorticityStretching") (uses := "fluid.equations.kinematics, fluid.equations.operators, fluid.euler.vorticity")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
For spacetime fields $`u,\omega:\mathbb R^{n+1}\to\mathbb R^n`, with time in
coordinate zero, the vortex-stretching term is the convective derivative of
the velocity along $`\omega`,

$$`
\bigl((\omega\cdot\nabla)u\bigr)_i=\sum_{j=1}^n\omega_j\,\partial_ju_i,
`

and the vorticity transport residual with viscosity $`\nu` is the vector

$$`
R_\omega(\nu)=D_t^u\omega-(\omega\cdot\nabla)u-\nu\Delta_x\omega.
`

When $`n=3`, $`\omega=\nabla\times u`, and $`u` is divergence free,
$`R_\omega(0)=0` is the unforced Euler vorticity equation and
$`R_\omega(\nu)=0` with $`\nu>0` is the Navier–Stokes vorticity equation.
In the definition $`\omega` is an independent vector field in any dimension;
for Navier–Stokes flow its identification with the curl and with the two-form
vorticity equation is a theorem.
:::

:::theorem "fluid.euler.vorticity_stretching_equation" (parent := "fluid.euler") (lean := "IncompressibleFlow.vorticityTransportResidual_eq_zero_iff, IncompressibleFlow.vorticityTransportResidual_zero_viscosity") (uses := "fluid.euler.vorticity_stretching_residual")
The residual vanishes exactly when

$$`
D_t^u\omega=(\omega\cdot\nabla)u+\nu\Delta_x\omega,
`

and at zero viscosity it reduces to the transport-stretching difference
$`R_\omega(0)=D_t^u\omega-(\omega\cdot\nabla)u`.
:::

:::proof "fluid.euler.vorticity_stretching_equation"
Both statements are rearrangements in the additive group of vector fields:
$`A-B-C=0` holds exactly when $`A=B+C`, and the scalar multiple
$`0\cdot\Delta_x\omega` vanishes.
:::

# Convective acceleration and Bernoulli's law

At a point where every velocity component is differentiable, the gradient
and antisymmetric parts of the velocity derivative separate convective
acceleration into kinetic-energy and vorticity terms. With
$`e=\frac12|u|^2` and
$`\Omega_{ij}=\partial_ju_i-\partial_i u_j`,

$$`
((u\cdot\nabla)u)_i
=\partial_i e+\sum_j u_j\Omega_{ij}.
`

:::theorem "fluid.euler.bernoulli" (parent := "fluid.euler") (lean := "IncompressibleFlow.bernoulliTransport_eq_zero_of_steady_unforced_euler, IncompressibleFlow.spatialGradient_bernoulliFunction_eq_zero_of_steady_irrotational_euler, IncompressibleFlow.convectiveDerivative_eq_spatialGradient_specificKineticEnergy_add_vorticityContraction, IncompressibleFlow.convectiveDerivative_eq_spatialGradient_specificKineticEnergy_of_vorticityTensor_eq_zero, IncompressibleFlow.bernoulliTransport_eq_kineticEnergyTransport_add_pressurePower, IncompressibleFlow.vorticityContraction, IncompressibleFlow.bernoulliFunction, IncompressibleFlow.bernoulliTransport") (uses := "fluid.euler.vorticity, fluid.euler.residual")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapters 1-2"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
Set $`B=p+e`. At a point where the velocity components and pressure are
differentiable, the steady, unforced balance
$`(u\cdot\nabla)u+\nabla p=0` gives

$$`
u\cdot\nabla B=0.
`

Thus the Bernoulli function is constant along streamlines on which these
hypotheses hold. If the flow is also irrotational at the point, then

$$`((u\cdot\nabla)u)_i=\partial_i e.`

The Euler balance then gives the stronger vector identity

$$`\nabla\left(p+\frac12|u|^2\right)=0.`

The theorem is pointwise; constancy of the Bernoulli function on a connected
region follows when these derivatives vanish throughout that region.
:::

:::proof "fluid.euler.bernoulli"
Pair the steady momentum balance
$`(u\cdot\nabla)u+\nabla p=0` with $`u`. The convective-power identity gives
$`u\cdot((u\cdot\nabla)u)=u\cdot\nabla e`, hence
$`u\cdot\nabla(e+p)=0`.

For the irrotational strengthening, expand the vorticity contraction:

$$`
\partial_i e+\sum_j u_j(\partial_ju_i-\partial_i u_j).
`

The derivative of $`e` is $`\sum_j u_j\partial_i u_j`, so those terms cancel
and leave $`\sum_j u_j\partial_j u_i`. If the vorticity components vanish,
the steady Euler component
$`((u\cdot\nabla)u)_i+\partial_i p=0` becomes
$`\partial_i(e+p)=0`.
:::

# Time-dependent potential flow

The preceding calculation also works when an irrotational flow changes with
time. Suppose we can write the velocity and force as spatial gradients,
$`u=\nabla_xv` and $`f=\nabla_xh`. Mixed derivatives commute, so the time
derivative of velocity is $`\nabla_xv_t`; the convective acceleration is
$`\nabla_x(|\nabla_xv|^2/2)`. The entire momentum equation is now one spatial
gradient:

$$`
\nabla_x\!\left(v_t+\frac12|\nabla_xv|^2+p-h\right)=0.
`

We can make it vanish by choosing the pressure. Incompressibility leaves a
separate condition on the potential: $`\Delta_xv=0`. This is the
potential-function reduction of Evans, §4.4.2.

:::theorem "fluid.euler.potential_flow" (parent := "fluid.euler") (lean := "IncompressibleFlow.eulerMomentumResidual_potentialPressure, IncompressibleFlow.potentialPressure, IncompressibleFlow.eulerMomentumResidual_spatialGradient, IncompressibleFlow.divergenceFreeAt_spatialGradient_iff, IncompressibleFlow.vorticityTensor_spatialGradient") (uses := "fluid.euler.residual, fluid.euler.vorticity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.4.2 (Potential functions)"
    page := "208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 73, endLine := 82 }
  }]
}
%%%
In any spatial dimension, let $`v` be $`C^2` at a spacetime point and let
$`h` be differentiable there. Define

$$`
u=\nabla_xv,\qquad p=h-v_t-\frac12|\nabla_xv|^2.
`

Then $`u` is irrotational and satisfies the pointwise momentum equation

$$`
u_t+(u\cdot\nabla_x)u+\nabla_xp=\nabla_xh.
`

Moreover, $`\nabla_x\cdot u=0` exactly when $`\Delta_xv=0`. On an open
region with $`v\in C^2` and $`h\in C^1`, the constructed velocity and pressure
are $`C^1`, so spatial harmonicity gives a classical Euler flow throughout
that region.
:::

:::proof "fluid.euler.potential_flow" (uses := "fluid.euler.bernoulli")
The antisymmetric velocity derivative is zero because its two terms are
mixed second derivatives of $`v`. The irrotational convective-acceleration
identity therefore turns $`(u\cdot\nabla_x)u` into the kinetic-energy
gradient. Commute time and space derivatives, then combine the four
gradients in the momentum residual. Substituting the displayed pressure
makes their scalar potential identically zero. Taking the divergence of
$`\nabla_xv` gives the spatial Laplacian directly.
:::

:::definition "fluid.euler.potential_solution" (parent := "fluid.euler") (lean := "Euler.potentialGlobalSmoothSolution, Euler.potentialInitialValueData, IncompressibleFlow.distributionallyDivergenceFree_initial_spatialGradient") (uses := "fluid.euler.classical_solutions, fluid.euler.potential_flow")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.4.2 (Potential functions)"
    page := "208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 73, endLine := 82 }
  }]
}
%%%
Let $`v,h\in C^\infty(\mathbb R\times\mathbb R^n)` and suppose
$`\Delta_xv(t,x)=0` for $`t>0`. Given Euler initial-value data with force
$`\nabla_xh` and initial velocity $`g(x)=\nabla_xv(0,x)`, the velocity
$`u=\nabla_xv` and pressure $`p=h-v_t-\frac12|\nabla_xv|^2` form a global
smooth solution. In particular,

$$`
\lim_{\substack{(t,y)\to(0,x)\\t>0}}u(t,y)=g(x).
`

If spatial harmonicity is supplied at time zero as well, the data constructor
derives distributional incompressibility of $`g` from the classical
divergence identity. The harmonic potential is part of the input.
:::

:::proof "fluid.euler.potential_solution"
Differentiating a smooth potential preserves smoothness of the velocity;
the time derivative and squared norm in the pressure do the same for
pressure. The pointwise reduction supplies momentum balance and
incompressibility at every positive time. Restriction of the smooth
velocity to the initial slice gives the prescribed trace. At time zero,
the classical-to-distributional divergence theorem turns the vanishing
Laplacian into the initial data's weak incompressibility condition.
:::

The time derivative in the pressure is visible in a simple planar example.
Take $`v(t,x,y)=(1+t)(x^2-y^2)` and zero force. Then

$$`
u=\bigl(2(1+t)x,-2(1+t)y\bigr),\qquad
p=-(x^2-y^2)-2(1+t)^2(x^2+y^2).
`

The first pressure term balances $`u_t`; the second balances convective
acceleration. The compiled example `PDE.Examples.Fluid.PotentialFlow` checks
the derivatives and harmonicity with the CAS, constructs the smooth solution,
and checks its initial trace. Its velocity grows linearly in space, so the
flow has infinite energy on the whole plane.

# Exact solid rotation

Consider the planar fields

$$`
u(x,y)=(-y,x),\qquad
p(x,y)=\frac{x^2+y^2}{2}.
`

The velocity is divergence-free. Its convective acceleration is
$`(u\cdot\nabla)u=(-x,-y)`, while $`\nabla p=(x,y)`, so pressure supplies the
centripetal force. This flow is rotational rather than irrotational:
$`\omega=2` and its Bernoulli function is $`p+\frac12|u|^2=x^2+y^2`.
It is constant along the circular streamlines, but not throughout the plane.

We reuse the polynomial differentiation from Foundations to check a vector
equation and its pressure constraint. The pressure itself is not harmonic;
its Laplacian balances the divergence of the convective acceleration. The
same velocity has zero strain, which connects this flow to the
{bpref "symbolic.rigid_rotation_energy"}[symmetric-gradient energy example].

:::theorem "fluid.euler.rotation" (parent := "fluid.euler") (lean := "NavierStokes.Symbolic.rotationField2_incompressible, NavierStokes.Symbolic.rotationField2_euler_momentum_zero, NavierStokes.Symbolic.rotationField2_pressure_poisson") (uses := "fluid.euler.residual, fluid.euler.pressure_recovery")
The verified CAS proves

$$`
\nabla\cdot(-y,x)=0,\qquad
(u\cdot\nabla)u+\nabla p=0,\qquad
-\Delta p=\nabla\cdot((u\cdot\nabla)u).
`

The symbolic calculation produces the differentiated residual, while the
generated theorem proves that the momentum and pressure residuals vanish on
all of $`\mathbb R^2`.
:::

:::proof "fluid.euler.rotation"
The divergence is $`\partial_x(-y)+\partial_yx=0`. Direct differentiation
gives

$$`
(u\cdot\nabla)u
=(-y\partial_x+x\partial_y)(-y,x)=(-x,-y),
`

which cancels $`\nabla p=(x,y)`. The checked proof reflects these polynomial
expressions, differentiates them symbolically, and closes the normalized
identities with `cas`. It also verifies $`-\Delta p=-2` and
$`\nabla\cdot((u\cdot\nabla)u)=-2`.
:::

The exact momentum proof is a one-line tactic call:

```Blueprint.leanExample
-- Prove the exact vector momentum residual is zero.
open CAS.Certificate
open NavierStokes.Symbolic

example :
    ResidualBound
      solidRotationEulerMomentumResidual2.vectorFn
      Set.univ 0 := by
  cas
```

:::theorem "fluid.euler.rotation_bridge" (parent := "fluid.euler") (lean := "NavierStokes.Symbolic.spacetimeSolidRotation_divergenceFreeAt, NavierStokes.Symbolic.spacetimeSolidRotation_planarVorticity_eq_two, NavierStokes.Symbolic.spacetimeSolidRotation_planarVorticityTransportResidual_eq_zero, NavierStokes.Symbolic.spacetimeSolidRotation_eulerMomentum_component") (uses := "fluid.euler.rotation, fluid.euler.vorticity_transport")
The symbolic certificate yields the analytic statements

$$`
\nabla_x\cdot u=0,\qquad
\omega=2,\qquad
D_t^u\omega=0,\qquad
D_t^u u+\nabla_xp=0.
`

These conclusions use the ordinary analytic operators
`partialDeriv`, `materialDerivative`, and `spatialGradient`.
:::

:::proof "fluid.euler.rotation_bridge"
The zero-error certificates make each evaluated symbolic residual vanish.
The bridge lemmas identify those evaluations with the corresponding analytic
operators. Since the certified vorticity is the constant $`2`, all of its
spacetime derivatives vanish, giving the transport equation as well.
:::

:::theorem "fluid.euler.rotation_zero_strain" (parent := "fluid.euler") (lean := "VariationalEquation.Symbolic.rigid_rotation_sym_energy_integrand_zero, VariationalEquation.Symbolic.rotationField2_symGrad_entry_zero") (uses := "fluid.euler.rotation, fluid.equations.stress")
The same rigid rotation has zero strain:

$$`
D(u)=0.
`

Thus the velocity gradient is antisymmetric, every strain entry vanishes,
and the symmetric-gradient energy density is zero.
:::

:::proof "fluid.euler.rotation_zero_strain"
The four spatial derivatives are $`0,-1,1,0`. In each strain component the
off-diagonal derivatives cancel and the diagonal derivative is zero. The
certified energy expression is therefore a sum of zero squares.
:::
