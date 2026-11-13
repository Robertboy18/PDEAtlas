/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic
import PDE.Fluid.Incompressible.ClassicalSolutions
import PDE.Fluid.Incompressible.Continuity
import PDE.Fluid.Incompressible.Kinematics
import PDE.Fluid.Incompressible.ModelHierarchy
import PDE.Fluid.Incompressible.Stress
import PDE.Fluid.Incompressible.WeakForm

/-!
# From conservation laws to incompressible flow

Particle paths, the continuity equation, and the Newtonian stress, leading to
the incompressible Euler, Stokes, and Navier–Stokes equations.
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
#doc (Manual) "From Conservation Laws to Incompressible Flow" =>

:::group "fluid.equations"
Incompressible fluid equations
:::

# From Transport to Fluid Motion

The simplest evolution in the hierarchy is a scalar carried by a prescribed
velocity. The {bpref "hyperbolic.transport.operator"}[transport equation]

$$`\partial_t\theta+u\cdot\nabla\theta=0`

says that $`\theta` is constant along particle paths. The velocity is known,
so the equation is linear in the transported scalar. The
{bpref "hyperbolic.transport.characteristic_chain_rule"}[characteristic chain
rule] is the scalar counterpart of the
{bpref "fluid.equations.particle_chain_rule"}[particle-path chain rule].

In one space dimension, allowing the transported quantity to determine its
own speed gives {bpref "hyperbolic.burgers.affine_ivp"}[inviscid Burgers],
$`\partial_tu+u\,\partial_xu=0`. Characteristics can intersect, smooth
solutions can form shocks, and weak solutions then require an entropy
condition. Incompressible Euler retains the self-transport mechanism, but the
velocity is vector-valued and pressure enforces the divergence-free
constraint.

A fluid is described in Eulerian variables by fields attached to positions in
space: density $`\rho(t,x)`, velocity $`u(t,x)`, and pressure $`p(t,x)`. A
particle released at $`a` follows a trajectory $`X(t,a)` satisfying

$$`
\frac{d}{dt}X(t,a)=u(t,X(t,a)).
`

If a scalar or vector field $`v` is observed along that particle path, the
chain rule gives

$$`
\frac{d}{dt}v(t,X(t,a))
  =\partial_t v+(u\mathbin\cdot\nabla)v.
`

This is the material derivative. For prescribed $`u` it is linear in the
transported field $`v`. The fluid nonlinearity appears when $`v=u`, because
the unknown velocity then transports itself.

:::definition "fluid.equations.particle_paths" (parent := "fluid.equations") (lean := "IncompressibleFlow.IsParticlePathAt, IncompressibleFlow.IsParticlePathOn")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
A particle path is represented by the local identity

$$`
X'(t)=u(t,X(t)).
`

The pointwise predicate is useful when only a local calculation is needed.
Its setwise form requires the same identity throughout a time interval.
:::

:::theorem "fluid.equations.particle_chain_rule" (parent := "fluid.equations") (lean := "IncompressibleFlow.hasDerivAt_spacetimeCurve, IncompressibleFlow.IsParticlePathAt.hasDerivAt_comp, IncompressibleFlow.IsParticlePathAt.hasDerivAt_comp_scalar") (uses := "fluid.equations.particle_paths")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
If $`X` is a particle path, the associated spacetime curve
$`t\mapsto(t,X(t))` has velocity $`(1,u(t,X(t)))`. Therefore every
differentiable spacetime field $`v` satisfies

$$`
\frac{d}{dt}v(t,X(t))
  =Dv(t,X(t))[1,u(t,X(t))].
`

For scalar $`v`, expanding the Fréchet derivative gives the checked identity

$$`
\frac{d}{dt}v(t,X(t))
  =\partial_t v(t,X(t))
   +\sum_{j=1}^n u_j(t,X(t))\,\partial_jv(t,X(t)).
`
:::

:::proof "fluid.equations.particle_chain_rule"
Write the spacetime trajectory as the sum of its time coordinate and the
zero-time embedding of $`X`. Their derivatives are respectively the time
basis vector and the embedded spatial velocity. The ordinary Fréchet chain
rule gives the directional derivative, and expansion in the Euclidean
coordinate basis separates its time coordinate from the spatial sum.
:::

# Mass and incompressibility

Conservation of mass is the continuity equation

$$`
\partial_t\rho+\nabla\mathbin\cdot(\rho u)=0.
`

:::definition "fluid.equations.continuity" (parent := "fluid.equations") (lean := "IncompressibleFlow.massFlux, IncompressibleFlow.scalarMaterialDerivative, IncompressibleFlow.continuityResidual") (uses := "fluid.equations.particle_chain_rule")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The mass flux is $`\rho u`, and the continuity residual is

$$`
R_\rho=\partial_t\rho+\nabla\cdot(\rho u).
`

The material derivative of density is
$`D_t^u\rho=\partial_t\rho+u\cdot\nabla\rho`.
:::

:::theorem "fluid.equations.continuity_decomposition" (parent := "fluid.equations") (lean := "IncompressibleFlow.continuityResidual_eq_scalarMaterialDerivative_add_density_mul_spatialDivergence") (uses := "fluid.equations.continuity")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
For differentiable density and velocity components, the product rule gives

$$`
R_\rho=D_t^u\rho+\rho\,\nabla\cdot u.
`
:::

:::proof "fluid.equations.continuity_decomposition"
Apply the product rule to each component
$`\partial_j(\rho u_j)`, sum over the spatial coordinates, and collect the
terms $`u_j\partial_j\rho`. The remaining sum is
$`\rho\sum_j\partial_ju_j`.
:::

:::theorem "fluid.equations.constant_density" (parent := "fluid.equations") (lean := "IncompressibleFlow.continuityResidual_const, IncompressibleFlow.continuityResidual_const_eq_zero_of_divergenceFreeAt, IncompressibleFlow.continuityResidual_const_eq_zero_iff_divergenceFreeAt") (uses := "fluid.equations.continuity_decomposition")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
If $`\rho=\rho_0` is constant, then

$$`
R_\rho=\rho_0\,\nabla\cdot u.
`

Every divergence-free flow therefore conserves constant density. When
$`\rho_0\ne0`, the continuity equation and incompressibility are equivalent.
:::

:::proof "fluid.equations.constant_density"
The time derivative of a constant vanishes, and constant scalar
multiplication passes through every spatial partial derivative. Thus the
continuity residual is $`\rho_0` times the divergence. If $`\rho_0` is
nonzero, their product vanishes exactly when the divergence vanishes.
:::

Incompressibility, $`\nabla\cdot u=0`, says that an infinitesimal fluid volume
neither expands nor contracts.

:::definition "fluid.equations.kinematics" (parent := "fluid.equations") (lean := "IncompressibleFlow.materialDerivative, IncompressibleFlow.DivergenceFree, IncompressibleFlow.DivergenceFreeAt, IncompressibleFlow.FiniteTimeResidualSolution, IncompressibleFlow.FiniteTimeClassicalSolution, IncompressibleFlow.GlobalResidualSolution, IncompressibleFlow.GlobalClassicalSolution, IncompressibleFlow.GlobalResidualSolution.toFiniteTime, IncompressibleFlow.GlobalClassicalSolution.toFiniteTime") (uses := "fluid.equations.particle_chain_rule, fluid.equations.constant_density")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
Write spacetime as $`\mathbb R^{n+1}`, with coordinate zero reserved for
time. The material derivative is

$$`
(D_t^u v)_i
=\partial_t v_i+\sum_{j=1}^n u_j\partial_jv_i,
`

and incompressibility sums only the spatial derivatives. The global condition
requires this sum to vanish everywhere; its pointwise form imposes the same
identity at one spacetime point.

An incompressible solution pairs an equation-specific momentum predicate with
incompressibility and initial data. A residual solution requires only those
equations; a classical solution adds the regularity that makes the totalized
derivatives analytic derivatives and the assigned initial value a one-sided
trace. Global solutions restrict canonically to any positive finite horizon.
Euler and Navier–Stokes are both instances of these definitions.
:::

# Momentum and stress

Incompressibility allows substantial deformation. For the planar velocity
$`u(x,y)=(ax,-ay)`, the divergence is $`a-a=0`, while particles follow
$`(x(t),y(t))=(e^{at}x(0),e^{-at}y(0))`. A small rectangle stretches in
one direction and contracts in the other; the area factor is
$`e^{at}e^{-at}=1`. This example helps us read
$`\nabla\cdot u=0`: it controls volume change, not the size of the velocity
or the amount of stretching.

Newton's law for a continuum reads

$$`\rho D_tu=\nabla\mathbin\cdot\sigma+\rho f,`

where $`\sigma` is the Cauchy stress tensor and $`f` is an external force per
unit mass. For an incompressible Newtonian fluid with constant density, the
stress splits into pressure and viscosity:

$$`\sigma=-pI+2\mu D(u),\qquad
D(u)=\frac12\bigl(\nabla u+\nabla u^{\mathsf T}\bigr).`

:::definition "fluid.equations.stress" (parent := "fluid.equations") (lean := "IncompressibleFlow.SpatialMatrix, IncompressibleFlow.spatialVelocityGradient, IncompressibleFlow.strainRateTensor, IncompressibleFlow.strainRateTrace, IncompressibleFlow.newtonianCauchyStress") (uses := "fluid.equations.kinematics")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The spatial velocity gradient has components
$`(\nabla u)_{ij}=\partial_j u_i`. Its symmetric part is the strain rate

$$`
D_{ij}(u)=\frac{\partial_j u_i+\partial_i u_j}{2},
`

and the Newtonian constitutive law is

$$`
\sigma_{ij}=-p\,\delta_{ij}+2\mu D_{ij}(u).
`
:::

Only the symmetric half of $`\nabla u` enters the constitutive law. The
antisymmetric part is half the vorticity tensor, so the Newtonian stress
ignores exactly the local rotation of the fluid.

:::theorem "fluid.equations.gradient_decomposition" (parent := "fluid.equations") (lean := "IncompressibleFlow.spatialVelocityGradient_eq_strainRateTensor_add_half_vorticityTensor, IncompressibleFlow.strainRateTensor_apply_swap") (uses := "fluid.equations.stress")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The velocity gradient splits into its symmetric and antisymmetric parts:

$$`
\partial_j u_i=D_{ij}(u)+\frac12\Omega_{ij}(u),
\qquad D_{ji}(u)=D_{ij}(u).
`

Here
$`\Omega_{ij}(u)=\partial_j u_i-\partial_i u_j` is twice the antisymmetric
part of the velocity gradient, developed as vorticity in the Euler section.
:::

:::proof "fluid.equations.gradient_decomposition"
Add and subtract $`\partial_i u_j`. Half of their sum is the strain rate,
and half of their difference is $`\Omega_{ij}/2`, the antisymmetric part.
Exchanging the two indices leaves the sum unchanged.
:::

To see why the symmetric part measures strain, let $`h` be an infinitesimal
separation between two particles. Along a smooth trajectory its linearized
evolution is $`h'=(\nabla u)h`, so

$$`
\frac{d}{dt}|h|^2=2h\cdot(\nabla u)h=2h\cdot D(u)h.
`

An antisymmetric matrix contributes zero to this quadratic form. It can
rotate the separation without changing its length. For the stretching flow
$`u=(ax,-ay)`, $`D(u)=\operatorname{diag}(a,-a)`; for solid rotation,
$`D(u)=0` even though the velocity and vorticity are nonzero.

The diagonal of $`D(u)` carries the volumetric information: for incompressible
flow the pressure is the only part of the stress that survives on the trace.

:::theorem "fluid.equations.strain_trace" (parent := "fluid.equations") (lean := "IncompressibleFlow.strainRateTrace_eq_spatialDivergence, IncompressibleFlow.strainRateTrace_eq_zero_of_divergenceFreeAt, IncompressibleFlow.newtonianCauchyStress_apply_swap") (uses := "fluid.equations.stress, fluid.equations.constant_density")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The strain trace is the divergence:

$$`
\operatorname{tr}D(u)=\sum_i\partial_i u_i=\nabla\cdot u.
`

Consequently, incompressible strain is trace free. The Newtonian stress is
symmetric because both the pressure tensor and $`D(u)` are symmetric.
:::

:::proof "fluid.equations.strain_trace"
On the diagonal,
$`D_{ii}=(\partial_i u_i+\partial_i u_i)/2=\partial_i u_i`.
Summing gives the divergence, which vanishes under incompressibility.
Symmetry of the stress follows componentwise from
$`\delta_{ij}=\delta_{ji}` and $`D_{ij}=D_{ji}`.
:::

Newton's law involves the stress only through $`\nabla\cdot\sigma`.
Differentiating the constitutive law componentwise turns the pressure part into
$`-\nabla p` and the strain part into a Laplacian plus a gradient of the
divergence, the latter being the same trace that incompressibility has just
removed.

:::theorem "fluid.equations.stress_divergence" (parent := "fluid.equations") (lean := "IncompressibleFlow.newtonianCauchyStressDivergence_eq, IncompressibleFlow.newtonianCauchyStressDivergence_eq_of_divergenceFree") (uses := "fluid.equations.strain_trace")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
For constant dynamic viscosity $`\mu`, taking the spatial divergence of the
Newtonian constitutive law gives

$$`
(\nabla\cdot\sigma)_i
  =-\partial_i p+\mu\Delta u_i+\mu\,\partial_i(\nabla\cdot u).
`

For a divergence-free velocity, the final term vanishes and therefore

$$`
\nabla\cdot\sigma=-\nabla p+\mu\Delta u.
`

The formal statement assumes differentiability of pressure and componentwise
$`C^2` regularity of velocity at the point, so that mixed spatial derivatives
commute. Its incompressible conclusion assumes divergence-freeness on the
whole field, since the gradient of the divergence must vanish at the point.
:::

:::proof "fluid.equations.stress_divergence"
Differentiate
$`\sigma_{ij}=-p\delta_{ij}+\mu(\partial_j u_i+\partial_i u_j)`
with respect to $`x_j` and sum over $`j`. The pressure terms select
$`-\partial_i p`; the first viscous sum is $`\mu\Delta u_i`. Commuting the
mixed derivatives in the second viscous sum gives
$`\mu\partial_i\sum_j\partial_j u_j`. This is
$`\mu\partial_i(\nabla\cdot u)`, which is zero when the divergence vanishes
identically.
:::

Substituting the reduced stress divergence into
$`\rho D_tu=\nabla\cdot\sigma+\rho f` at unit density is all that separates the
Cauchy momentum balance from the Navier–Stokes equation.

:::theorem "fluid.equations.cauchy_to_navier_stokes" (parent := "fluid.equations") (lean := "IncompressibleFlow.newtonianCauchyMomentumResidual_eq_navierStokesMomentumResidual, IncompressibleFlow.newtonianCauchyMomentumResidual") (uses := "fluid.equations.stress_divergence, fluid.equations.kinematics")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
At unit density, the Cauchy momentum residual is

$$`
R_C=D_t^u u-\nabla\cdot\sigma-f.
`

For a divergence-free Newtonian velocity field with the stated
differentiability, it is exactly the Navier–Stokes residual:

$$`
R_C
  =D_t^u u+\nabla p-\mu\Delta u-f
  =R_{NS}.
`

Thus the Cauchy momentum balance and the reduced Navier–Stokes equation are
the same pointwise equation under these hypotheses.
:::

:::proof "fluid.equations.cauchy_to_navier_stokes"
Substitute
$`\nabla\cdot\sigma=-\nabla p+\mu\Delta u` into
$`D_t^u u-\nabla\cdot\sigma-f`. Distributing the minus sign gives
$`D_t^u u+\nabla p-\mu\Delta u-f`, component by component.
:::

For constant density $`\rho_0>0`, divide the momentum equation by
$`\rho_0`, replace pressure by $`p/\rho_0`, and set
$`\nu=\mu/\rho_0`. Together with $`\nabla\cdot u=0`, this gives

$$`
\partial_tu+(u\mathbin\cdot\nabla)u+\nabla p
  =\nu\Delta u+f.
`

The equation must be paired with a spatial domain and boundary conditions.
On a rigid wall, impermeability requires $`u\cdot n=0`; the viscous no-slip
condition strengthens this to $`u=0`. Whole-space problems instead prescribe
decay or integrability at infinity, while periodic problems identify opposite
faces of a box. These choices affect pressure recovery, energy identities, and
the meaning of a weak solution.

:::definition "fluid.equations.operators" (parent := "fluid.equations") (lean := "IncompressibleFlow.timeDerivative, IncompressibleFlow.convectiveDerivative, IncompressibleFlow.spatialVectorLaplacian, NavierStokes.viscousTerm") (uses := "foundations.coordinates.spatial_gradient, fluid.equations.kinematics, fluid.equations.stress_divergence")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The operators distinguish $`\partial_tu`, $`(u\cdot\nabla_x)v`,
$`\nu\Delta_xu`, and $`\nabla_xp`. Every spatial operator uses only
coordinates $`1,\ldots,n`; coordinate zero remains time. This matters because
the ambient fields live on spacetime, where an unqualified Laplacian would
also differentiate twice in time.
:::

:::theorem "fluid.equations.material_decomposition" (parent := "fluid.equations") (lean := "IncompressibleFlow.materialDerivative_eq_timeDerivative_add_convectiveDerivative") (uses := "fluid.equations.operators")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The material derivative decomposes exactly as

$$`
D_t^u v=\partial_t v+(u\cdot\nabla_x)v.
`
:::

:::proof "fluid.equations.material_decomposition"
Evaluate both sides in a velocity component. The definitions have the same
time partial and the same finite sum of spatial directional derivatives, so
the componentwise equality is immediate.
:::

# Common weak-form data

:::definition "fluid.equations.weak_test_data" (parent := "fluid.equations") (lean := "IncompressibleFlow.IsWeakMomentumTest, IncompressibleFlow.velocityTestPairing, IncompressibleFlow.initialVelocityTestPairing") (uses := "fluid.equations.kinematics")
%%%
source := {
  document := "wiedemann-euler-weak"
  spans := #[{
    page := "Equation (3)"
    text := some { path := "Blueprint/Sources/WiedemannEulerWeak.md", startLine := 1, endLine := 14 }
  }]
}
%%%
On a finite horizon $`[0,T]`, a momentum test field is a smooth compactly
supported spacetime vector field $`\varphi` satisfying $`\varphi(T,x)=0`.
It may be nonzero at $`t=0`, which exposes the initial boundary term after
integration by parts. The velocity and initial pairings are

$$`
\langle u(t),\psi\rangle
=\int_{\mathbb R^n}u(t,x)\cdot\psi(x)\,dx,
\qquad
\langle u_0,\psi\rangle
=\int_{\mathbb R^n}u_0(x)\cdot\psi(x)\,dx.
`

These are shared test data and pairings; the Euler and Navier–Stokes weak
formulations supply their own momentum integrands.
:::
