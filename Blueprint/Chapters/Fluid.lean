/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Fluid.AxisymmetricSwirl
import Blueprint.Chapters.Fluid.Boussinesq
import Blueprint.Chapters.Fluid.ExactFlows
import Blueprint.Chapters.Fluid.MillenniumProblem
import Blueprint.Chapters.Fluid.SteadyStokes
import Blueprint.Chapters.Fluid.WeakFoundations
import PDE.CoordinateSystems.Axisymmetric
import PDE.Fluid.Axisymmetric.StreamFunction

/-!
# Incompressible fluid mechanics

Continuum kinematics, Euler flow, viscous flow, and the Navier–Stokes global
regularity problem.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option verso.blueprint.subNumberingPrefix "first"

set_option linter.hashCommand false in
#doc (Manual) "Incompressible Fluid Mechanics" =>
%%%
shortTitle := "Fluid Mechanics"
htmlSplit := .never
%%%

In Eulerian fluid mechanics the velocity field has two roles at once: it is the
unknown motion, and it is the field that transports that motion. This makes the
transport term nonlinear. Written out, the equation is Newton's
law for a continuum,

$$`
\partial_tu+(u\mathbin\cdot\nabla)u+\nabla p
  =\nu\Delta u+f,\qquad
\nabla\mathbin\cdot u=0,
`

with the material acceleration balanced by pressure, viscous diffusion, and any
external forcing, and incompressibility saying that fluid volumes are preserved.
Set $`\nu=0` and it is Euler; drop the nonlinear transport term and it is Stokes.
The equation brings together several earlier subjects: advection is
hyperbolic, viscosity is parabolic, and pressure is not evolved at all but
recovered from an elliptic constraint.

Two explicit flows separate these roles. In
{bpref "fluid.euler.rotation"}[solid rotation], the velocity turns along
circular streamlines, and a quadratic pressure balances the centripetal
acceleration. In the {bpref "fluid.navier_stokes.shear"}[forced sine shear],
advection vanishes and forcing balances viscous diffusion. Each example tests
individual terms of the general equation, and its CAS certificate proves the
residual identities exactly.

# From conservation laws to incompressible flow

Velocity and pressure are fields on space rather than labels attached permanently
to individual particles. Pressure and viscosity transfer momentum between
neighboring regions; an external body force adds momentum from outside the fluid.
Sobolev spaces and compactness enter for weak solutions, and energy estimates
control those solutions without automatically restoring smoothness.

## What is formalized, and in what order

Each solution concept comes after the analysis it needs. The equations come
first: particle paths and the material derivative, the continuity equation and
its constant-density reduction, the Cauchy stress and the strain-trace
identities that turn Cauchy's momentum law into the Navier–Stokes form, and the
common weak-form test data. Then the functional analysis of divergence-free
fields: the solenoidal kernel, its weak and Bochner closure, the cubic
cancellation of the convection form on that kernel, and abstract pressure
recovery from a closed-range divergence. Inviscid flow follows, from Euler
residuals and solution concepts through
{bpref "fluid.euler.pressure_recovery"}[pressure as an elliptic constraint],
vorticity transport and stretching, Bernoulli's law, time-dependent potential
flow with recovered pressure and initial trace, and exact rotation. The
Chen–Hou Boussinesq formulation contributes its rescaling and normalization
identities, a fixed-power similarity reduction, and Poisson inversion by the
half-plane Green potential for compactly supported $`C^2` sources with an odd
extension across the boundary. Viscous flow brings back the Stokes and
Navier–Stokes residuals and their hierarchy, a certified shear flow, classical
solutions with pressure recovery, the vorticity form, and the weak and
{bpref "fluid.navier_stokes.leray_hopf"}[Leray–Hopf] classes with the energy
inequality, to which the zero flow belongs. The Taylor–Green vortex and
Kovasznay's wake are certified exact Navier–Stokes flows. The steady Stokes
problem is solved by minimizing its energy on bounded domains, and the pressure
of a minimum is recovered in $`H^1_{\mathrm{loc}}` on arbitrary open domains.
For axisymmetric flow with swirl, profiles in the squared radius give a
divergence-free Cartesian velocity, of finite energy under weighted moment
bounds; when the profiles satisfy the reduced equations, the velocity satisfies
the three-dimensional vorticity equation and has a pressure on convex sets.
Last comes the three-dimensional regularity problem: Fefferman's
alternatives (A) and (C) on $`\mathbb R^3` as two Lean propositions over the
classical solution class, an abstract continuation alternative for norm
trajectories, and the zero datum as a solved instance of the existence
predicate.

The De Gregorio model of transport and stretching in one dimension has its
equation-level theory here. Its blowup on the real line, the $`a=1` conclusion
of Chen–Hou–Huang's Theorem 1, is formalized on top of that theory in the
companion repository [BlowupZoo](https://github.com/Robertboy18/BlowupZoo): weighted stability and continuation construct a
global normalized trajectory from smooth initial data near the reference
profile, and the physical reconstruction gives finite-time blowup and
convergence to a nonzero stationary profile in dynamic coordinates.

The route here draws on {Informal.citet "evans-2010"}[]: transport from §2.1,
nonlinear conservation laws from
Chapter 3, potential functions from §4.4.2, diffusion from §2.3 and Chapter 7,
elliptic pressure recovery from Chapter 6, the Sobolev and compactness tools
from Chapter 5, and the variational Stokes problem from §8.4.4.
{Informal.citet "majda-bertozzi-2002"}[] supplies the fluid-specific kinematics
and vorticity viewpoint; {Informal.citet "leray-1934"}[] and Fefferman supply the
weak-solution and global-regularity statements, {Informal.citet "temam-2001"}[]
the solenoidal function spaces, and {Informal.citet "chen-hou-2022"}[] the nearly
self-similar Boussinesq analysis.

## Axisymmetric coordinates

Axial symmetry replaces the three-dimensional rotation group by rotations
around one fixed axis. Scalar fields are invariant under these rotations,
whereas velocity fields are equivariant. In cylindrical variables the natural
meridian measure is $`r\,dr\,dz`, and a streamfunction reconstructs the radial
and axial velocity components while enforcing incompressibility. The classical
analysis of {Informal.citet "ukhovskii-yudovich-1968"}[] is an early systematic
source for this axisymmetric formulation.

The weight $`r` has a geometric meaning: a meridian rectangle of area
$`dr\,dz` sweeps out a ring of volume $`2\pi r\,dr\,dz`. After integrating
out the angle, conservation must still account for that growing circumference.
Thus incompressibility becomes
$`\partial_r(ru_r)+\partial_z(ru_z)=0`, and the streamfunction enforces it
by making the two terms opposite mixed derivatives.

The rotation action, meridian lifts, streamfunction identities, and the
radial-four-plus-axial lift of the stream operator concern coordinates, not
flows. The flows come in
{ref "fluid-axisymmetric-swirl"}[Axisymmetric Flow with Swirl], where profiles
in the squared radius $`s=r^2` give velocities that are smooth across the
axis. The inverse direction, recovering the streamfunction from the vorticity,
is formalized for an abstract stream operator with a supplied bounded inverse:
composed with a bounded velocity reconstruction, it gives a Biot–Savart
operator whose norm is at most the product of the two constants.

:::group "fluid.axisymmetric"
Axisymmetric coordinates and streamfunctions
:::

:::definition "fluid.axisymmetric.coordinates" (parent := "fluid.axisymmetric") (lean := "PDE.CoordinateSystems.axisRotation, PDE.CoordinateSystems.IsInvariantUnderAxisRotation, PDE.CoordinateSystems.IsEquivariantUnderAxisRotation, PDE.CoordinateSystems.meridianCoordinates, PDE.CoordinateSystems.meridianLift")
Rotation through $`\theta` around the third coordinate axis preserves the
cylindrical variables $`r=\sqrt{x_1^2+x_2^2}` and $`z=x_3`. Scalar fields
may therefore be represented by meridian profiles $`g(r,z)`, while vector
fields use the corresponding equivariance condition.
:::

:::theorem "fluid.axisymmetric.rotation_geometry" (parent := "fluid.axisymmetric") (lean := "PDE.CoordinateSystems.axisRotation_add, PDE.CoordinateSystems.cylindricalRadius_axisRotation, PDE.CoordinateSystems.axialCoordinate_axisRotation, PDE.CoordinateSystems.isInvariantUnderAxisRotation_meridianLift") (uses := "fluid.axisymmetric.coordinates")
The rotations form an additive action,

$$`
R_{\theta+\phi}x=R_\theta(R_\phi x),
`

preserve $`r` and $`z`, and every meridian lift $`x\mapsto g(r(x),z(x))` is
rotation invariant.
:::

:::proof "fluid.axisymmetric.rotation_geometry"
Expand the first two coordinates using the angle-addition formulas for sine
and cosine. Their squared sum is unchanged, the third coordinate is fixed,
and invariance of a meridian lift follows because its two inputs are
unchanged.
:::

Invariance of $`r` and $`z` is what makes a meridian streamfunction
$`\psi(r,z)` a legitimate unknown: a swirl-free equivariant velocity field is
determined by two meridian components, and in the measure $`r\,dr\,dz` its
incompressibility says that $`(ru_r,ru_z)` is divergence-free in the
half-plane, which is the form a rotated gradient of one scalar takes.

:::definition "fluid.axisymmetric.streamfunction" (parent := "fluid.axisymmetric") (lean := "AxisymmetricFlow.streamfunctionRadialFlux, AxisymmetricFlow.streamfunctionAxialFlux, AxisymmetricFlow.streamfunctionVelocityReconstruction, AxisymmetricFlow.axisymmetricStreamOperator, AxisymmetricFlow.radialFourAxialLaplacian") (uses := "fluid.axisymmetric.coordinates")
For a meridian streamfunction $`\psi(r,z)`, we use

$$`
r u_r=-\partial_z\psi,\qquad r u_z=\partial_r\psi,
\qquad
L\psi=\partial_{rr}\psi-r^{-1}\partial_r\psi+\partial_{zz}\psi.
`

Division by $`r` is totalized in Lean, so velocity and vorticity statements
that use it retain an explicit off-axis hypothesis $`r\ne0`.
:::

:::theorem "fluid.axisymmetric.streamfunction_identities" (parent := "fluid.axisymmetric") (lean := "AxisymmetricFlow.divergence_streamfunctionFlux_eq_zero_of_contDiff, AxisymmetricFlow.radial_mul_reconstructedRadialVelocity, AxisymmetricFlow.radial_mul_reconstructedAxialVelocity, AxisymmetricFlow.axisymmetricStreamOperator_radialLift") (uses := "fluid.axisymmetric.streamfunction")
A $`C^2` streamfunction generates conservative meridian flux with zero
divergence. Away from $`r=0`, the reconstructed velocities satisfy the two
displayed flux identities, and for $`\psi=r^2\phi`,

$$`
L(r^2\phi)
=r^2\left(\partial_{rr}\phi+\frac3r\partial_r\phi+\partial_{zz}\phi\right).
`
:::

:::proof "fluid.axisymmetric.streamfunction_identities"
The divergence cancellation is equality of mixed partial derivatives. The
velocity identities cancel the nonzero radius in the reconstruction formulas.
For the radial lift, apply the product rule twice to $`r^2\phi`, substitute
into $`L`, and collect the radial terms.
:::

The coefficient $`3/r` identifies the new operator: a radial function in
four transverse dimensions has Laplacian
$`\phi_{rr}+3r^{-1}\phi_r`. Adding the axial derivative gives a
five-dimensional Laplacian acting on this lifted profile. This is why the
substitution $`\psi=r^2\phi` is useful for elliptic estimates. The identity
holds off the axis; whether the lifted profile extends smoothly across $`r=0`
depends on the original streamfunction near the axis.

# Conservation and Incompressibility

Particle paths and material derivatives turn local conservation of mass and
momentum into the Eulerian equations.

{include 2 Blueprint.Chapters.Fluid.Equations}

# Solenoidal Spaces, Compactness, and Pressure

Weak solutions of the fluid equations live on divergence-free fields, and the
energy estimates that control them come from a cancellation that holds only
there. The results specialize the weak-compactness theorems of the variational
chapter and the Bochner constraint theorems of the parabolic chapter to a
single linear constraint.

{include 2 Blueprint.Chapters.Fluid.WeakFoundations}

# Euler, Symmetry, and Boussinesq Flow

{include 2 Blueprint.Chapters.Fluid.Euler}
{include 2 Blueprint.Chapters.Fluid.Boussinesq}

# Stokes and Navier–Stokes Flow

{include 2 Blueprint.Chapters.Fluid.NavierStokes}
{include 2 Blueprint.Chapters.Fluid.ExactFlows}
{include 2 Blueprint.Chapters.Fluid.SteadyStokes}

# Axisymmetric Flow with Swirl
%%%
tag := "fluid-axisymmetric-swirl"
%%%

Axisymmetric flow with swirl is the setting of the computed scenario of
{Informal.citet "luo-hou-2014"}[] for three-dimensional Euler blowup. Away
from the axis its equations resemble the planar Boussinesq system, with the
squared swirl in the role of the temperature.

{include 2 Blueprint.Chapters.Fluid.AxisymmetricSwirl}

# The Three-Dimensional Regularity Problem

{include 2 Blueprint.Chapters.Fluid.MillenniumProblem}
