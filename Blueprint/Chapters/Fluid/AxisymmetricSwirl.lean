/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Fluid.NavierStokes
import Blueprint.Commands.Figures
import PDE.Fluid.Axisymmetric.CartesianReconstruction
import PDE.Fluid.Axisymmetric.CartesianVorticity
import PDE.Fluid.Axisymmetric.FiniteEnergy
import PDE.Fluid.Axisymmetric.LocalEvolution
import PDE.Fluid.Axisymmetric.NavierStokesEvolution
import PDE.Fluid.Axisymmetric.PhysicalEvolution
import PDE.Fluid.Axisymmetric.ReducedNavierStokes

/-!
# Axisymmetric flow with swirl

The reduced swirl, vorticity, and streamfunction equations; the Cartesian
velocity rebuilt from squared-radius profiles; its curl, vorticity transport,
local pressure, and finite energy.
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

set_option linter.hashCommand false in
#doc (Manual) "Axisymmetric Flow with Swirl" =>

:::group "fluid.axisymmetric_swirl"
Axisymmetric flow with swirl
:::

An axisymmetric velocity has three cylindrical components $`u_r,u_\theta,u_z`,
all functions of $`(r,z,t)`. For smooth Cartesian axisymmetric fields, the
swirl $`u_\theta` and azimuthal vorticity $`\omega_\theta` vanish on the
axis. Away from the axis, Hou and Li (Comm. Pure Appl. Math. 61, 2008) evolve

$$`
u_1=\frac{u_\theta}{r},\qquad
\omega_1=\frac{\omega_\theta}{r},\qquad
\psi_1=\frac{\psi}{r^2},
`

where $`\psi` is the Stokes streamfunction. The meridional velocity is then
$`u_r=-r\,\partial_z\psi_1` and $`u_z=2\psi_1+r\,\partial_r\psi_1`, and the
three reduced equations use the operator
$`\partial_r^2+3r^{-1}\partial_r+\partial_z^2`, which is the Laplacian of a
radial function in four transverse variables. The formulation goes back to
{Informal.citet "ukhovskii-yudovich-1968"}[].

:::definition "fluid.axisymmetric_swirl.reduced_system" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.ReducedFields, AxisymmetricFlow.reducedSwirlResidual, AxisymmetricFlow.reducedVorticityResidual, AxisymmetricFlow.reducedStreamFunctionResidual, AxisymmetricFlow.SatisfiesReducedSystemOn, AxisymmetricFlow.reducedRadialVelocity, AxisymmetricFlow.reducedAxialVelocity") (uses := "fluid.axisymmetric.streamfunction")
Off the axis, the reduced Navier–Stokes system for
$`(u_1,\omega_1,\psi_1)` with viscosity $`\nu` is

$$`
\begin{aligned}
\partial_tu_1+u_r\partial_ru_1+u_z\partial_zu_1
  &=2u_1\,\partial_z\psi_1+\nu\,L u_1,\\
\partial_t\omega_1+u_r\partial_r\omega_1+u_z\partial_z\omega_1
  &=2u_1\,\partial_zu_1+\nu\,L\omega_1,\\
-L\psi_1&=\omega_1,
\end{aligned}
\qquad L=\partial_r^2+\tfrac3r\partial_r+\partial_z^2.
`

The source terms describe stretching and vorticity production:
swirl is stretched by axial variation of the streamfunction, and the
centrifugal term $`\partial_z(u_1^2)` creates azimuthal vorticity. Lean records
each equation as a pointwise residual in the meridian coordinates, and
the reduced system asks all three to vanish on a chosen domain and time
set.
:::

Smoothness of the reduced profiles at the axis needs more than vanishing
of the numerators there. We instead start with smooth functions of $`s=r^2`
and set $`u_1=U(r^2,z)` and $`\psi_1=\Psi(r^2,z)`. The resulting Cartesian
formulas contain no division by the radius.

:::definition "fluid.axisymmetric_swirl.cartesian_velocity" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.axisymmetricVelocity, AxisymmetricFlow.meridionalVelocity, AxisymmetricFlow.swirlVelocity, AxisymmetricFlow.squaredCylindricalLift") (uses := "fluid.axisymmetric_swirl.reduced_system, fluid.axisymmetric.coordinates")
For profiles $`U,\Psi` of $`(s,z)` and $`x=(x_1,x_2,x_3)` with
$`s=x_1^2+x_2^2`, the reconstructed velocity is the sum of

$$`
\begin{aligned}
u_{\mathrm{mer}}(x)&=\bigl(-x_1\Psi_z,\;-x_2\Psi_z,\;2\Psi+2s\,\Psi_s\bigr),\\
u_{\mathrm{swirl}}(x)&=\bigl(-x_2U,\;x_1U,\;0\bigr),
\end{aligned}
`

with every profile evaluated at $`(s,x_3)`. In cylindrical components these are
$`u_r=-r\Psi_z`, $`u_z=2\Psi+2r^2\Psi_s` and $`u_\theta=rU`.
:::

{leanpde_figure "axisymmetric-meridional-flow"}

The simplest profile, $`\Psi(s,z)=z` with no swirl, gives the strain flow
$`(-x_1,-x_2,2x_3)` of the figure: a material cylinder narrows and lengthens,
and its volume $`2\pi R^2H` stays fixed because the radial factor in the
meridian measure compensates for the loss of meridional area.

:::theorem "fluid.axisymmetric_swirl.cartesian_divergence_free" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.spatialFieldDivergenceFree_axisymmetricVelocity, AxisymmetricFlow.isEquivariantUnderAxisRotation_axisymmetricVelocity, AxisymmetricFlow.axisymmetricVelocity_transverse_eq_zero_of_mem_symmetryAxis, AxisymmetricFlow.contDiff_axisymmetricVelocity") (uses := "fluid.axisymmetric_swirl.cartesian_velocity")
If $`U` is $`C^1` and $`\Psi` is $`C^2` on the whole $`(s,z)`-plane, the
reconstructed velocity is divergence free on all of $`\mathbb R^3`, the axis
included. It is equivariant under rotations about the $`x_3`-axis, and on the
axis its first two components vanish. Smooth profiles give a smooth velocity.
:::

:::proof "fluid.axisymmetric_swirl.cartesian_divergence_free"
The swirl part is divergence free because $`\partial_1(-x_2U)+\partial_2(x_1U)`
equals $`-2x_1x_2U_s+2x_1x_2U_s=0`. For the meridional part, the chain rule
through $`s=x_1^2+x_2^2` gives

$$`
\partial_1(-x_1\Psi_z)+\partial_2(-x_2\Psi_z)=-2\Psi_z-2s\Psi_{sz},
\qquad
\partial_3(2\Psi+2s\Psi_s)=2\Psi_z+2s\Psi_{sz},
`

which cancel. Equivariance follows because $`s` and $`x_3` are rotation
invariant while $`(-x_1,-x_2)` and $`(-x_2,x_1)` rotate with the point.
:::

:::theorem "fluid.axisymmetric_swirl.curl" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.spatialCurl_axisymmetricVelocity, AxisymmetricFlow.meridionalVorticityCoefficient") (uses := "fluid.axisymmetric_swirl.cartesian_velocity, fluid.euler.vorticity")
For $`C^1` swirl and $`C^2` streamfunction profiles,

$$`
\nabla\times u=\bigl(x_2M-x_1U_z,\;-x_1M-x_2U_z,\;2U+2s\,U_s\bigr),
\qquad M=\Psi_{zz}+8\Psi_s+4s\Psi_{ss}.
`

The vorticity of the swirl has the same shape as the meridional velocity of a
streamfunction, with $`U` in place of $`\Psi`. The azimuthal part is
$`\omega_\theta=-rM`, so $`\omega_1=-M`, and $`M` is the operator $`L` of the
reduced system rewritten in the variable $`s`.
:::

:::proof "fluid.axisymmetric_swirl.curl"
The curl is linear, so the meridional and swirl parts are treated separately.
Each component is a product of a coordinate with a lifted profile; the chain
rule for $`s` produces the factors $`2x_1` and $`2x_2`, and collecting terms
gives the displayed coefficients.
:::

The evolution equations are best stated in spacetime profiles $`U,\Omega,\Psi`
of $`(t,s,z)`. With the transport operator

$$`
D_t=\partial_t-2s\Psi_z\,\partial_s+(2\Psi+2s\Psi_s)\,\partial_z
`

and the squared-radius form $`L_s=8\partial_s+4s\partial_s^2+\partial_z^2` of
$`L`, the swirl and vorticity equations read
$`D_tU=2U\Psi_z+\nu L_sU` and $`D_t\Omega=2UU_z+\nu L_s\Omega`.

:::definition "fluid.axisymmetric_swirl.squared_radius_residuals" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.squaredRadiusNavierStokesSwirlResidual, AxisymmetricFlow.squaredRadiusNavierStokesVorticityResidual, AxisymmetricFlow.squaredRadiusEulerSwirlResidual, AxisymmetricFlow.squaredRadiusEulerVorticityResidual, AxisymmetricFlow.spacetimeAxisymmetricVorticityFromCoefficients") (uses := "fluid.axisymmetric_swirl.reduced_system, fluid.axisymmetric_swirl.curl")
The squared-radius residuals are

$$`
R_U=D_tU-2U\Psi_z-\nu L_sU,\qquad
R_\Omega=D_t\Omega-2UU_z-\nu L_s\Omega,
`

and $`\nu=0` gives the Euler versions. The vorticity reconstructed from the
coefficients is

$$`
\omega=\bigl(-x_1U_z-x_2\Omega,\;-x_2U_z+x_1\Omega,\;2U+2sU_s\bigr),
`

in which $`\Omega` is a separate unknown. It becomes the curl of the velocity
only once the stream equation $`\Omega=-L_s\Psi` holds.
:::

:::theorem "fluid.axisymmetric_swirl.vorticity_transport" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.navierStokesVorticityTransportResidual_axisymmetric_eq_zero, AxisymmetricFlow.eulerVorticityTransportResidual_axisymmetric_eq_zero, AxisymmetricFlow.navierStokesVorticityTransportResidual_axisymmetric_eq_zero_on, AxisymmetricFlow.eulerVorticityTransportResidual_axisymmetric_eq_zero_on") (uses := "fluid.axisymmetric_swirl.squared_radius_residuals, fluid.euler.vorticity_stretching_residual")
If $`U,\Omega,\Psi` are smooth and $`R_U=R_\Omega=0`, the Cartesian velocity
$`u` and the reconstructed vorticity $`\omega` satisfy the three-dimensional
vorticity equation

$$`
\partial_t\omega+(u\cdot\nabla)\omega-(\omega\cdot\nabla)u-\nu\Delta\omega=0
`

everywhere in spacetime. For Euler, $`C^2` swirl and streamfunction and a
$`C^1` vorticity coefficient suffice. Local versions hold on an open set of
profile arguments, where the profiles need not extend past its boundary.
:::

:::proof "fluid.axisymmetric_swirl.vorticity_transport"
Each Cartesian component of the transport residual is computed explicitly and
turns out to be a combination of the lifted reduced residuals with polynomial
coefficients in $`x`. The stretching term $`(\omega\cdot\nabla)u` supplies the
sources $`2U\Psi_z` and $`2UU_z`, and the lifted viscous term reproduces
$`L_s`. When both reduced residuals vanish, every component vanishes.
:::

:::theorem "fluid.axisymmetric_swirl.local_pressure" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.exists_pressure_momentum_equation_of_reducedEquationsOn, AxisymmetricFlow.spatialCurl_velocitySlice_eq_vorticityFromCoefficients_of_contDiffOn") (uses := "fluid.axisymmetric_swirl.vorticity_transport, fluid.navier_stokes.pressure_from_vorticity")
Let $`U,\Omega,\Psi` be smooth on an open set $`D` of profile arguments and
satisfy $`\Omega=-L_s\Psi`, $`R_U=0` and $`R_\Omega=0` there. On every open
convex spatial set $`S` and every time set $`I` whose points map into $`D`,
there is a pressure $`p(t,\cdot)` with

$$`
\partial_tu+(u\cdot\nabla)u+\nabla p=\nu\Delta u
\qquad\text{on }I\times S.
`

The pressure is chosen independently on each time slice.
:::

:::proof "fluid.axisymmetric_swirl.local_pressure"
The stream equation identifies $`\omega` with $`\nabla\times u` near each point
of $`D`, after replacing the profiles by compactly supported smooth ones that
agree nearby. The vorticity equation then says that the vector field
$`\nu\Delta u-D_tu` has zero curl on each slice. On a convex open set a
curl-free smooth field is a gradient, which is the Navier–Stokes pressure
theorem for the vorticity form.
:::

:::theorem "fluid.axisymmetric_swirl.finite_energy" (parent := "fluid.axisymmetric_swirl") (lean := "AxisymmetricFlow.finite_energy_axisymmetricVelocity_of_weighted_moments") (uses := "fluid.axisymmetric_swirl.cartesian_velocity, fluid.axisymmetric.coordinates")
Let $`U` be continuous and $`\Psi` be $`C^1`, and write
$`u_1=U(r^2,z)`, $`\psi_1=\Psi(r^2,z)`. If
$`r^2u_1^2`, $`r^2\psi_1^2`, $`r^2(\partial_r\psi_1)^2` and
$`r^2(\partial_z\psi_1)^2` are integrable for the meridian measure
$`r\,dr\,dz`, then $`u\in L^2(\mathbb R^3)` and

$$`
\int_{\mathbb R^3}|u|^2\,dx
=2\pi\int_0^\infty\!\!\int_{\mathbb R}
r^2\bigl(u_1^2+(\partial_r\psi_1)^2+(\partial_z\psi_1)^2\bigr)\,r\,dz\,dr.
`
:::

:::proof "fluid.axisymmetric_swirl.finite_energy"
In cylindrical coordinates $`|u|^2=r^2u_1^2+r^2(\partial_z\psi_1)^2
+(2\psi_1+r\partial_r\psi_1)^2`. Expanding the last square gives
$`4\psi_1^2+4r\psi_1\partial_r\psi_1+r^2(\partial_r\psi_1)^2`. Against the
weight $`r`, the first two terms are $`\partial_r(2r^2\psi_1^2)`, which
integrates to zero on almost every axial line because the moment of
$`\psi_1^2` is finite. The cylindrical change of variables then gives the
factor $`2\pi`.
:::
