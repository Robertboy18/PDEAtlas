/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.GreenRepresentation
import Blueprint.Chapters.Fluid.Equations
import Blueprint.Chapters.Fluid.Euler
import PDE.Analysis.Calculus.Jet.NormalTaylor
import PDE.Analysis.Evolution.FiniteRankResponse
import PDE.CoordinateSystems.Polar
import PDE.Elliptic.Classical.OneDimensional.Dirichlet
import PDE.FDeriv.Polar.Laplacian
import PDE.Fluid.Boussinesq.Similarity.Reduction
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling
import PDE.Fluid.Boussinesq.VorticityStream.Normalization
import PDE.Fluid.Boussinesq.VorticityStream.PoissonSymmetry
import PDE.Fluid.Boussinesq.VorticityStream.PrimitiveBridge
import PDE.Spaces.Holder.HigherOrder.Norm

/-!
# Inviscid Boussinesq flow, dynamic normalization, and similarity reduction
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
#doc (Manual) "Inviscid Boussinesq Flow" =>

:::group "fluid.boussinesq"
Two-dimensional inviscid Boussinesq flow
:::

The inviscid Boussinesq system couples incompressible momentum to an advected
scalar. In the vertical-buoyancy convention used here,

$$`
\partial_t u+(u\cdot\nabla)u+\nabla p=\theta e_2,
\qquad \nabla\cdot u=0,
\qquad \partial_t\theta+u\cdot\nabla\theta=0.
`

Chen and Hou introduce the upper-half-plane vorticity–streamfunction system
and its dynamic rescaling in §2.1, equations (2.3)–(2.7)
{Informal.citet "chen-hou-2022"}[]. We keep that
formulation separate from the standard primitive velocity–pressure equations:
the buoyancy orientation and scalar-vorticity sign are explicit. A checked
curl calculation identifies exactly which primitive convention yields the
paper's vorticity source. The dynamic rescaling of the upper-half-plane
equations, its normalization, and an independent fixed-power primitive
calculation are checked as well, and the half-plane Green potential inverts the
Poisson problem for compactly supported $`C^2` sources with an odd extension
across the boundary.

The scalar drives rotation through its horizontal variation. With the
counterclockwise convention
$`\omega=\partial_1u_2-\partial_2u_1`, taking curl of the displayed
buoyancy force gives $`\partial_1\theta`. A spatially constant temperature
has zero curl and its force can be absorbed into the pressure by replacing
$`p` with $`p-\theta x_2`. For sufficiently smooth fields, differentiating
the transport equation gives

$$`
(\partial_t+u\cdot\nabla)\nabla\theta
=-(\nabla u)^{\mathsf T}\nabla\theta.
`

Temperature is constant along each particle path, yet its gradient can grow
as neighboring paths stretch and compress. That growing gradient feeds the
vorticity equation, whose velocity in turn transports the temperature.
The feedback explains why the transported scalar remains dynamically active.
Reversing the curl or buoyancy convention reverses the corresponding source
sign.

:::definition "fluid.boussinesq.classical" (parent := "fluid.boussinesq") (lean := "Boussinesq.BoussinesqFields, Boussinesq.buoyancyForce, Boussinesq.IsClassicalSolutionOn") (uses := "fluid.equations.operators")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2, equations (2.3)–(2.7)"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 1, endLine := 26 }
  }]
}
%%%
A classical Boussinesq field consists of velocity $`u`, temperature $`\theta`,
and pressure $`p`. On the chosen set of times all three fields are jointly
$`C^1`, their relevant slices are classically differentiable, and the three
displayed equations hold pointwise. The impermeable boundary condition is a
separate predicate, not part of the whole-space model. Velocity is an unknown
here, not reconstructed from vorticity or a half-plane streamfunction.
:::

For the rescaling calculation, it is useful to eliminate pressure and recover
velocity from a streamfunction. With $`C^2` regularity, its mixed partials cancel
in the divergence, while taking curl leaves a Laplacian with a sign determined
by our convention. Recovering the streamfunction from vorticity then requires
solving a Poisson problem in the half-plane.

:::definition "fluid.boussinesq.planar_streamfunction" (parent := "fluid.boussinesq") (lean := "IncompressibleFlow.planarStreamVelocity, IncompressibleFlow.spatialPlanarVorticity, IncompressibleFlow.spatialPlanarClockwiseVorticity") (uses := "fluid.equations.operators")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2, equation (2.3c)"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 1, endLine := 26 }
  }]
}
%%%
For a planar streamfunction $`\phi`, define

$$`
u=(-\partial_2\phi,\partial_1\phi).
`

The counterclockwise scalar curl of a planar velocity is
$`\partial_1u_2-\partial_2u_1`; the clockwise curl
$`\partial_2u_1-\partial_1u_2` is the convention of the paper.
:::

:::theorem "fluid.boussinesq.planar_streamfunction_identities" (parent := "fluid.boussinesq") (lean := "IncompressibleFlow.divergence_planarStreamVelocity_eq_zero, IncompressibleFlow.spatialPlanarVorticity_planarStreamVelocity, IncompressibleFlow.spatialPlanarClockwiseVorticity_planarStreamVelocity") (uses := "fluid.boussinesq.planar_streamfunction")
For a $`C^2` streamfunction, the velocity is incompressible, its standard
scalar curl is $`\Delta\phi`, and its clockwise scalar curl is $`-\Delta\phi`.
:::

:::proof "fluid.boussinesq.planar_streamfunction_identities"
Expand the two velocity components. The divergence is
$`-\partial_1\partial_2\phi+\partial_2\partial_1\phi`, which vanishes by
the $`C^2` mixed-partial theorem. Expanding either scalar curl leaves the two
diagonal second derivatives with the corresponding sign.
:::

With the sign fixed, the paper's system can be stated in the three scalar
unknowns $`(\omega,\theta,\phi)`: the clockwise vorticity is transported and
driven by $`\partial_1\theta`, the temperature is transported, and the
streamfunction is tied to $`\omega` by a Dirichlet problem on the upper
half-plane. Velocity appears only as $`(-\partial_2\phi,\partial_1\phi)`.

:::definition "fluid.boussinesq.vorticity_stream_model" (parent := "fluid.boussinesq") (lean := "Boussinesq.VorticityStreamFields, Boussinesq.IsClassicalVorticityStreamSolutionOn, Boussinesq.upperHalfPlane") (uses := "fluid.boussinesq.planar_streamfunction_identities")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2, equations (2.3a)–(2.3c)"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 1, endLine := 26 }
  }]
}
%%%
On $`\mathbb R^2_+=\{x_2>0\}`, the physical equations are

$$`
\partial_t\omega+u\cdot\nabla\omega=\partial_1\theta,
\qquad
\partial_t\theta+u\cdot\nabla\theta=0,
\qquad
-\Delta\phi=\omega.
`

The boundary trace is $`\phi(x_1,0,t)=0`. The fields are defined on the whole
plane. Vorticity and temperature are jointly $`C^1` on the admitted times,
with ambient time differentiability there; every streamfunction slice is
spatially $`C^2`. No joint time regularity of the streamfunction is required.
The equations are imposed only in the open upper half-plane.
:::

The definition stores $`-\Delta\phi=\omega` and the zero trace as separate
equations.

:::theorem "fluid.boussinesq.vorticity_stream_bridges" (parent := "fluid.boussinesq") (lean := "Boussinesq.spatialPlanarClockwiseVorticity_vorticityStreamVelocity, Boussinesq.divergence_vorticityStreamVelocity_eq_zero, Boussinesq.normalVelocity_eq_zero_on_horizontalBoundary_of_zeroStreamFunction") (uses := "fluid.boussinesq.vorticity_stream_model")
The streamfunction equation identifies $`\omega` with the clockwise curl of
$`u`; the reconstructed velocity is incompressible; and a differentiable zero
streamfunction trace implies zero normal velocity at $`x_2=0`.
:::

:::proof "fluid.boussinesq.vorticity_stream_bridges"
The first two claims are the planar streamfunction identities. For the boundary
claim, restrict $`\phi` to the horizontal coordinate line. Its trace is the
constant zero function, so its tangential derivative $`\partial_1\phi`
vanishes. This derivative is precisely the normal velocity component.
:::

The primitive and vorticity-stream formulations are related by taking the
clockwise curl of the momentum equation. The pressure drops out,
incompressibility turns the curl of the convective term into
$`u\cdot\nabla\omega`, and the buoyancy $`\kappa\theta e_2` contributes
$`-\kappa\,\partial_1\theta`; matching this with the paper's source
$`+\partial_1\theta` is what pins down the buoyancy orientation.

:::theorem "fluid.boussinesq.primitive_vorticity_bridge" (parent := "fluid.boussinesq") (lean := "Boussinesq.spatialPlanarClockwiseVorticity_buoyancyForceWithCoefficient, Boussinesq.BoussinesqFields.clockwiseVorticity_equation_of_momentum, Boussinesq.BoussinesqFields.clockwiseVorticity_equation_of_downwardMomentum, Boussinesq.BoussinesqFields.toVorticityStreamFields_isClassicalSolutionOn") (uses := "fluid.boussinesq.classical, fluid.boussinesq.vorticity_stream_bridges, fluid.euler.vorticity_from_momentum")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2, equations (2.3a)–(2.3c)"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 9, endLine := 26 }
  }]
}
%%%
Assume $`u` is jointly $`C^2` on spacetime and, at the time considered,
$`p` and $`\theta` are respectively $`C^2` and $`C^1` on the whole plane.
If the primitive momentum force is $`\kappa\theta e_2` and clockwise
vorticity is $`\omega=\partial_2u_1-\partial_1u_2`, then on every open
spatial domain where the primitive momentum equation and incompressibility
hold,

$$`
\partial_t\omega+u\cdot\nabla\omega=-\kappa\,\partial_1\theta.
`

Thus the paper's positive source is the downward-buoyancy choice
$`\kappa=-1`. Under that convention, with a supplied $`C^2` streamfunction
satisfying $`u=(-\partial_2\phi,\partial_1\phi)` and the zero boundary
trace, a primitive solution with jointly continuously differentiable temperature
solving both the momentum equation with force $`-\theta e_2` and the temperature
transport equation induces the full upper-half-plane vorticity–streamfunction solution predicate.
:::

:::proof "fluid.boussinesq.primitive_vorticity_bridge"
Take clockwise curl locally inside the open spatial domain. Equality on a
neighborhood gives equality of the required coordinate derivatives, while
mixed derivatives cancel the pressure curl. For a divergence-free planar
velocity, the curl of the convective term is $`u\cdot\nabla\omega`; the
vertical force contributes $`-\kappa\partial_1\theta`. The streamfunction identities then provide
incompressibility and $`-\Delta\phi=\omega`, while the primitive scalar
transport equation and zero trace give the remaining solution fields and
boundary condition.
:::

Self-similar blow-up is studied by rescaling space, time, and the amplitudes of
$`\omega` and $`\theta` with time-dependent factors, with the aim that a
solution collapsing to the origin becomes one converging to a stationary
profile. The factors are not free: the streamfunction scale is forced by
$`-\Delta\phi=\omega`, and transforming the source $`\partial_1\theta` requires
the amplitude relation $`C_\theta C_l=C_\omega^2`.

The sign of the length rate determines whether these coordinates shrink or
expand in physical space. The
De Gregorio blowup in the companion repository [BlowupZoo](https://github.com/Robertboy18/BlowupZoo) gives an expanding
real-line example with the corresponding physical clock.

:::definition "fluid.boussinesq.dynamic_rescaling" (parent := "fluid.boussinesq") (lean := "Boussinesq.DynamicRescalingData, Boussinesq.SatisfiesDynamicRescalingLawsAt, Boussinesq.dynamicallyRescaledFields, Boussinesq.SatisfiesDynamicRescaledSystemOn") (uses := "fluid.boussinesq.vorticity_stream_model")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1, equations (2.4)–(2.7)"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 1, endLine := 26 }
  }]
}
%%%
At rescaled time $`\tau`, set

$$`
\widetilde\omega(x,\tau)=C_\omega\omega(C_lx,t(\tau)),\qquad
\widetilde\theta(x,\tau)=C_\theta\theta(C_lx,t(\tau)),
`

$$`
\widetilde\phi(x,\tau)=C_\omega C_l^{-2}\phi(C_lx,t(\tau)).
`

The scale laws are $`C_\omega'=c_\omega C_\omega`,
$`C_l'=-c_lC_l`, $`C_\theta'=c_\theta C_\theta`, and
$`t'=C_\omega`, together with $`C_\theta C_l=C_\omega^2` and
$`c_\theta=c_l+2c_\omega`, with $`C_l>0` so dilation preserves the upper
half-plane. The complete transformed-system predicate reuses
the canonical pair of rescaled scalar equations and adds the streamfunction
Poisson equation and zero boundary trace.
:::

After the change of variables, the rescaled scalar fields obey equations of the
same transport type as before, with two modifications: the transport velocity
acquires the dilation term $`c_lx`, and each equation gains a linear amplitude
term with coefficient $`c_\omega` or $`c_\theta`.

:::definition "fluid.boussinesq.rescaled_system" (parent := "fluid.boussinesq") (lean := "Boussinesq.rescaledTransportVelocity, Boussinesq.rescaledVorticityResidual, Boussinesq.rescaledTemperatureResidual, Boussinesq.SatisfiesRescaledVorticityEquationAtTime, Boussinesq.SatisfiesRescaledTemperatureEquationAtTime, Boussinesq.SatisfiesRescaledScalarEquationsOn") (uses := "fluid.boussinesq.vorticity_stream_model")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1, equation (2.8)"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 9, endLine := 26 }
  }]
}
%%%
For rate functions $`c_l,c_\omega,c_\theta`, the rescaled transport velocity is

$$`
V(x,\tau)=c_l(\tau)x+u(x,\tau).
`

The scalar part of the rescaled system is the pair of pointwise equations

$$`
\partial_\tau\omega+V\cdot\nabla\omega
 =c_\omega\omega+\partial_1\theta,
\qquad
\partial_\tau\theta+V\cdot\nabla\theta=c_\theta\theta.
`

The equations are stated for arbitrary rate functions, independently of any
particular scaling data, and may be imposed either at one time or on a
specified space-time domain. The two residual functions are the left side
minus the right side of the corresponding equation.
:::

Writing each equation as a residual makes exact solutions and approximate
profiles comparable: an exact solution has zero residual, whereas the paper's
approximate profile has a small residual that must be estimated in a weighted
space.

:::theorem "fluid.boussinesq.rescaled_residuals" (parent := "fluid.boussinesq") (lean := "Boussinesq.satisfiesRescaledVorticityEquationAtTime_iff_residual_eq_zero, Boussinesq.satisfiesRescaledTemperatureEquationAtTime_iff_residual_eq_zero") (uses := "fluid.boussinesq.rescaled_system")
Each rescaled scalar equation holds on a domain exactly when its pointwise
residual vanishes throughout that domain.

$$`
L_\omega=R_\omega\text{ on }\Omega
\Longleftrightarrow \mathcal R_\omega=0\text{ on }\Omega,
\qquad
L_\theta=R_\theta\text{ on }\Omega
\Longleftrightarrow \mathcal R_\theta=0\text{ on }\Omega.
`
:::

:::proof "fluid.boussinesq.rescaled_residuals"
Expand the residual as the left side minus the right side and rearrange.
:::

The equations are imposed only in the open half-plane, yet the normalization
reads off derivatives at the origin, which lies on the boundary. For
fields smooth across the boundary the gap is closed by continuity: an identity
between continuous functions that holds on a set persists on its closure, and
the same argument applies to its spatial derivatives.

:::theorem "fluid.boussinesq.rescaled_boundary_continuation" (parent := "fluid.boussinesq") (lean := "Boussinesq.satisfiesRescaledVorticityEquationAtTime_closure, Boussinesq.satisfiesRescaledTemperatureEquationAtTime_closure, Boussinesq.partialDeriv_rescaledVorticityEquationAtTime_eq_on_closure, Boussinesq.secondPartialDeriv_rescaledTemperatureEquationAtTime_eq_on_closure") (uses := "fluid.boussinesq.rescaled_system")
For globally continuously differentiable representatives, either rescaled scalar equation holding
on a spatial domain also holds on its closure. If the domain is open, then
with one further degree of regularity for each spatial differentiation, the
once-differentiated vorticity equation and twice-differentiated temperature
equation extend to the closure as well. This applies in particular to the open
upper half-plane.

Writing $`L_\omega=\partial_\tau\omega+V\cdot\nabla\omega`,
$`R_\omega=c_\omega\omega+\partial_1\theta`,
$`L_\theta=\partial_\tau\theta+V\cdot\nabla\theta`, and
$`R_\theta=c_\theta\theta`, the conclusions are

$$`
L_\omega=R_\omega\text{ on }\Omega
\Longrightarrow
L_\omega=R_\omega\text{ and }\partial_iL_\omega=\partial_iR_\omega
\text{ on }\overline{\Omega},
`

$$`
L_\theta=R_\theta\text{ on }\Omega
\Longrightarrow
L_\theta=R_\theta\text{ and }
\partial_i\partial_jL_\theta=\partial_i\partial_jR_\theta
\text{ on }\overline{\Omega}.
`
:::

:::proof "fluid.boussinesq.rescaled_boundary_continuation"
Both sides of each interior identity are continuous. Equality therefore
passes to the closure. On an open domain, the differentiated statements follow
by first differentiating the equality and then applying the same closure
argument to the continuous derivative fields.
:::

The rescaled equations become a theorem rather than a definition once the scale
laws are imposed. Differentiating the pullbacks by the chain rule, the dilation
term comes from $`C_l'=-c_lC_l`, the amplitude terms from $`C_\omega'` and
$`C_\theta'`, and the physical time derivative enters through $`t'=C_\omega`;
the amplitude compatibility is what makes the transformed source match the
transformed advection terms.

:::theorem "fluid.boussinesq.dynamic_rescaling_equations" (parent := "fluid.boussinesq") (lean := "Boussinesq.vorticityEquation_dynamicallyRescaledFields, Boussinesq.temperatureEquation_dynamicallyRescaledFields, Boussinesq.streamFunctionEquation_dynamicallyRescaledFields, Boussinesq.dynamicallyRescaledFields_satisfySystemOn") (uses := "fluid.boussinesq.dynamic_rescaling, fluid.boussinesq.rescaled_system")
A classical upper-half-plane solution on an open physical-time set satisfies
the following transformed system at every rescaled time whose physical-time
image belongs to that set and at which the scale laws hold:

$$`
\partial_\tau\widetilde\omega+
 (c_lx+\widetilde u)\cdot\nabla\widetilde\omega
 =c_\omega\widetilde\omega+\partial_1\widetilde\theta,
`

$$`
\partial_\tau\widetilde\theta+
 (c_lx+\widetilde u)\cdot\nabla\widetilde\theta
 =c_\theta\widetilde\theta,
\qquad -\Delta\widetilde\phi=\widetilde\omega,
`

with the zero streamfunction boundary trace preserved.
:::

:::proof "fluid.boussinesq.dynamic_rescaling_equations"
Differentiate the three pullbacks. The derivative of $`C_lx` contributes
$`-c_l C_lx`, which cancels advection by $`c_lx`. The reconstructed velocity
has scale $`C_\omega C_l^{-1}`. Vorticity advection and the physical
vorticity time-derivative term both carry $`C_\omega^2`; temperature advection
carries $`C_\omega C_\theta`. The source derivative carries $`C_\theta C_l`,
equal to $`C_\omega^2` by compatibility. The streamfunction scale contributes
$`C_\omega C_l^{-2}C_l^2=C_\omega`, preserving the Poisson equation.
Positive $`C_l` preserves the upper half-plane, and the boundary trace remains
zero under tangential dilation.
:::

The normalization also relies on symmetry: the paper's profile has odd
vorticity and even temperature under reflection in the vertical axis. Vorticity
parity does not automatically pass to the streamfunction, because $`\phi` is
determined by $`\omega` only through the Dirichlet problem. The reflected and
negated streamfunction solves the same problem, so uniqueness in a suitable
class transfers the parity.

:::theorem "fluid.boussinesq.poisson_symmetry_transfer" (parent := "fluid.boussinesq") (lean := "Boussinesq.IsClassicalUpperHalfPlaneDirichletPoissonSolution.tangentiallyOdd_of_mem, Boussinesq.tangentialReflectedNegation, Boussinesq.IsClassicalUpperHalfPlaneDirichletPoissonSolution, Boussinesq.IsClassicalUpperHalfPlaneDirichletPoissonSolution.reflectedNegation, PDE.Common.laplacian_comp_coordinateReflection") (uses := "fluid.boussinesq.vorticity_stream_model")
Let $`R(x_1,x_2)=(-x_1,x_2)` and let $`\mathcal A` be an admissible class of
whole-plane streamfunctions, closed under $`\phi\mapsto-\phi\circ R`.
Suppose $`\phi\in\mathcal A` is $`C^2` on the whole plane and the Dirichlet
problem is unique in $`\mathcal A`. Then

$$`
-\Delta\phi=\omega\text{ in }\mathbb H,\qquad
\phi|_{\partial\mathbb H}=0,\qquad
\omega\circ R=-\omega
\quad\Longrightarrow\quad
\phi\circ R=-\phi.
`

The theorem keeps $`\mathcal A` explicit. Uniqueness among all smooth
functions on the unbounded half-plane would be false without a decay, energy,
or representation condition.
:::

:::proof "fluid.boussinesq.poisson_symmetry_transfer"
The Laplacian is invariant under $`R`, so $`-\phi\circ R` solves the same
Poisson equation as $`\phi`. It has the same zero boundary trace and remains
in $`\mathcal A` by reflection stability. Uniqueness in $`\mathcal A` gives
$`-\phi\circ R=\phi`.
:::

Uniqueness is an assumption in the previous theorem. When the streamfunction is
given explicitly by the half-plane Green function, the same parity can instead
be read off from the kernel: reflection preserves the half-plane and the
method-of-images kernel, so oddness of the source transfers to the potential
directly.

:::theorem "fluid.boussinesq.green_potential_symmetry" (parent := "fluid.boussinesq") (lean := "Boussinesq.halfSpaceGreenPotential_tangentiallyOdd, Boussinesq.halfSpaceGreenPotential_tangentiallyOdd_of_integrable_log_weight, Boussinesq.halfSpaceGreenPotential_vanishesOnHorizontalBoundary, Boussinesq.contDiff_two_halfSpaceGreenPotential_of_normalOdd, Boussinesq.halfSpaceGreenPotential_satisfiesPoissonEquation_of_normalOdd, Boussinesq.halfSpaceGreenPotential_isClassicalDirichletSolution_of_normalOdd, Boussinesq.halfSpaceGreenPotential_tangentiallyOdd_of_testFunction") (uses := "elliptic.green.half_space.potential_geometry, elliptic.green.half_space.planar_images_integrable, elliptic.green.half_space.planar_inversion, fluid.boussinesq.vorticity_stream_model")
If $`\omega` is odd under
$`R(x_1,x_2)=(-x_1,x_2)` and its method-of-images Green integrand is
integrable at every field point, then

$$`
\phi(x)=\int_{\mathbb H}G_{\mathbb H}(y,x)\omega(y)\,dy
`

is odd under $`R` and has zero horizontal boundary trace. These conclusions
are proved from kernel geometry. Normal oddness together with integrability of
$`\Phi_2(x-\cdot)\omega` identifies the same integral with the whole-space
convolution, without compact support. If, in addition, $`\omega` is a
compactly supported $`C^2` whole-space function, then the integral is $`C^2`
and satisfies $`-\Delta\phi=\omega` on the upper half-plane. The approximate
profile of the paper has a nonintegrable $`r^{\bar\alpha_1}\simeq r^{-1/3}`
far field, which Section 7.2.1 treats by a semi-analytic homogeneous
streamfunction and an angular Dirichlet ODE before estimating a
faster-decaying numerical remainder.
:::

:::proof "fluid.boussinesq.green_potential_symmetry"
Apply the generic half-space potential theorem to reflection in coordinate
zero. This reflection preserves $`x_2>0`; kernel invariance and the
measure-preserving change of variables transfer oddness of $`\omega` to
$`\phi`. Boundary cancellation is pointwise in the source variable before
integration. Under the normal odd-extension hypothesis, the planar
method-of-images theorem identifies the potential with $`\Phi_2*\omega`
whenever that convolution is integrable. The compact $`C^2` inversion theorem
then proves the pointwise Poisson equation.
:::

The semi-analytic far-field ansatz in Section 7.2.1 is governed by the exact
polar identity

$$`
-\Delta_{\mathrm{pol}}\bigl(r^{2+\bar\alpha_1}f(\beta)\bigr)
=r^{\bar\alpha_1}
  \left(-f''(\beta)-(2+\bar\alpha_1)^2f(\beta)\right).
`

Thus the angular Dirichlet equation
$`(-\partial_\beta^2-(2+\bar\alpha_1)^2)f=g_1` produces the uncut source
$`r^{\bar\alpha_1}g_1(\beta)` at positive radii. Lean proves this homogeneous
polar calculation. It also proves the exact commutator introduced by the
radial cutoff $`\chi`: the extra terms involve only
$`\Delta_{\mathrm{rad}}\chi` and $`\chi'`. A general $`C^2` pullback theorem
identifies this polar operator with the Cartesian Euclidean Laplacian away
from $`r=0`. These identities are the
{bpref "foundations.coordinates.planar_polar_homogeneous"}[homogeneous polar
Laplacian theorem].

:::theorem "fluid.boussinesq.angular_dirichlet_inverse" (parent := "fluid.boussinesq") (lean := "PDE.Elliptic.Classical.OneDimensional.dirichletSolution, PDE.Elliptic.Classical.OneDimensional.dirichletSolution_zero, PDE.Elliptic.Classical.OneDimensional.dirichletSolution_right, PDE.Elliptic.Classical.OneDimensional.dirichletSolution_equation, PDE.Elliptic.Classical.OneDimensional.contDiff_dirichletSolution, PDE.Elliptic.Classical.OneDimensional.abs_dirichletSolution_le, PDE.Elliptic.Classical.OneDimensional.abs_deriv_dirichletSolution_le, PDE.Elliptic.Classical.OneDimensional.exists_dirichletSolution_near_of_residual_bound, PDE.CoordinateSystems.exists_angularDirichletSolution, PDE.CoordinateSystems.neg_planarPolarLaplacian_dirichletSolution, PDE.Elliptic.Classical.OneDimensional.oscillator_eq_of_initial_jet, PDE.Elliptic.Classical.OneDimensional.oscillator_odd_about_zero, PDE.Elliptic.Classical.OneDimensional.dirichletSolution_odd_about_right, PDE.Elliptic.Classical.OneDimensional.dirichletSolution_second_deriv_right_eq_zero, PDE.FDeriv.contDiffAt_two_polarCoord, PDE.FDeriv.contDiffAt_profileFromPolar_rpow_mul, EuclideanLaplacian.neg_laplacian_profileFromPolar_rpow_add_two_mul, PDE.CoordinateSystems.neg_laplacian_profileFromPolar_dirichletSolution") (uses := "foundations.coordinates.planar_polar_homogeneous")
Let $`g:\mathbb R\to\mathbb R` be continuous, set $`L=\pi/2`, and
suppose $`-2<\alpha<0`. With $`a=2+\alpha`, there is a classical solution

$$`-f''-a^2f=g,\qquad f(0)=f(L)=0.`

The construction keeps the resonance condition explicit. Define

$$`
\begin{aligned}
C(\beta)&=\int_0^\beta\cos(as)g(s)\,ds,\\
S(\beta)&=\int_0^\beta\sin(as)g(s)\,ds.
\end{aligned}
`

Then

$$`
\begin{aligned}
f(\beta)&=A\sin(a\beta)\\
&\quad+\frac{\cos(a\beta)S(\beta)-\sin(a\beta)C(\beta)}{a},\\
A&=\frac{\sin(aL)C(L)-\cos(aL)S(L)}{a\sin(aL)}.
\end{aligned}
`

Here $`0<a<2`, so $`0<aL<\pi` and the denominator is nonzero.
Continuous forcing gives $`f\in C^2`. If $`|g|\leq M` on $`[0,L]`, with
$`M\geq0`, the formula also gives the explicit sufficient bound for $`0\leq\beta\leq L`:

$$`
|f(\beta)|\leq\frac{2ML}{a}
\left(1+\frac1{|\sin(aL)|}\right).
`

On the same interval, its first derivative satisfies

$$`
|f'(\beta)|\leq2ML\left(1+\frac1{|\sin(aL)|}\right).
`

The homogeneous streamfunction $`r^{2+\alpha}f(\beta)` therefore has
negative polar Laplacian $`r^\alpha g(\beta)` for $`r>0`.
A certified residual gives a quantitative correction as well. Let $`q\in C^2`
have exact zero endpoint values and suppose

$$`|g+q''+a^2q|\leq\delta\quad\text{on }[0,L].`

Apply the same inverse to this residual and add the correction to $`q`.
The result satisfies the exact forced equation and boundary values, with
value error at most $`2\delta L(1+1/|\sin(aL)|)/a` and first-derivative
error at most $`2\delta L(1+1/|\sin(aL)|)`. Thus a tighter residual
certificate improves both error bounds through the same theorem.

The inverse also gives a Cartesian field. For positive radius and
$`-\pi<\beta<\pi`, the inverse polar Jacobian proves $`C^2` regularity of
the reconstructed streamfunction. The local chart round trip then gives

$$`
-\Delta U(r\cos\beta,r\sin\beta)=r^\alpha g(\beta).
`

This excludes the origin and the chart's negative horizontal cut. If the
forcing is odd about $`L`, then the solution is odd there too:
$`f(2L-\beta)=-f(\beta)` and $`f''(L)=0`. Uniqueness follows from the conserved
energy of the difference of two oscillator solutions with the same initial
value and slope. These are tangential angular identities; the normal extension
of the source vorticity can jump at the physical boundary and needs a separate
weak argument.
:::

:::proof "fluid.boussinesq.angular_dirichlet_inverse"
Differentiate the two integrals by the fundamental theorem of calculus.
The terms involving $`g` cancel in the first derivative and combine to
$`-g` in the second, giving the forced equation. At the left endpoint both
integrals vanish; the chosen amplitude cancels the value at the right
endpoint. Bounding sine and cosine by one bounds each integral by $`M\beta`
and gives the displayed estimate. The homogeneous polar identity then
supplies the radial factor.
:::

:::theorem "fluid.boussinesq.stream_symmetry_bridge" (parent := "fluid.boussinesq") (lean := "Boussinesq.hasReflectionSymmetryAtTime_of_streamFunction, PDE.Common.IsOddUnderCoordinateReflection.partialDeriv_same, PDE.Common.IsOddUnderCoordinateReflection.partialDeriv_of_ne, Boussinesq.planarStreamVelocity_zero_isOddUnderTangentialReflection, Boussinesq.planarStreamVelocity_one_isEvenUnderTangentialReflection") (uses := "fluid.boussinesq.vorticity_stream_bridges, fluid.boussinesq.poisson_symmetry_transfer, fluid.boussinesq.green_potential_symmetry")
Let $`R(x_1,x_2)=(-x_1,x_2)` and
$`u=(-\partial_2\phi,\partial_1\phi)`. If a $`C^1` streamfunction is odd under
$`R`, then

$$`
\partial_2\phi(Rx)=-\partial_2\phi(x),\qquad
\partial_1\phi(Rx)=\partial_1\phi(x),
`

and therefore $`u_1(Rx)=-u_1(x)` while $`u_2(Rx)=u_2(x)`. If in addition
$`\phi(x_1,0)=0`, then $`u_2(x_1,0)=0`. Thus the scalar symmetries together
with odd streamfunction parity and the Dirichlet trace imply all velocity
conditions used by the normalization calculation.
:::

:::proof "fluid.boussinesq.stream_symmetry_bridge"
Differentiate $`\phi\circ R=-\phi`. Tangential differentiation introduces
one sign from $`R` and one from oddness, while normal differentiation
introduces only the sign from oddness. The boundary identity follows by
differentiating the zero trace tangentially.
:::

Dynamic rescaling leaves the rates $`c_l,c_\omega,c_\theta` undetermined. The
paper fixes two of them by requiring the origin traces $`\omega_x(0)` and
$`\theta_{xx}(0)` to stay constant in time, the third being the compatibility
law $`c_\theta=c_l+2c_\omega`, and the symmetry bridge supplies the velocity
conditions this calculation uses. Because division is totalized in Lean, the
nondegeneracy $`\omega_x(0)\ne0` that makes the quotient meaningful is carried
as an explicit hypothesis.

:::definition "fluid.boussinesq.normalization" (parent := "fluid.boussinesq") (lean := "Boussinesq.HasReflectionSymmetryAtTime, Boussinesq.vorticityXAtOrigin, Boussinesq.temperatureXXAtOrigin, Boussinesq.tangentialVelocityXAtOrigin, Boussinesq.SatisfiesRescalingNormalizationAt") (uses := "fluid.boussinesq.rescaled_system, fluid.boussinesq.stream_symmetry_bridge")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1, equation (2.9)"
    text := some {
      path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 14, endLine := 26
    }
  }]
}
%%%
At the origin write $`\omega_x=\partial_1\omega`,
$`\theta_{xx}=\partial_1^2\theta`, and $`u_x=\partial_1u_1`. The normalization
is

$$`
c_l=\frac{2\theta_{xx}(0)}{\omega_x(0)},\qquad
c_\omega=\frac12c_l+u_x(0),\qquad
c_\theta=c_l+2c_\omega,
`

with the necessary condition $`\omega_x(0)\ne0`. The accompanying symmetry
predicates distinguish the minimal cancellations used at the origin from the
streamfunction-level assumptions that imply them.
:::

Whether the traces are in fact preserved is decided by their evolution
equations. Differentiating the rescaled vorticity equation once and the
temperature equation twice in $`x_1` and evaluating at the origin, the symmetry
conditions remove the normal and undifferentiated transport terms and leave two
linear scalar ODEs in which the rates appear as coefficients.

:::theorem "fluid.boussinesq.normalization_trace_odes" (parent := "fluid.boussinesq") (lean := "Boussinesq.deriv_vorticityXAtOrigin, Boussinesq.deriv_temperatureXXAtOrigin") (uses := "fluid.boussinesq.normalization, fluid.boussinesq.rescaled_boundary_continuation")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Footnote following equation (2.10)"
    text := some {
      path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 14, endLine := 26
    }
  }]
}
%%%
For sufficiently smooth space-time fields satisfying the rescaled equations
on the open upper half-plane and the stated symmetries,

$$`
\frac{d}{d\tau}\omega_x(0)=
 (c_\omega-c_l-u_x(0))\omega_x(0)+\theta_{xx}(0),
`

$$`
\frac{d}{d\tau}\theta_{xx}(0)=
 \bigl(c_\theta-2(c_l+u_x(0))\bigr)\theta_{xx}(0).
`

These are derived from equation (2.8) by differentiating in the tangential
direction, extending the differentiated identities continuously to the
origin, and commuting space and time derivatives. The fields are represented
by smooth extensions across the boundary, but the equations are assumed only
on the open upper half-plane.
:::

:::proof "fluid.boussinesq.normalization_trace_odes"
Differentiate the vorticity equation once and the temperature equation twice
in the tangential variable. At the origin, parity and the two zero traces
remove the normal and undifferentiated transport terms. Expanding the remaining
advection products gives the two displayed scalar ODEs.
:::

:::theorem "fluid.boussinesq.normalization_preservation" (parent := "fluid.boussinesq") (lean := "Boussinesq.deriv_vorticityXAtOrigin_eq_zero, Boussinesq.deriv_temperatureXXAtOrigin_eq_zero, Boussinesq.vorticityXAtOrigin_eqOn_const, Boussinesq.temperatureXXAtOrigin_eqOn_const") (uses := "fluid.boussinesq.normalization_trace_odes")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1, equations (2.9)–(2.10)"
    text := some {
      path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 14, endLine := 26
    }
  }]
}
%%%
Substitution of the three normalization identities makes both trace-ODE
right-hand sides zero. Hence, on an open connected time domain where the
regularity, upper-half-plane equations, symmetries, and normalization hold at every
time,

$$`
\omega_x(0,\tau)=\omega_x(0,\tau_0),\qquad
\theta_{xx}(0,\tau)=\theta_{xx}(0,\tau_0).
`
:::

:::proof "fluid.boussinesq.normalization_preservation"
The first normalization identity implies
$`c_l\omega_x(0)=2\theta_{xx}(0)`. Together with the formulas for
$`c_\omega` and $`c_\theta`, elementary algebra cancels both ODE right-hand
sides. A differentiable real-valued function whose derivative vanishes on an
open connected set is constant there.
:::

Constant rates make the rescaled equations autonomous; a stationary profile
is an additional condition. The fixed-power construction starts with
time-independent primitive profiles and a single exponent $`\lambda`.
The exponents of $`\theta` and $`p` are forced by requiring buoyancy and
pressure to balance $`\partial_tu`. This ansatz is checked against the
primitive classical predicate rather than the vorticity-stream model.

:::definition "fluid.boussinesq.similarity_ansatz" (parent := "fluid.boussinesq") (lean := "Boussinesq.SelfSimilarProfile, Boussinesq.selfSimilarCoords, Boussinesq.selfSimilarAnsatz") (uses := "fluid.boussinesq.classical")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1"
    text := some { path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 1, endLine := 26 }
  }]
}
%%%
For an exponent $`\lambda` and profiles $`U,\Theta,P`, set

$$`
y=\frac{x}{(1-t)^{1+\lambda}},\qquad
u=(1-t)^\lambda U(y),\qquad
\theta=(1-t)^{\lambda-1}\Theta(y),\qquad
p=(1-t)^{2\lambda}P(y).
`

The ansatz is an instance of the common backward-similarity transformation.
The quotient formula is used analytically only for $`t<1`, where the real-power
base is positive.
:::

Substituting the ansatz into the Boussinesq system, every term of the momentum
equation carries the factor $`(1-t)^{\lambda-1}`, every term of the temperature
equation carries $`(1-t)^{\lambda-2}`, and time differentiation of the profiles
produces the scaling terms $`-\lambda U+(1+\lambda)(y\cdot\nabla)U` and
$`(1-\lambda)\Theta+(1+\lambda)y\cdot\nabla\Theta`. Dividing out the powers
leaves a stationary system in the similarity variable.

:::definition "fluid.boussinesq.profile_equations" (parent := "fluid.boussinesq") (lean := "Boussinesq.velocityProfileScalingTerm, Boussinesq.momentumProfileResidual, Boussinesq.temperatureProfileResidual, Boussinesq.HasClassicalSelfSimilarProfileRegularity, Boussinesq.SatisfiesSelfSimilarProfileEquations, Boussinesq.IsClassicalSelfSimilarProfile") (uses := "fluid.boussinesq.similarity_ansatz")
The stationary profile equations are

$$`
\nabla\cdot U=0,
`

$$`
-\lambda U+(1+\lambda)(y\cdot\nabla)U
 +(U\cdot\nabla)U+\nabla P-\Theta e_2=0,
`

$$`
(1-\lambda)\Theta+(1+\lambda)y\cdot\nabla\Theta
 +U\cdot\nabla\Theta=0.
`

The profile predicate also requires global first-order classical regularity;
the residual equalities alone would otherwise use totalized derivatives.
:::

The reduction is exact rather than asymptotic: each physical residual is a
nonzero power of $`1-t` times the corresponding profile residual, so for $`t<1`
vanishing of one is equivalent to vanishing of the other. The direction checked
here goes from profile to physical solution, including the transfer of
regularity.

:::theorem "fluid.boussinesq.exact_reduction" (parent := "fluid.boussinesq") (lean := "Boussinesq.momentumResidual_selfSimilarAnsatz, Boussinesq.temperatureResidual_selfSimilarAnsatz, Boussinesq.divergence_selfSimilarAnsatz_velocity, Boussinesq.IsClassicalSelfSimilarProfile.isSelfSimilarSolutionOn") (uses := "fluid.boussinesq.profile_equations")
Every classical profile satisfying the reduced equations generates a classical
solution of the physical Boussinesq system on any time set contained in
$`(-\infty,1)`.
:::

:::proof "fluid.boussinesq.exact_reduction"
Differentiate the backward ansatz using the common similarity chain rule.
Velocity time differentiation, convection, pressure gradient, and buoyancy all
carry the factor $`(1-t)^{\lambda-1}`. Temperature time differentiation and
temperature advection both carry $`(1-t)^{\lambda-2}`, while divergence carries
$`(1-t)^{-1}`. The three physical residuals are therefore these nonzero factors
times the three reduced residuals. The regularity part follows by composing the
$`C^1` profiles with the smooth positive backward power scales on $`t<1`.
:::

:::theorem "fluid.boussinesq.zero_profile" (parent := "fluid.boussinesq") (lean := "Boussinesq.zeroSelfSimilarProfile_isClassicalSelfSimilarProfile, Boussinesq.zeroSelfSimilarProfile_isSelfSimilarSolutionOn_Iio") (uses := "fluid.boussinesq.exact_reduction")
The zero velocity, temperature, and pressure profiles satisfy the reduced
equations and generate the zero classical solution for every $`t<1`.
:::

:::proof "fluid.boussinesq.zero_profile"
All profile derivatives and nonlinear terms vanish. Applying the exact
reduction theorem gives the physical solution.
:::

# Approximate responses with exact error accounting

The stability argument in Chen–Hou separates a leading evolution from a finite-rank
perturbation. The response to each perturbation column is a spatial field evolving
in time. Section 2.8 explains how to use a computed response while preserving the
exact evolution equation {Informal.citet "chen-hou-2022"}[].

Write $`L` for the full linearized operator, $`\chi` for the prescribed response
columns, $`G(t)` for their approximation, and $`a(t)` for their coefficients.
The response contribution is

$$`
\widehat W_2(t)=\int_0^t G(t-s)a(s)\,ds.
`

Its error includes both the initial mismatch and the evolution residual:

$$`
R(t)=(G(0)-\chi)a(t)
  +\int_0^t \bigl(G'(t-s)-LG(t-s)\bigr)a(s)\,ds.
`

:::theorem "fluid.boussinesq.approximate_response" (parent := "fluid.boussinesq") (lean := "PDE.Analysis.Evolution.hasDerivAt_map_responseIntegral, PDE.Analysis.Evolution.hasDerivAt_map_add_responseIntegral, PDE.Analysis.Evolution.norm_responseError_le")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{ page := "Section 2.8.1, equations (2.39)–(2.41)" }]
}
%%%
For a continuously differentiable response and continuous coefficients,
$`\widehat W_2'=L\widehat W_2+\chi a+R`. If the complementary trajectory satisfies
$`W_1'=LW_1-\chi a-R`, their sum solves $`W'=LW` exactly and has the initial
value of $`W_1`.

The general statement evaluates values and spatial evolution through bounded maps
from a regularity space into the equation space. It does not assume that $`L` is
bounded on the equation space. A bound $`\eta` on the initial mismatch and a
time-dependent bound $`\varepsilon` on the response residual give

$$`
\|R(t)\|\leq\eta\|a(t)\|
  +\int_0^t\|a(s)\|\varepsilon(t-s)\,ds,\qquad t\geq0.
`
:::

:::proof "fluid.boussinesq.approximate_response"
The moving-endpoint integral rule gives the initial-response term and the
integral of the response derivative. Subtract the spatial evolution inside the
integral and retain the difference in $`R`. Adding the complementary equation
cancels the forcing and error. The norm estimate follows from the operator bounds
and the Bochner integral inequality.
:::

# Analytic correction before weighted estimates

Small numerical errors can change a function's vanishing order. For example,
$`f(x)=\delta x+x^3` has a small linear coefficient, but $`|f(x)|/|x|^3` is
unbounded near zero whenever $`\delta\neq0`. A singular weight therefore needs
exact cancellation of the low-order terms before numerical bounds are applied.

Let $`Q` extract the derivative traces that must vanish, and let $`\Psi` reconstruct
correction fields with $`Q\Psi=\mathrm{id}`. For an approximate trajectory $`g`,
set $`M=QL\Psi` and solve the coefficient equation

$$`
a'=Ma-Q(g'-Lg),\qquad a(0)=-Q(g(0)-\chi).
`

:::theorem "fluid.boussinesq.derivative_trace_map" (parent := "fluid.boussinesq") (lean := "HolderSpace.CKGammaOn.ofDerivativeFields, HolderSpace.CKGammaOn.derivative_ofDerivativeFields, HolderSpace.CKGammaOn.norm_ofDerivativeFields_le, HolderSpace.CKGammaOn.evansNorm_ofDerivativeFields_le, LipschitzOnWith.holderOnWith_of_norm_le, HolderSpace.CKGammaOn.jetEvalCLM, HolderSpace.CKGammaOn.jetEvalCLM_apply, HolderSpace.CKGammaOn.norm_jetEvalCLM_le, HolderSpace.CKGammaOn.hasFDerivWithinAt_derivative_closure, HolderSpace.CKGammaOn.hasFDerivWithinAt_gradient_closure")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{ page := "Section 2.8.2, derivative constraints in (2.50)" }]
}
%%%
For a field in the bounded $`C^{k,\gamma}` space on $`\Omega`, evaluation of all
derivatives through order $`k` at a point $`x\in\overline\Omega` is a bounded
linear map into the finite coefficient space with its maximum norm:

$$`
Q_x f=(D^\alpha f(x))_{|\alpha|\leq k},\qquad \|Q_x\|\leq1.
`

The bound uses the Hölder graph norm. At a boundary point, the derivative values
are the continuous extensions of the interior derivatives. Selecting the required
coordinates gives a trace map for the correction; constructing its right inverse
still requires the chosen spatial correction fields.
If $`\Omega` is open and convex, the fields of order below $`k` have the
prescribed derivatives within $`\overline\Omega`. This also identifies the
traces with boundary derivatives, without extending the function across the boundary.
For a field with two further derivatives available, differentiating its assembled
gradient within the closure gives its assembled Hessian.

Ordinary formulas $`v_\alpha` can define a field in this space directly. On an open
$`\Omega`, require continuity on the closure, the successor derivative identities
in the interior, uniform bounds $`\|v_\alpha\|_\infty\leq C_\alpha`, and top-order
Hölder bounds $`[v_\alpha]_\gamma\leq H_\alpha`. The construction preserves the
given interior derivatives and boundary traces. Its graph norm is at most $`B`
when every $`C_\alpha\leq B` and every top-order $`C_\alpha+H_\alpha\leq B`.
Evans's derivative-sum norm satisfies

$$`
\begin{aligned}
\|f\|_{\mathrm{Evans}}&\leq\sum_{|\alpha|\leq k}C_\alpha\\
&\quad+\sum_{|\alpha|=k}H_\alpha.
\end{aligned}
`

For a top-order field with Lipschitz constant $`L_\alpha`, interpolation supplies
the bound

$$`
H_\alpha=(2C_\alpha)^{1-\gamma}L_\alpha^\gamma.
`

The value and Lipschitz bounds are uniform on the closure; the domain may be
unbounded. These per-field constants are inputs, so improving their certificates
does not change the construction or the norm comparison.
:::

:::proof "fluid.boussinesq.derivative_trace_map"
Project each derivative field and evaluate its continuous extension at $`x`.
Each value is bounded by the corresponding uniform norm, which is bounded by
the graph norm. Taking the maximum preserves that bound.
For the boundary derivative, use the interior derivative relation and the continuity
of its assembled gradient on the closure. The mean value estimate on a convex
domain extends differentiability to the boundary with that limiting gradient.
Differentiate the finite coordinate sum to obtain the Hessian relation.
For the construction, bundle the bounded continuous fields and their top-order
Hölder representatives. Each zero extension agrees locally with its ordinary
formula at interior points, so the supplied derivative identities give graph
compatibility. Taking maxima or summing the supplied budgets gives the two norm
bounds. Interpolate the range bound $`2C_\alpha` at exponent zero with the
Lipschitz bound at exponent one to obtain the stated Hölder constant.
:::

:::theorem "fluid.boussinesq.exact_response_jets" (parent := "fluid.boussinesq") (lean := "ContinuousLinearMap.exactRightInverse, ContinuousLinearMap.comp_exactRightInverse, ContinuousLinearMap.norm_exactRightInverse_le, ContinuousLinearMap.norm_exactRightInverse_sub_le, ContinuousLinearMap.norm_comp_exactRightInverse_le, PDE.Analysis.Evolution.exists_response_jet_correction_on_of_norm_sub_le, PDE.Analysis.Evolution.responseJetCoefficients, PDE.Analysis.Evolution.exists_response_jet_correction, PDE.Analysis.Evolution.responseJetCoefficients_spec_on, PDE.Analysis.Evolution.exists_response_jet_correction_on, PDE.Analysis.Evolution.norm_responseJetCoefficients_le, PDE.Analysis.Evolution.norm_responseJetResidual_le") (uses := "fluid.boussinesq.derivative_trace_map")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{ page := "Section 2.8.2, equations (2.49)–(2.53)" }]
}
%%%
A proposed spatial reconstruction $`\Phi` can first be made exact. Suppose
its coordinate residual satisfies

$$`
\|\mathrm{id}-Q\Phi\|\leq\delta<1.
`

The Neumann inverse defines $`\Psi=\Phi(Q\Phi)^{-1}` and gives $`Q\Psi=\mathrm{id}`.
The correction retains quantitative bounds:

$$`
\begin{aligned}
\|\Psi\|&\leq\frac{\|\Phi\|}{1-\delta},\\
\|\Psi-\Phi\|&\leq\frac{\|\Phi\|\delta}{1-\delta},\\
\|L\Psi\|&\leq\frac{\|L\Phi\|}{1-\delta}.
\end{aligned}
`

Only the coefficient space must be complete. A finite-dimensional application
therefore needs a certified residual bound, rather than an exact inverse matrix.
The residual must use the coefficient space's operator norm; for the full
derivative trace map above, the coefficient norm is the maximum norm.

On a closed time interval $`[0,T]`, suppose the approximate trajectory is
differentiable within the interval and its extracted residual is continuous.
With this exact reconstruction, the coefficient equation has an exact solution. The corrected trajectory $`\widetilde g=g+\Psi a` has zero extracted initial error, and

$$`
\begin{aligned}
\widetilde g'&=L\widetilde g+\widetilde R,\\
\widetilde R&=(\mathrm{id}-\Psi Q)(g'-L\widetilde g),\\
Q\widetilde R&=0.
\end{aligned}
`

The general version includes the value map between the two regularity spaces.
It allows any complete normed coefficient space. The spatial correction fields
need not be eigenfunctions: their remaining evolution error stays in
$`\widetilde R`. Only data on $`[0,T]` are required; at its endpoints the
evolution equation uses the corresponding one-sided time derivative.

The same exact coefficient solution has quantitative bounds. Let $`U(t,s)` be
the propagator of $`a'=Ma`. For a fixed $`0\leq t\leq T`, suppose

$$`
\begin{aligned}
\|U(t,s)\|&\leq C_t(s),\\
\|Q(g'(s)-Lg(s))\|&\leq\varepsilon(s),\\
0&\leq s\leq t,
\end{aligned}
`

and $`C_t\varepsilon` is integrable. Then

$$`
\begin{aligned}
\|a(t)\|&\leq C_t(0)\|Q(g(0)-\chi)\|\\
&\quad+\int_0^t C_t(s)\varepsilon(s)\,ds.
\end{aligned}
`

Keeping the envelopes inside the integral preserves their time dependence.
The remaining spatial error obeys

$$`
\begin{aligned}
\|\widetilde R(t)\|&\leq\|\mathrm{id}-\Psi Q\|\\
&\quad\cdot\bigl(\|g'(t)-Lg(t)\|\\
&\qquad+\|L\Psi\|\|a(t)\|\bigr).
\end{aligned}
`

These estimates keep the correction's contribution explicit. Sharper bounds on
the propagator, extracted residual, or spatial correction can be supplied to the
same analytic theorem.
:::

:::proof "fluid.boussinesq.exact_response_jets"
The coordinate residual has norm below one, so its geometric series converges
and inverts $`Q\Phi`. Composing with $`\Phi` gives the exact right inverse.
The geometric-series norm bound gives the reconstruction estimates; applying
$`L` before taking the norm retains the sharper bound on $`L\Phi`.
Use variation of constants for the bounded coefficient operator $`M`, integrating
only over the prescribed time interval. The fundamental theorem of calculus within
a closed interval gives the derivative at its endpoints as well. Differentiate
$`g+\Psi a`, substitute the coefficient equation, and apply
$`Q\Psi=\mathrm{id}`. This cancels the extracted traces while leaving the full
residual explicit.
Apply the propagator formula and the integral norm inequality to bound the
coefficients. Apply the projection bound to the full corrected residual to
bound its remaining spatial error.
:::

:::theorem "fluid.boussinesq.cubic_weight_from_jets" (parent := "fluid.boussinesq") (lean := "PDE.Analysis.norm_div_cube_le_of_second_jet_eq_zero, PDE.Analysis.normal_segment_taylor_bounds_of_derivative_fields, PDE.Analysis.norm_div_cube_le_of_derivative_fields, HolderSpace.CKGammaOn.normal_segment_taylor_bounds, HolderSpace.CKGammaOn.norm_div_cube_le_of_hessian_bound, HolderSpace.CKGammaOn.norm_hessian_eq_matrix_norm") (uses := "fluid.boussinesq.derivative_trace_map")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{ page := "Section 2.8.4" }]
}
%%%
Suppose a field's value, gradient, and Hessian vanish at the origin, it is $`C^3`
near every point of the segment from $`0` to $`x`, and its third derivative has
operator norm at most $`K` along that segment. Then, for $`x\neq0`,

$$`
\frac{\|f(x)\|}{\|x\|^3}\leq\frac K6.
`

A more general variant uses supplied derivative fields $`D` and $`H` within
the segment. If $`f(0)=D(0)=0` and

$$`
\|H(y)\|\leq K\|y\|,\qquad y\in[0,x],
`

the same cubic bound holds. Here $`D` is the derivative of $`f` and $`H` is the
derivative of $`D` within the segment. This allows a segment that starts on or
lies along the domain boundary; no smooth extension across that boundary is needed.
The Hessian envelope can be verified directly, without differentiating $`H`.

These estimates apply to vector-valued fields on any real normed space and retain
the factor $`1/6` for numerical error budgets.

For a scalar field in the bounded $`C^{k,\gamma}` space on an open convex domain,
apply the estimate to $`D^\alpha f` whenever $`|\alpha|+2\leq k`. Its gradient
and Hessian are already supplied by the derivative graph, even at the boundary.
The Hessian's coordinate matrix satisfies

$$`
\begin{aligned}
A_\alpha(y)_{ij}&=D^{\alpha+e_i+e_j}f(y),\\
\|H_\alpha(y)\|&=\|A_\alpha(y)\|_{2\to2}.
\end{aligned}
`

Thus a certified Euclidean matrix norm bound supplies the required Hessian envelope
with its original constant. This is the Euclidean operator norm, rather than an
entrywise or row-sum norm. The value and first-derivative traces of $`D^\alpha f`
must vanish exactly at the base point. Tighter numerical envelopes can be supplied
to the same analytic theorem.
:::

:::proof "fluid.boussinesq.cubic_weight_from_jets"
Parametrize the segment by $`\gamma(t)=tx`, $`0\leq t\leq1`. Compare the
operator-valued derivative with the quadratic majorant to obtain
$`\|D(tx)\|\leq K\|x\|^2t^2/2`. A second mean value comparison gives
$`\|f(tx)\|\leq K\|x\|^3t^3/6`. Both comparisons use derivatives within
the segment, including its endpoints. For the smooth version, the third derivative
bound and the zero Hessian at the origin supply the required Hessian envelope.
Set $`t=1` and divide by the positive factor $`\|x\|^3`.
For the Hölder fields, assemble the derivatives by finite coordinate sums and apply
these same comparisons. The Riesz isometry identifies the curried Hessian with
the Euclidean matrix operator and preserves its norm.
:::
