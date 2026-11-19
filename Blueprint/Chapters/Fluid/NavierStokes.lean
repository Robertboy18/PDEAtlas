/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Fluid.Euler
import Blueprint.Chapters.Parabolic.WeakEvolution.Galerkin
import Blueprint.Chapters.Parabolic.WeakEvolution.TimeRegularity
import Blueprint.Chapters.Sobolev.Compactness
import Blueprint.Chapters.Sobolev.Core
import Blueprint.CodeExamples
import PDE.Analysis.Integration.InnerProductByParts
import PDE.Fluid.Incompressible.EnergyIdentities
import PDE.Fluid.NavierStokes.PressureFromVorticity
import PDE.Fluid.NavierStokes.Energy
import PDE.Fluid.NavierStokes.SimilarityPrincipal
import PDE.Fluid.NavierStokes.GlobalSolutions
import PDE.Fluid.NavierStokes.LerayHopf
import PDE.Fluid.NavierStokes.LerayHopf.EnergySpace
import PDE.Fluid.NavierStokes.Operators
import PDE.Fluid.NavierStokes.Problem
import PDE.Fluid.NavierStokes.Symbolic.Stationary.Shear
import PDE.Fluid.NavierStokes.WeakSolutions
import PDE.Fluid.NavierStokes.ZeroSolutions.Classical
import PDE.Fluid.NavierStokes.ZeroSolutions.LerayHopf
import CAS.CEGA

/-!
# Stokes and Navier-Stokes flow

The Stokes and Navier–Stokes residuals and their hierarchy with Euler, a
certified shear flow, pressure recovery from the vorticity equation, and the
classical, weak, and Leray–Hopf solution concepts.
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
#doc (Manual) "Stokes and Incompressible Navier–Stokes" =>

:::group "fluid.navier_stokes"
Navier–Stokes
:::

The Stokes system keeps pressure and viscosity but neglects inertial
transport:

$$`
\partial_tu+\nabla p=\nu\Delta u+f,
\qquad \nabla\mathbin\cdot u=0.
`

It is linear in $`(u,p)` and gives the basic diffusive model for a viscous
incompressible fluid. Restoring self-advection gives Navier–Stokes:

$$`
\partial_tu+(u\mathbin\cdot\nabla)u+\nabla p
  =\nu\Delta u+f,
\qquad \nabla\mathbin\cdot u=0.
`

If $`U` and $`L` are characteristic velocity and length scales, their
Reynolds number is

$$`\operatorname{Re}=\frac{UL}{\nu}`

and is positive when all three scales are positive. In the dimensionless
equation it measures the competition between inertia and viscosity. Small
Reynolds number suppresses convection and leads to Stokes flow. Large Reynolds
number makes the inviscid Euler equation the leading interior model, although
viscosity can remain decisive near boundaries.

The ratio comes from estimating the two terms at the same length scale:
$`|(u\cdot\nabla)u|` has scale $`U^2/L`, while $`|\nu\Delta u|` has scale
$`\nu U/L^2`. Their ratio is $`UL/\nu`. This is a dimensional comparison;
proving a Stokes approximation or an inviscid limit also requires estimates
on the actual solution and its boundary behavior.

:::definition "fluid.navier_stokes.residuals" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.stokesMomentumResidual, IncompressibleFlow.navierStokesMomentumResidual") (uses := "fluid.euler.residual, fluid.equations.material_decomposition")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
The pointwise residuals are

$$`
\begin{aligned}
R_S&=\partial_tu+\nabla p-\nu\Delta u-f,\\
R_{NS}&=D_t^u u+\nabla p-\nu\Delta u-f.
\end{aligned}
`

Each momentum equation is the assertion that its residual vanishes.
:::

The three residuals share their pressure and forcing terms, so each pair
differs by a single term. The resulting identities are algebraic and hold at
every point, without any regularity assumption.

:::theorem "fluid.navier_stokes.model_hierarchy" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.stokesMomentumResidual_eq_zero_iff, IncompressibleFlow.navierStokesMomentumResidual_eq_zero_iff, IncompressibleFlow.navierStokesMomentumResidual_eq_eulerMomentumResidual_sub_viscousTerm, IncompressibleFlow.navierStokesMomentumResidual_zero_viscosity, IncompressibleFlow.navierStokesMomentumResidual_eq_stokesMomentumResidual_add_convection, IncompressibleFlow.navierStokesMomentumResidual_eq_stokesMomentumResidual_of_convection_eq_zero") (uses := "fluid.navier_stokes.residuals")
The residuals recover the Stokes and Navier–Stokes equations and satisfy

$$`
R_{NS}=R_E-\nu\Delta u,
\qquad
R_{NS}=R_S+(u\cdot\nabla)u.
`

Thus zero viscosity recovers Euler. At a point where convection vanishes, the
Navier–Stokes and Stokes residuals agree.
:::

:::proof "fluid.navier_stokes.model_hierarchy"
Use $`D_t^u u=\partial_tu+(u\cdot\nabla)u` and collect the vector terms.
The zero-residual equivalences are the corresponding rearrangements of
$`A-B=0` into $`A=B`.
:::

# A certified forced shear flow

Let

$$`
u(x,y)=(\sin y,0),\qquad p=0,\qquad
f=(\sin y,0),\qquad \nu=1.
`

The velocity is divergence-free, and $`(u\cdot\nabla)u=0` because the field
depends only on $`y` while advection points in the $`x` direction. Since
$`\Delta(\sin y)=-\sin y`, the forcing balances viscosity.

The sine mode in the parabolic chapter decayed because this same Laplacian
was left unbalanced. Here forcing keeps the profile stationary. The symbolic
calculation can therefore reuse familiar scalar derivatives; the fluid
content is the additional check that incompressibility and convection behave
as claimed.

:::theorem "fluid.navier_stokes.shear" (parent := "fluid.navier_stokes") (lean := "NavierStokes.Symbolic.shearVelocity2_incompressible, NavierStokes.Symbolic.shearVelocity2_forced_navierStokes_momentum_zero, NavierStokes.Symbolic.shearNavierStokesResidualCert2") (uses := "fluid.navier_stokes.model_hierarchy")
The verified CAS proves the exact identities

$$`
\nabla\cdot u=0,\qquad
(u\cdot\nabla)u+\nabla p-\Delta u-f=0
`

on all of $`\mathbb R^2`. The momentum theorem is also stored as a
zero-error residual certificate. CEGA projects that checked object into the
ordinary residual goal. Here `cega` selects the certificate's proved `sound`
field and checks that its residual, domain, and error budget match the target;
no derivative is recomputed and no external solver is called.
:::

:::proof "fluid.navier_stokes.shear"
The divergence is $`\partial_x(\sin y)+\partial_y0=0`, and
$`\partial_xu=0` makes convection vanish. Finally,
$`-\Delta u=(\sin y,0)=f`. The reflected expressions therefore normalize to
zero componentwise, which is exactly the proposition proved by `cas`.
:::

The certificate closes an ordinary proof goal:

```Blueprint.leanExample
-- Project a checked zero residual into the proof goal.
open CAS.Certificate
open NavierStokes.Symbolic

example :
    ResidualBound
      shearNavierStokesMomentumResidual2.vectorFn
      Set.univ 0 := by
  cega using shearNavierStokesResidualCert2
```

:::theorem "fluid.navier_stokes.shear_integral" (parent := "fluid.navier_stokes") (lean := "NavierStokes.Symbolic.shearVelocity2_forced_navierStokes_euclidean_component_integral_zero") (uses := "fluid.navier_stokes.shear")
For every integration domain and every velocity component,

$$`
\int_\Omega
\bigl((u\cdot\nabla)u_i+\partial_i p-\Delta u_i-f_i\bigr)\,dx=0.
`

The integrand is the combined analytic residual, which vanishes identically,
so the identity needs no integrability of the separate terms.
:::

:::proof "fluid.navier_stokes.shear_integral"
The semantic bridge identifies the analytic integrand with the evaluated
symbolic residual. That residual vanishes at every point, so its integral over
the chosen domain is zero.
:::

For an approximate or numerically generated field, a validated backend may
instead supply a positive error,

$$`\|R_{NS}(x)\|\leq\varepsilon\qquad(x\in\Omega),`

and CEGA projects such a certificate in the same way, proving a uniform
residual estimate.

# Initial-value data

:::definition "fluid.navier_stokes.data" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.DistributionallyDivergenceFree, IncompressibleFlow.SpatialFieldDivergenceFree.distributionallyDivergenceFree, NavierStokes.Problem") (uses := "fluid.equations.kinematics, fluid.equations.operators")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "1"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A Navier–Stokes problem consists of a positive viscosity $`\nu`, forcing
$`f`, and initial velocity $`u_0`.  Incompressibility of $`u_0` is stated in
distributions:

$$`
\int_{\mathbb R^n}u_0\mathbin\cdot\nabla\psi=0
`

for every smooth compactly supported scalar test function.  Smooth
classically divergence-free fields satisfy this definition by integration by
parts, so the same datum can be used by both classical and weak theories.
:::

# Classical solutions

:::definition "fluid.navier_stokes.pointwise" (parent := "fluid.navier_stokes") (lean := "NavierStokes.PointwiseResidualSolution, NavierStokes.PointwiseResidualSolution.momentumResidual_eq_zero") (uses := "fluid.navier_stokes.data")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "1"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A finite-time pointwise solution consists of velocity and pressure on
$`(0,T)\times\mathbb R^n`, the momentum equation, incompressibility, and the
prescribed value at $`t=0`. The equation is imposed on the open positive-time
domain using totalized ambient derivatives, so a residual solution carries
no differentiability.
:::

Smoothness at positive times turns the totalized derivatives into classical
ones.

:::definition "fluid.navier_stokes.classical" (parent := "fluid.navier_stokes") (lean := "NavierStokes.SmoothSolution, NavierStokes.GlobalPointwiseResidualSolution, NavierStokes.GlobalPointwiseResidualSolution.momentumResidual_eq_zero, NavierStokes.GlobalSmoothSolution") (uses := "fluid.navier_stokes.pointwise, fluid.equations.kinematics")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "1-2"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A finite-time smooth solution adds ambient smoothness at positive times and
one-sided continuity at the initial surface. A global pointwise residual
solution is posed on $`(0,\infty)\times\mathbb R^n`; it restricts to every
finite positive horizon. Global smoothness is relative to the physical closed half-space
$`[0,\infty)\times\mathbb R^n`, so nothing is assumed at negative times.
Restricting a global smooth solution to a positive finite horizon gives a
finite-time smooth solution, smoothness included. As for Euler, a smooth
solution is a weak solution only once the $`L^2` bounds, weak-gradient
integrability, decay, and spacetime integrability of the weak class are proved.
:::

With classical derivatives available, the divergence of the momentum equation
can be taken as for Euler; the viscous term is the only new contribution.

:::theorem "fluid.navier_stokes.pressure_recovery" (parent := "fluid.navier_stokes") (lean := "NavierStokes.spatialDivergence_viscousTerm, IncompressibleFlow.spatialDivergence_spatialVectorLaplacian_eq_spatialLaplacian_spatialDivergence, IncompressibleFlow.spatialDivergence_spatialVectorLaplacian_eq_zero_of_eventually_divergenceFreeAt, IncompressibleFlow.pressurePoissonResidual_eq_zero_of_eventually_momentum_eq_add, NavierStokes.SmoothSolution.pressurePoissonResidual_eq_zero, NavierStokes.GlobalSmoothSolution.pressurePoissonResidual_eq_zero") (uses := "fluid.navier_stokes.classical, fluid.euler.pressure_poisson")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
At every positive-time point of a smooth Navier–Stokes solution,

$$`
-\Delta_xp
=\nabla_x\cdot((u\cdot\nabla_x)u)-\nabla_x\cdot f.
`

The viscosity does not alter this pressure source. For a componentwise
$`C^3` incompressible velocity,

$$`
\nabla_x\cdot(\nu\Delta_xu)
=\nu\Delta_x(\nabla_x\cdot u)=0.
`

The result is available for both finite-time and global smooth solutions.
:::

:::proof "fluid.navier_stokes.pressure_recovery"
Take the spatial divergence of momentum. Local incompressibility makes the
divergence of $`\partial_tu` vanish. Commutation of the spatial divergence
with the vector Laplacian makes the viscous contribution vanish as well.
The remaining identity is exactly the pressure Poisson residual equation.
:::

# Pressure from the vorticity equation

The pressure Poisson equation is one consequence of the momentum balance.
Conversely, in a force-free flow the momentum equation determines
$`\nabla_xp=\nu\Delta_xu-D_t^uu`, so pressure can be reconstructed from the
velocity alone whenever that candidate field is a gradient. The compatibility
condition is exactly the vorticity equation.

:::definition "fluid.navier_stokes.vorticity_form" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.spatialVorticityForm, IncompressibleFlow.vorticityFormTransportResidual, IncompressibleFlow.spacetimeSpatialCurl") (uses := "fluid.euler.vorticity, fluid.euler.vorticity_stretching_residual, fluid.equations.operators")
For a spacetime velocity $`u:\mathbb R^{n+1}\to\mathbb R^n`, the spatial
vorticity two-form has components

$$`
\Omega_{ij}=\partial_iu_j-\partial_ju_i,
`

the transpose, equivalently the negative, of the antisymmetric
velocity-gradient convention used for the Euler vorticity tensor. Its
transport-diffusion residual with viscosity $`\nu` is

$$`
R_{ij}=D_t^u\Omega_{ij}
+\sum_{k=1}^n\bigl(\partial_iu_k\,\Omega_{kj}+\partial_ju_k\,\Omega_{ik}\bigr)
-\nu\Delta_x\Omega_{ij},
`

where the deformation sum is the coordinate form of the Lie derivative of a
two-form along $`u`. In three dimensions the vector vorticity is the curl of
each time slice, $`\omega(t,x)=\nabla\times u(t,\cdot)(x)`; for a $`C^1`
velocity its components are the cyclic two-form entries
$`\omega_1=\Omega_{23}`, $`\omega_2=\Omega_{31}`, $`\omega_3=\Omega_{12}`.
No incompressibility is built into these definitions.
:::

In three dimensions an antisymmetric matrix has three independent entries, and
for $`\Omega` these are the components of $`\nabla\times u`. The two-form
residual and the vector residual introduced for Euler should therefore carry
the same information, and they do, up to a correction proportional to
$`\nabla\cdot u` that disappears for incompressible flow.

:::theorem "fluid.navier_stokes.vorticity_form_vector_equivalence" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.vorticityFormTransportResidual_eq_zero_iff_vectorVorticity, IncompressibleFlow.vorticityFormTransportResidual_eq_zero_of_vectorVorticity, IncompressibleFlow.vorticityTransportResidual_eq_zero_of_vorticityForm") (uses := "fluid.navier_stokes.vorticity_form, fluid.euler.vorticity_stretching_residual, fluid.equations.kinematics")
Let $`u:\mathbb R^4\to\mathbb R^3` be $`C^3` and let $`(t,x)` be a
spacetime point at which $`\nabla\cdot u=0`. Then the two-form residual
vanishes at $`(t,x)` if and only if the vector residual does:

$$`
R_{ij}=0\ \text{for all }i,j
\quad\Longleftrightarrow\quad
D_t^u\omega-(\omega\cdot\nabla)u-\nu\Delta_x\omega=0,
\qquad\omega=\nabla\times u.
`

The implication from the two-form equation to the vector equation needs only
$`C^1` regularity.
:::

:::proof "fluid.navier_stokes.vorticity_form_vector_equivalence"
Each cyclic component of the two-form residual equals the corresponding
component of the vector residual plus the correction
$`(\nabla\cdot u)\,\omega_k`; this is an exact identity obtained by expanding
the deformation sum and regrouping it in terms of the curl components. At a
point where the divergence vanishes, the correction disappears and the three
cyclic components of $`R` are the three components of the vector residual.
The remaining components of $`R` follow from the antisymmetry of $`\Omega`.
:::

The connection with pressure runs through the antisymmetrized derivative of the
candidate field $`F(u)=\nu\Delta_xu-D_t^uu`. Differentiating $`F(u)` and
commuting mixed derivatives reproduces, term by term, the two-form residual
with the opposite sign, so the vorticity equation is precisely the statement
that $`F(u)` has a symmetric Jacobian.

:::theorem "fluid.navier_stokes.pressure_candidate_curl" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual, IncompressibleFlow.antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual_of_contDiffAt, IncompressibleFlow.navierStokesPressureCandidate_eventuallyEq, IncompressibleFlow.contDiffAt_navierStokesPressureCandidate") (uses := "fluid.navier_stokes.vorticity_form, fluid.navier_stokes.residuals")
Write $`F(u)=\nu\Delta_xu-D_t^uu` for the pressure-gradient candidate: the
force-free Navier–Stokes momentum equation is $`\nabla_xp=F(u)`. If $`u` is
$`C^3`, or merely $`C^3` at the spacetime point $`x`, then at $`x`

$$`
\partial_iF(u)_j-\partial_jF(u)_i=-R_{ij}.
`

The candidate depends only on the velocity germ: if $`u=v` on a
neighborhood of $`x`, then $`F(u)=F(v)` on a neighborhood of $`x`. It is
$`C^1` near every point at which $`u` is $`C^3`.
:::

:::proof "fluid.navier_stokes.pressure_candidate_curl"
Expand $`D_t^uu` componentwise and differentiate. The antisymmetrised
derivative of $`\partial_tu` is $`\partial_t\Omega_{ij}`, that of the
Laplacian is $`\Delta_x\Omega_{ij}`, and the convective term
$`\sum_ku_k\partial_ku_j` contributes $`\sum_ku_k\partial_k\Omega_{ij}` plus
the deformation sum
$`\sum_k(\partial_iu_k\Omega_{kj}+\partial_ju_k\Omega_{ik})` after commuting
the mixed derivatives, which is where third derivatives are used. Collecting
terms gives minus the two-form residual. Since $`F(u)` is built from finitely
many partial derivatives at each point, it is determined by the germ of
$`u`; the local statements follow by replacing $`u` with a compactly
supported $`C^3` field that agrees with it near $`x`.
:::

A $`C^1` field with symmetric Jacobian on an open convex set is a gradient, by
integration along segments from a base point. Applied slice by slice to
$`F(u)`, this converts the vorticity equation into the existence of a pressure
closing the force-free momentum equation.

:::theorem "fluid.navier_stokes.pressure_from_vorticity" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.exists_pressure_navierStokes_momentum_equation_of_vorticity, IncompressibleFlow.exists_pressure_euler_momentum_equation_of_vorticity, IncompressibleFlow.exists_pressure_navierStokes_momentum_equation_of_vectorVorticity, IncompressibleFlow.exists_pressure_euler_momentum_equation_of_vectorVorticity_of_contDiffAt_two") (uses := "fluid.navier_stokes.pressure_candidate_curl, fluid.navier_stokes.vorticity_form_vector_equivalence, fluid.navier_stokes.residuals")
Let $`s\subseteq\mathbb R^n` be open and convex, let $`I\subseteq\mathbb R`
be any set of times, and let $`u:\mathbb R^{n+1}\to\mathbb R^n` be $`C^3` at
every point $`(t,x)` with $`t\in I` and $`x\in s`, satisfying the two-form
vorticity equation $`R_{ij}(t,x)=0` there. Then there is a pressure
$`p:\mathbb R\to\mathbb R^n\to\mathbb R` such that for all $`t\in I` and
$`x\in s`, the slice $`p(t,\cdot)` has gradient $`F(u)(t,x)` at $`x` and

$$`
D_t^uu+\nabla_xp=\nu\Delta_xu\qquad\text{at }(t,x).
`

For $`\nu=0` this reconstructs the force-free Euler pressure,
$`D_t^uu+\nabla_xp=0`. In three dimensions the two-form hypothesis may be
replaced by $`\nabla\cdot u=0` together with the vector vorticity equation
$`D_t^u\omega=(\omega\cdot\nabla)u+\nu\Delta_x\omega` for
$`\omega=\nabla\times u`, again for Navier–Stokes and for Euler.

The pressure is selected slice by slice, with no condition in time, and $`I`
may exclude a blow-up time: only local regularity at the selected points is
used. The reconstructed momentum equation is force free
because the vorticity equation carries no forcing term.
:::

:::proof "fluid.navier_stokes.pressure_from_vorticity"
At each selected time the candidate $`F(u)(t,\cdot)` is $`C^1` on $`s`, and
by the antisymmetry identity its Jacobian is symmetric exactly because the
vorticity residual vanishes. On an open convex set, a $`C^1` field with
symmetric derivative is a gradient: integrating along segments from a base
point produces a potential whose gradient is the field. Choosing such a
potential for every $`t\in I` defines $`p`, and rewriting
$`\nabla_xp=\nu\Delta_xu-D_t^uu` gives the momentum equation. The
three-dimensional statements first convert the vector vorticity equation into
the two-form equation using incompressibility.
:::

Pressure reconstruction completes the pointwise picture: on the selected slices
the velocity alone fixes the pressure gradient. Estimates, on the other hand,
come from integrated quantities, first among them the kinetic energy, and these
have to be defined so that they make sense for weak velocities whose
derivatives exist only distributionally.

:::definition "fluid.navier_stokes.energy" (parent := "fluid.navier_stokes") (lean := "NavierStokes.kineticEnergy, NavierStokes.initialKineticEnergy, NavierStokes.enstrophy, NavierStokes.classicalVelocityGradientDissipation, NavierStokes.weakGradientDissipation") (uses := "fluid.equations.operators")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "1-2"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The kinetic energy is

$$`E(t)=\frac12\int_{\mathbb R^n}|u(t,x)|^2\,dx,`

and we also define the initial-data energy, enstrophy, and two forms of viscous
dissipation. The classical dissipation differentiates $`u` pointwise; the weak
quantity integrates
the square of a separately supplied distributional-gradient witness.  Keeping
these definitions distinct avoids applying totalized classical derivatives
to an energy-class velocity.
:::

# Weak solutions

:::definition "fluid.navier_stokes.weak_form" (parent := "fluid.navier_stokes") (lean := "NavierStokes.weakMomentumIntegrand, NavierStokes.WeakMomentumIntegrableOn") (uses := "fluid.navier_stokes.data, fluid.navier_stokes.energy, fluid.equations.weak_test_data")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "3"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Momentum test fields are smooth and compactly supported and vanish at the
terminal time, but they may be nonzero at $`t=0`.  Integration by parts then
gives

$$`
\int_0^T\!\!\int_{\mathbb R^n}
\left[-u\mathbin\cdot\phi_t-(u\otimes u):\nabla\phi
-p\,\nabla\mathbin\cdot\phi+\nu Du:\nabla\phi-f\mathbin\cdot\phi\right]
=\int_{\mathbb R^n}u_0\mathbin\cdot\phi(0).
`

The integrability predicate requires spatial integrability of the combined
momentum integrand at every physical time, and time integrability of its
spatial integral rather than of each summand. The initial pairing is
integrable by the $`L^2` initial datum and compactly supported smooth test.
This pressure-retaining identity is used
by a weak solution with a pressure representative; solenoidal tests remove its pressure term.
:::

:::definition "fluid.navier_stokes.weak" (parent := "fluid.navier_stokes") (lean := "NavierStokes.WeakSolution, NavierStokes.WeakSolution.weak_momentum_eq, NavierStokes.WeakSolution.weakDivergencePairing_eq_zero, NavierStokes.PressureWeakSolution, NavierStokes.PressureWeakSolution.toWeakSolution") (uses := "fluid.navier_stokes.weak_form")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "3"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A pressure-free weak solution tests momentum only against solenoidal fields. It stores a velocity with $`L^2` slices at every time in
$`[0,T]`, an explicit distributional spatial gradient $`D u` with $`L^2`
slices and weak-derivative identities at every time in $`(0,T]`, the combined
iterated integrability of the momentum integrand, weak incompressibility of
every velocity slice, and the initial datum as a boundary functional. The
initial datum is required only to lie in $`L^2`, and forcing has $`L^2`
spatial slices at every physical time. The viscous term uses $`D u`, never a
classical derivative of the weak velocity.

A weak solution with a pressure representative additionally supplies an $`L^2` pressure slice at
every physical time and the pressure-retaining identity for all momentum
tests. Restricting to solenoidal tests gives its checked projection to
a pressure-free weak solution; the converse would require pressure reconstruction.
:::

The componentwise gradient witnesses use the
{bpref "sobolev.weak_derivative"}[weak-derivative relation] developed in the
Sobolev chapter. The fluid formulation adds the momentum identity,
incompressibility, pressure, and time dependence; it keeps the same weak
calculus.

# Energy and Leray–Hopf solutions

:::theorem "fluid.navier_stokes.pointwise_energy_identities" (parent := "fluid.navier_stokes") (lean := "IncompressibleFlow.partialDeriv_specificKineticEnergy, IncompressibleFlow.convectivePower_eq_kineticEnergyTransport, IncompressibleFlow.spatialDivergence_kineticEnergyFlux_eq_kineticEnergyTransport_add, IncompressibleFlow.convectivePower_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt, IncompressibleFlow.spatialDivergence_pressureFlux_eq_pressurePower_add, IncompressibleFlow.pressurePower_eq_spatialDivergence_pressureFlux_of_divergenceFreeAt") (uses := "fluid.navier_stokes.model_hierarchy, fluid.equations.kinematics")
%%%
source := {
  document := "majda-bertozzi"
  spans := #[{
    page := "Chapter 1"
    text := some { path := "Blueprint/Sources/MajdaBertozzi.md", startLine := 1, endLine := 11 }
  }]
}
%%%
For a differentiable velocity field, the convective power is transport of
the specific kinetic energy $`e=\frac12|u|^2`:

$$`
\bigl((u\cdot\nabla)u\bigr)\cdot u=u\cdot\nabla e.
`

Where pressure is also differentiable, pressure work satisfies

$$`
u\cdot\nabla p=\nabla\cdot(pu)-p\,\nabla\cdot u.
`

Under incompressibility, the pressure contribution is a spatial divergence.
The kinetic-energy flux obeys

$$`\nabla\cdot(eu)=u\cdot\nabla e+e\,\nabla\cdot u.`

Thus incompressibility also turns the convective power into
$`\nabla\cdot(eu)`.
:::

:::proof "fluid.navier_stokes.pointwise_energy_identities"
Differentiate $`e=\frac12\sum_i u_i^2` componentwise and apply the product
rule. Multiplication by $`u_j` and summation over $`j` gives the convective
identity. Applying the product rule to each $`\partial_j(eu_j)` and
$`\partial_j(pu_j)` gives the two flux identities; their compressibility
terms vanish when $`\nabla\cdot u=0`.
:::

The abstract time-regularity step behind this calculation is the
{bpref "parabolic.lions_magenes_energy_identity"}[Lions–Magenes energy
identity]. Under the Gelfand-triple hypotheses stated there, an $`L^2_tV`
trajectory with weak time derivative in $`L^2_tV^*` has a continuous
$`H`-valued representative and an exact squared-norm identity. Applying it to
Navier–Stokes requires the equation to supply that dual-space time regularity.

For a smooth solution with zero forcing and enough spatial decay and
integrability to differentiate under the integral and integrate by parts,
multiply the Navier–Stokes equation by $`u` and integrate over
$`\mathbb R^3`:

$$`\frac12\frac{d}{dt}\int|u|^2\,dx
+\nu\int|\nabla u|^2\,dx
=-\int(u\cdot\nabla)u\cdot u\,dx
-\int\nabla p\cdot u\,dx.`

The pressure term vanishes by incompressibility:
$`\int\nabla p\cdot u=-\int p\,\nabla\cdot u=0`. The nonlinear term
also vanishes:
$`\int(u\cdot\nabla)u\cdot u=\frac12\int u\cdot\nabla|u|^2
=-\frac12\int|u|^2\nabla\cdot u=0`.
These cancellations give the energy identity:

$$`\frac12\|u(t)\|_{L^2}^2+\nu\int_0^t\|\nabla u(s)\|_{L^2}^2\,ds
=\frac12\|u_0\|_{L^2}^2.`

Kinetic energy decreases by the accumulated viscous dissipation.

:::definition "fluid.navier_stokes.energy_space_slices" (parent := "fluid.navier_stokes") (lean := "NavierStokes.WeakSolution.velocityL2Slice, NavierStokes.WeakSolution.gradientL2Slice, NavierStokes.WeakSolution.initialVelocityL2, NavierStokes.WeakSolution.velocityWeakL2Slice") (uses := "fluid.navier_stokes.weak")
A pressure-free weak solution on $`[0,T]` stores $`L^2` membership of every
velocity slice and of every weak-gradient slice at positive times. The
corresponding Hilbert-space classes are

$$`
u(t)\in L^2(\mathbb R^n;\mathbb R^n)\quad(0\le t\le T),\qquad
Du(t)\in L^2(\mathbb R^n;\mathbb R^{n\times n})\quad(0<t\le T),
`

the classes of $`x\mapsto u(t,x)` and $`x\mapsto Du(t,x)`, extended by the
zero class outside $`[0,T]` and $`(0,T]` respectively, together with the class
$`u_0\in L^2(\mathbb R^n;\mathbb R^n)` of the prescribed initial velocity. The
velocity slice is also recorded as an element of $`L^2` carrying the weak
topology, which is the topology in which Leray–Hopf solutions are
continuous in time.
:::

:::theorem "fluid.navier_stokes.energy_l2_identities" (parent := "fluid.navier_stokes") (lean := "NavierStokes.WeakSolution.kineticEnergy_eq_velocityL2Slice_norm_sq, NavierStokes.WeakSolution.initialKineticEnergy_eq_initialVelocityL2_norm_sq, NavierStokes.WeakSolution.weakGradientDissipation_eq_gradientL2Slice_norm_sq, NavierStokes.WeakSolution.weakGradientDissipation_integrableOn_of_gradient_memLp") (uses := "fluid.navier_stokes.energy_space_slices, fluid.navier_stokes.energy")
For a weak solution, the physical energy quantities are the squared Hilbert
norms of the corresponding $`L^2` classes:

$$`
E(t)=\frac12\lVert u(t)\rVert_{L^2}^2\quad(0\le t\le T),\qquad
E_0=\frac12\lVert u_0\rVert_{L^2}^2,
`

$$`
\int_{\mathbb R^n}|Du(t,x)|^2\,dx=\lVert Du(t)\rVert_{L^2}^2\quad(0<t\le T).
`

If moreover $`t\mapsto Du(t)` belongs to $`L^2(0,T;L^2)`, that is, the
gradient slice map is square integrable in time on $`[0,T]`, then the weak
dissipation $`t\mapsto\int|Du(t,x)|^2\,dx` is integrable on $`[0,T]`. These
identities let the energy inequality of a Leray–Hopf solution be read either
as a statement about integrals of the representative or as a statement in the
Hilbert space $`L^2`.
:::

:::proof "fluid.navier_stokes.energy_l2_identities"
The squared $`L^2` norm is the $`L^2` inner product of the class with
itself, which Mathlib expresses as the integral of the pointwise inner
product. The class agrees almost everywhere with the chosen slice, so the
integrands coincide almost everywhere with the kinetic-energy and
squared-gradient densities, up to the constant one half. For time
integrability, membership of the slice map in Bochner $`L^2` makes its
squared norm integrable, and the pointwise identity transfers integrability
to the dissipation.
:::

The Leray–Hopf class uses both readings: its a priori bounds are
$`L^\infty_tL^2_x` and $`L^2_tL^2_x` membership of the slice maps,
while its energy inequality is written with the integrals $`E(t)` and
$`\int|Du|^2`.

:::definition "fluid.navier_stokes.leray_hopf" (parent := "fluid.navier_stokes") (lean := "NavierStokes.LerayHopfSolution, NavierStokes.LerayHopfSolution.velocity_gradient_memLp, NavierStokes.LerayHopfSolution.energy_inequality, NavierStokes.PressureRepresentativeLerayHopfSolution, NavierStokes.PressureRepresentativeLerayHopfSolution.toLerayHopfSolution") (uses := "fluid.navier_stokes.weak, fluid.navier_stokes.energy")
%%%
source := {
  document := "leray-1934"
  spans := #[{
    page := "193-248"
    text := some { path := "Blueprint/Sources/Leray1934.md", startLine := 1, endLine := 10 }
  }]
}
%%%
The Leray–Hopf definition adds to the pressure-free weak solution
$`L^\infty_tL^2_x` velocity, $`L^2_tL^2_x` weak gradient, continuity in the
weak $`L^2` topology, the prescribed $`L^2` initial trace,
force-work integrability, and the energy inequality measured from the initial
datum. It uses a chosen representative: velocity slices and the initial trace
are imposed at every time in $`[0,T]` and the weak gradient at every time in
$`(0,T]`, while the initial datum is required only to lie in $`L^2`.

A Leray–Hopf solution with a pressure representative supplies the separate
pressure-retaining refinement and projects to this pressure-free class.

For this representative, the energy inequality holds for every
$`t\in[0,T]`:

$$`\frac12\|u(t)\|_{L^2}^2+\nu\int_0^t\|\nabla u(s)\|_{L^2}^2\,ds
\leq\frac12\|u_0\|_{L^2}^2+\int_0^t\langle f(s),u(s)\rangle\,ds.`

The force-work term measures external energy input. At zero forcing, the
inequality bounds kinetic energy plus accumulated weak-gradient dissipation
by the initial kinetic energy. Equality would require the additional
regularity needed to justify the smooth integrations by parts.
:::

The linear weak-evolution chapter already supplies
{bpref "parabolic.galerkin.weak_compactness"}[Galerkin weak compactness].
For Navier–Stokes, weak convergence alone does not identify the quadratic
term $`u\otimes u`. On bounded subdomains,
{bpref "sobolev.rellich_full_subcritical"}[Rellich–Kondrachov compactness]
and {bpref "parabolic.aubin_lions_hilbert"}[Aubin–Lions compactness] are the
model inputs for obtaining strong spacetime convergence. Once strong
$`L^2` convergence is available,
{bpref "parabolic.bilinear_l2_l1_limit"}[the bilinear $`L^2`-to-$`L^1`
limit theorem] identifies the corresponding quadratic product. A whole-space
construction also needs localization and control at infinity. These are the
additional nonlinear compactness steps between the abstract parabolic
machinery and Leray's global weak existence theorem.

The product estimate shows exactly where strong convergence enters. Write

$$`
u_j\otimes u_j-u\otimes u
=(u_j-u)\otimes u_j+u\otimes(u_j-u).
`

On a fixed spacetime region, Hölder's inequality gives

$$`
\|u_j\otimes u_j-u\otimes u\|_{L^1}
\leq \|u_j-u\|_{L^2}
       \bigl(\|u_j\|_{L^2}+\|u\|_{L^2}\bigr).
`

Strong $`L^2` convergence makes the first factor vanish and bounds the
second. Weak convergence preserves the linear divergence constraint, but
does not provide this vanishing factor for convection. This is the role of
compactness in an existence proof, beyond writing down the weak equation.

# Energy in similarity variables

The linearized stationary operator in
{Informal.citet "hou-wang-yang-2025"}[§4.1] includes a dilation drift as
well as the usual viscous and transport terms. Its energy calculation starts
with smooth compact test fields.

:::theorem "fluid.navier_stokes.similarity_principal_energy" (parent := "fluid.navier_stokes") (lean := "PDE.Analysis.integral_inner_advection_eq_neg_half_divergence, PDE.Analysis.integral_inner_advection_eq_zero, PDE.Analysis.integral_inner_dilation_eq_neg, PDE.Analysis.integral_inner_similarity_drift, NavierStokes.similarity_principal_pairing_lower_bound, NavierStokes.similarity_principal_weak_pairing_lower_bound, NavierStokes.similarityPrincipalForm, NavierStokes.similarityPrincipalForm_apply, NavierStokes.similarityPrincipalForm_lower_bound, NavierStokes.similarityPrincipalForm_isCoercive, NavierStokes.solenoidalSimilarityPrincipalForm, NavierStokes.solenoidalSimilarityPrincipalForm_isCoercive, NavierStokes.existsUnique_solenoidal_similarity_principal_solution") (uses := "fluid.navier_stokes.energy")
%%%
source := {
  document := "hou-wang-yang-2025"
  spans := #[{
    citation := "Section 4.1"
    text := some { path := "Blueprint/Sources/NavierStokesNonuniqueness.md", startLine := 18, endLine := 24 }
  }]
}
%%%
Let $`u\in C_c^2(\mathbb R^3;\mathbb R^3)` and let $`b` be a
divergence-free $`C^1` transporting field. The dilation identity gives

$$`
\int\left(-\frac12u-\frac12(x\cdot\nabla)u\right)\cdot u
=\frac14\int|u|^2.
`

$$`\int (b\cdot\nabla)u\cdot u=0.
`

Suppose a continuous matrix field $`Q` satisfies the compensation inequality

$$`v\cdot(Db(x)+Q(x))v\geq-\eta|v|^2`

for every $`x` and $`v`. Define the unprojected principal expression

$$`
\begin{aligned}
A_Qu={}&-\frac12u-\frac12(x\cdot\nabla)u-\Delta u\\
&+(b\cdot\nabla)u+(u\cdot\nabla)b+Qu.
\end{aligned}
`

Then

$$`
\begin{aligned}
\int A_Qu\cdot u
&\geq\left(\frac14-\eta\right)\int|u|^2\\
&\quad+\sum_{i=1}^3\int|\partial_i u|^2.
\end{aligned}
`

The same lower bound holds on any bounded open domain for
$`u\in H^1_0(\Omega;\mathbb R^3)`, with weakly divergence-free background
$`b\in W^{1,\infty}(\Omega;\mathbb R^3)` and
$`Q\in L^\infty(\Omega;\mathbb R^{3\times3})`. Here divergence and $`Db` are weak
Sobolev derivatives, and compensation is required almost everywhere.
In this setting the left side is the weak pairing
$`\langle A_Qu,u\rangle_{H^{-1},H^1_0}`.
The viscous term is the Dirichlet pairing $`\int_\Omega|\nabla u|^2`;
no second weak derivative of $`u` is assumed. The bounded coordinate
functions supply the dilation pairing. Weak integration by parts proves
transport cancellation directly on the completed space.

When $`\eta<1/4`, the constructed bounded-domain form is coercive in the
full $`H^1` norm, with modulus

$$`c=\min\{1/4-\eta,1\}>0.`

Restricting both arguments to the closed weak-divergence kernel preserves
coercivity. Thus, for every continuous dual load $`\ell`, there is a unique
$`u\in H^1_{0,\sigma}(\Omega)` satisfying

$$`
\begin{aligned}
\langle A_Qu,v\rangle&=\ell(v),\\
&\quad v\in H^1_{0,\sigma}(\Omega).
\end{aligned}
`

This solves the compensated principal linear variational equation. The
operator is built from the bounded weak coefficients and coordinate
multipliers, and its evaluation formula is proved from that construction.
The compensation inequality is accepted directly, so a certified $`Q` can be
used without an exact spectral negative-part formula.
An application must still certify the actual $`Q`,
remove pressure or the Leray projection against divergence-free tests,
and pass from bounded domains to the required whole-space limit. PDEAtlas constructs distinct suitable Leray–Hopf solutions from any unstable profile (`NavierStokes.Nonuniqueness.of_unstableProfile`).
The certificates for the paper's numerical profile and unstable eigenpair, and with them the nonuniqueness theorem `NavierStokes.nonuniqueness`,
are formalized in the companion repository [BlowupZoo](https://github.com/Robertboy18/BlowupZoo), at its level 8.
:::

:::proof "fluid.navier_stokes.similarity_principal_energy"
Apply integration by parts to $`|u|^2` and the identity spatial field. Its
divergence is three, giving the one-quarter drift coefficient. The same
argument with $`b` gives zero transport energy. The Laplacian supplies the
sum of squared coordinate derivatives, and the certified compensation
inequality bounds the remaining zeroth-order pairing.
The positive mass and Dirichlet coefficients control the full Sobolev norm.
The divergence kernel is closed because divergence is a continuous linear
map; Lax–Milgram applied to the restricted form gives the principal solve.
:::

# The zero solution

:::theorem "fluid.navier_stokes.zero_classical" (parent := "fluid.navier_stokes") (lean := "NavierStokes.exists_zero_smoothSolution_on, NavierStokes.exists_zero_globalSmoothSolution, NavierStokes.zeroSmoothSolution, NavierStokes.zeroGlobalSmoothSolution") (uses := "fluid.navier_stokes.classical")
For zero initial velocity and zero forcing, the zero velocity and pressure
give

$$`
  u(t,x)\equiv0,\qquad p(t,x)\equiv0,\qquad
  \partial_tu-\nu\Delta u+(u\!\cdot\!\nabla)u+\nabla p=0
`

on every finite horizon and globally for every $`\nu>0`.
:::

:::proof "fluid.navier_stokes.zero_classical"
Choose $`u(t,x)\equiv0` and $`p(t,x)\equiv0`. Every derivative, nonlinear
term, pressure gradient, and divergence vanishes, and the initial trace equals
the zero datum. Constant zero fields are smooth on every finite horizon and on
the full nonnegative-time domain, which gives both forms of the result.
:::

:::theorem "fluid.navier_stokes.zero_leray_hopf" (parent := "fluid.navier_stokes") (lean := "NavierStokes.exists_zero_lerayHopfSolution_on, NavierStokes.zeroLerayHopfSolution") (uses := "fluid.navier_stokes.leray_hopf")
For every positive viscosity and every positive finite horizon, zero velocity,
zero pressure, zero forcing, and zero initial data give a checked Leray–Hopf
solution. In particular,

$$`
  u\equiv0,\qquad
  \frac12\|u(t)\|_{L^2}^2
    +\nu\int_0^t\|\nabla u(s)\|_{L^2}^2\,ds=0
`

for $`0\leq t\leq T`.
:::

:::proof "fluid.navier_stokes.zero_leray_hopf"
Use zero velocity, weak gradient, pressure, forcing, and initial data. Every
weak momentum and incompressibility pairing is zero. The zero representative
belongs to both energy spaces, all test-function pairings are constantly zero,
and the energy inequality reduces to $`0\leq0`.
:::
