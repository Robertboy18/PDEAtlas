/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.HigherRegularity
import PDE.Hyperbolic.FirstOrder.PlaneWave
import PDE.Hyperbolic.FirstOrder.SymmetricEnergy
import PDE.Hyperbolic.FirstOrder.SymmetricSystem

/-!
# Symmetric hyperbolic systems

Plane waves and energy estimates for symmetric first-order systems.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Symmetric First-Order Systems" =>

:::group "hyperbolic.symmetric_systems"
Symmetric first-order systems
:::

For a first-order system, the principal symbol determines characteristic
speeds and directions. Symmetry turns that algebraic object into a
self-adjoint operator, so the finite-dimensional spectral theorem gives
hyperbolicity and the PDE admits an energy identity.

The energy argument has three stages: symbol algebra, a local energy-flux
balance, and integration in space and time. Its estimates concern a given,
sufficiently regular solution.

:::definition "hyperbolic.system.principal_symbol" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.principalSymbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "421"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a system

$$`u_t+\sum_{j=1}^n B_j(x,t)u_{x_j}=f(x,t),`

the principal symbol at the covector $`\xi` is
$`B(x,t;\xi)=\sum_j\xi_jB_j(x,t)`.
:::

Freezing the coefficients at a point and inserting a plane-wave ansatz reduces
the system to the eigenvalue problem for this symbol, so the classification of
the system is phrased entirely through its spectrum.

:::definition "hyperbolic.system.hyperbolicity" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsHyperbolicAt, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsHyperbolic, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsStrictlyHyperbolicAt, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsStrictlyHyperbolic") (uses := "hyperbolic.system.principal_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "421-422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A system is hyperbolic at $`(t,x)` when, for every real covector $`\xi`, the
symbol has a real eigenbasis:

$$`
B(t,x;\xi)r_k=\lambda_k r_k,\qquad
\lambda_k\in\mathbb R,\qquad
\operatorname{span}\{r_1,\ldots,r_m\}=\mathbb R^m.
`

It is hyperbolic when this holds throughout the PDE domain. Strict
hyperbolicity additionally requires $`\lambda_i\ne\lambda_j` for
$`i\ne j` whenever $`\xi\ne0`.
:::

Strict hyperbolicity is the stronger notion, but its defining condition is
imposed only for $`\xi\ne0`, so the implication to plain hyperbolicity needs a
separate remark about the zero covector.

:::theorem "hyperbolic.system.strict_is_hyperbolic" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsStrictlyHyperbolicAt.isHyperbolicAt, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsStrictlyHyperbolic.isHyperbolic") (uses := "hyperbolic.system.hyperbolicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "421-422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Pointwise and domain-wide strict hyperbolicity imply the corresponding
hyperbolicity predicates:

$$`
\operatorname{StrictHyp}(B)\Longrightarrow\operatorname{Hyp}(B).
`
:::

:::proof "hyperbolic.system.strict_is_hyperbolic"
For nonzero covectors, discard the pairwise-distinctness condition from the
strict hyperbolicity data and retain its real eigenbasis. At the zero
covector the symbol is the zero operator, for which the standard basis is an
eigenbasis with eigenvalue zero.
:::

Verifying the eigenbasis condition covector by covector is rarely practical.
Symmetry of the coefficient operators is a checkable pointwise condition that
implies it.

:::definition "hyperbolic.system.symmetry" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsSymmetricAt, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsSymmetric")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A symmetric system has a self-adjoint coefficient operator $`B_j(x,t)` in
every spatial direction at every point of its PDE domain.
:::

:::theorem "hyperbolic.system.symmetric_is_hyperbolic" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.IsSymmetric.isHyperbolic") (uses := "hyperbolic.system.hyperbolicity, hyperbolic.system.symmetry")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "421-422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`B_j(t,x)^*=B_j(t,x)` for every spatial direction, then

$$`
B(t,x;\xi)^*
=\left(\sum_j\xi_jB_j(t,x)\right)^*
=\sum_j\xi_jB_j(t,x)
=B(t,x;\xi).
`

Every symmetric first-order system is therefore hyperbolic.
:::

:::proof "hyperbolic.system.symmetric_is_hyperbolic"
Real linear combinations of self-adjoint coefficient operators are
self-adjoint, so every principal symbol is self-adjoint. The
finite-dimensional spectral theorem supplies an orthonormal basis of real
eigenvectors, exactly the pointwise hyperbolicity condition.
:::

Symmetry does more than diagonalize the symbol. Pairing the equation with $`u`
turns each term $`\langle B_ju_{x_j},u\rangle` into half a spatial derivative
of $`\langle B_ju,u\rangle` plus a correction involving $`\partial_jB_j`, so
the density $`\tfrac12|u|^2` obeys a local balance law with an explicit flux
and an explicit production term.

:::theorem "hyperbolic.system.local_energy_flux" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.local_energy_flux_identity_at, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.local_energy_flux_identity") (uses := "hyperbolic.system.symmetry")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "426-427"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
This is the pointwise form of the integration-by-parts energy calculation on
Evans pp. 426-427. At a point where the coefficients are symmetric, the field
and coefficient maps are differentiable, and the system equation holds, the
identity keeps the variable-coefficient correction
$`\frac12\sum_j\langle(\partial_jB_j)u,u\rangle`. The domain-wide form
supplies pointwise symmetry from a symmetric system.
:::

:::proof "hyperbolic.system.local_energy_flux"
Pair the system equation with $`u`. Symmetry rewrites
$`\langle B_j u_{x_j},u\rangle` as one half of the derivative of
$`\langle B_ju,u\rangle`, minus the derivative-of-coefficient correction.
The time term is one half of $`\partial_t|u|^2`, giving the local balance.
:::

Integrating the local balance over a spatial slice removes the flux
divergence when the spatial flux has compact support. Differentiating the
slice energy also requires domination of the time derivative, as specified
in the next theorem.

:::theorem "hyperbolic.system.global_energy_balance" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.integral_spatialEnergyTimeDerivative_eq_production, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.hasDerivAt_spatialEnergy_of_solution") (uses := "hyperbolic.system.local_energy_flux")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "426-427"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under explicit dominated-differentiation hypotheses, pointwise
differentiability and the system equation, and compactly supported $`C^1`
spatial flux slices, the spatial energy is differentiable and

$$`E'(t)=\int_{\mathbb R^n}\left(
\langle f,u\rangle+\frac12\sum_j
\langle(\partial_jB_j)u,u\rangle\right)\,dx.`
:::

:::proof "hyperbolic.system.global_energy_balance" (uses := "hyperbolic.system.local_energy_flux")
The dominated-differentiation hypothesis moves the time derivative through
the spatial integral. Integrate the local balance over space; each compactly
supported flux divergence has zero integral, leaving only forcing and the
variable-coefficient production term.
:::

The exact balance is not yet an estimate, because the production term has no
sign; it is controlled by a linear expression in the energy.

:::theorem "hyperbolic.system.integrated_energy_production" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.energyProductionField_le, PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.integral_spatialEnergyProduction_le") (uses := "hyperbolic.system.global_energy_balance")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "426-427"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`C` almost everywhere bounds
$`\sum_j\lVert\partial_jB_j\rVert`, the integrated production satisfies

$$`\int_{\mathbb R^n}\mathrm{production}\,dx
\leq F(t)+(1+C)E(t),`

where $`F(t)=\frac12\int_{\mathbb R^n}|f(t,x)|^2\,dx`.
The production, the forcing energy, and the solution energy are assumed
integrable on the slice.
:::

:::proof "hyperbolic.system.integrated_energy_production"
Cauchy–Schwarz and Young's inequality bound
$`\langle f,u\rangle` by one half of the forcing and solution squares.
Operator norm bounds control each coefficient-derivative term by its norm
times $`|u|^2`. Summing the pointwise inequalities and integrating gives the
claim.
:::

:::theorem "hyperbolic.system.conditional_energy_estimate" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.spatialEnergy_le_gronwallBound") (uses := "hyperbolic.system.integrated_energy_production")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "426-427"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a closed time interval, assume continuous total energy, the exact-balance and
production-bound hypotheses at each earlier time, $`F(t)\leq\varepsilon`, and
the initial energy is at most $`\delta`. Mathlib's Grönwall inequality then
gives

$$`E(t)\leq\operatorname{gronwallBound}
(\delta,1+C,\varepsilon,t-a).`
:::

:::proof "hyperbolic.system.conditional_energy_estimate" (uses := "hyperbolic.system.global_energy_balance, hyperbolic.system.integrated_energy_production")
Combine the exact energy derivative with the production bound to obtain
$`E'(t)\leq\varepsilon+(1+C)E(t)`. The initial bound
$`E(a)\leq\delta` and continuity of $`E` put this in Mathlib's right-derivative
Grönwall form, whose explicit solution is the stated bound.
:::

The estimate points to uniqueness. The operator is linear, so the difference
of two solutions with the same forcing and initial data solves the problem
with zero data, where $`\delta=\varepsilon=0`. The weak-solution construction
also proves uniqueness in $`L^2`.

The energy method controls solutions without exhibiting any. For constant
coefficients and no forcing the symbol's eigenvalue problem produces explicit
solutions, profiles transported along a linear phase.

:::theorem "hyperbolic.system.plane_wave_substitution" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.homogeneousConstant_operator_planeWave_eq_zero_iff") (uses := "hyperbolic.system.principal_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a homogeneous constant-coefficient system, the vector-profile wave

$$`u(t,x)=\psi(-\omega t+\langle\xi,x\rangle)`

solves the equation at a differentiability point exactly when
$`B(\xi)\psi'=\omega\psi'` there.
:::

:::proof "hyperbolic.system.plane_wave_substitution"
The chain rule gives $`u_t=-\omega\psi'` and
$`u_{x_j}=\xi_j\psi'`. Substitution into the constant-coefficient operator
produces $`(B(\xi)-\omega I)\psi'`, whose vanishing is exactly the displayed
eigenvalue relation.
:::

Taking $`\psi=\phi v` with a fixed polarization vector separates the profile
from the symbol condition.

:::theorem "hyperbolic.system.scalar_plane_wave_substitution" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.homogeneousConstant_operator_profilePlaneWave_eq_zero_iff") (uses := "hyperbolic.system.plane_wave_substitution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`\psi(s)=\phi(s)v` the equation holds exactly
when $`\phi'=0` at the point or the polarization satisfies
$`B(\xi)v=\omega v`. The latter relation gives a solution for every
differentiable scalar profile.
:::

:::proof "hyperbolic.system.scalar_plane_wave_substitution" (uses := "hyperbolic.system.plane_wave_substitution")
For $`\psi(s)=\phi(s)v`, differentiation gives
$`\psi'(s)=\phi'(s)v`. The vector-profile condition factors as
$`\phi'(s)(B(\xi)v-\omega v)=0`, so it holds precisely when either factor
vanishes.
:::

Imposing the eigenvector condition at every profile parameter, rather than at
one point, upgrades the pointwise substitution to a solution of the
initial-value problem.

:::theorem "hyperbolic.system.plane_wave_initial_value_problem" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.planeWave_satisfies_initialValueProblem") (uses := "hyperbolic.system.plane_wave_substitution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If the vector profile is differentiable and its eigenvalue condition holds
for every profile parameter, the plane wave solves the initial-value problem and has trace
$`\psi(\langle\xi,x\rangle)` at $`t=0`.
:::

:::proof "hyperbolic.system.plane_wave_initial_value_problem" (uses := "hyperbolic.system.plane_wave_substitution")
Apply the pointwise substitution theorem at every profile parameter to obtain
the homogeneous PDE. Evaluating the phase at $`t=0` removes the
$`-\omega t` term and gives the claimed initial trace.
:::

For a polarized profile the eigenvector condition $`B(\xi)v=\omega v` is a
single algebraic identity independent of the profile.

:::theorem "hyperbolic.system.profile_plane_wave_initial_value_problem" (parent := "hyperbolic.symmetric_systems") (lean := "PDE.Hyperbolic.FirstOrder.LinearFirstOrderSystem.profilePlaneWave_satisfies_initialValueProblem") (uses := "hyperbolic.system.plane_wave_initial_value_problem, hyperbolic.system.scalar_plane_wave_substitution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "422"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`B(\xi)v=\omega v` and $`\phi` is differentiable, then

$$`
u(t,x)=\phi\bigl(-\omega t+\langle\xi,x\rangle\bigr)v
`

solves the homogeneous constant-coefficient initial-value problem and has the
exact trace $`u(0,x)=\phi(\langle\xi,x\rangle)v`.
:::

:::proof "hyperbolic.system.profile_plane_wave_initial_value_problem" (uses := "hyperbolic.system.scalar_plane_wave_substitution")
By linearity, the eigenvalue hypothesis gives the eigenvalue condition for the
vector profile at every phase, whatever the value of
$`\phi'`, so the vector-profile initial-value theorem gives the PDE and the trace.
:::

# Scope of the energy method

Mollifying the spatial operator first gives a bounded-operator evolution
problem. For coefficients continuous in time in spatial $`L^\infty` norm,
the construction works for each $`\varepsilon>0` with $`L^2` initial data
and $`L^2_tL^2_x` forcing. Symmetric spatial $`W^{1,\infty}` coefficients
with uniformly bounded derivative norms give an energy bound independent
of $`\varepsilon`.

With $`H^1` initial data and $`L^2_tH^1_x` forcing, we can also pass to the
original system. On a finite interval $`[a,b]`, with $`a<b`, assume the
symmetric matrix entries belong to spatial $`W^{1,\infty}`. Their values
must be continuous in time in spatial $`L^\infty` norm on that interval,
and their spatial derivative norms must be uniformly bounded there.
Under these hypotheses the construction gives an $`L^\infty_tH^1_x`
solution of the original principal system,
with $`L^2_tL^2_x` time derivative and a continuous $`L^2` representative
attaining the initial data.

The proof bounds the mollified trajectories in $`H^1`, passes to a joint
weak Bochner limit of states and time derivatives, and identifies the
unmollified coefficient terms. Weak closedness preserves the time-dependent
energy bound. The integrated initial identity supplies the continuous
$`L^2` trace. The principal system has no zeroth-order coefficient.

The same coefficient assumptions also allow merely $`L^2` initial data and
prescribed forcing $`F(t,x)` square-integrable on time-space. Almost every
spatial slice of $`F` defines an $`L^2` class; constructing these classes
as a Bochner forcing lets the Cauchy argument apply.
The resulting continuous $`L^2` curve attains the initial datum. Its energy
bound uses the sum of the product integrals of $`F_p^2`, without a factor
for the number of components.

The weak equation uses this same $`F`. Every joint product-$`L^2` state
satisfying that equation with the same initial boundary datum agrees with
the constructed state almost everywhere for the product measure.
Reconstructing a competitor's Bochner sections reduces this to uniqueness
of the Bochner class, without assuming time regularity of the competitor.
The initial value is attained by the continuous $`L^2` curve and enters the
weak equation through its initial boundary term.
