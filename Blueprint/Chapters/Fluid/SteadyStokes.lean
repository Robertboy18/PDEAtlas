/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Fluid.NavierStokes
import PDE.Fluid.Stokes.Pressure.CompactTests
import PDE.Fluid.Stokes.Pressure.Potential
import PDE.Fluid.Stokes.Regularity.Residual
import PDE.Fluid.Stokes.Regularity.Vorticity
import PDE.Fluid.Stokes.Variational.Energy
import PDE.Fluid.Stokes.Variational.Existence
import PDE.Fluid.Stokes.Variational.Residual

/-!
# The steady Stokes problem

Existence and uniqueness of the divergence-free energy minimizer, local
regularity of its residual, and the pressure recovered from it.
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
#doc (Manual) "The Steady Stokes Problem" =>

:::group "fluid.steady_stokes"
The steady Stokes problem
:::

Dropping the nonlinear term and the time derivative from the Navier–Stokes
equations leaves the Stokes system

$$`
-\Delta u+\nabla p=f,\qquad \nabla\cdot u=0\ \text{in }\Omega,\qquad
u=0\ \text{on }\partial\Omega,
`

at unit viscosity. The pressure is the Lagrange multiplier of the constraint
$`\nabla\cdot u=0`. {Informal.citet "evans-2010"}[] treats the problem in this
way, by minimizing the Dirichlet energy over divergence-free fields. The
Euler–Lagrange equation determines the pressure as a multiplier.

:::definition "fluid.steady_stokes.energy" (parent := "fluid.steady_stokes") (lean := "IncompressibleFlow.Stokes.energy, IncompressibleFlow.Stokes.energy_eq_integral, IncompressibleFlow.Stokes.residual") (uses := "fluid.navier_stokes.weak_form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.4.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a domain $`\Omega\subset\mathbb R^n`, a force $`f\in L^2(\Omega;\mathbb R^n)`
and $`u\in H^1_0(\Omega;\mathbb R^n)`, the Stokes energy is

$$`
E_f(u)=\frac12\int_\Omega|\nabla u|^2\,dx-\int_\Omega f\cdot u\,dx,
`

with $`|\nabla u|` the Frobenius norm of the full gradient matrix. The Stokes
residual of $`u` is the vector of distributions $`\Delta u_j+f_j`, defined
through the weak first derivatives of $`u`.
:::

:::theorem "fluid.steady_stokes.minimizer" (parent := "fluid.steady_stokes") (lean := "IncompressibleFlow.Stokes.existsUnique_minimizes_energy, IncompressibleFlow.Stokes.stationary_of_minimizes_energy") (uses := "fluid.steady_stokes.energy")
Let $`n>0` and let $`\Omega` be bounded. For every $`f\in L^2`, there is
exactly one $`u\in H^1_0(\Omega;\mathbb R^n)` with $`\nabla\cdot u=0` that
minimizes $`E_f` among all divergence-free fields in $`H^1_0`. The minimizer
satisfies

$$`
\int_\Omega\nabla u:\nabla v\,dx=\int_\Omega f\cdot v\,dx
\qquad\text{for all }v\in H^1_0\text{ with }\nabla\cdot v=0.
`
:::

:::proof "fluid.steady_stokes.minimizer"
The divergence is a bounded linear map on $`H^1_0`, so its kernel is a closed
subspace and therefore a Hilbert space. On a bounded domain the Poincaré
inequality makes the Dirichlet form coercive there, and the direct method for
a coercive symmetric form on a closed subspace gives a unique minimizer. The
weak equation is the derivative of $`t\mapsto E_f(u+tv)` at $`t=0`, which is
admissible because $`u+tv` stays divergence free.
:::

The weak equation tests only against divergence-free fields. To recover
pressure, we factor the residual through the divergence of a general test
field. The constrained minimum supplies this factorization, and local
regularity gives a measurable pressure representing the resulting functional.

:::theorem "fluid.steady_stokes.regularity" (parent := "fluid.steady_stokes") (lean := "IncompressibleFlow.Stokes.exists_locally_memLp_residual_of_minimizes_energy, IncompressibleFlow.Stokes.exists_vorticity_weak_derivatives_of_minimizes_energy") (uses := "fluid.steady_stokes.minimizer, fluid.navier_stokes.vorticity_form")
Let $`u` be a divergence-free minimizer of $`E_f` on an open set $`\Omega`.
Then the residual $`\Delta u+f` is represented by a function that is square
integrable on every compact subset of $`\Omega`, and every component
$`\partial_ju_i-\partial_iu_j` of the vorticity has weak first derivatives
that are locally square integrable. No second derivative of $`u` is assumed.
:::

:::proof "fluid.steady_stokes.regularity"
Testing the weak equation against $`\partial_i\varphi\,e_j-\partial_j\varphi\,e_i`,
which is divergence free, shows that the residual is weakly curl free. Each
vorticity component then satisfies
$`\Delta\omega_{ij}=\partial_jf_i-\partial_if_j` in distributions, a Poisson
equation whose right-hand side is a derivative of an $`L^2` field, and the
interior estimate for such equations gives locally square integrable first
derivatives. Because $`\nabla\cdot u=0`, the Laplacian of $`u` is the
divergence of the vorticity tensor, which gives the local $`L^2` representative
of the residual.
:::

:::theorem "fluid.steady_stokes.pressure" (parent := "fluid.steady_stokes") (lean := "IncompressibleFlow.Stokes.exists_pressure_of_minimizes_energy, IncompressibleFlow.Stokes.exists_pressure_compact_test_identity_of_minimizes_energy, IncompressibleFlow.Stokes.exists_pressure_distribution_of_minimizes_energy, IncompressibleFlow.Stokes.exists_pressure_local_sobolev_of_minimizes_energy") (uses := "fluid.steady_stokes.regularity")
Let $`n>0`, let $`\Omega\subset\mathbb R^n` be any open set, and let
$`f\in L^2(\Omega;\mathbb R^n)`. Suppose $`u\in H^1_0(\Omega;\mathbb R^n)`
is divergence free and minimizes $`E_f` against every divergence-free
$`H^1_0` competitor. There is a measurable pressure $`p` that is square integrable on
every compact subset of $`\Omega`, whose distributional gradient is
$`\Delta u+f`, and for which

$$`
\int_\Omega\nabla u:\nabla v\,dx
=\int_\Omega p\,\nabla\cdot v\,dx+\int_\Omega f\cdot v\,dx
`

for every $`v\in H^1(\Omega;\mathbb R^n)` that vanishes outside a compact
subset of $`\Omega`. The test field need not be divergence free.
The same pressure has an $`H^1(V)` representative on every open $`V` with
compact closure contained in $`\Omega`. Neither connectedness nor simple
connectedness is required.
:::

:::proof "fluid.steady_stokes.pressure"
The residual is a locally $`L^2` field with zero weak curl, so it has weak
potentials on balls. To make these potentials agree, use the algebraic
functional obtained by factoring the first variation through divergence.
On a smaller coordinate box, the difference between that functional and
integration against a local potential annihilates all coordinate derivatives.
It is therefore a constant times the integral. Adding this constant to the
potential makes it represent the prescribed functional.

The adjusted potentials represent the same functional on overlaps and hence
agree almost everywhere there. A countable open subcover gives a measurable
gluing. Compact-local $`L^2` bounds for both the pressure and its weak gradient
give its $`H^1` representatives on relatively compact open subsets.
The identity for smooth compactly supported tests is the definition of the
distributional gradient.
It extends to compactly supported $`H^1` tests by localizing the stress
$`\nabla u-p\,I` with a cutoff equal to one near the support of the test, so
that every integral involves only local $`L^2` bounds.
:::

Existence of the minimizer uses boundedness through Poincaré's inequality.
Pressure recovery starts from an actual minimum on any open domain: the
minimum provides the common algebraic potential that fixes the local
constants, and curl-freeness alone would not justify gluing on an arbitrary
domain.
