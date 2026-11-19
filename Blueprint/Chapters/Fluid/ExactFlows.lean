/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Fluid.NavierStokes
import Blueprint.Commands.Figures

/-!
# Exact planar flows

The Taylor–Green vortex and Kovasznay's wake, with their Navier–Stokes
residuals checked symbolically.
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
#doc (Manual) "Exact Planar Flows" =>

In the two exact flows treated here, the nonlinear term becomes a pressure
gradient or balances diffusion exactly. Each is stated in coordinates: the velocity, the pressure,
and the divergence and momentum residuals are explicit functions of $`(t,x,y)`
or $`(x,y)`, written with one-variable derivatives, and the `cas` tactic
checks that the residuals vanish. Both proofs are compiled examples in
`PDE.Examples.Research` and appear here as worked examples. Neither flow has
finite energy on the whole plane, so they illustrate the equations and not the
Leray–Hopf theory.

# The Taylor–Green vortex

The planar Taylor–Green vortex

$$`
u=e^{-2t}\sin x\cos y,\qquad
v=-e^{-2t}\cos x\sin y,\qquad
p=-\tfrac12e^{-4t}\bigl(\sin^2x+\sin^2y\bigr)
`

is divergence free and solves the Navier–Stokes momentum equations with unit
viscosity at every $`(t,x,y)`. This is
the Taylor–Green momentum identity together with
the Taylor–Green incompressibility identity.

The streamfunction is $`\psi=e^{-2t}\sin x\sin y`, so the vorticity is
$`\omega=-\Delta\psi=2\psi`. Since $`\omega` is a function of $`\psi`,
$`(u\cdot\nabla)\omega=0`, and the nonlinear term in the momentum equation is
a gradient, balanced by $`p`. What is left is $`\partial_tu=\Delta u`, which
holds because $`u` is a Laplacian eigenfunction with eigenvalue $`-2`. In Lean
each partial derivative is computed by its own lemma and the residuals then
reduce by `cas`.

{leanpde_figure "taylor-green-vortex"}

The streamlines in the figure do not move. Every Fourier mode of the flow has
$`|k|^2=2`, so viscosity scales the whole pattern by $`e^{-2t}` and the energy
in a period square falls as $`\pi^2e^{-4t}`. The vortex was introduced by
{Informal.citet "taylor-green-1937"}[] as initial data for the
three-dimensional energy cascade; in the plane the same field is an exact
solution.

# Kovasznay's wake

With viscosity $`\nu=1/3`, the stationary field

$$`
u=1-e^{-x}\cos2y,\qquad
v=-\tfrac12e^{-x}\sin2y,\qquad
p=-\tfrac12e^{-2x}
`

is divergence free and solves the stationary Navier–Stokes momentum equations
at every $`(x,y)`. This is the Kovasznay momentum identity together
with the Kovasznay incompressibility identity.

The perturbation of the uniform stream is $`e^{\lambda x}` times a Fourier
mode $`e^{iky}` with $`\lambda=-1` and $`k=2`. Convection by the unit stream
and diffusion balance on it exactly when $`\nu(\lambda^2-k^2)=\lambda`, which
holds for $`\nu=1/3`. The quadratic self-interaction of the perturbation is
a gradient, and the pressure $`p=-\tfrac12e^{2\lambda x}` absorbs it. The
Lean proof again computes each derivative separately and closes the two
residuals with `cas`.

{leanpde_figure "kovasznay-flow"}

{Informal.citet "kovasznay-1948"}[] found this flow as a model of
the wake behind a periodic grid. The figure shows the part that makes it a
wake: in the shaded region near the grid, $`e^{-x}\cos2y>1` and the fluid runs
backwards, while downstream the perturbation decays like $`e^{-x}` and the
uniform stream takes over.
