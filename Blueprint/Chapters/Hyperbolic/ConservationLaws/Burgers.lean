/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws.WeakSolutions
import Blueprint.Commands.Figures
import PDE.Hyperbolic.ConservationLaw.Burgers.AffineSolution
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.EntropyShock
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.InitialTrace
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Rarefaction
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Shock

/-!
# Burgers equation

The affine classical solution of inviscid Burgers, and its entropy-admissible
shock, rarefaction, and Riemann solutions.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Burgers Equation" =>

# Explicit and Riemann solutions

:::definition "hyperbolic.burgers.affine_ivp" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.burgersAffineIVP, BurgersEquation.burgersAffineSolution")
For affine initial data $`u(0,x)=a x+c`, the characteristic construction gives
$`u(t,x)=(a x+c)/(1+a t)`. The accompanying problem imposes the PDE on
$`\{(t,x):0\leq t,\ 1+at\ne0\}` and records the initial trace.
When $`a<0` this domain also contains the branch $`t>-1/a` beyond the
singular time.
:::

For affine data the footpoint equation $`x=\xi+t(a\xi+c)` is linear in $`\xi`,
so the characteristic construction can be carried out in closed form and the
Jacobian denominator becomes $`1+at`.

:::theorem "hyperbolic.burgers.affine_solution" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.burgersAffineSolution_satisfiesPDEProblem") (uses := "hyperbolic.burgers.affine_ivp")
For $`u(0,x)=ax+c`, the explicit profile

$$`
u(t,x)=\frac{ax+c}{1+at}
`

satisfies $`u_t+u\,u_x=0` wherever $`t\geq0` and $`1+at\ne0`, and
recovers the affine initial trace. The pre-shock part of this domain is
$`t\geq0`, $`1+at>0`: all forward time for $`a\geq0`, and
$`0\leq t<-1/a` for $`a<0`.
:::

:::proof "hyperbolic.burgers.affine_solution" (uses := "hyperbolic.burgers.affine_ivp")
Split the problem into its evolution equation and initial condition.
On the specified domain, the denominator is nonzero, so the explicit time and
space derivative formulas reduce $`u_t+u\,u_x` to a rational expression whose
two terms cancel. On the time-zero slice, direct simplification gives
$`u(0,x)=ax+c`.
:::

When $`a<0` the gradient $`u_x=a/(1+at)` of the affine profile blows up at
$`t=-1/a`, the simplest instance of crossing characteristics. The Riemann
problem, with constant states $`u_L` and $`u_R` separated by a jump at the
origin, is the model for what happens afterwards, and for the flux
$`f(u)=u^2/2` the scalar jump conditions become explicit: the Rankine–Hugoniot
secant speed is the average of the two states.

:::theorem "hyperbolic.burgers.lax_shock" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.Riemann.laxShock_admissible_shockSpeed") (uses := "hyperbolic.conservation.jump_conditions")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "153-155"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For Burgers data with $`u_R<u_L`, the speed $`(u_L+u_R)/2` satisfies the
Rankine–Hugoniot relation and the Lax compressive shock inequalities.
:::

:::proof "hyperbolic.burgers.lax_shock"
For the flux $`f(u)=u^2/2`, the Rankine–Hugoniot quotient is
$`\bigl(f(u_L)-f(u_R)\bigr)/(u_L-u_R)=(u_L+u_R)/2`. Since
$`u_R<u_L`, their arithmetic mean lies strictly between them. Because the
characteristic speed is $`f'(u)=u`, these are exactly the two Lax
inequalities.
:::

Lax admissibility is a statement about the speed alone. Whether the two-state
profile traveling at that speed solves the equation is a separate question,
answered by the general planar-shock theorem.

:::theorem "hyperbolic.burgers.weak_shock" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.Riemann.shockProfile_isWeakSolution") (uses := "hyperbolic.conservation.weak_solution, hyperbolic.conservation.jump_conditions")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "153-155"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every pair of states $`u_L,u_R\in\mathbb R`, the Burgers shock profile

$$`
u(t,x)=\begin{cases}
u_L,& x<\tfrac{u_L+u_R}{2}\,t,\\
u_R,& x\ge\tfrac{u_L+u_R}{2}\,t
\end{cases}
`

is a weak solution of $`u_t+(u^2/2)_x=0` on all of spacetime. No ordering of
the states is required: the expansive profile with $`u_L<u_R` is a weak
solution as well.
:::

:::proof "hyperbolic.burgers.weak_shock" (uses := "hyperbolic.conservation.planar_shock_weak")
The profile is the scalar planar shock with left state $`u_L`, right state
$`u_R` and speed $`(u_L+u_R)/2`. For the flux $`f(u)=u^2/2` this speed
satisfies
$`f(u_R)-f(u_L)=\tfrac{u_R^2-u_L^2}{2}=\tfrac{u_L+u_R}{2}\,(u_R-u_L)`,
which is the Rankine–Hugoniot relation for every pair of states, so the
general planar-shock theorem applies.
:::

One entropy pair already separates the two orderings. Take
$`\eta(u)=u^2/2` and $`q(u)=u^3/3`, so $`q'(u)=u\eta'(u)`. Using the
right-minus-left jump convention and $`s=(u_L+u_R)/2` gives

$$`
[q]-s[\eta]
=\frac{u_R^3-u_L^3}{3}
-\frac{u_L+u_R}{2}\,\frac{u_R^2-u_L^2}{2}
=\frac{(u_R-u_L)^3}{12}.
`

This is the coefficient of the interface measure in
$`\partial_t\eta(u)+\partial_xq(u)`. It is negative for a compressive
shock and positive for an expansion shock, so the expansion shock already
fails this one test. Admissibility requires the sign for every convex
entropy pair.

The entropy inequality is what survives of a small viscosity. With
$`u_t+uu_x=\varepsilon u_{xx}` in place of the inviscid law, the Cole–Hopf
substitution $`u=-2\varepsilon\,\partial_x\log\varphi` turns the Riemann
problem into a heat equation for $`\varphi`, and the solution can be written
with two error functions. The figure evaluates it for three values of
$`\varepsilon`. For expansive data the viscous profiles approach the fan and
stay away from the expansion shock, although both are weak solutions of the
limit equation; for compressive data they steepen into the Lax shock. Each
viscous solution satisfies $`\partial_t\eta(u)+\partial_xq(u)\le
\varepsilon\,\partial_{xx}\eta(u)` for convex $`\eta`, and letting
$`\varepsilon\to0` leaves exactly the entropy inequality. The
{bpref "hyperbolic.conservation.vanishing_viscosity"}[vanishing-viscosity
theorem] for systems proves this passage to the limit for bounded classical
viscous solutions that are continuous up to $`t=0` and converge almost
everywhere. The viscous solutions in the figure start from the discontinuous
Riemann datum, so for them the limit is a computation.

{leanpde_figure "entropy-selection"}

:::theorem "hyperbolic.burgers.entropy_shock" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.Riemann.shockProfile_isEntropyWeakSolution") (uses := "hyperbolic.conservation.entropy_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "153-155"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u_R<u_L` and set $`s=(u_L+u_R)/2`. The two-state profile with jump
along $`x=st` is an entropy weak solution on all of spacetime. For every
$`C^1` entropy pair $`(\eta,q)` with convex $`\eta` and
$`q'(v)=v\eta'(v)`, it satisfies

$$`
\int_{\mathbb R^2}\bigl(\eta(u)\varphi_t+q(u)\varphi_x\bigr)\,dt\,dx\geq0
\qquad\bigl(0\leq\varphi\in C^1_c(\mathbb R^2)\bigr).
`
:::

:::proof "hyperbolic.burgers.entropy_shock"
Rankine–Hugoniot gives the weak equation. Integration by parts on the two
sides of the shock expresses the entropy integral as
$`A\int_{\mathbb R}\varphi(t,st)\,dt`, where

$$`
A=q(u_L)-q(u_R)-s\bigl(\eta(u_L)-\eta(u_R)\bigr)
 =\int_{u_R}^{u_L}\eta'(v)(v-s)\,dv.
`

Since $`s` is the midpoint, $`\int_{u_R}^{u_L}(v-s)\,dv=0`. Subtracting
$`\eta'(s)` from the other factor leaves
$`(\eta'(v)-\eta'(s))(v-s)\geq0`, because the derivative of a convex
function is monotone. Thus $`A\geq0`, which gives the required sign for
every nonnegative test.
:::

For $`u_L<u_R`, the entropy solution joins the constant states by the
self-similar fan $`u=x/t`.

:::theorem "hyperbolic.burgers.entropy_rarefaction" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.Riemann.rarefactionProfile_isEntropyWeakSolution_on_forwardHalfSpace") (uses := "hyperbolic.conservation.entropy_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "153-155"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`u_L\leq u_R`, the profile

$$`
u(t,x)=\begin{cases}
u_L,& x<u_Lt,\\
x/t,& u_Lt\leq x<u_Rt,\\
u_R,& x\geq u_Rt
\end{cases}
\qquad(t>0)
`

is an entropy weak solution on the positive-time half-plane.
:::

:::proof "hyperbolic.burgers.entropy_rarefaction"
Split the half-plane into the two constant regions and the fan
$`u=x/t`. The conservation law and every smooth entropy identity hold
classically in each region. The profile is continuous across both fan
boundaries, so integration by parts creates no jump measure there. Summing
the three regional identities therefore gives the weak equation and the
entropy inequality, in fact with equality inside the fan.
:::

The shock and the rarefaction cover the two orderings of the states, and
selecting between them by the sign of $`u_L-u_R` gives a single formula for
every pair. The new point is the initial trace.

:::theorem "hyperbolic.burgers.riemann_solution" (parent := "hyperbolic.conservation") (lean := "BurgersEquation.Riemann.riemannSolution_isEntropySolutionWithInitialTrace") (uses := "hyperbolic.conservation.entropy_solution, hyperbolic.conservation.weak_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "153-155"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every pair of constant left and right states, the explicit Burgers
Riemann profile selects the shock branch when $`u_R<u_L` and the rarefaction
branch otherwise. It is an entropy weak solution for positive time and
converges strongly in $`L^1_{\mathrm{loc}}` to the discontinuous Riemann
datum as $`t\downarrow0`.
:::

:::proof "hyperbolic.burgers.riemann_solution" (uses := "hyperbolic.burgers.entropy_shock, hyperbolic.burgers.entropy_rarefaction")
Split on the order of the two states. The strict branch restricts the
whole-space entropy shock to positive time; the other branch uses the
entropy rarefaction and almost-everywhere invariance. For each fixed
$`x\ne0`, the profile equals the corresponding initial state once
$`t>0` is small enough. Both the profile and the datum are bounded in
absolute value by $`M=\max(|u_L|,|u_R|)`. Their measurable difference is
therefore dominated by $`2M` on each bounded interval. Dominated
convergence gives the strong $`L^1_{\mathrm{loc}}` trace.
:::
