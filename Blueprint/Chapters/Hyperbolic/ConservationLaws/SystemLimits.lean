/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws.ScalarTheory
import Blueprint.Commands.Figures
import PDE.Hyperbolic.ConservationLaw.System.GradientBlowup.Global
import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.Limit
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Existence

/-!
# Blowup and viscosity for systems

Gradient blowup for `2 × 2` systems in Riemann coordinates, small viscous
shock profiles, and the vanishing-viscosity limit.
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
#doc (Manual) "Blowup and Viscosity for Systems" =>

# Blowup, viscous profiles, and vanishing viscosity

Smooth data do not stay smooth for systems either. For a $`2\times2` system
with Riemann coordinates the invariants satisfy transport equations along
the two families of characteristics, and differentiating the equation for
one of them along its own characteristic gives a Riccati inequality for its
slope.

:::theorem "hyperbolic.conservation.gradient_blowup" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.not_exists_global_of_compressive_invariant") (uses := "hyperbolic.conservation.riemann_invariant, hyperbolic.conservation.system_flux_forms")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§11.3.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f:\mathbb R^2\to\mathbb R^2` be $`C^2` and strictly hyperbolic at
every state, and let $`\Phi` be a global diffeomorphism of the state plane
whose components are Riemann invariants: $`D\Phi_i\,Df=\lambda_{1-i}\,D\Phi_i`.
Assume that the speed carried by each invariant increases strictly in that
invariant. If $`g` is continuous with compact support and
$`(\Phi_i\circ g)'(x_0)<0` for some $`i` and $`x_0`, then there is no
$`C^2` solution of $`u_t+f(u)_x=0` on $`t>0` with $`u(0,\cdot)=g` whose
derivatives up to order two extend continuously to $`t\ge0`.
:::

:::proof "hyperbolic.conservation.gradient_blowup"
Along a characteristic of the family that transports $`\Phi_i(u)`, the
slope $`y=\partial_x\Phi_i(u)` satisfies $`y'\le-\kappa\,y^2` up to a
positive factor that is bounded below uniformly, because the solution
stays in a compact set of states determined by the compactly supported data.
A negative initial value $`y(0)` therefore reaches $`-\infty` before time
$`(\kappa|y(0)|)^{-1}`, contradicting the continuity of the second jet on
any longer slab.
:::

Viscosity is the physical reason for choosing Lax shocks, and for systems
it can be tested directly on travelling waves. A viscous profile of speed
$`s` from $`u_L` to $`u_R` is a $`C^2` curve $`v` with

$$`
v''=Df(v)\,v'-s\,v',\qquad v(-\infty)=u_L,\quad v(+\infty)=u_R,\quad v'(\pm\infty)=0,
`

so that $`u(t,x)=v((x-st)/\varepsilon)` solves $`u_t+f(u)_x=\varepsilon u_{xx}`.

:::theorem "hyperbolic.conservation.viscous_profile" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.exists_small_viscousProfile_iff_lax, PDE.Hyperbolic.ConservationLaw.System.IsViscousProfile") (uses := "hyperbolic.conservation.system_jump, hyperbolic.conservation.characteristic_classes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§11.4.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f` be $`C^\infty` on $`\mathbb R^m` with $`m>0`, strictly hyperbolic
at every state, with every family genuinely nonlinear, and fix a state $`q`.
There are $`0<\delta<\rho` such that for every $`u_R\ne q` with
$`|u_R-q|<\delta` and every speed $`s`, a viscous profile from $`q` to
$`u_R` with values in the ball of radius $`\rho` exists if and only if
$`(q,u_R,s)` satisfies Rankine–Hugoniot and
$`\lambda_k(u_R)<s<\lambda_k(q)` for some $`k`.
:::

:::proof "hyperbolic.conservation.viscous_profile"
Integrating once and using the end conditions at $`-\infty` gives the
first-order system $`v'=f(v)-f(q)-s(v-q)`; letting $`v\to u_R` gives
Rankine–Hugoniot. Near $`q` every nonzero Rankine–Hugoniot jump lies,
together with its speed, on one of $`m` shock curves, one per family. For
$`u_R` on the $`k`-th curve the two rest points $`q` and $`u_R` lie on a
one-dimensional invariant graph of the first-order system, and the flow on
it runs from $`q` to $`u_R` exactly when the shock is compressive. Genuine
nonlinearity makes the derivative of the shock speed along the curve
nonzero, which turns that orientation into the Lax inequality.
:::

The last step is the limit $`\varepsilon\to0` for general solutions, not
only travelling waves, with the convergence of the viscous family taken as a
hypothesis.

:::theorem "hyperbolic.conservation.vanishing_viscosity" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.entropySolution_of_vanishingViscosity_commonData, PDE.Hyperbolic.ConservationLaw.System.entropySolution_of_vanishingViscosity_convergingData") (uses := "hyperbolic.conservation.system_entropy_inequality, hyperbolic.conservation.weak_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "646-649"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f` be $`C^1`, let $`\varepsilon_i\ge0` tend to $`0`, and let each
$`u_i` be $`C^2` on $`t>0`, continuous on $`t\ge0`, and a classical solution
of $`\partial_tu_i+\partial_xf(u_i)=\varepsilon_i\partial_{xx}u_i` with
$`|u_i|\le M` almost everywhere. Suppose $`u_i(0,\cdot)=g` for all $`i`, or
more generally $`u_i(0,\cdot)\to g` in $`L^1_{\mathrm{loc}}` for a locally
integrable $`g`. If $`u_i\to v` almost everywhere on $`t>0`, then $`v` is
almost everywhere measurable there, bounded by $`M`, a weak initial-value solution with datum
$`g`, and satisfies the entropy inequality for every $`C^1` convex entropy
pair.
:::

:::proof "hyperbolic.conservation.vanishing_viscosity"
Multiply the viscous equation by a test function and integrate by parts
twice in $`x`; the viscous term becomes $`\varepsilon_i\int u_i\varphi_{xx}`,
which tends to zero by the uniform bound. Dominated convergence passes to the
limit in the remaining terms. For a convex entropy pair, the chain rule gives
$`\partial_t\eta(u_i)+\partial_xq(u_i)=\varepsilon_i\partial_{xx}\eta(u_i)
-\varepsilon_iD^2\eta(u_i)(\partial_xu_i,\partial_xu_i)`, and the last
term is nonpositive, so it can be dropped before passing to the limit.
:::
