/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.TimeRegularity
import PDE.Analysis.Evolution.Integrated.ClassicalTrajectory
import PDE.Analysis.Evolution.Integrated.EnergyBounds
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Integrated.TimeDistribution
import PDE.Analysis.Evolution.Integrated.Uniqueness

/-!
# Integrated weak evolution

Hilbert and Gelfand integrated weak solutions: consistency with
differentiable trajectories, recovered time derivatives, energy bounds,
uniqueness, and continuous dependence.
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
#doc (Manual) "Integrated Weak Evolution" =>

# Integrated weak solutions

:::definition "parabolic.integrated_weak_solution" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsIntegratedWeakSolution, PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution") (uses := "parabolic.gelfand_triple, parabolic.gelfand_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "378-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`a<b`. In one Hilbert space $`V`, the integrated formulation uses its inner product
for both the time term and initial datum. More generally, let
$`V\hookrightarrow H\hookrightarrow V^*` be a Gelfand triple, let
$`B(t):V\to V^*` be induced by a time-dependent bilinear form, and fix
$`u_0\in H` and $`\ell\in L^2(a,b;V^*)`. A Gelfand integrated weak solution is a Bochner
class $`u\in L^2(a,b;V)` for which the tested spatial-form and forcing terms are
integrable and the following identity holds:

$$`
-\int_a^b (u(t),v)_H\,\tau'(t)\,dt+\int_a^b B(t)u(t)[v]\,\tau(t)\,dt
=\int_a^b \ell(t)[v]\,\tau(t)\,dt+(u_0,v)_H\,\tau(a)
`

This is required for every $`v\in V` and every scalar function
$`\tau:\mathbb R\to\mathbb R` differentiable at each point of $`[a,b]`, with
$`\tau,\tau'\in L^2(a,b)` and $`\tau(b)=0`. The forcing pairing is integrable by Hölder
under the stated $`L^2` assumption; the definition records integrability of both tested
terms explicitly.
Both versions are invariant under almost-everywhere changes of the forcing or
trajectory.
:::

A solution concept stated for Bochner classes should agree with the pointwise
one on trajectories regular enough for both to make sense. In the case
$`H=V`, integration by parts against a scalar time test provides this
consistency check.

:::theorem "parabolic.classical_integrated_identity" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.SatisfiesWeakEvolutionOn.integrated_test_identity, PDE.Analysis.Evolution.SatisfiesWeakEvolutionOn.integrated_initial_identity, PDE.Analysis.Evolution.SatisfiesWeakEvolutionOn.integrated_initial_identity_L2") (uses := "parabolic.smooth_weak_evolution, parabolic.integrated_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-378"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Suppose the Hilbert-space weak evolution has the stated time derivative throughout the interval.
For the chosen spatial and scalar time tests, assume the derivative pairing $`(u',v)_H`,
the scalar test derivative, and $`B(t)u(t)[v]\tau(t)` are interval-integrable.
Integration by parts then gives the distributional time-test identity. Tests vanishing only
at the final endpoint retain the initial boundary term. Replacing the trajectory by an
almost-everywhere equal Bochner $`L^2` representative gives the identity used by the
Hilbert integrated weak formulation.
:::

:::proof "parabolic.classical_integrated_identity"
Under these hypotheses, pair the pointwise weak equation with a scalar time test and integrate.
Integration by parts changes
$`\int (u'(t),v)_H\tau(t)\,dt` into
$`-\int(u(t),v)_H\tau'(t)\,dt` plus endpoint terms. A test vanishing at both
ends removes both terms; a test vanishing only at the final endpoint leaves
$`(u(a),v)_H\tau(a)`. Almost-everywhere replacement of $`u` does not change
any Bochner integral, giving the completed-space identity.
:::

In the opposite direction, the integrated identity determines a time
derivative, and from there the Lions–Magenes theory applies to every
integrated weak solution.

:::theorem "parabolic.integrated_residual_derivative" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.hasWeakTimeDerivative_residual, PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.ae_weak_equation, PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2") (uses := "parabolic.integrated_weak_solution, parabolic.gelfand_weak_time_derivative, parabolic.lions_magenes_finite_interval")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "378-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

If $`B(t):V\to V^*` is strongly measurable and essentially uniformly
bounded, the time-tested integrated equation identifies the residual

$$`g(t)=\ell(t)-B(t)u(t)`

as an element of $`L^2(a,b;V^*)` and proves that it is the Gelfand weak time
derivative of $`u`.  Consequently $`g+B(\cdot)u=\ell` almost everywhere.
For $`a<b`, the same theorem chain returns a continuous pivot
representative with left endpoint exactly $`u_0`; the trace equality comes
from the initial-endpoint test.
:::

:::proof "parabolic.integrated_residual_derivative"
Uniform boundedness of $`B(t)` sends $`u\in L^2(V)` to
$`B(\cdot)u\in L^2(V^*)`, so $`g=\ell-B(\cdot)u` is a valid Bochner class.
Move the form term in the integrated equation to the right; the remaining
identity is exactly the Gelfand weak-derivative test formula for $`g`.
Lions–Magenes supplies the continuous pivot representative. Comparing the
initial boundary term in the integrated identity with its fundamental
theorem formula forces the left trace to equal $`u_0`.
:::

With the derivative and the continuous pivot representative in hand, the
exact energy identity is available, and coercivity together with a uniform
bound on the forcing turns it into the estimate that the Galerkin
approximations satisfy. Continuity of $`\ell` on $`[a,b]` is used only to
make a pointwise forcing
an $`L^2(a,b;V^*)` class; the estimate itself uses the bound $`M` alone.

:::theorem "parabolic.integrated_energy_bound" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_with_energy_bound") (uses := "parabolic.integrated_residual_derivative, parabolic.lions_magenes_energy_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "376-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a<b`, let $`B` be strongly measurable and essentially uniformly
bounded, and let $`\ell` be continuous on $`[a,b]`. Assume $`C>0`, $`M\geq0`,
$`B(t)(v,v)\geq C\|v\|_V^2`, and $`\|\ell(t)\|_{V^*}\leq M` for every
$`t\in[a,b]` and $`v\in V`. Every integrated weak solution admits a
continuous pivot representative with the prescribed initial value and, for
every $`t\in[a,b]`,

$$`\frac12\lVert u_H(t)\rVert_H^2+
\frac C2\int_a^t\lVert u(s)\rVert_V^2\,ds
\le \frac12\lVert u_0\rVert_H^2+
\frac{M^2}{2C}(t-a).`

This is the final-solution counterpart of Evans's uniform Galerkin estimate.
The theorem also reconstructs an $`L^2(a,b;V^*)` weak derivative; endpoint
values refer to the returned continuous representative.
:::

:::proof "parabolic.integrated_energy_bound" (uses := "parabolic.integrated_residual_derivative, parabolic.lions_magenes_energy_identity")
Recover the weak time derivative and Lions–Magenes representative from the
integrated identity, identify the initial endpoint, and combine the exact
pivot energy identity with coercivity and Young's inequality.
:::

For two solutions with the same data the forcing cancels from the
difference, so no bound on $`\ell` is needed and coercivity can be relaxed to
a Gårding inequality. The lower-order term $`\gamma\lVert Jw\rVert_H^2` that
the inequality introduces into the energy balance is absorbed by an integral
Grönwall argument on the pivot norm of the difference.

:::theorem "parabolic.integrated_garding_uniqueness" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.unique_of_garding") (uses := "parabolic.integrated_residual_derivative, parabolic.lions_magenes_energy_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a<b` and let $`B` be strongly measurable and essentially uniformly
bounded. Assume, for all $`t\in[a,b]` and $`v\in V`,

$$`\theta\lVert v\rVert_V^2\le
B(t)(v,v)+\gamma\lVert Jv\rVert_H^2`

with $`\theta\ge0` and $`\gamma\in\mathbb R`. Two integrated weak solutions with the same
forcing and initial datum are equal as $`L^2(a,b;V)` classes. This follows
Evans's lower-order uniqueness argument; the unshifted form need not be
nonnegative.
:::

:::proof "parabolic.integrated_garding_uniqueness" (uses := "parabolic.integrated_residual_derivative, parabolic.lions_magenes_energy_identity")
Apply the Lions–Magenes identity to the difference, discard the nonnegative
energy term, and use integral Grönwall on the squared pivot norm. Almost
everywhere equality of included representatives then gives equality in
$`L^2(a,b;V)` by injectivity of $`J`.
:::

With $`\theta>0`, keeping the differences of forcing and initial data, instead
of setting them to zero, turns the same computation into a stability estimate.

:::theorem "parabolic.integrated_continuous_dependence" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.difference_garding_energy_bound_L2, PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.norm_sub_le_of_coercive_L2") (uses := "parabolic.integrated_residual_derivative, parabolic.lions_magenes_energy_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "376-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Consider two solutions for the same strongly measurable, essentially uniformly
bounded form on $`[a,b]`, where $`a<b`. Assume the Gårding inequality with
$`\theta>0`. Subtracting their integrated equations gives
the Gårding energy inequality for the continuous pivot-space difference, with both the
difference of initial data and the difference of $`L^2(V^*)` forcings visible.
In the strictly coercive case $`C>0`, a common initial datum gives the operator estimate

$$`\lVert u_1-u_2\rVert_{L^2(a,b;V)}
  \le C^{-1}\lVert\ell_1-\ell_2\rVert_{L^2(a,b;V^*)}.`

The zero-data specialization gives uniqueness, and the quantitative
continuous-dependence form completes the Galerkin solution operator from
regular to arbitrary $`L^2` loads.
:::

:::proof "parabolic.integrated_continuous_dependence"
Subtract the two integrated equations. The difference is an integrated weak
solution with initial datum $`u_{01}-u_{02}` and forcing
$`\ell_1-\ell_2`. Apply the Lions–Magenes energy identity, use the Gårding
lower bound on the form, and estimate the dual forcing by Young's inequality.
The stated estimate retains the lower-order pivot integral; a further Grönwall
step can bound it. With common initial data and strict coercivity, integration
and cancellation give
$`\|u_1-u_2\|_{L^2(V)}\leq C^{-1}\|\ell_1-\ell_2\|_{L^2(V^*)}`.
:::
