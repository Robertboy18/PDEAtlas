/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws.ScalarCharacteristics
import Blueprint.Commands.Figures
import PDE.Hyperbolic.ConservationLaw.Scalar.ConvexShock
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
import PDE.Hyperbolic.ConservationLaw.Scalar.PlanarShock
import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Entropy
import PDE.Hyperbolic.ConservationLaw.Scalar.Weak
import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
import PDE.Hyperbolic.ConservationLaw.System.InitialValue
import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannInitialValue
import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannSolution
import PDE.Hyperbolic.ConservationLaw.System.PlanarShock

/-!
# Weak and entropy solutions for conservation laws

Scalar and system weak formulations, classical solutions as weak solutions,
entropy admissibility, and the Rankine–Hugoniot and Lax jump conditions.
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
#doc (Manual) "Weak and Entropy Solutions" =>

:::definition "hyperbolic.conservation.system_weak_solution" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.IsWeakSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "612-615"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The local interior equation on an arbitrary open domain is
the Bochner-valued identity $`\int(\phi_tu+\phi_xf(u))=0` against compactly
supported scalar $`C^1` tests, assuming the state and flux are locally
integrable. The interior definition has no initial term and no initial
trace.
:::

Because the identity is obtained from the pointwise law by moving derivatives
onto the test function, every sufficiently regular pointwise solution
satisfies it, so the weak notion extends the classical one.

:::theorem "hyperbolic.conservation.system_classical_to_weak" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.isWeakSolution_of_pointwise_of_contDiff") (uses := "hyperbolic.conservation.system_flux_forms, hyperbolic.conservation.system_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "612-615"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
As a regular special case, every globally $`C^1` pointwise system solution
with globally $`C^1` flux is weak on the chosen open domain.
:::

:::proof "hyperbolic.conservation.system_classical_to_weak"
Multiply the pointwise conservation law by a compactly supported scalar test
function and integrate. Vector-valued integration by parts moves the time
and space derivatives from $`u` and $`f(u)` onto the test function. Compact
support removes every boundary term, leaving exactly the Bochner integral
identity in the definition of a system weak solution.
:::

The point of the weak formulation is that it also admits discontinuous states.
The simplest is a single jump moving at constant speed, and for it the weak
equation reduces to one algebraic condition on the two states and the speed,
the Rankine–Hugoniot relation.

Write $`[u]=u_R-u_L` and $`[f]=f(u_R)-f(u_L)`. Away from the interface
$`x=st`, both states are constant, so the residual is zero there. Across
the interface, distributional differentiation gives

$$`
\partial_tu+\partial_x f(u)=([f]-s[u])\,\delta_{x=st},
\qquad
\langle\delta_{x=st},\varphi\rangle
=\int_{\mathbb R}\varphi(t,st)\,dt.
`

The term $`s[u]` is the change in stored quantity as the jump moves; $`[f]`
is the flux imbalance. Conservation requires them to cancel, component by
component for a system.

:::theorem "hyperbolic.conservation.planar_shock_weak" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.RankineHugoniot.isWeakSolution_planarShock, PDE.Hyperbolic.ConservationLaw.System.isWeakSolution_planarShock_iff_rankineHugoniot, PDE.Hyperbolic.ConservationLaw.Scalar.RankineHugoniot.isWeakSolution_planarShock") (uses := "hyperbolic.conservation.system_weak_solution, hyperbolic.conservation.system_jump, hyperbolic.conservation.weak_solution, hyperbolic.conservation.jump_conditions")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "612-615"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For states $`u_L,u_R\in\mathbb R^m` and a speed $`s\in\mathbb R`, the planar
shock is the two-state profile

$$`
u(t,x)=\begin{cases}u_L,& x<st,\\ u_R,& x\ge st.\end{cases}
`

If the vector Rankine–Hugoniot relation $`f(u_R)-f(u_L)=s\,(u_R-u_L)` holds,
then $`u` is a weak solution of $`u_t+(f(u))_x=0` on all of spacetime. The
flux $`f\colon\mathbb R^m\to\mathbb R^m` is arbitrary: no continuity or
differentiability is assumed. Conversely, if the planar shock is a weak
solution on spacetime, then the Rankine–Hugoniot relation holds. The scalar
case is recorded separately against the scalar weak formulation, with the
same hypothesis and conclusion.
:::

:::proof "hyperbolic.conservation.planar_shock_weak"
The profile and its flux composition take only two values, so both are
locally integrable. For a compactly supported $`C^1` test $`\varphi`, the weak
integral splits into the contribution of the constant state $`u_R` over all
of spacetime, which vanishes because the integral of each partial derivative
of $`\varphi` is zero, and the integral of the jump terms over the half-plane
$`x<st`. The divergence theorem on that half-plane turns the latter into the
interface integral $`\int_{\mathbb R}\varphi(t,st)\,dt` multiplied by the
vector $`f(u_L)-f(u_R)-s\,(u_L-u_R)`. Rankine–Hugoniot makes this coefficient
zero. For the converse, a nonnegative test function with positive interface
integral forces the coefficient itself to vanish.
:::

Rankine–Hugoniot places no restriction on the direction of a jump, so the weak
equation alone does not single out a solution. The additional selection
principle is an inequality rather than an equation: entropy pairs, which for
classical solutions satisfy an exact conservation identity, are required to be
dissipated in the distributional sense.

:::definition "hyperbolic.conservation.system_entropy_inequality" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.SatisfiesEntropyInequalityFor, PDE.Hyperbolic.ConservationLaw.System.SatisfiesEntropyInequality, PDE.Hyperbolic.ConservationLaw.System.IsEntropyWeakSolution") (uses := "hyperbolic.conservation.system_entropy_pair, hyperbolic.conservation.system_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "646-649"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix an open set $`U` of spacetime, a state $`u` with values in $`\mathbb R^m`,
and an entropy pair $`(\eta,q)` compatible with the flux $`f`. The state
satisfies the entropy inequality for $`(\eta,q)` on $`U` when $`\eta(u)` and
$`q(u)` are locally integrable on $`U` and

$$`
0\le\int\bigl(\eta(u)\,\varphi_t+q(u)\,\varphi_x\bigr)\,dx\,dt
`

for every compactly supported $`C^1` test function $`\varphi\ge0` on $`U`.
This is the distributional form of $`\partial_t\eta(u)+\partial_xq(u)\le0`.
The state satisfies the entropy inequality when this holds for every convex
entropy pair of $`f`, and it is an entropy weak solution on $`U` when it is
in addition a weak solution there. No boundedness of $`u` is assumed, and all
three predicates are stable under restriction to smaller open sets and under
changes of $`u` on a null set.
:::

The first system to which these definitions apply is the p-system, whose
elementary waves are explicit spacetime profiles.

:::theorem "hyperbolic.conservation.p_system_elementary_wave_weak" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.isWeakSolution_elementaryWaveSolution") (uses := "hyperbolic.conservation.p_system_elementary_wave, hyperbolic.conservation.p_system, hyperbolic.conservation.system_weak_solution")
Let the stress law $`p` be $`C^2` on $`\mathbb R` with $`p'>0` and $`p''>0`
everywhere. For every family $`k\in\{0,1\}`, every left state
$`u_L=(v_L,w_L)` and every strength $`\sigma\in\mathbb R`, the physical
elementary wave $`W_k(\sigma;u_L)`, which is a rarefaction fan or a planar
Hugoniot shock according to the sign of $`\sigma`, is a weak solution of the
p-system

$$`
v_t-w_x=0,\qquad w_t-p(v)_x=0
`

on the open forward half-space $`\{t>0\}`.
:::

:::proof "hyperbolic.conservation.p_system_elementary_wave_weak" (uses := "hyperbolic.conservation.planar_shock_weak, hyperbolic.conservation.p_system_hugoniot_branch, hyperbolic.conservation.p_system_rarefaction_fan, hyperbolic.conservation.self_similar_wave")
Split on the family and on the sign of the strength. On a shock branch,
$`p'>0` makes the stress difference quotient positive, so the Hugoniot
endpoint satisfies Rankine–Hugoniot and the planar shock is a weak solution
on all of spacetime; restrict it to $`t>0`. On a rarefaction branch,
$`p''>0` makes the sound speed increasing in the strain, which orders the two
edge speeds of the fan. Inside the wedge the self-similar middle state is
$`C^1` and solves the system pointwise, because its tangent is a right
eigenvector of the flux Jacobian with eigenvalue $`x/t`; on each edge it
agrees continuously with the adjacent constant state, so integrating by parts
region by region produces no interface terms.
:::

A single elementary wave joins a left state to the one-parameter family of
right states on its wave curve, so reaching an arbitrary nearby right state
takes one wave from each of the two families.

:::theorem "hyperbolic.conservation.p_system_local_entropy_riemann" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.exists_local_mechanicalEntropySolutionWithInitialTrace") (uses := "hyperbolic.conservation.p_system_hyperbolic, hyperbolic.conservation.p_system_entropy, hyperbolic.conservation.system_weak_solution, hyperbolic.conservation.system_entropy_inequality")
Assume $`p` is $`C^2`, $`p'>0`, and $`p''>0`, and let a $`C^1`
potential $`P` satisfy $`P'=p`. For every left state there is an open
neighborhood containing it such that each right state in that neighborhood
admits an explicit two-wave p-system solution. The solution is weak on
positive time, converges strongly in local $`L^1` to the Riemann datum, and
satisfies the mechanical entropy inequality on the forward half-space.
:::

:::proof "hyperbolic.conservation.p_system_local_entropy_riemann" (uses := "hyperbolic.conservation.p_system_elementary_wave_weak")
The two local elementary-wave curves have the characteristic eigenvectors as
their zero-strength tangents. Strict hyperbolicity makes those tangents a
basis, so the inverse function theorem gives unique small strengths joining
the left state to every nearby right state. Concatenating the corresponding
shock or rarefaction profiles yields a self-similar weak solution.
Rankine–Hugoniot handles jumps, convex mechanical entropy gives the
admissible sign, and the shrinking width of the wave fan proves local
$`L^1` convergence to the Riemann datum as $`t\downarrow0`.
:::

{leanpde_figure "p-system-riemann-fan"}

The figure takes $`p(v)=e^v`, for which the sound speed $`c=e^{v/2}` and
the invariants are explicit. In spacetime the $`0`-rarefaction opens to the
left of the origin, and the $`1`-shock moves to the right, with the
$`1`-characteristics from both sides running into it. In the state plane
the path goes down the $`0`-rarefaction curve, on which $`w-A(v)` is
constant, and then along the Hugoniot curve of family $`1`. The strengths in
the figure are chosen large enough to be visible; the theorem applies to
right states in a neighborhood of $`u_L` of unspecified size.

For a single equation the vector formulation specializes to $`m=1`, but the
scalar theory has its own predicates, in which the Burgers profiles and the
convex-flux jump theory are stated.

:::definition "hyperbolic.conservation.weak_solution" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.IsWeakSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "135-142"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A weak solution of $`u_t + (f(u))_x=0` is defined on an open domain. Both
$`u` and $`f(u)` are required to be locally integrable, and the equation is
tested against compactly supported $`C^1` functions after moving derivatives
onto the test function. The definition does not assume that $`u` itself is
differentiable.
:::

The interior definition never sees the initial line. Initial data enter
either through a boundary term in the weak identity or through a separate
trace condition.

:::definition "hyperbolic.conservation.weak_ivp" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.IsWeakInitialValueSolution, PDE.Hyperbolic.ConservationLaw.Scalar.HasInitialTraceLocallyL1, PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropySolutionWithInitialTrace, PDE.Hyperbolic.ConservationLaw.System.IsWeakInitialValueSolution.interior") (uses := "hyperbolic.conservation.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "135-160"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The shared forward-half-space weak initial-value formulation allows compactly
supported scalar tests to meet $`t=0` and includes the boundary term. Its
Bochner-valued identity covers both scalar laws and finite-dimensional
systems; in Euclidean state spaces it is the coordinate-free form of the
usual component equations. Restricting to tests supported away from $`t=0`
recovers the interior weak equation. The complementary trace
formulation combines that interior equation with strong convergence to
a locally integrable datum $`u_0` in $`L^1_{\mathrm{loc}}(\mathbb R)` as
$`t\downarrow0`. The scalar entropy version combines the trace with the
positive-time entropy solution.
:::

As for systems, classical solutions are weak solutions.

:::theorem "hyperbolic.conservation.classical_to_weak" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.isWeakSolution_of_pointwise_of_contDiff") (uses := "hyperbolic.conservation.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "135-137"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A $`C^1` pointwise solution with a $`C^1` flux satisfies
{uses "hyperbolic.conservation.weak_solution"}[].
:::

:::proof "hyperbolic.conservation.classical_to_weak"
Expand the flux residual, apply the chain rule, and integrate
the spacetime divergence against a compactly supported test function.
Boundary terms vanish because of compact support.
:::

Uniqueness fails for scalar weak solutions exactly as it does for systems, and
the remedy is the same entropy inequality.

:::definition "hyperbolic.conservation.entropy_solution" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropyWeakSolution") (uses := "hyperbolic.conservation.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "145-160"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The scalar entropy predicate is stated for any flux $`f` and uses $`f'` in the
compatibility relation; it is the standard notion when $`f` is $`C^1`, as in
every theorem that uses it. An entropy pair consists of globally $`C^1`
functions $`\eta,q` satisfying $`q'=\eta'f'`. A weak solution on the open domain
$`U` is an entropy weak solution when, for every such pair with $`\eta` convex
on $`\mathbb R`, $`\eta(u)` and $`q(u)` are locally integrable on $`U` and the
integrated entropy inequality holds for every nonnegative $`C^1` test with
compact support contained in $`U`.
:::

For piecewise constant states the weak equation and admissibility become
algebraic conditions on the jump.

:::definition "hyperbolic.conservation.jump_conditions" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.RankineHugoniot, PDE.Hyperbolic.ConservationLaw.Scalar.LaxShock")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "136-142"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a jump from $`u_L` to $`u_R` moving with speed $`s`, the
Rankine–Hugoniot relation is

$$`
f(u_R)-f(u_L)=s(u_R-u_L).
`

When $`u_L\ne u_R`, this selects the secant speed
$`s=(f(u_R)-f(u_L))/(u_R-u_L)`. The scalar Lax inequalities

$$`
f'(u_R)<s<f'(u_L)
`

encode compressive admissibility through the characteristic speeds on the two
sides.
:::

Both conditions can be read off from the graph of a convex flux: the shock
speed is the slope of the chord between the two states, and convexity orders
the chords through any intermediate state.

:::theorem "hyperbolic.conservation.convex_secant_speed" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.rankineHugoniotSpeed_eq_slope, PDE.Hyperbolic.ConservationLaw.Scalar.slope_right_lt_rankineHugoniotSpeed, PDE.Hyperbolic.ConservationLaw.Scalar.rankineHugoniotSpeed_lt_slope_left") (uses := "hyperbolic.conservation.jump_conditions")
For any flux $`f\colon\mathbb R\to\mathbb R` and states $`u_L,u_R`, the
Rankine–Hugoniot speed

$$`
s(u_L,u_R)=\frac{f(u_R)-f(u_L)}{u_R-u_L}
`

is the secant slope of $`f` between the two states; both sides are the
totalized value $`0` when $`u_L=u_R`. If $`f` is strictly convex on
$`\mathbb R`, then for every intermediate state $`u_R<k<u_L`,

$$`
\frac{f(k)-f(u_R)}{k-u_R}<s(u_L,u_R)<\frac{f(u_L)-f(k)}{u_L-k}.
`

These strict chord inequalities are the Oleinik form of admissibility for a
compressive jump; no differentiability of $`f` is assumed.
:::

:::proof "hyperbolic.conservation.convex_secant_speed"
The secant identity is the definition of the slope after exchanging the two
endpoints. For the chord inequalities, write the shock speed as the slope of
$`f` over $`[u_R,u_L]`. Strict convexity makes secant slopes strictly
increasing in each endpoint, so the slope over the initial segment
$`[u_R,k]` lies strictly below the slope over the whole interval, which in
turn lies strictly below the slope over the final segment $`[k,u_L]`.
:::

The chord inequalities compare the shock speed with secants through an
intermediate state. Replacing those secants by the tangent slopes at the two
endpoints gives the Lax inequalities, and this is where differentiability of
$`f` at $`u_L` and $`u_R` enters.

:::theorem "hyperbolic.conservation.convex_lax_shock" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.laxShock_rankineHugoniotSpeed, PDE.Hyperbolic.ConservationLaw.Scalar.RankineHugoniot.laxShock_iff_right_lt_left") (uses := "hyperbolic.conservation.jump_conditions")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "136-142"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f` be strictly convex on $`\mathbb R` and differentiable at the two
states $`u_L` and $`u_R`. If $`u_R<u_L`, the Rankine–Hugoniot speed
$`s=s(u_L,u_R)` satisfies the Lax shock inequalities

$$`
f'(u_R)<s<f'(u_L).
`

More generally, if $`u_R\ne u_L` and $`s` is any speed satisfying
$`f(u_R)-f(u_L)=s\,(u_R-u_L)`, then the Lax inequalities hold for $`s` if and
only if $`u_R<u_L`. For a strictly convex flux, a Rankine–Hugoniot jump is
therefore Lax-admissible exactly when it is compressive.
:::

:::proof "hyperbolic.conservation.convex_lax_shock" (uses := "hyperbolic.conservation.convex_secant_speed")
Write the shock speed as the secant slope of $`f` over $`[u_R,u_L]`. For a
strictly convex function, the derivative at the left endpoint of an interval
lies strictly below the secant slope, which lies strictly below the derivative
at the right endpoint; with $`u_R<u_L` this reads $`f'(u_R)<s<f'(u_L)`. For
the equivalence, Rankine–Hugoniot with distinct states forces $`s` to be the
secant speed. In the expansive case $`u_L<u_R` the same secant inequalities
give $`f'(u_L)<s`, which contradicts the Lax inequality $`s<f'(u_L)`.
:::

# Curved shocks with varying states

The jump calculation also works when the interface bends and the states on
either side vary. Let the interface be $`x=s(t)` and define
$`[v](t)=v_R(t,s(t))-v_L(t,s(t))`. Integrating by parts on the two sides
leaves an interface contribution with coefficient $`s'[u]-[f(u)]`.
Rankine–Hugoniot cancels this contribution; entropy requires the analogous
coefficient to have a sign.

:::theorem "hyperbolic.conservation.curved_entropy_shock" (parent := "hyperbolic.conservation") (uses := "hyperbolic.conservation.entropy_solution, hyperbolic.conservation.jump_conditions") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.Shock.isEntropyWeakSolution_profile_of_convex")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§3.4 (shocks and entropy)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f,s\in C^1(\mathbb R)` and $`u_L,u_R\in C^1(\mathbb R^2)`.
Assume $`u_L` solves $`u_t+(f(u))_x=0` on $`x<s(t)` and $`u_R`
solves it on $`x>s(t)`. Suppose at every interface point

$$`s'(t)[u](t)=[f(u)](t),\qquad
u_R(t,s(t))\le u_L(t,s(t)),`

and $`f` is convex on the interval between these two traces. Then the
piecewise field is a weak solution and satisfies every $`C^1` convex
entropy inequality on all of $`\mathbb R^2`.
:::

:::proof "hyperbolic.conservation.curved_entropy_shock"
The classical residuals vanish in the two open regions. Integration by
parts with the moving boundary reduces the weak residual to the
Rankine–Hugoniot coefficient, which is zero. For an entropy pair
$`(\eta,q)` with $`q'=\eta'f'`, the same calculation gives

$$`\int_{\mathbb R^2}\bigl(\eta(u)\varphi_t+q(u)\varphi_x\bigr)\,dt\,dx
=\int_{\mathbb R}\bigl(s'[\eta(u)]-[q(u)]\bigr)
\varphi(t,s(t))\,dt.`

The integral on the right uses the time parameter along the interface.
Convexity of the flux between the downward traces, together with convexity
of the entropy, makes its coefficient nonnegative. Thus every nonnegative
compactly supported test gives the entropy inequality. Neither constant
traces nor a straight interface is used.
:::
