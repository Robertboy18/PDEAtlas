/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws.Burgers
import Blueprint.Commands.Figures
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Slope
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Uniqueness
import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Contraction
import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.TraceContraction
import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Uniqueness
import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.L1
import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.NWave
import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.InitialValue
import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Minimizers
import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.UniformlyConvex
import PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.InitialValue
import PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.Profile

/-!
# The scalar theory

Oleinik's one-sided bound and the uniqueness it gives, Kružkov's local `L¹`
contraction, the Lax–Oleinik formula, the Riemann problem for a uniformly
convex flux, and the N-wave asymptotics.
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
#doc (Manual) "The Scalar Theory" =>

# Uniqueness, the Lax–Oleinik formula, and large times

Burgers's equation showed that the weak equation alone admits too many
solutions. For a scalar law $`u_t+F(u)_x=0` there are two standard ways to
restore uniqueness. Oleinik's condition is a one-sided bound on the spatial
slope, and it is the route {Informal.citet "evans-2010"}[] takes in §3.4 for a
uniformly convex flux. Kružkov's route compares two entropy solutions through
the inequalities for $`|u-k|`, which follow from the convex entropy
inequalities by approximation.

:::definition "hyperbolic.conservation.oleinik_bound" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.HasOleinikBound, PDE.Hyperbolic.ConservationLaw.HasOleinikBound.ae_time_increment_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "145-160"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A function $`u` on spacetime has Oleinik bound $`C\ge0` if

$$`
u(t,x+z)-u(t,x)\le C\Bigl(1+\frac1t\Bigr)z
`

for almost every $`(t,x,z)` with $`t>0` and $`z>0`.
:::

The bound only limits upward jumps. A compressive shock, where $`u` drops,
satisfies it; an expansion shock, where $`u` rises across a line, violates it
for small $`z`. For a convex flux this one-sided information is enough to
decide uniqueness, with no entropy pair in sight.

:::theorem "hyperbolic.conservation.oleinik_uniqueness" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.IsWeakInitialValueSolution.ae_eq_of_oleinik") (uses := "hyperbolic.conservation.oleinik_bound, hyperbolic.conservation.weak_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "145-160"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`F` be $`C^2` and convex. If $`u` and $`v` are weak initial-value
solutions with the same datum $`g`, both essentially bounded on
$`t>0`, and each has some Oleinik bound, then $`u=v` almost everywhere on
$`t>0`.
:::

:::proof "hyperbolic.conservation.oleinik_uniqueness"
Each solution has a Lipschitz potential $`w` with $`w_x=u` weakly, and
the weak equation makes $`w` a solution of $`w_t+F(w_x)=0` almost
everywhere with initial value $`\int_0^xg`. The Oleinik bound says that
$`w(t,\cdot)` is semiconcave for $`t>0`. Uniqueness for semiconcave
Hamilton–Jacobi solutions identifies the two potentials, and uniqueness of
weak derivatives then identifies $`u` and $`v` almost everywhere. The
one-sided bound is the key input.
:::

Kružkov's inequalities take the opposite approach. They hold for every
$`C^1` flux, convex or not, and compare any two entropy solutions directly
by doubling the variables.

:::theorem "hyperbolic.conservation.kruzhkov_contraction" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropySolutionWithInitialTrace.local_l1_contraction_ae, PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropySolutionWithInitialTrace.exists_local_l1_contraction_ae") (uses := "hyperbolic.conservation.weak_ivp, hyperbolic.conservation.entropy_solution")
Let $`F` be $`C^1` and let $`u` and $`v` be entropy solutions with initial
traces $`u_0` and $`v_0`, both bounded by $`M` almost everywhere. If
$`|F'|\le c` on $`[-M,M]`, then for almost every $`T>0`, with a null set depending on the interval
$`[a,b]`,

$$`
\int_{a+cT}^{b-cT}|u(T,x)-v(T,x)|\,dx\le\int_a^b|u_0(x)-v_0(x)|\,dx.
`
:::

:::proof "hyperbolic.conservation.kruzhkov_contraction"
Test the entropy inequality for $`u` with $`k=v(s,y)` and the one for
$`v` with $`k=u(t,x)`, add, and integrate against a test function
concentrating on the diagonal $`(t,x)=(s,y)`. This gives
$`\partial_t|u-v|+\partial_x q(u,v)\le0` in the sense of distributions,
with $`|q(u,v)|\le c|u-v|`. Integrating over the trapezoid that shrinks at
speed $`c` and using the strong initial traces gives the inequality.
:::

The shrinking interval is the domain of dependence of $`[a,b]`: information
travels at most at speed $`c`, as in the energy argument for the wave
equation. Equal traces force the right side to vanish on every interval.

:::theorem "hyperbolic.conservation.kruzhkov_uniqueness" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropySolutionWithInitialTrace.unique_ae, PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropySolutionWithInitialTrace.unique_at_all_positive_times") (uses := "hyperbolic.conservation.kruzhkov_contraction")
For a $`C^1` flux, two bounded entropy solutions with the same initial trace
agree almost everywhere on $`t>0`. If the chosen representatives attain
their left traces in time, their time slices agree almost everywhere at
every $`T>0`, not only for almost every $`T`.
:::

:::proof "hyperbolic.conservation.kruzhkov_uniqueness"
The contraction with $`u_0=v_0` makes almost every slice vanish on every
interval, hence almost everywhere in space, and Fubini gives the spacetime
statement. For the second claim, the contraction is rerun from the left
trace at a fixed time instead of from almost every time.
:::

# The Lax–Oleinik formula

For a uniformly convex flux the solution can be written down. Let
$`L=F^*` be the Legendre transform and $`h(y)=\int_0^yg`. The
Hamilton–Jacobi value

$$`
w(t,x)=\min_y\Bigl(tL\Bigl(\frac{x-y}{t}\Bigr)+h(y)\Bigr)
`

is the Hopf–Lax formula for $`w_t+F(w_x)=0`, and its derivative
$`u=w_x` is the candidate. At a minimizing footpoint $`y^*` the slope is
$`L'((x-y^*)/t)`, so $`u=(F')^{-1}((x-y^*)/t)`: the value carried along the
straight characteristic from $`y^*`.

:::theorem "hyperbolic.conservation.lax_oleinik" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.LaxOleinik.solution_spec_of_deriv2_lower_bound, PDE.Hyperbolic.ConservationLaw.LaxOleinik.laxOleinik_formula_of_deriv2_lower_bound, PDE.Hyperbolic.ConservationLaw.LaxOleinik.ae_norm_solution_le_eLpNorm_of_deriv2_lower_bound, PDE.Hyperbolic.ConservationLaw.LaxOleinik.solution, PDE.Hyperbolic.ConservationLaw.LaxOleinik.solution_slope_le_of_deriv2_lower_bound, PDE.Hyperbolic.ConservationLaw.LaxOleinik.hasOleinikBound_solution_of_deriv2_lower_bound") (uses := "hyperbolic.conservation.weak_ivp, hyperbolic.conservation.oleinik_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "145-160"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`F` be $`C^2` with $`F''\ge\theta>0` and let $`g\in L^\infty`. The
minimum defining $`w(t,x)` is attained, the footpoint can be chosen
monotone in $`x` and is unique outside a countable set of $`x` for each
$`t>0`, and at almost every spatial point

$$`
u(t,x)=(F')^{-1}\Bigl(\frac{x-y^*(t,x)}{t}\Bigr)=\partial_xw(t,x).
`

The function $`u` is a weak initial-value solution with datum $`g`, and
$`|u|\le\|g\|_{L^\infty}` almost everywhere.
The actual selected representative also satisfies the sharp one-sided bound

$$`u(t,x+z)-u(t,x)\le\frac{z}{\theta t}
\qquad(t>0,\ x\in\mathbb R,\ z\ge0).`

This includes points with nonunique minimizing footpoints. In particular it
satisfies the weaker Oleinik bound $`C(1+1/t)z` of the definition, with
$`C=1/\theta`.
:::

:::proof "hyperbolic.conservation.lax_oleinik"
The lower bound on $`F''` makes $`L` finite, strictly convex and
superlinear, so minimizers exist and move monotonically with $`x`. A
monotone function has countably many jumps, which gives the uniqueness of
the footpoint and the differentiability of $`w` in $`x` off a countable set.
The weak equation for $`u` comes from the almost-everywhere Hamilton–Jacobi
equation for $`w`, integrated by parts against $`\varphi_x`. The bound by
$`\|g\|_{L^\infty}` is inherited from the datum through the footpoint
formula.
For the slope estimate, monotonicity of the chosen footpoint gives
$`(x+z-y^*(t,x+z))/t-(x-y^*(t,x))/t\le z/t`.
Uniform convexity makes $`(F')^{-1}` increasing and
$`1/\theta`-Lipschitz. If the first argument is smaller, the solution
difference is nonpositive; otherwise that Lipschitz estimate gives
$`z/(\theta t)`. This uses the minimizing selection itself, so no
differentiability at a shock is needed.
:::

With the formula and the uniqueness theorem in hand, the Riemann problem can
be solved for every uniformly convex flux, not only for Burgers.

:::theorem "hyperbolic.conservation.scalar_riemann" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.exists_riemann_initial_value_solution, PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.riemannSolution, PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.rarefactionProfile") (uses := "hyperbolic.conservation.oleinik_uniqueness, hyperbolic.conservation.entropy_solution, hyperbolic.conservation.weak_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "153-155"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`F` be $`C^2` with $`F''\ge\theta>0`, and let $`G=(F')^{-1}`. For all
states $`u_L,u_R`, the profile equal to the Lax shock at the Rankine–Hugoniot
speed when $`u_R<u_L`, and to

$$`
u(t,x)=\begin{cases}
u_L,& x<F'(u_L)t,\\
G(x/t),& F'(u_L)t\le x<F'(u_R)t,\\
u_R,& x\ge F'(u_R)t
\end{cases}
`

when $`u_L\le u_R`, is a weak initial-value solution and an entropy weak
solution for $`t>0`, with a strong $`L^1_{\mathrm{loc}}` trace. It is
invariant under the positive dilations $`(t,x)\mapsto(at,ax)`, bounded by $`\max(|u_L|,|u_R|)`,
equal to $`u_L` and $`u_R` outside the cone
$`|x|<\max(|F'(u_L)|,|F'(u_R)|)\,t`, and satisfies
$`u(t,x+z)-u(t,x)\le z/(\theta t)` for positive times and nonnegative increments. Every bounded
weak initial-value solution with the same data and some Oleinik bound equals it
almost everywhere on positive time.
:::

:::proof "hyperbolic.conservation.scalar_riemann"
The shock branch uses the planar-shock theorem and strict convexity for the
Lax inequalities. On the fan, $`G` is Lipschitz with constant
$`\theta^{-1}`, which gives the slope bound $`z/(\theta t)`, and the profile
is a classical solution of $`u_t+F'(u)u_x=0` joined continuously to the
constant states. Uniqueness is the Oleinik theorem applied to the
constructed profile and the competitor.
:::

# Large times

The N-wave comparison profile has expanding negative and positive lobes,
separated from the zero state by shocks. A zero lobe parameter removes that
lobe. The parameters come from extrema of the initial primitive, rather than
from the separate integrals of the positive and negative parts of the
compactly supported datum. For Burgers's flux the comparison profile is

$$`
N(t,x)=\begin{cases}x/t,& -\sqrt{pt}<x<\sqrt{qt},\\0,&\text{otherwise,}\end{cases}
\qquad
p=-2\min_x\int_{-\infty}^xg,\quad q=2\max_x\int_x^\infty g.
`

For a general flux the fan is centred at $`F'(0)t` and its slope and width
are scaled by $`F''(0)`.

:::theorem "hyperbolic.conservation.n_wave" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.LaxOleinik.exists_integral_abs_sub_nWave_le, PDE.Hyperbolic.ConservationLaw.LaxOleinik.nWave, PDE.Hyperbolic.ConservationLaw.LaxOleinik.negativeLobeMass, PDE.Hyperbolic.ConservationLaw.LaxOleinik.positiveLobeMass") (uses := "hyperbolic.conservation.lax_oleinik")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "145-160"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`F` be $`C^3` with $`F''\ge\theta>0` and $`F(0)=0`, and let
$`g\in L^\infty` vanish almost everywhere outside a bounded interval, with
both lobe masses $`p` and $`q` positive. Then there is a constant $`C` such
that, for the Lax–Oleinik solution $`u`,

$$`
\int_{\mathbb R}|u(t,x)-N(t,x)|\,dx\le\frac{C}{\sqrt t}\qquad(t>0).
`
:::

:::proof "hyperbolic.conservation.n_wave"
Write $`t=s^2`. For large $`s`, the solution vanishes outside the two
fronts $`F'(0)t-\sqrt{pF''(0)t}` and $`F'(0)t+\sqrt{qF''(0)t}`, up to a
bounded distance. On an interior interval of length $`O(s)` the footpoint
stays in the bounded support and the slope differs from the linear profile
$`(x/t-F'(0))/F''(0)` by $`O(s^{-2})`, using a third-order expansion of the
flux at $`0`. Two strips of bounded width near the fronts, where both
functions are $`O(s^{-1})`, contribute the leading error $`O(s^{-1})`. For
bounded $`s` the bound follows from $`|u|\le\|g\|_\infty` and the finite
propagation of the support.
:::

{leanpde_figure "n-wave"}

The figure rescales so that the N-wave becomes a single fixed shape. The
left panel shows $`\sqrt t\,u` against $`x/\sqrt t`, and the profiles
settle onto the rescaled N-wave. The right panel is the $`L^1` error on a
log scale; it follows the slope $`-1/2` of the theorem. The datum is placed
so that the minimum of $`\int_0^yg` sits away from the jump, which is what
makes the rate $`t^{-1/2}` sharp rather than a crude upper bound for this
example.
