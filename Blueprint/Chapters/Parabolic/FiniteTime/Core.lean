/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.Regularity
import PDE.Analysis.Evolution.Core.FiniteTimeBlowup
import PDE.Analysis.Evolution.ODE.MaximalContinuation
import PDE.Representations.Similarity.Pointwise
import PDE.Solution.Singularity.FiniteTime.Comparison.QuadraticGrowth
import PDE.Solution.Singularity.FiniteTime.Moment.Weighted
import PDE.Solution.Singularity.FiniteTime.Norm.SpatialSupremum
import PDE.Solution.Singularity.FiniteTime.Norm.Trajectory
import PDE.Solution.Singularity.FiniteTime.Riccati.Explicit

/-!
# Finite-time singularity interfaces

Equation-independent norm blow-up, weighted moments, explicit Riccati
trajectories, and quadratic differential comparison.
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
#doc (Manual) "Finite-Time Singularity Interfaces" =>

:::group "parabolic.blowup"
Finite-time blow-up models
:::

# Mathematical Context

Finite-time blow-up can prevent a nonlinear parabolic solution from existing
globally. Starting from smooth initial data, we ask whether a solution remains
smooth or a specified norm becomes unbounded as $`t` approaches a finite
time $`T`.

The mechanisms studied here are *equation-independent*: they reduce the PDE
question to an ODE comparison. The prototypical argument has three steps:

1. *Derive a differential inequality.* A suitable functional of the
   solution (a weighted moment, an eigenfunction projection, or a spatial
   norm) satisfies $`y'\geq ay^p` for some $`p>1`.

2. *Compare with the ODE.* Assume $`a>0` and $`y_0>0`. The inequality
   $`y'\geq ay^2` (the Riccati case $`p=2`) is compared with the exact ODE
   solution $`y(t)=y_0/(1-ay_0(t-t_0))`, which blows up at the horizon
   $`T=t_0+1/(ay_0)`.

3. *Transfer to the PDE.* The comparison bounds the time interval on which
   the functional can remain finite. An estimate relating the functional to
   a PDE norm transfers this obstruction to the solution; a continuation
   theorem is needed to identify the endpoint of its maximal lifespan.

This strategy appears in Kaplan (1963) for eigenfunction moments, Fujita
(1966) for critical exponents, Levine (1973) for concavity methods, and
Evans (2010, pp. 547–549) for the weighted eigenfunction argument. To apply
the proved comparison and transfer results, a model must supply its
differential inequality, the required positivity and interval regularity,
and the estimate connecting its observable to the chosen PDE norm.

# Generic finite-time language

:::definition "parabolic.blowup.norm_trajectory" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NormBlowsUpAt")

A trajectory $`u : \mathbb R\to E` in a type equipped with a norm blows up at
$`T` when

$$`\lVert u(t)\rVert\longrightarrow+\infty\qquad\text{as }t\uparrow T.`

This is an equation-independent predicate. It can be applied to scalar
observables, Banach-space solution trajectories, and Sobolev- or
$`L^p`-valued evolutions.
:::

Because the predicate concerns only the scalar function
$`t\mapsto\lVert u(t)\rVert`, blow-up can be transported by any operation
whose effect on norms is controlled. Multiplication by a scalar amplitude,
composition with a linear isometry, and addition of an eventually bounded
error are three such operations; the amplitude case is the one that
similarity profiles use.

:::theorem "parabolic.blowup.amplitude_profile" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NormBlowsUpAt.of_smul") (uses := "parabolic.blowup.norm_trajectory")

Let $`E` be a seminormed module over a normed field $`\mathbb K`. If
$`\lVert A(t)\rVert\to+\infty` as $`t\uparrow T` and a profile family
$`v(t)\in E` satisfies

$$`c\le \lVert v(t)\rVert`

eventually for some $`c>0`, then $`A(t)v(t)` blows up in the norm of $`E`.
This is the quotient-friendly route for Sobolev and $`L^p` profiles: once a
dilation or pullback has been defined on the function space itself, the
argument needs only a lower norm bound and never chooses a pointwise
representative.
:::

:::proof "parabolic.blowup.amplitude_profile"
By the scalar-multiplication norm identity, the norm of the product is
$`\lVert A(t)\rVert\lVert v(t)\rVert`. Eventually this is bounded below by
$`c\lVert A(t)\rVert`. Multiplication by the positive constant $`c` preserves
convergence to $`+\infty`, so the product norm also diverges.
:::

The amplitude theorem runs in one direction only: a divergent amplitude
produces blow-up. A linear isometry preserves the norm exactly, so with it
the transfer is an equivalence.

:::theorem "parabolic.blowup.isometric_embedding" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NormBlowsUpAt.comp_linearIsometry_iff") (uses := "parabolic.blowup.norm_trajectory")

A linear isometric embedding preserves and reflects norm blow-up. This lets a
trajectory move between isometric models of a Sobolev or $`L^p` space without
choosing representatives or reproving its asymptotic norm behavior.
:::

:::proof "parabolic.blowup.isometric_embedding"
Unfold norm blow-up and composition. A linear isometry satisfies
$`\lVert Lu\rVert=\lVert u\rVert` pointwise, so the two convergence statements
are identical.
:::

An isometry changes the trajectory without changing its norm. A singular
leading term plus a controlled correction changes the norm by an eventually
bounded amount.

:::theorem "parabolic.blowup.bounded_remainder" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NormBlowsUpAt.iff_of_norm_sub_eventually_bounded") (uses := "parabolic.blowup.norm_trajectory")

If $`\lVert u(t)-v(t)\rVert` is eventually bounded as $`t\uparrow T`, then
$`u` blows up at $`T` if and only if $`v` does. Thus an eventually bounded
remainder neither creates nor removes norm blow-up.
:::

:::proof "parabolic.blowup.bounded_remainder"
Suppose $`\lVert u-v\rVert\leq C` eventually. To force
$`\lVert v(t)\rVert` above a threshold $`R`, first force
$`\lVert u(t)\rVert` above $`R+C`. The triangle inequality
$`\lVert u\rVert\leq\lVert u-v\rVert+\lVert v\rVert` then gives the desired
bound. The reverse implication is the same argument after using
$`\lVert v-u\rVert=\lVert u-v\rVert`.
:::

:::theorem "parabolic.blowup.no_continuous_extension" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NormBlowsUpAt.not_exists_continuousWithinAt_extension") (uses := "parabolic.blowup.norm_trajectory")

A trajectory whose norm blows up at $`T` has no left-continuous extension
through $`T`. More precisely, there is no function continuous within
$`(-\infty,T]` at $`T` that agrees with the trajectory for every $`t<T`.
:::

:::proof "parabolic.blowup.no_continuous_extension"
A continuous extension $`v` would converge to the finite value $`v(T)` from
within $`(-\infty,T]`. Restrict this convergence to times below $`T` and use
the pointwise agreement $`v=u` there. This gives a finite left limit for
$`u`, contradicting norm blow-up.
:::

That obstruction uses the norm alone. Paired with an existence statement for
integral curves it becomes a continuation alternative: for an autonomous $`C^1`
field on a complete space, an integral curve that fails to continue past a
finite time can have no limit there, and norm blow-up is one way for the
limit to fail.

:::theorem "parabolic.blowup.continuation_alternative" (parent := "parabolic.blowup") (lean := "PDE.Analysis.Evolution.exists_right_extension_of_tendsto, PDE.Analysis.Evolution.exists_right_extension_of_cauchy, PDE.Analysis.Evolution.exists_right_extension_of_tendsto_of_local, PDE.Analysis.Evolution.not_exists_continuous_extension_Iic_of_norm_tendsto_atTop, PDE.Analysis.Evolution.not_exists_continuous_extension_Iic_of_norm_tendsto_atTop_along, PDE.Analysis.Evolution.not_tendsto_nhds_of_norm_tendsto_atTop") (uses := "parabolic.blowup.norm_trajectory")

Let $`E` be a complete real normed space, $`f:E\to E`, $`a<b`, and let
$`u:\mathbb R\to E` be an integral curve of the autonomous equation

$$`u'(t)=f(u(t))\qquad(a<t<b).`

If $`u(t)\to x` as $`t\uparrow b` and $`f` is $`C^1` at $`x`, then there
are $`c>b` and $`v:\mathbb R\to E` with $`v=u` on $`(a,b)` and
$`v'(t)=f(v(t))` for all $`t\in(a,c)`. The same conclusion holds when
$`u` is Cauchy as $`t\uparrow b` and $`f` is $`C^1` at every point, and,
without completeness, when a local solution through $`(b,x)` on some
$`(b-\varepsilon,b+\varepsilon)` is supplied and $`f` is merely continuous
at $`x`.

Conversely, in any normed group, if $`\lVert u(t)\rVert\to+\infty` as
$`t\uparrow T`, then no $`v:\mathbb R\to E` with $`v(t)=u(t)` for all
$`t<T` is continuous within $`(-\infty,T]` at $`T`. The same holds along
any nontrivial clock $`\sigma\to T^-` for which
$`\lVert u(\sigma(s))\rVert\to+\infty`, and more basically a trajectory whose
norm tends to infinity along a nontrivial filter converges to no point.

The obstruction half is the no-extension theorem for norm blow-up stated
without the blow-up predicate, together with its reparametrized and
raw-filter variants.
:::

:::proof "parabolic.blowup.continuation_alternative"
For continuation, extend $`u` to $`\bar u` by the value $`x` at $`b`. On
$`(a,b)` the derivative $`f(u(t))` tends to $`f(x)`, so $`\bar u` has left
derivative $`f(x)` at $`b`. Since $`f` is $`C^1` at $`x`, the
Picard–Lindelöf theorem supplies a local solution $`w` with $`w(b)=x` on
$`(b-\varepsilon,b+\varepsilon)`. Define $`v=\bar u` for $`t\le b` and
$`v=w` for $`t\ge b`. Away from $`b` the curve $`v` locally coincides with a
solution; at $`b` its left and right derivatives are both $`f(x)`, so $`v`
is differentiable there with the correct derivative. In the Cauchy form,
completeness produces the limit $`x`.

For the obstruction, a left-continuous extension $`v` would give
$`u(t)=v(t)\to v(T)` as $`t\uparrow T`, hence
$`\lVert u(t)\rVert\to\lVert v(T)\rVert<\infty`, contradicting divergence of
the norm.
:::

Everything so far concerns a single trajectory in a normed space. A spatial
field $`u(x,t)` has no preferred norm; the pointwise supremum over $`x` is
the least committal choice, and since a slice may be unbounded the supremum
has to be allowed the value $`+\infty`.

:::definition "parabolic.blowup.generic_solution" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.spatialSupNorm, PDE.Solution.Singularity.FiniteTime.SpatialSupNormBlowsUpAt")

For a field $`u : X\to\mathbb R\to E`, the pointwise spatial supremum is the
extended nonnegative real

$$`
S_u(t)=\sup_{x\in X}\operatorname{ofReal}\lVert u(x,t)\rVert
\in\mathbb R_{\ge0}\cup\{+\infty\}.
`

In Lean this is `⨆ x, ENNReal.ofReal ‖u x t‖`. An unbounded spatial slice
therefore has value $`+\infty`. The limit $`S_u(t)\to+\infty` alone does
not identify a blow-up time: the stationary field $`u(x,t)=x` on
$`\mathbb R` has $`S_u(t)=+\infty` at every time.

`SpatialSupNormBlowsUpAt u T` requires both this limit as $`t\uparrow T`
and finite spatial slices for all $`t<T` sufficiently close to $`T`.
The finite bound may depend on $`t`; no uniform bound in time is imposed.
General divergence statements use `Tendsto (spatialSupNorm u)` directly,
so they also apply to fields with unbounded slices.

This is a pointwise supremum: changing one value of $`u` can change $`S_u`.
Sobolev and $`L^p` trajectories use norm divergence at the finite horizon in their own normed
state space, for example through the scalar-amplitude blow-up criterion.
:::

A supremum dominates each of its terms, so divergence of the field along one
spatial sample, which may move with time, already forces divergence of
$`S_u`.

:::theorem "parabolic.blowup.sample_transfer" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.tendsto_spatial_sup_norm_nhds_top_of_sample, PDE.Solution.Singularity.FiniteTime.SpatialSupNormBlowsUpAt.of_sample") (uses := "parabolic.blowup.generic_solution")

If the norm along a possibly time-dependent spatial sample $`x(t)` tends to
$`+\infty`, then the extended pointwise spatial supremum also tends to
$`+\infty`. This limit transfer holds along any filter of times.
For the left limit at $`T`, the single-point blow-up criterion also takes
eventual finiteness of the slices and concludes finite-time blow-up.
:::

:::proof "parabolic.blowup.sample_transfer"
For every time $`t`, the sampled quantity
$`\operatorname{ofReal}\lVert u(x(t),t)\rVert` is one term in the supremum
defining $`S_u(t)`. The sampled norm tends to $`+\infty`, hence so does its
`ENNReal.ofReal` image. Monotonicity of convergence to the top element then
transfers the limit to $`S_u`. Together with the supplied finite-slice
condition, this proves divergence of the spatial supremum norm.
:::

For a similarity ansatz the natural sample is the physical point
$`x(t)=x_0+(T-t)^{\beta}y_0`, whose similarity coordinate stays at $`y_0`;
along it the profile value is frozen and only the amplitude
$`(T-t)^{-\alpha}` varies. Every ansatz divergence theorem in the
equation-specific chapters works this way. A positive amplitude exponent
and one nonzero profile value suffice for divergence. A bounded profile
also gives finite spatial slices, so the field satisfies the blow-up
predicate.

:::definition "parabolic.blowup.self_similar_profile" (parent := "parabolic.blowup") (lean := "PDE.Representations.Similarity.scaledProfileAnsatz, PDE.Representations.Similarity.backwardSelfSimilarAnsatz, PDE.Representations.Similarity.concentrationAnsatz")

A pointwise profile $`f : X \to E`, amplitude exponent $`\alpha`, spatial
exponent $`\beta`, center $`x_0`, and time $`T` determine

$$`
u(x,t)=(T-t)^{-\alpha}
f\!\left((T-t)^{-\beta}(x-x_0)\right).
`

The pointwise construction is polymorphic in the spatial and value types:
scalar, vector-valued, complex-valued, and system profiles can share it when
the required real scaling operations exist. This is a pointwise profile
construction; it assumes no differentiability until an equation-specific
theorem requires it.

An $`L^p` or Sobolev profile is instead an almost-everywhere equivalence
class. Its similarity theory needs dilation pullbacks on that quotient and a
weak form of the reduced equation, instead of pointwise composition.
Once the quotient-level pullback is available, the scalar-amplitude blow-up criterion
supplies the abstract amplitude-times-profile step.
:::

# Weighted-moment bridge

:::definition "parabolic.blowup.weighted_moment" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.weightedSpatialMoment")

For a scalar field $`u`, measure $`\mu`, and spatial weight $`w`, define

$$`
\mathcal M_w[u](t)=\int_X w(x)u(x,t)\,d\mu(x).
`

The spatial type and measure are arbitrary. Euclidean geometry enters only
through a model-specific choice of weight. Mathlib's Bochner integral is
totalized, so the weighted spatial moment is defined even for a nonintegrable
integrand, where the integral is set to zero. Every theorem that reads this
expression as a moment therefore assumes integrability.
:::

Against a nonnegative weight, the moment cannot exceed the largest value of
the field times the mass of the weight.

:::theorem "parabolic.blowup.weighted_moment_bound" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.ofReal_abs_weighted_spatial_moment_le_spatial_sup_norm_mul_mass") (uses := "parabolic.blowup.weighted_moment, parabolic.blowup.generic_solution")

If $`w` is almost everywhere nonnegative and integrable, and
$`x\mapsto w(x)u(x,t)` is integrable, then

$$`
\operatorname{ofReal}\left|\mathcal M_w[u](t)\right|
\le
S_u(t)\operatorname{ofReal}\!\left(\int_X w\,d\mu\right).
`

Because $`S_u(t)` takes values in the extended nonnegative reals, this estimate
also covers unbounded slices without an auxiliary boundedness hypothesis. The
weight need not have mass one.
:::

:::proof "parabolic.blowup.weighted_moment_bound"
First bound the absolute value of the Bochner integral by the integral of the
absolute value and rewrite that integral as a nonnegative extended integral.
Almost everywhere, nonnegativity of $`w` and the definition of $`S_u(t)` give
$$`
|w(x)u(x,t)|\leq w(x)S_u(t).
`
Monotonicity of the nonnegative Lebesgue integral permits this pointwise bound, after which the
constant $`S_u(t)` is pulled outside. Integrability and nonnegativity of $`w`
identify the remaining extended integral with
$`\operatorname{ofReal}\int_X w\,d\mu`.
:::

Dividing the estimate by a positive mass turns it into a lower bound for
$`S_u(t)` in terms of the moment, so once a PDE argument has driven
$`|\mathcal M_w[u](t)|` to infinity the supremum must follow.

:::theorem "parabolic.blowup.weighted_moment_transfer" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.tendsto_spatial_sup_norm_nhds_top_of_abs_weighted_spatial_moment") (uses := "parabolic.blowup.weighted_moment_bound")

If the nonnegative integrable weight has positive mass, the weighted field is
integrable eventually, and $`|\mathcal M_w[u](t)|\to+\infty` as
$`t\uparrow T`, then the extended pointwise spatial supremum tends to
$`+\infty`.

The theorem works along any filter of times and needs no spatial slice
bound. A PDE-specific theorem supplies divergence of the chosen moment;
eventual finiteness of the slices is the additional condition needed to
conclude divergence of the spatial supremum norm.
:::

:::proof "parabolic.blowup.weighted_moment_transfer"
Divide the weighted-moment estimate by the positive finite mass
$`m=\int_Xw\,d\mu`. The resulting quantity
$`\operatorname{ofReal}|\mathcal M_w[u](t)|/m` tends to $`+\infty` and is
eventually bounded above by $`S_u(t)`. The order characterization of
convergence to the top element therefore proves divergence of the extended
spatial supremum.
:::

# Riccati comparison model

:::definition "parabolic.blowup.riccati_solution" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.Riccati.solution, PDE.Solution.Singularity.FiniteTime.Riccati.horizon")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "547"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For $`y'=a y^2` with initial value $`y(t_0)=y_0`, the explicit candidate is

$$`
y(t)=\frac{y_0}{1-a y_0(t-t_0)},
\qquad
T=t_0+\frac{1}{a y_0}.
`

The formula is total as a Lean function, including at its pole. Analytic
statements therefore work on $`t<T` under $`a y_0>0`.

Evans notes the scalar model $`y'=y^2` before beginning the weighted
eigenfunction argument. The theorem carries a coefficient $`a`, an arbitrary
initial time, and the horizon formula.
:::

The formula is only a candidate until its derivative has been computed. The
relevant hypothesis is the sign of the product $`a y_0`, not separate signs of
$`a` and $`y_0`.

:::theorem "parabolic.blowup.riccati_ode" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.Riccati.deriv_solution_of_lt_horizon") (uses := "parabolic.blowup.riccati_solution")

If $`a y_0>0` and $`t<T`, the explicit formula satisfies $`y'=a y^2` at
$`t`.
:::

:::proof "parabolic.blowup.riccati_ode"
The denominator factors as
$`1-a y_0(t-t_0)=a y_0(T-t)`. Positivity of $`a y_0` and the inequality
$`t<T` make both factors nonzero. The quotient rule can therefore be applied
to the explicit formula, and a ring calculation reduces the derivative to
$`a y(t)^2`.
:::

Solving the equation before the horizon is half of the comparison model; the
other half identifies the limit at the horizon. For divergence to
$`+\infty`, rather than $`-\infty`, we assume $`a>0` and $`y_0>0`.

:::theorem "parabolic.blowup.riccati_diverges" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.Riccati.tendsto_solution_nhdsLT_horizon_atTop, PDE.Solution.Singularity.FiniteTime.Riccati.solution_norm_blows_up_at") (uses := "parabolic.blowup.riccati_solution")

If $`a>0` and $`y_0>0`, then $`y(t)` tends to $`+\infty` as $`t` approaches
$`T` from below. The corollary states this as
`NormBlowsUpAt (Riccati.solution a y₀ t₀) (Riccati.horizon a y₀ t₀)`.
:::

:::proof "parabolic.blowup.riccati_diverges"
Rewrite the solution as $`1/(a(T-t))`. As $`t\uparrow T`, the positive
quantity $`T-t` tends to zero from the right, so its reciprocal tends to
$`+\infty`; multiplication by $`1/a>0` preserves that limit. Positivity of
the trajectory identifies order divergence with norm divergence.
:::

:::theorem "parabolic.blowup.riccati_reciprocal_distance" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.Riccati.solution_eq_one_div_mul_horizon_sub") (uses := "parabolic.blowup.riccati_solution")

Whenever $`a y_0\ne0`, the solution has the reciprocal-distance form

$$`y(t)=\frac{1}{a(T-t)}.`

This algebraic identity is total in $`t`; its analytic use is on the
pre-blow-up interval.
:::

:::proof "parabolic.blowup.riccati_reciprocal_distance"
Substitute the definition of $`T` and factor the original denominator as
$`a y_0(T-t)`. Since $`a y_0\ne0`, also $`y_0\ne0`; cancelling this factor
from the numerator and denominator yields $`1/(a(T-t))`. Lean's total
division makes the resulting identity valid even at $`t=T`.
:::

# Quadratic differential-growth comparison

The Riccati solution $`y(t)=1/(a(T-t))` is the *comparison function* for
blow-up arguments. A trajectory satisfying $`y'\geq ay^2` is compared with it
by differentiating $`1/y`, bounding its derivative by $`-a`, and integrating.

This comparison principle is a standard engine behind ODE-based
blow-up results for parabolic equations. The mathematical content varies from
problem to problem: Kaplan uses a first-eigenfunction moment, Fujita uses
scaling, and Levine uses a concavity inequality. The Riccati comparison is
one scalar tool for turning differential growth into a finite-time obstruction. Evans (2010,
pp. 548–549) uses it to conclude the blow-up theorem for superlinear heat
equations.

:::theorem "parabolic.blowup.quadratic_reciprocal_bound" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.QuadraticGrowth.inv_le_initial_inv_sub") (uses := "parabolic.blowup.riccati_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "548-549"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`y(t_0)>0` and $`a\ge0`. If $`y` is continuous on $`[t_0,T]`,
differentiable in its interior, and

$$`a\,y(t)^2\le y'(t),`

then positivity propagates and

$$`
\frac{1}{y(t)}
\le
\frac{1}{y(t_0)}-a(t-t_0).
`

No separate positivity hypothesis is needed away from $`t_0`: monotonicity
supplies it.

Evans obtains the related inequality
$`\eta'\ge -\lambda_1\eta+\eta^2` for a weighted PDE observable and removes
the linear term by an exponential change of variables. The Lean theorem is
the autonomous quadratic comparison step of that argument.
:::

:::proof "parabolic.blowup.quadratic_reciprocal_bound"
The differential inequality first shows that $`y` is nondecreasing, hence it
stays positive after $`t_0`. The reciprocal is therefore differentiable in
the interior, with
$$`
\left(\frac1y\right)'=-\frac{y'}{y^2}\leq-a.
`
Apply the mean-value inequality to $`1/y` on $`[t_0,t]` and rearrange the
result.
:::

The reciprocal bound is stated on a closed interval $`[t_0,T]`, but it
already contains the blow-up: its right-hand side equals $`a(\tau-t)` for
$`\tau=t_0+1/(a y(t_0))`, so $`y(t)\ge 1/(a(\tau-t))` before the horizon.

:::theorem "parabolic.blowup.quadratic_diverges" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.QuadraticGrowth.norm_blows_up_at_riccati_horizon") (uses := "parabolic.blowup.quadratic_reciprocal_bound")

Under $`a>0` and $`y(t_0)>0`, the same differential inequality implies

$$`
y(t)\longrightarrow+\infty
\qquad\text{as}\qquad
t\uparrow \tau=t_0+\frac{1}{a\,y(t_0)}.
`

The hypotheses require continuity only on the half-open interval before the
horizon, so Lean's total value $`y(\tau)` plays no role in the
norm-divergence conclusion.
:::

:::proof "parabolic.blowup.quadratic_diverges"
For each $`t` before the horizon $`\tau`, restrict the hypotheses to the
compact interval $`[t_0,t]` and apply the reciprocal estimate. Its right-hand
side is exactly $`a(\tau-t)`, and positivity permits inversion, giving
$`(a(\tau-t))^{-1}\leq y(t)`. The lower bound tends to $`+\infty` as
$`t\uparrow\tau`, so order comparison proves divergence of $`y` and hence
norm blow-up.
:::

If the hypotheses are instead known on a closed interval $`[t_0,T]`, the
same estimate says something about $`T` rather than about a limit: the
horizon cannot belong to the interval, because there the right-hand side
would be zero while $`1/y>0`. This endpoint form bounds whatever interval the
hypotheses hold on; $`T` need not be a maximal time.

:::theorem "parabolic.blowup.quadratic_horizon" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.QuadraticGrowth.right_endpoint_lt_riccati_horizon") (uses := "parabolic.blowup.quadratic_reciprocal_bound")

If $`a>0` and the stated inequalities hold on $`[t_0,T]`, then its right
endpoint satisfies

$$`T<t_0+\frac{1}{a\,y(t_0)}.`

This is the scalar comparison mechanism in
Kaplan-type eigenfunction and moment arguments; see Kaplan (1963,
DOI 10.1002/cpa.3160160307) and Quittner–Souplet (2019,
DOI 10.1007/978-3-030-18222-9).
:::

:::proof "parabolic.blowup.quadratic_horizon"
If $`T<t_0`, the claim is immediate because the Riccati horizon lies strictly
after $`t_0`. Otherwise suppose the horizon $`\tau` belonged to
$`[t_0,T]`. Applying the reciprocal estimate at $`\tau` makes its right-hand
side zero, while positivity of $`y(\tau)` makes $`1/y(\tau)>0`, a
contradiction.
:::
