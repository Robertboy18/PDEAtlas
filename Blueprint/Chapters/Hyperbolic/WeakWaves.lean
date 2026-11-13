/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.HamiltonJacobi
import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Integral
import PDE.Hyperbolic.WeakWave.Compactness.GalerkinExistence
import PDE.Hyperbolic.WeakWave.Compactness.WeakLimits
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import PDE.Hyperbolic.WeakWave.Galerkin.IntegratedIdentities

/-!
# Weak wave solutions

Weak formulations and distributional solution concepts for waves.
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

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Weak Waves by Galerkin Approximation" =>

:::group "hyperbolic.weak_wave"
Weak wave equations
:::

Evans §7.2.1–2 (pp. 398–406) defines weak solutions of the second-order
hyperbolic Dirichlet problem, constructs finite-dimensional Galerkin
approximations, proves their energy bounds, and passes to a weak limit. We work
over a Gelfand triple $`V\hookrightarrow H\hookrightarrow V^*`, and the
existence theorem takes as hypothesis a bounded projected Galerkin family whose
stable trial projections converge strongly to the identity on $`V`.

# Example: The Concrete Gelfand Triple for Weak Waves

For the wave equation on a bounded domain $`\Omega\subset\mathbb R^n`, the
standard Gelfand triple is

$$`
V=H^1_0(\Omega)\hookrightarrow H=L^2(\Omega)
\hookrightarrow V^*=H^{-1}(\Omega).
`

Each space carries one part of the wave:

- $`V=H^1_0(\Omega)` is the *energy space*. Poincaré's inequality makes
  $`\|\nabla u\|_{L^2}` an equivalent norm on this space; it measures the
  potential energy stored in spatial gradients. The zero boundary condition is
  encoded by the subscript 0. A wave displacement $`u(t)\in V` has finite
  potential energy.

- $`H=L^2(\Omega)` is the *pivot space*. It measures kinetic energy:
  $`\|u_t(t)\|_H^2=\int_\Omega|u_t|^2\,dx`. The total wave energy is
  $`E(t)=\frac12\|u_t(t)\|_{L^2}^2+\frac12\|\nabla u(t)\|_{L^2}^2`
  for the unit-speed Dirichlet wave equation.

- $`V^*=H^{-1}(\Omega)` is the *dual space*. The acceleration $`u_{tt}`
  lives here: it is a distribution of regularity one spatial derivative below
  $`L^2`. This is natural because the wave equation $`u_{tt}=-Au+f` has
  $`Au=-\Delta u:H^1_0\to H^{-1}` as a bounded operator.

The embeddings are dense and continuous, and the pivot space $`H` identifies
with its own dual via the Riesz theorem. This identification turns the chain

$$`V\hookrightarrow H\cong H^*\hookrightarrow V^*`

into a Gelfand triple. Lions and Magenes
(1972, Vol. I, Ch. 1) introduced this framework; Evans (2010, pp. 398–400)
adapts it to second-order hyperbolic equations.

With $`B(u,v)=\int_\Omega\nabla u\cdot\nabla v`, the abstract identity
$`u_{tt}+Bu=\ell` is exactly the weak Dirichlet wave equation
$`\langle u_{tt},v\rangle+\int_\Omega\nabla u\cdot\nabla v=\langle\ell,v\rangle`.

# The Galerkin Construction for Weak Waves

The construction follows the parabolic case with one difference:
the wave equation is *second order in time*, so both displacement and
velocity must be approximated simultaneously, and the energy identity
involves kinetic and potential terms rather than a single dissipative form.

At dimension $`m`, one solves the system of $`2m` ODEs

$$`(u_m''(t),w_k)_H+B(u_m(t),w_k)=\langle\ell(t),w_k\rangle,
\quad k=1,\ldots,m,`

with projected initial displacement and velocity. For an autonomous symmetric
stiffness form $`B`, testing with $`u_m'(t)` gives, almost everywhere,

$$`\frac{d}{dt}\left[\frac12\|u_m'(t)\|_H^2+\frac12B(u_m(t),u_m(t))\right]
=\langle\ell(t),u_m'(t)\rangle.`

For pivot-valued forcing in $`L^2(H)`, Grönwall's inequality, coercivity of
$`B`, and uniform projection stability give the bounds
$`\|u_m\|_{L^\infty(V)}+\|u_m'\|_{L^\infty(H)}+\|u_m''\|_{L^2(V^*)}\leq C`
independently of $`m`. Weak compactness in reflexive Bochner spaces extracts
a common limit.

:::definition "hyperbolic.weak_wave.solution" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "398-401"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix a finite interval $`a<b` and forcing $`\ell\in L^2(a,b;V^*)`.
A weak wave consists of displacement in $`L^2(V)`, velocity in $`L^2(H)`,
and acceleration in $`L^2(V^*)`. Integrated time-derivative identities carry
the initial traces, and the spatial equation
$`u_{tt}+B(t)u=\ell` holds almost everywhere in $`V^*`.
:::

The solution concept is stated for the limit object; the construction begins
one level down, with a finite-dimensional trial space $`S_m` in which the
abstract equation becomes a linear system of ordinary differential equations
for the coefficients.

:::theorem "hyperbolic.weak_wave.finite_dimensional_existence" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.GelfandGalerkin.exists")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "401-402"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On each finite-dimensional trial space, a bounded strongly measurable
stiffness operator and an integrable dual forcing produce a global
Carathéodory solution of the second-order Galerkin coefficient system on the
chosen finite interval.
:::

:::proof "hyperbolic.weak_wave.finite_dimensional_existence"
The second-order equation is rewritten as a first-order affine system for
displacement and velocity. Finite-dimensional Carathéodory existence applies,
and projection to the two state components recovers the two almost-everywhere
equations and initial values.
:::

A coefficient trajectory lives in $`S_m`; to compare it with the eventual
limit it must be read as an element of the three Bochner spaces in which weak
waves live.

:::definition "hyperbolic.weak_wave.galerkin_realization" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.SecondOrderSolutionOn.displacementLp, Hyperbolic.Variational.SecondOrderSolutionOn.velocityLp, Hyperbolic.Variational.SecondOrderSolutionOn.accelerationLp") (uses := "hyperbolic.weak_wave.finite_dimensional_existence")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "401-405"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the acceleration realization, assume additionally that the ODE forcing is
represented in $`L^2(a,b;V^*)` and that $`B` is strongly measurable almost
everywhere and essentially bounded. Under these hypotheses, a finite-dimensional
Galerkin trajectory is realized canonically as a displacement in $`L^2(a,b;V)`,
a velocity in $`L^2(a,b;H)`, and an acceleration in $`L^2(a,b;V^*)`.
The acceleration is the residual projected through a stable trial projection,
since the finite system tests only against its own trial space. This
projected residual agrees almost everywhere with the coefficient
acceleration embedded in $`V^*`.
:::

Once realized in Bochner spaces, the Galerkin trajectory satisfies the same
two integrated time identities that define a weak wave. The integrated form
matters: a boundary value of an $`L^2` class has no meaning, whereas pairing
against a time test $`\tau` with $`\tau(b)=0` records the initial value
unambiguously.

:::theorem "hyperbolic.weak_wave.galerkin_time_identities" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.SecondOrderSolutionOn.displacementIdentity, Hyperbolic.Variational.SecondOrderSolutionOn.velocityIdentity") (uses := "hyperbolic.weak_wave.galerkin_realization")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "402-405"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Write $`J:V\to H` for the inclusion, and let $`q_m,p_m\in S_m` be the
finite-level initial displacement and velocity. The Galerkin displacement
$`u_m`, pivot velocity $`v_m`, and dual acceleration $`a_m` satisfy, for
every $`w\in V` and time test $`\tau` with $`\tau(b)=0`,

$$`
-\int_a^b (Ju_m,Jw)_H\tau'
=\int_a^b(v_m,Jw)_H\tau+(Jq_m,Jw)_H\tau(a),
`

$$`
-\int_a^b(v_m,Jw)_H\tau'
=\int_a^b\langle a_m,w\rangle\tau+(Jp_m,Jw)_H\tau(a).
`
:::

:::proof "hyperbolic.weak_wave.galerkin_time_identities"
Pair the coefficient equations with an ambient test and integrate by parts
against $`\tau`. The final-time term vanishes because $`\tau(b)=0`; the
initial terms are the pairings with $`Jq_m` and $`Jp_m`. Almost-everywhere
agreement of the canonical Bochner realizations gives the displayed identities.
:::

The time identities hold against every $`w\in V`, but the spatial equation
does not: at finite level it is known only after projecting the test onto
$`S_m`. What does survive uniformly is a bound, because the stable projection
has norm at most $`K` independently of $`m`.

:::theorem "hyperbolic.weak_wave.galerkin_acceleration_bound" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.SecondOrderSolutionOn.norm_projectedDual_le, Hyperbolic.Variational.SecondOrderSolutionOn.norm_accelerationLp_le_stable, Hyperbolic.Variational.SecondOrderSolutionOn.projectedEquationLpAE") (uses := "hyperbolic.weak_wave.galerkin_realization")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "403-405"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Uniform energy stability of the trial projection yields a
dimension-independent $`L^2(V^*)` acceleration bound. The corresponding
almost-everywhere spatial equation evaluates the stiffness and forcing on
the projected ambient test.
:::

:::proof "hyperbolic.weak_wave.galerkin_acceleration_bound"
The projected dual residual is the forcing minus the stiffness applied to the
Galerkin displacement. Boundedness of the stiffness, stability of the trial
projection, and the displacement and forcing norms control this
residual in $`L^2(V^*)`, with constants independent of dimension. Evaluating the
projection against a test gives the projected spatial equation.
:::

Passing to the limit is a closedness question in the weak topology. The
integrated identities and the equation are linear, so they survive weak
convergence once the operator field is essentially bounded.

:::theorem "hyperbolic.weak_wave.weak_limit_closed" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.of_weak_limits") (uses := "hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "405-406"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
With fixed forcing and common exact initial data, the weak-wave predicate is
closed under a common weak limit in
$`L^2(V)\times L^2(H)\times L^2(V^*)`, assuming the operator field is
measurable and essentially bounded.
:::

:::proof "hyperbolic.weak_wave.weak_limit_closed"
Bounded linear maps pass the displacement identity and the time-test velocity
identity to the limit. Bounded operator-valued multiplication passes
$`B(t)u_m` weakly, and uniqueness of weak limits identifies the limiting
acceleration equation.
:::

Galerkin approximations are not exact weak waves, since their spatial equation
is only projected, so closedness alone does not apply to them. The missing
ingredient is strong convergence of the projections to the identity on $`V`:
pairing weakly convergent residuals with strongly convergent tests
$`P_mw\to w` recovers the ambient equation in the limit.

:::theorem "hyperbolic.weak_wave.projected_limit" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.equationAE_of_projected_galerkin_weak_limits") (uses := "hyperbolic.weak_wave.galerkin_acceleration_bound")
The projected spatial equations pass to the full ambient equation when the
displacements and accelerations have common weak limits, the displacement
family is uniformly bounded, and the stable trial projections converge
strongly to the identity on $`V`. The coefficient field is measurable and
essentially bounded.

$$`a(t)+B(t)u(t)=\ell(t)\quad\text{for almost every }t.`
:::

:::proof "hyperbolic.weak_wave.projected_limit"
The residuals $`\ell-Bu_m` converge weakly in $`L^2(V^*)`. Uniform projection
stability lifts $`P_mw\to w` to strong convergence on $`L^2(V)` tests.
Pairing the bounded weak residuals with those strongly convergent tests
identifies the acceleration limit with $`\ell-Bu`.
:::

Combining the uniform bounds with the two limit theorems yields existence.

:::theorem "hyperbolic.weak_wave.compactness_existence" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.exists_of_bounded_projected_galerkin_family_with_improvedRegularity") (uses := "hyperbolic.weak_wave.solution, hyperbolic.weak_wave.galerkin_time_identities, hyperbolic.weak_wave.projected_limit")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "405-406"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume a bounded projected Galerkin family with stable trial projections
converging to the identity. Every approximation must have the same exact
initial displacement $`q_0` and velocity $`p_0` in its integrated boundary
identities. Then it has a weak-wave limit with these data. Uniform
almost-everywhere energy bounds pass to the limit as
$`L^\infty(V)` and $`L^\infty(H)` bounds for displacement and velocity.
:::

:::proof "hyperbolic.weak_wave.compactness_existence" (uses := "hyperbolic.weak_wave.projected_limit")
We follow Evans (2010, pp. 405–406) in the abstract Gelfand-triple setting.

*Uniform bounds.* The assumed energy bounds give
$`\|u_m\|_{L^\infty(V)}+\|u_m'\|_{L^\infty(H)}\leq C`, and the accelerations are
assumed bounded, $`\|u_m''\|_{L^2(V^*)}\leq C`, both independent
of the trial dimension $`m`.

*Weak compactness.* The spaces $`L^2(a,b;V)`, $`L^2(a,b;H)`, and
$`L^2(a,b;V^*)` are reflexive Banach spaces. The uniform bounds place the
Galerkin family in a bounded ball of their product. Reflexive weak compactness,
applied simultaneously to the three coordinates, gives weak limits
$`u\in L^2(V)`, $`v\in L^2(H)`, $`a\in L^2(V^*)`.

*Passing the equation to the limit.* Bounded linear time-test functionals
pass both integrated identities to the limit, retaining their fixed initial
boundary terms. The projected spatial limit theorem
{uses "hyperbolic.weak_wave.projected_limit"}[] supplies the ambient equation
by weak–strong testing. Together these give the weak-wave predicate.

*Essential supremum bounds.* The set of $`L^2(V)` functions satisfying
$`\|u(t)\|_V\leq C` almost everywhere is norm-closed and convex, hence
weakly closed in $`L^2(V)`. The displacement limit belongs to that same set.
The identical argument in $`L^2(H)` preserves the velocity bound.
:::

In practice the Galerkin data are projections $`q_m=P_mq_0` and $`p_m=P_mp_0`
of the exact data, so they vary with $`m`. Strong convergence of the projected
data is enough to pass the initial boundary terms of the integrated identities
to the limit.

:::theorem "hyperbolic.weak_wave.projected_initial_data" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.of_projected_galerkin_weak_limits_of_initial_tendsto") (uses := "hyperbolic.weak_wave.solution, hyperbolic.weak_wave.galerkin_time_identities, hyperbolic.weak_wave.projected_limit")
Suppose the projected Galerkin families have common weak limits, a uniform
displacement bound, and stable trial projections converging to the identity.
Their initial data may vary with the approximation index, provided
$`q_m\to q_0` strongly in $`V` and $`p_m\to p_0` strongly in $`H`. Then the
limits form a weak wave with initial data $`q_0,p_0`.

The common weak limits are hypotheses; weak compactness extracts them from
bounded families.
:::

:::proof "hyperbolic.weak_wave.projected_initial_data" (uses := "hyperbolic.weak_wave.projected_limit")
Pass the time integrals through weak convergence. Strong convergence of
$`q_m` and $`p_m` gives convergence of both initial boundary pairings against
each fixed test. The projected spatial limit theorem
{uses "hyperbolic.weak_wave.projected_limit"}[] supplies the remaining ambient
equation under the same measurable, essentially bounded coefficient hypothesis.
:::

The displacement of a weak wave is only an $`L^2(V)` class, so $`u(t)` has no
meaning at an individual time. The integrated displacement identity
nevertheless says that $`u` has a weak time derivative in $`V^*`, namely the
embedded velocity, which is enough regularity to select a continuous
pivot-valued representative. The energy-uniqueness argument evaluates that
representative at a terminal time $`\sigma`.

:::theorem "hyperbolic.weak_wave.continuous_representative" (parent := "hyperbolic.weak_wave") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.exists_displacementContinuousRepresentative") (uses := "hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "400-401"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every weak-wave displacement has a strongly continuous representative in the
pivot space on the closed time interval, agreeing almost everywhere with the
embedded $`L^2(V)` representative and taking the prescribed initial value.
:::

:::proof "hyperbolic.weak_wave.continuous_representative"
Apply the finite-interval continuous-representative theorem to the integrated
displacement equation, with the pivot velocity embedded into $`V^*` as its
weak time derivative. This gives a continuous pivot-space representative
agreeing almost everywhere with $`Ju`. The initial boundary term identifies
its value at the lower endpoint with $`Jq_0`.
:::
