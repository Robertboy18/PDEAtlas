/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ClassicalWave
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalExistence
import PDE.Hyperbolic.NonlinearWave.Cauchy.WeakFormulation
import PDE.Hyperbolic.NonlinearWave.EnergyIdentity
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Transport
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Vanishing
import PDE.Hyperbolic.NonlinearWave.ConservedEnergyBounds
import PDE.Hyperbolic.NonlinearWave.DomainOfDependence
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardConservation
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.OneDimension.Conservation
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.QuadraticLowerBound
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.TwoDimensions.Conservation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Lifespan
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.OddPower
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.OddPower.Lifespan
import PDE.Hyperbolic.NonlinearWave.RealLine.Cauchy
import PDE.Hyperbolic.NonlinearWave.Stability

/-!
# Nonlinear wave equations

Nonlinear wave constructions, classical regularity, energy, propagation, and uniqueness.
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
#doc (Manual) "Nonlinear Wave Equations" =>

:::group "hyperbolic.nonlinear_wave"
Semilinear wave equations
:::

# Constructing energy solutions

We start with the Dirichlet problem in the energy space. Let
$`\Omega\subset\mathbb R^n` be nonempty, bounded and open, with $`n>0`,
and let $`a(x)` be an autonomous bounded measurable symmetric uniformly
elliptic matrix. No regularity of the boundary is required. For initial data
in $`H^1_0(\Omega)\times L^2(\Omega)` and a locally Lipschitz map
$`N:H^1_0(\Omega)\times L^2(\Omega)\to L^2(\Omega)`,
the Dirichlet wave semigroup and its Duhamel integral construct a maximal
continuous trajectory $`(q,p)`. On each compact initial interval
before the lifetime, the trajectory supplies Bochner classes satisfying
$`q_t=p` and $`q_{tt}-\operatorname{div}(a\nabla q)=N(q,p)` weakly,
with both prescribed initial values. A scalar term $`+f(q)` on the left
therefore corresponds to $`N(q,p)=-f(q)`. For a general scalar source, the
mapping estimates for $`N` are hypotheses. For $`f(s)=|s|^{r-1}s`, they
are proved when $`1\le r\le n/(n-2)` in dimensions $`n\ge3`, and for every
finite real $`r\ge1` in dimensions one and two.

A separate theorem proves uniqueness among weak solutions represented by
continuous curves in this energy space. If $`N` is Lipschitz on every bounded energy ball, a
finite maximal lifetime forces the state norm to exceed every bound near
that endpoint. Local Lipschitz continuity alone does not give the uniform
constants on balls needed for this conclusion in infinite dimensions.

To see why the uniformity matters, restart the construction.
Write $`U=(q,p)` and let $`S(t)` be the linear wave evolution. On a short
interval after $`t_0`, the mild equation reads

$$`
U(t_0+\tau)=S(\tau)U(t_0)
+\int_0^\tau S(\tau-s)\,(0,N(U(t_0+s)))\,ds.
`

If the state stays in a ball of radius $`R`, a Lipschitz bound on a larger
ball makes this integral map a contraction for one common positive time
$`\delta(R)`, also chosen so the map preserves the ball of candidate
curves. Its value does not shrink as $`t_0` approaches a finite endpoint.
Restart less than $`\delta(R)` before that endpoint and uniqueness glues
the new solution to the old one, extending the trajectory past it.

An a priori bound therefore yields global existence when it controls the
norm used by the local construction. On a bounded Dirichlet domain,
Poincaré supplies the $`L^2` displacement bound from the gradient bound.
For the smooth whole-space construction below, a separate tame composition
estimate turns a uniform displacement bound on a time strip into the higher
Sobolev bound needed for continuation.

The linear homogeneous wave evolution conserves its quadratic energy;
conservation of a nonlinear potential energy is a separate statement. The
energy identities below concern classical solutions under stated regularity,
integrability, and flux hypotheses, and give no critical-power global theory
for the energy-space constructor.

# A global energy solution on whole space

On all of space, a globally Lipschitz scalar reaction gives a global energy
construction for arbitrary data. The condition $`f(0)=0` matters here:
$`|f(s)|\le L|s|` makes composition preserve $`L^2(\mathbb R^n)` even
though the domain has infinite measure.

:::theorem "hyperbolic.semiwave.whole_space_cauchy" (parent := "hyperbolic.nonlinear_wave") (lean := "PDE.Hyperbolic.NonlinearWave.Cauchy.exists_unique_energySolution, PDE.Hyperbolic.NonlinearWave.Cauchy.IsEnergySolution.weakWave_on, PDE.Hyperbolic.NonlinearWave.Cauchy.IsEnergySolution.weak_pde")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 12 (nonlinear wave equations)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
Let $`f:\mathbb R\to\mathbb R` be globally Lipschitz with $`f(0)=0`.
For every dimension and every
$`(u_0,v_0)\in H^1(\mathbb R^n)\times L^2(\mathbb R^n)`, there is a
continuous forward energy trajectory $`(u,v)` attaining both data strongly
and satisfying

$$`
u(t)-u_0=\int_0^t v(s)\,ds,\qquad
v(t)-v_0=\int_0^t\bigl(\Delta u(s)-f(u(s))\bigr)\,ds
`

for every $`t\ge0`, in $`L^2` and the $`H^1` dual respectively.
It is unique among forward energy-continuous trajectories satisfying these
integrated PDE equations with the same data.

On every interval $`[0,b]` with $`b>0`, the trajectory has the Bochner
weak-wave formulation. Take any spatial $`H^1` test $`w` and time test
$`\tau` with an everywhere-defined derivative on $`[0,b]`,
$`\tau,\tau'\in L^2(0,b)`, and $`\tau(b)=0`. Its scalar weak equation is

$$`
-\int_0^b (v,w)_{L^2}\tau'\,dt
+\int_0^b\bigl((\nabla u,\nabla w)_{L^2}+(f(u),w)_{L^2}\bigr)\tau\,dt
=(v_0,w)_{L^2}\tau(0).
`

The gradient pairings use the actual Sobolev weak derivatives. No smallness,
compact support, or classical regularity of the data is assumed.
:::

:::proof "hyperbolic.semiwave.whole_space_cauchy" (uses := "evolution.semigroup.strongly_continuous, elliptic.lax_milgram")
The coercive form $`\int(uw+\nabla u\cdot\nabla w)` first constructs the
linear wave evolution for $`1-\Delta` through Lax–Milgram and Hille–Yosida.
The Lipschitz source $`u-f(u)` cancels the added mass. Iterated Picard
estimates construct its Duhamel trajectory for all forward times.
Dense-generator observations give the integrated equations for arbitrary
energy data. Conversely, linear weak uniqueness identifies every energy
PDE solution with that mild trajectory, so fixed-point uniqueness applies
to the PDE class itself. Time integration by parts gives the displayed
scalar identity and its initial velocity term.
:::

This construction asserts the PDE for nonnegative time. Its extension to
negative times serves the integrals. The next construction starts from
bounded smooth scalar data on the real line and obtains classical regularity
directly.

# A classical wave from bounded scalar data

Consider $`f(s)=1+\sin s` with displacement $`g(x)=\sin(x^2)` and
velocity $`h(x)=\cos(x^2)`. The reaction is globally Lipschitz and the
initial profiles are bounded and smooth. Their derivatives need no uniform
bound, and $`f(0)=1` is allowed. In one dimension the characteristic
integral constructs a classical solution from these data for every
nonnegative time.

Let $`H` be the free d'Alembert wave with data $`(g,h)`. The same
zero-data Duhamel operator used in the linear chapter takes, for $`t\ge0`,
the form

$$`
(KF)(t,x)=\frac12\int_0^t
  \int_{x-(t-s)}^{x+(t-s)}F(s,y)\,dy\,ds.
`

The nonlinear equation $`u_{tt}-u_{xx}+f(u)=0` asks us to solve
$`u=H-K(f\circ u)`. On a finite strip $`[0,T]\times\mathbb R`,
bounded continuous fields form a complete space in the supremum norm.
Continuity here is joint in time and space. The estimate
$`|f(z)|\le |f(0)|+L|z|` keeps the source bounded, and
$`\|KF\|_\infty\le T^2\|F\|_\infty/2` keeps its Duhamel field bounded.

:::theorem "hyperbolic.semiwave.classical_strip" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.existsUnique_nonlinearStrip_of_boundedContinuousData_anyTime, WaveEquation.dist_iterate_nonlinearStripMap_le, WaveEquation.stripRestriction_nonlinearStripSolution") (uses := "hyperbolic.wave.duhamel_solution")
For bounded continuous $`g,h:\mathbb R\to\mathbb R`, a globally
$`L`-Lipschitz $`f`, and every finite $`T\ge0`, there is a unique
bounded continuous solution $`u_T` of $`u_T=H-K(f\circ u_T)` on
$`[0,T]\times\mathbb R`. If $`0\le S\le T`, restricting $`u_T` to
$`[0,S]\times\mathbb R` gives $`u_S`.
:::

:::proof "hyperbolic.semiwave.classical_strip"
Write $`\Phi_T(w)=H-K(f\circ w)`. Its Lipschitz constant is at most
$`LT^2/2`, which need not be less than one. Repeated time integration
gives the stronger estimate

$$`
\|\Phi_T^m(w)-\Phi_T^m(v)\|_\infty
\le \frac{(LT^2)^m}{m!}\,\|w-v\|_\infty.
`

For each fixed $`T`, the coefficient tends to zero as $`m\to\infty`.
Some iterate therefore contracts, giving a unique fixed point of
$`\Phi_T` on that whole strip. There is no small-time restriction on
$`T`. The value at time $`t` uses source values only between $`0` and
$`t`, so restriction to a shorter strip still solves its integral
equation. Uniqueness identifies the restricted solution.
:::

The integral solution is initially only continuous. To get two derivatives,
we insert it into the Duhamel formula twice. Extend $`u_T` by clipping
only its time argument to $`[0,T]`, and call this continuous extension
$`\widetilde u_T`. Define

$$`
v_1=H-K(f\circ\widetilde u_T),\qquad
v_2=H-K(f\circ v_1).
`

With $`g\in C^2` and $`h\in C^1`, the free field $`H` is $`C^2`.
The one-dimensional Duhamel operator sends continuous forcing to a jointly
$`C^1` field, so $`v_1` is $`C^1`. If $`f\in C^1`, its composition
with $`v_1` is $`C^1`, and the linear Duhamel regularity theorem makes
$`v_2` jointly $`C^2`. Causality identifies both insertions with
$`u_T` on the closed forward strip. This proves regularity of the actual
fixed point from ordinary scalar regularity of the data and reaction.

:::theorem "hyperbolic.semiwave.classical_cauchy" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.exists_global_classical_solution_of_bounded_data") (uses := "hyperbolic.semiwave.classical_strip, hyperbolic.wave.duhamel_solution")
Let $`f:\mathbb R\to\mathbb R` be $`C^1` and globally Lipschitz,
and let $`g\in C^2(\mathbb R)` and $`h\in C^1(\mathbb R)` have
bounded ranges. There is a field $`u\in C^2(\mathbb R^2)` such that

$$`
u_{tt}-u_{xx}+f(u)=0\quad(t\ge0),\qquad
u(0,x)=g(x),\qquad u_t(0,x)=h(x).
`

Both prescribed values are joint spacetime traces:

$$`
\lim_{(s,y)\to(0,x)}u(s,y)=g(x),\qquad
\lim_{(s,y)\to(0,x)}u_t(s,y)=h(x).
`

For every finite $`T\ge0`, the field is bounded on
$`[0,T]\times\mathbb R`; the bound may depend on $`T`.
No integrability, smallness, vanishing condition on $`f(0)`, or bound on
the derivatives of $`g,h` is assumed.
:::

:::proof "hyperbolic.semiwave.classical_cauchy"
The compatible strip solutions define one field for all forward times.
Near any positive time, choose a fixed larger horizon. Compatibility makes
the field agree on that neighborhood with the $`C^2` second insertion
for this horizon. Near time zero, use the signed-time extension from the
unit strip. These local representations prove global $`C^2` regularity;
the nonlinear PDE is asserted for nonnegative time.

The Duhamel field has zero initial displacement and velocity, so subtracting
it from $`H` retains both assigned initial values. Continuity of $`u`
and $`u_t` then gives the two joint traces. On every finite forward
strip the field agrees with the bounded continuous fixed point, giving the
stated horizon-dependent bound.
:::

The uniqueness assertion in this construction concerns bounded continuous
solutions of the integral equation on each finite strip. The raw classical
endpoint above states existence; comparisons between general classical
fields use the energy and cone arguments below. Global forward existence
also allows growth in time: for a constant reaction $`f\equiv c` and
zero initial data, the constructed field is $`u(t,x)=-ct^2/2` for
$`t\ge0`.

# Maximal smooth waves in three dimensions

For smooth compact data in three dimensions, the reaction need only be
smooth and vanish at zero. Its derivatives may grow without bound as its
argument grows. The construction uses a high Sobolev space to obtain the
classical field and then proves that smoothness persists up to its maximal
time. A finite lifespan imposes an amplitude obstruction.

:::theorem "hyperbolic.semiwave.maximal_smooth_wave" (parent := "hyperbolic.nonlinear_wave") (lean := "PDE.Hyperbolic.NonlinearWave.Cauchy.exists_maximal_smooth_wave")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§12.3.2, Theorem 2: maximal construction and terminal unboundedness"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 100, endLine := 104 } }] }
%%%
Let $`f\in C^\infty(\mathbb R)` with $`f(0)=0`, and let
$`g,h\in C_c^\infty(\mathbb R^3)`. There are a lifespan
$`T_*\in(0,\infty]` and a field smooth on
$`[0,T_*)\times\mathbb R^3` satisfying

$$`
u_{tt}-\Delta u+f(u)=0\quad(0<t<T_*),\qquad
u(0,x)=g(x),\qquad \partial_t^+u(0,x)=h(x).
`

Every competing solution with these data that is $`C^2` for $`0<t<T`
and $`C^1` up to $`t=0` has $`T\le T_*`. If $`T_*<\infty`, then

$$`
\forall a<T_*\;\forall B\in\mathbb R\;\exists t\in[\max(0,a),T_*)\;
\exists x\in\mathbb R^3,\qquad |u(t,x)|>B.
`

Thus the displacement is unbounded on every terminal time strip.
:::

:::proof "hyperbolic.semiwave.maximal_smooth_wave" (uses := "evolution.semigroup.strongly_continuous")
Start with the mild evolution in $`H^5(\mathbb R^3)\times H^4(\mathbb R^3)`.
Smooth composition is locally Lipschitz there. Sobolev embedding recovers
a classical field, and persistence at higher orders makes it smooth for
smooth compact data. Classical uniqueness identifies competing solutions
with this trajectory, so its maximal lifetime is also maximal among the
stated classical competitors.

If displacement were bounded on a terminal strip, the tame composition
estimate would bound the source by an affine function of the Sobolev state
norm on that strip. Grönwall would then bound the full state and allow
continuation past $`T_*`, contradicting maximality.
:::

# Energy estimates

Multiplying $`u_{tt}-\Delta u+V'(u)=0` by $`u_t` gives a local balance
between the time derivative of the energy density and the divergence of the
spatial flux. Integrating this identity gives conservation when the density
is integrable and the boundary flux vanishes.

- *Global bounds.* When the potential $`V\geq 0` (defocusing case), the
  conserved energy bounds the kinetic, gradient, and potential contributions
  individually. In particular, it controls $`u_t` and $`D_xu` in $`L^2`.
  Full inhomogeneous $`H^1\times L^2` control also requires an $`L^2`
  bound on $`u`, for example from $`V(z)\geq\mu z^2` with $`\mu>0`.
  These estimates can feed a continuation theorem with a compatible local
  existence theory and continuation criterion.

- *Finite propagation.* For a nonnegative normalized potential, the local
  energy identity and Cauchy–Schwarz on the lateral cone flux give unit-speed
  propagation. Locally Lipschitz reactions also admit a difference-energy
  argument without a sign condition on the potential.

- *Stability and uniqueness.* The augmented difference energy controls the
  separation between two solutions, giving Lipschitz continuous dependence
  on initial data and immediate uniqueness.

- *Blow-up obstruction.* When $`V` can be negative (focusing case with
  $`\beta<0`), the conserved energy can start negative. The Levine–Glassey
  convexity method then gives a finite upper bound for any classical
  lifespan satisfying the stated compact-support and differentiation
  hypotheses. This rules out global classical continuation without
  identifying a norm that diverges at the endpoint.

:::definition "hyperbolic.semiwave.operator" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.semilinearWaveOperator, WaveEquation.semilinearWaveEnergyDensity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "659-660"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The potential $`V` of the nonlinearity $`f` satisfies
$`\operatorname{deriv}V=f`. Thus the semilinear wave operator is

$$`u_{tt}-\Delta u+V'(u).`

The corresponding energy density is
$`\frac12(u_t^2+|D_xu|^2)+V(u)`.
:::

Multiplying the operator by $`u_t` is the whole content of the local identity:
the chain rule gives $`\partial_tV(u)=V'(u)u_t`, so the potential term joins
the classical kinetic and gradient terms in a single divergence-form balance.

:::theorem "hyperbolic.semiwave.local_energy" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.semilinearWaveEnergyBalanceResidual_eq_partialDeriv_sub_sum, WaveEquation.semilinearWaveEnergyBalanceResidual_eq_mul_operator, WaveEquation.semilinearWaveEnergyBalanceResidual_eq_zero") (uses := "hyperbolic.semiwave.operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "660-661"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a $`C^1` potential and a $`C^2` field, the local energy-balance
defect equals

$$`u_t\bigl(u_{tt}-\Delta u+V'(u)\bigr).`

Consequently every classical semilinear wave has zero local energy defect.
:::

:::proof "hyperbolic.semiwave.local_energy"
The classical kinetic-gradient identity gives $`u_t(u_{tt}-\Delta u)`.
The chain rule differentiates the potential energy as $`V'(u)u_t`.
:::

Integrating the density over a whole time slice defines the total energy.
Because the integral is a Bochner integral over
$`\mathbb R^n`, it is a total expression that returns a value even when the
density fails to be integrable, so every statement about it carries its own
integrability hypotheses.

:::definition "hyperbolic.semiwave.global_energy" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.semilinearWaveSpatialEnergyDensity, WaveEquation.semilinearWaveSpatialEnergy") (uses := "hyperbolic.semiwave.operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "659-660"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At time $`t`, the total semilinear-wave energy is

$$`
E(t)=\int_{\mathbb R^n}
\left(\frac12|u_t|^2+\frac12|D_xu|^2+V(u)\right)(x,t)\,dx.
`

The Bochner integral of a nonintegrable density is zero. Each conservation
theorem must therefore assume or derive integrability before interpreting
this expression as physical energy.
:::

Differentiating $`E(t)` under the integral and applying the local identity
leaves only the spatial divergence of the flux, whose integral vanishes when
the flux has compact support on each slice. The theorem takes domination of
the time derivative and compact support of the flux as hypotheses on the
solution.

:::theorem "hyperbolic.semiwave.global_energy_conservation" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.hasDerivAt_semilinearWaveSpatialEnergy_eq_zero, WaveEquation.semilinearWaveSpatialEnergy_conserved") (uses := "hyperbolic.semiwave.local_energy, hyperbolic.semiwave.global_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "659-660"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`V` be $`C^1` and $`u` be a globally $`C^2` solution of
$`u_{tt}-\Delta u+V'(u)=0`. Assume every energy slice is integrable, the time
derivative of the density admits an integrable local dominator near every
time, and each fixed-time spatial flux component $`u_tu_{x_i}` has compact
support. Then

$$`E'(t)=0,\qquad E(t)=E(t_0)`

for all real $`t,t_0`. No sign condition on $`V` is required for
conservation. The domination hypothesis justifies differentiation under the
spatial integral, while compact support makes every integrated flux
derivative vanish.
:::

:::proof "hyperbolic.semiwave.global_energy_conservation" (uses := "hyperbolic.semiwave.local_energy")
We follow Evans (2010, pp. 659–660).

*Differentiation under the integral.* The local domination hypothesis
justifies applying the Leibniz rule to
$`E(t)=\int e(x,t)\,dx` where
$`e=\frac12(u_t^2+|\nabla u|^2)+V(u)`. This gives
$`E'(t)=\int\partial_t e(x,t)\,dx`.

*Local balance to flux divergence.* The local energy identity (proved
above) shows that $`\partial_t e=\nabla\cdot(u_t\nabla u)` whenever the
semilinear wave equation holds. The chain-rule derivative of $`V(u)` is
$`V'(u)u_t`, and this cancels with the corresponding term in
$`u_t(u_{tt}-\Delta u+V'(u))=0`.

*Integration by parts.* The spatial integral of $`\nabla\cdot(u_t\nabla u)`
equals the boundary flux by Gauss's theorem. Compact support of each
$`u_tu_{x_i}` makes this boundary flux vanish. Therefore $`E'(t)=0`.

The conservation identity $`E(t)=E(t_0)` then follows from the
one-dimensional mean-value theorem: a differentiable function with zero
derivative on an interval is constant.
:::

## Conservation from separate compact slices

Suppose only that each displacement $`u(t,\cdot)` has compact support;
its supporting set may depend on $`t`. Differentiating a whole-space
integral still needs control over a time neighborhood. For a $`C^1`
reaction, the wave equation supplies a common support on every finite
forward slab, which closes that step.

The following results concern the closed forward half-space. Write
$`E_+(t)` for the same energy integral using the differential within
$`[0,\infty)\times\mathbb R^n`. At zero this uses the actual right
time derivative, and at positive times it agrees with the ordinary energy.

:::theorem "hyperbolic.semiwave.compact_slice_energy" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.forwardSemilinearWaveEnergy_eq_of_compact_slices") (uses := "hyperbolic.semiwave.global_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§12.1.1, Theorem 1, with a C¹ reaction"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 86, endLine := 91 } }] }
%%%
Let $`n>0`, $`V\in C^2(\mathbb R)`, and $`V(0)=0`.
Suppose $`u` is $`C^2` on the closed forward half-space, satisfies
$`u_{tt}-\Delta u+V'(u)=0` at positive times, and
$`u(t,\cdot)` has compact support for every $`t\ge0`. Then

$$`E_+(t)=E_+(0)\qquad(t\ge0).`

No common spatial support, sign condition on $`V`, or assumption about
negative-time values is required.
:::

:::proof "hyperbolic.semiwave.compact_slice_energy" (uses := "hyperbolic.semiwave.local_energy")
Baire category supplies a time interval with common compact displacement
support. Since $`V'` is locally Lipschitz, finite propagation transports
that support across each finite forward slab. The local energy balance
can then be integrated on one fixed compact spatial region. A smooth
extension across the initial face identifies the initial energy with the
right differential; the answer is independent of the extension.
:::

For a merely continuous reaction, this support-propagation argument is no
longer available in the same form. In low dimensions a direct estimate of
the flux at spatial infinity suffices.

:::theorem "hyperbolic.semiwave.continuous_reaction_energy_low_dimensions" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.forwardSemilinearWaveEnergy_eq_of_compact_slices_one, WaveEquation.forwardEnergy_eq_of_compact_slices_two") (uses := "hyperbolic.semiwave.global_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§12.1.1, Theorem 1, in dimensions one and two"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 93, endLine := 98 } }] }
%%%
Let $`V\in C^1(\mathbb R)` and $`V(0)=0`. Suppose
$`u_{tt}-\Delta u+V'(u)=0` at positive times and
$`u(t,\cdot)` has compact support for each $`t\ge0`.
If $`n=1` and $`u` is $`C^3` on the closed forward half-space, or
$`n=2` and $`u` is $`C^4` there, then

$$`E_+(t)=E_+(0)\qquad(t\ge0).`

There is no sign or growth condition on $`V`.
:::

:::proof "hyperbolic.semiwave.continuous_reaction_energy_low_dimensions" (uses := "hyperbolic.semiwave.local_energy")
In one dimension, characteristic transport bounds the first derivatives
locally uniformly in time. Separate compact slices make the endpoint flux
vanish at each time, and dominated convergence removes the endpoints of a
finite rectangular energy balance. Local constancy then gives conservation
on the connected forward time interval.

In two dimensions, the equation supplies uniform smallness of the potential
at spatial infinity on each finite slab. Integrating the energy and
momentum balances leaves an annular stress term. The annulus area grows
quadratically in its radius, while the cutoff's second derivatives decay
quadratically. Their factors cancel, so the small potential tail makes
the remaining term vanish.
:::

:::theorem "hyperbolic.semiwave.quadratic_lower_energy" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.forwardSemilinearWaveEnergy_eq_of_compact_slices_of_quadratic_lower_bound") (uses := "hyperbolic.semiwave.global_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§12.1.1, Theorem 1, with a quadratic lower bound near zero"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 93, endLine := 98 } }] }
%%%
Let $`n>0`, $`V\in C^1(\mathbb R)`, and $`V(0)=0`. Assume that for
some real $`C`, $`V(z)\ge-Cz^2` throughout a neighborhood of zero.
If $`u` is $`C^2` on the closed forward half-space, solves
$`u_{tt}-\Delta u+V'(u)=0` at positive times, and has compact
displacement support separately at each $`t\ge0`, then

$$`E_+(t)=E_+(0)\qquad(t\ge0).`
:::

:::proof "hyperbolic.semiwave.quadratic_lower_energy" (uses := "hyperbolic.semiwave.local_energy")
Adding a suitable multiple of $`u^2` to the cone energy makes it
nonnegative on the attained value range. The potential's local lower bound
controls this modification near zero; continuity controls it away from zero.
Grönwall then propagates zero Cauchy data across backward cones, in both time
directions. Baire category gives a time near which all slices vanish outside
one ball, so the Cauchy data there have common compact support, and finite
propagation carries it across each finite slab. The resulting common support
allows the ordinary energy balance to be integrated.
:::

For a merely continuous reaction in dimension $`n\ge3`, conservation is
proved only under the quadratic lower bound, which is an additional
hypothesis and not a consequence of continuity. The two-dimensional annular
argument leaves a factor $`R^{n-2}` in higher dimensions, and uniform
smallness of the potential tail gives no decay rate that cancels it.

Conservation alone says nothing about the size of the individual terms, since
$`V(u)` may be negative. Under $`V\geq0` each of the three contributions is
nonnegative and hence bounded by their sum, which conservation pins to the
initial energy. These are a priori bounds on a given solution.

:::theorem "hyperbolic.semiwave.global_energy_bounds" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.semilinearWaveSpatialEnergy_nonneg, WaveEquation.integral_semilinearWaveKineticEnergy_le_spatialEnergy, WaveEquation.integral_semilinearWaveGradientEnergy_le_spatialEnergy, WaveEquation.integral_semilinearWavePotentialEnergy_le_spatialEnergy, WaveEquation.integral_semilinearWaveKineticEnergy_le_referenceEnergy, WaveEquation.integral_semilinearWaveGradientEnergy_le_referenceEnergy, WaveEquation.integral_semilinearWavePotentialEnergy_le_referenceEnergy") (uses := "hyperbolic.semiwave.global_energy_conservation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "659-660"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If in addition $`V\ge0`, then the total energy and each of its normalized
kinetic, spatial-gradient, and potential contributions are nonnegative, and
each contribution is bounded by $`E(t)`. Under the conservation hypotheses,
the same quantities at any later time are bounded by the initial energy
$`E(t_0)`.
:::

:::proof "hyperbolic.semiwave.global_energy_bounds" (uses := "hyperbolic.semiwave.global_energy_conservation")
Nonnegativity of $`V` makes every term of the energy density nonnegative.
Each individual integral is therefore bounded by their sum. Conservation
replaces that sum at time $`t` by $`E(t_0)`, giving the reference-time
bounds.
:::

Localizing the same computation to a ball that shrinks at unit speed gives the
semilinear analogue of the moving-ball energy identity of the linear chapter.
The potential contributes twice: inside the density being differentiated, and
through the boundary swept out by the shrinking sphere.

:::theorem "hyperbolic.semiwave.transport" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.sphereIntegral_semilinearWaveConeBoundaryFlux_eq_sub, WaveEquation.hasDerivAt_semilinearBackwardConeEnergy, WaveEquation.hasDerivAt_semilinearBackwardConeEnergy_of_solution") (uses := "hyperbolic.semiwave.local_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "661"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`n>0`, a $`C^1` potential, a globally $`C^2` field, and $`t<T`, the
derivative of the total energy on the shrinking ball
$`B(c,T-t)` is the sum of its local volume defect and lateral cone flux. If
the equation holds throughout that ball, the volume defect vanishes and only
the lateral flux

$$`u_tD_xu\cdot\nu-
  \left(\frac12(u_t^2+|D_xu|^2)+V(u)\right)`

remains. Its sphere integral equals the classical lateral flux minus the
potential energy swept out by the shrinking boundary. Both identities follow
from the Reynolds transport and Gauss formulas on balls.
:::

:::proof "hyperbolic.semiwave.transport" (uses := "hyperbolic.semiwave.local_energy")
Reynolds transport differentiates the energy on the shrinking ball and
produces the swept-boundary term. Integrating the local balance converts the
spatial divergence into a sphere flux by Gauss's theorem. On a solution the
volume residual vanishes, and separating the potential gives the displayed
lateral flux.
:::

With $`V\geq0` the lateral flux is nonpositive by the same Cauchy–Schwarz step
as in the linear case, and with $`V(0)=0` the zero state has zero potential
energy, so the cone energy of a solution with zero data on the base ball
cannot leave zero. As in the global bounds, the sign condition makes the
energy control its parts; conservation itself did not need it.

:::theorem "hyperbolic.semiwave.finite_propagation" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.eq_zero_on_open_backwardCone_semilinear, WaveEquation.eq_zero_on_closed_backwardCone_semilinear") (uses := "hyperbolic.semiwave.transport")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "661"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive spatial dimension, suppose $`V` is $`C^1`, nonnegative, and
$`V(0)=0`. If a globally $`C^2` classical solution
of $`u_{tt}-\Delta u+V'(u)=0` has zero displacement and velocity on the base
ball, then it vanishes in the corresponding open backward cone. This is
Evans's theorem.
For the closed-cone theorem, require the data to vanish on the closed base
ball. The conclusion then includes the lateral boundary and vertex.
:::

:::proof "hyperbolic.semiwave.finite_propagation"
The proof is the energy argument for finite propagation (Evans, 2010,
p. 661).

*Monotonicity of cone energy.* Define
$`e(t)=\int_{B(c,T-t)}(\frac12 u_t^2+\frac12|\nabla u|^2+V(u))\,dx`
on the shrinking ball $`B(c,T-t)`. By the transport theorem (proved above),
$`e'(t)` equals the lateral cone flux. The flux integrand is
$`u_t\nabla u\cdot\nu-(\frac12 u_t^2+\frac12|\nabla u|^2+V(u))`.
By Cauchy–Schwarz,

$$`
u_t\nabla u\cdot\nu
\leq |u_t||\nabla u|
\leq \frac12 u_t^2+\frac12|\nabla u|^2.
`

Since $`V(u)\geq 0` (with
$`V(0)=0`), the full integrand is nonpositive. Therefore $`e'(t)\leq 0`.

*Zero initial energy.* The zero data on the base ball give $`e(t_0)=0`
(using $`V(0)=0` for the potential term). Combined with monotonicity,
$`e(t)=0` for all $`t\in[t_0,T)`.

*Vanishing of the solution.* Zero kinetic-gradient energy forces
$`u_t=0` and $`\nabla u=0` almost everywhere in each shrinking ball.
The connected-component argument (integrating zero velocity along vertical
segments from the initial surface) gives $`u\equiv 0` in the open cone. With
closed-base data, continuity extends the conclusion to the closed cone
boundary. The formal proof takes a more general route: it adds a multiple of
$`u^2` to the cone energy, which allows any $`V` with $`V(z)\ge -Cz^2` near
zero, and applies Grönwall; for $`V\ge0` the bound holds with $`C=0`.
:::

Stability and uniqueness come from applying the energy method to the
difference $`w=u-v` of two solutions. The difference satisfies a wave equation
with source $`-(f(u)-f(v))`, which the Lipschitz bound controls by $`K|w|`; to
absorb this term the difference energy is augmented by $`\frac12\int w^2`, and
the augmented quantity obeys a Grönwall inequality with rate $`1+K`.

:::theorem "hyperbolic.semiwave.exponential_stability" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.semilinearWaveSpatialEnergy_sub_le_exp_abs") (uses := "hyperbolic.semiwave.local_energy")
If $`f` is globally $`K`-Lipschitz and $`u,v` solve
$`w_{tt}-\Delta w+f(w)=0`, assume both fields are globally $`C^2`, every
augmented difference-energy slice is integrable, and its time derivative
has an integrable dominator valid almost everywhere in space throughout a
common time neighborhood of each time. Assume also that each fixed-time
difference-energy flux component has compact support. Then the augmented
difference energy satisfies

$$`
E_{u-v}(t)\leq E_{u-v}(a)
\exp\bigl((1+K)|t-a|\bigr).
`

Here $`E_{u-v}` includes the auxiliary coercive term $`\frac12|u-v|^2`,
which is unrelated to any primitive of $`f`.
:::

:::proof "hyperbolic.semiwave.exponential_stability"
Subtract the equations. Lipschitz continuity bounds the nonlinear residual
in the difference-energy identity and gives
$`|E'(t)|\leq(1+K)E(t)`. A two-sided Grönwall argument yields the estimate
for arbitrary time order.
:::

The augmented energy is half the sum of the three squared $`L^2` norms.
In particular, $`\|u(t)-v(t)\|_{L^2}^2\le 2E_{u-v}(t)`. Taking square roots
of the exponential estimate gives continuous dependence on the Cauchy data
in the energy norm.

:::theorem "hyperbolic.semiwave.coercive_stability" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.integral_semilinearWaveDifferenceCoerciveSum_le_exp_abs") (uses := "hyperbolic.semiwave.exponential_stability")
The exponential estimate controls the integral of the squared velocity
difference, spatial-gradient difference, and field difference by
$`2E_{u-v}(a)\exp((1+K)|t-a|)`.
:::

:::proof "hyperbolic.semiwave.coercive_stability" (uses := "hyperbolic.semiwave.exponential_stability")
For the quadratic auxiliary potential $`z\mapsto z^2/2`, coercivity bounds the
sum of the three squared difference terms by twice the augmented energy at
time $`t`. Compose this estimate with exponential stability of that energy
between $`a` and $`t`.
:::

Equal Cauchy data at one time make the augmented difference energy vanish
there, and the exponential bound then keeps it zero at every time. Because the
augmented energy controls $`\int w^2` on each slice and $`w` is continuous,
this yields pointwise equality everywhere, under the same integrability and
compact-flux hypotheses as the stability estimate.

:::theorem "hyperbolic.semiwave.uniqueness" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.semilinearWave_eq_of_eq_cauchyData") (uses := "hyperbolic.semiwave.exponential_stability")
Let $`u` and $`v` solve
$`w_{tt}-\Delta w+f(w)=0` for the same globally Lipschitz $`f`. If

$$`
u(t_0,\cdot)=v(t_0,\cdot),\qquad
u_t(t_0,\cdot)=v_t(t_0,\cdot),
`

then $`u(t,x)=v(t,x)` everywhere, under the analytic integrability and flux
hypotheses used by the energy argument.
:::

:::proof "hyperbolic.semiwave.uniqueness"
Equal Cauchy data make the augmented difference energy zero at the reference
time. Exponential stability keeps it zero on every time slice, and coercivity
then forces the pointwise field difference to vanish.
:::

The global statement needs integrability over whole slices. Working instead
with the quadratic cone energy of $`w` on the shrinking ball removes every
integrability hypothesis, since continuous functions are integrable over
bounded balls; the price is that the conclusion is confined to the backward
cone, exactly as for the linear domain of dependence.

:::theorem "hyperbolic.semiwave.cone_uniqueness" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.eq_on_closed_backwardCone_of_eq_cauchyData_semilinear, WaveEquation.eq_on_open_backwardCone_of_eq_cauchyData_semilinear") (uses := "hyperbolic.wave.operator")
Let $`n\ge1`, let $`f` be globally $`K`-Lipschitz, and let
$`u,v\in C^2(\mathbb R^{n+1})`. Fix a center $`c\in\mathbb R^n` and times
$`a,T`, and suppose both fields satisfy

$$`
w_{tt}-\Delta w+f(w)=0\quad\text{for } a\le t<T,\ |x-c|<T-t,
`

that is, inside the open backward cone with vertex $`(T,c)`. If
$`u(a,\cdot)=v(a,\cdot)` and $`u_t(a,\cdot)=v_t(a,\cdot)` on the closed base
ball $`\overline B(c,T-a)`, then

$$`
u(t,x)=v(t,x)\quad\text{whenever } a\le t\le T,\ |x-c|\le T-t .
`

With data agreeing only on the open base ball $`B(c,T-a)`, the conclusion
holds on the open cone $`a\le t<T`, $`|x-c|<T-t`. No sign condition on
$`f` is needed, and the only regularity hypothesis is that both fields are
globally $`C^2`; this localizes the global uniqueness theorem above.
:::

:::proof "hyperbolic.semiwave.cone_uniqueness" (uses := "hyperbolic.semiwave.transport, hyperbolic.wave.finite_propagation")
Let $`w=u-v` and consider the quadratic cone energy

$$`
E(t)=\frac12\int_{B(c,T-t)}\bigl(w_t^2+|D_xw|^2+w^2\bigr)\,dx,
`

the semilinear cone energy of $`w` for the potential $`z^2/2`. By the
shrinking-ball transport theorem its derivative is the lateral cone flux plus
the volume term $`\int w_t\,(w_{tt}-\Delta w+w)\,dx`. Cauchy–Schwarz makes
the lateral flux nonpositive, and subtracting the two equations gives
$`w_{tt}-\Delta w=-(f(u)-f(v))`, so the Lipschitz bound controls the volume
term by $`(1+K)E(t)`. Grönwall's inequality yields
$`E(t)\le E(a)e^{(1+K)(t-a)}`, and equal Cauchy data give $`E(a)=0`. Hence
the classical cone energy of $`w` vanishes on $`[a,T)`, which forces $`w=0`
throughout the closed cone by the vanishing argument of the linear theory.
The open-cone version applies the closed-cone statement to a slightly smaller
cone through each interior point.
:::

# Negative-energy obstruction

:::theorem "hyperbolic.semiwave.negative_energy_riccati_horizon" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.right_endpoint_le_riccati_horizon_of_negative_conserved_energy, WaveEquation.right_endpoint_lt_riccati_horizon_of_negative_conserved_energy") (uses := "hyperbolic.semiwave.operator, hyperbolic.semiwave.global_energy")
Let $`V\in C^1(\mathbb R)` with $`V(0)=0` satisfy the growth condition

$$`
z\,V'(z)\le\Lambda\,V(z)\quad\text{for all }z,\qquad \Lambda>2,
`

and let $`I(t)=\frac12\int_{\mathbb R^n}u^2\,dx` and
$`P(t)=\int_{\mathbb R^n}u\,u_t\,dx` be the spatial quadratic mass and
momentum. Suppose that on the half-open slab $`[t_0,T)`, $`t_0<T`, the field
$`u` is $`C^2` on a time neighborhood of every slice, solves
$`u_{tt}-\Delta u+V'(u)=0`, has compactly supported slices, admits the
integrable local dominators needed to differentiate $`I` and $`P` under the
integral, and has conserved energy $`E(t)=E(t_0)`. If

$$`
E(t_0)<0\qquad\text{and}\qquad P(t_0)>0,
`

then

$$`
T\le t_0+\left(\frac{\Lambda-2}{4}\,\frac{P(t_0)}{I(t_0)}\right)^{-1}.
`

If the same hypotheses hold on the closed slab $`[t_0,T]` with $`t_0\le T`,
the inequality is strict. Energy conservation enters as a hypothesis; the
odd-power specialization below derives it from the conservation theorem.
:::

:::proof "hyperbolic.semiwave.negative_energy_riccati_horizon"
Differentiating under the integral gives $`I'=P` and
$`P'=\int u_t^2+u\,u_{tt}\,dx`. Using the equation, integrating by parts on
the compactly supported slice, and applying the growth condition,

$$`
P'\ \ge\ \int u_t^2\,dx-\int|D_xu|^2\,dx-\Lambda\int V(u)\,dx
\ =\ \Bigl(1+\frac\Lambda2\Bigr)\int u_t^2\,dx
+\Bigl(\frac\Lambda2-1\Bigr)\int|D_xu|^2\,dx-\Lambda E(t_0),
`

so $`P'\ge(1+\Lambda/2)\int u_t^2\,dx` because $`E(t_0)<0` and
$`\Lambda>2`. Negative conserved energy with $`V(0)=0` also forces $`I>0`
on the slab. Cauchy–Schwarz, $`P^2\le2I\int u_t^2\,dx`, then gives the
concavity inequality $`I\,P'\ge\frac{\Lambda+2}{4}P^2`, that is,
$`(P/I)'\ge\frac{\Lambda-2}{4}(P/I)^2`. The scalar Riccati comparison
shows that the positive ratio $`P/I` cannot remain finite beyond the
displayed horizon, so a solution on a closed slab ends strictly before it,
and a half-open lifespan ends no later than it.
:::

For the odd-power potential $`V(z)=\frac{m^2}2z^2+\frac\beta{2k+2}z^{2k+2}`
the growth condition holds with $`\Lambda=2k+2`, because
$`zV'(z)-(2k+2)V(z)=-km^2z^2\le0` whenever $`m^2\geq0`, and the requirement
$`\Lambda>2` becomes $`k>0`. Negative energy is the other hypothesis of the
horizon bound, and the lemma below shows that with $`m^2\geq0` it can only
occur for $`\beta<0`, so the obstruction is a focusing phenomenon.

:::theorem "hyperbolic.semiwave.negative_energy_is_focusing" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.coupling_neg_of_oddPower_spatialEnergy_neg")
For the odd-power potential
$`V(z)=\frac{m^2}{2}z^2+\frac{\beta}{2k+2}z^{2k+2}`, if $`m^2\geq0` and

$$`
E(t)=\int_{\mathbb R^n}
\left(\frac12|u_t|^2+\frac12|\nabla u|^2+V(u)\right)\,dx<0,
`

then $`\beta<0`.
:::

:::proof "hyperbolic.semiwave.negative_energy_is_focusing"
Argue by contradiction. If both the mass coefficient and the nonlinear
coupling were nonnegative, every term in the odd-power potential would be
nonnegative. The spatial energy would then be nonnegative, contradicting the
assumed negative energy.
:::

Specializing the abstract horizon to $`\Lambda=2k+2` turns the constant
$`\frac{\Lambda-2}4` into $`\frac k2`. The specialization also discharges the
conserved-energy hypothesis: for compactly supported classical slices with the
stated domination, the conservation theorem earlier in this chapter supplies
$`E(t)=E(t_0)` on the slab, so only negative initial energy and positive
initial momentum remain as assumptions about the data.

:::theorem "hyperbolic.semiwave.negative_energy_lifespan" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.right_endpoint_le_riccati_horizon_of_oddPower_negative_energy") (uses := "hyperbolic.semiwave.negative_energy_is_focusing")
Let $`I(t)` be the spatial quadratic mass and $`P(t)=I'(t)` its quadratic
momentum. For a nonnegative mass coefficient $`m^2`, $`k>0`, and
$`t_0<T`, negative initial energy and $`P(t_0)>0` force the half-open
classical lifespan $`[t_0,T)` to satisfy

$$`
T\leq t_0+
\left(\frac{k}{2}\frac{P(t_0)}{I(t_0)}\right)^{-1}.
`

The hypotheses include the compact support and dominated
differentiation needed for the mass, momentum, and energy identities.
:::

:::proof "hyperbolic.semiwave.negative_energy_lifespan" (uses := "hyperbolic.semiwave.negative_energy_riccati_horizon")
Keep $`I(t)=\frac12\int u^2\,dx` and $`P(t)=I'(t)=\int uu_t\,dx`.
The preceding virial estimate with $`\Lambda=2k+2` gives
$`I''(t)\ge (k+2)\int|u_t|^2\,dx+k\int|\nabla u|^2\,dx+2(k+1)|E_0|`,
where $`E_0=E(t_0)=E(t)<0`. Energy conservation follows from the stated
integrability, domination and flux hypotheses.

The virial and Cauchy–Schwarz estimates imply that the positive ratio
$`y=P/I` satisfies $`y'\geq (k/2)y^2`. Hence
$`(1/y)'\leq-k/2`. Integrating from $`t_0` and using $`y(t_0)>0` forces

$$`
t-t_0 < \frac{2}{k\,y(t_0)}
       = \frac{2I(t_0)}{kP(t_0)}.
`

The half-open endpoint theorem converts this strict interior inequality into
the displayed non-strict upper bound for $`T`.
:::

A finite upper bound on $`T` for every slab $`[t_0,T)` on which the hypotheses
hold is incompatible with a solution defined for all $`t\geq t_0`. The
positivity hypothesis on $`P(t_0)` drops out of this conclusion, because the
virial forcing makes the momentum eventually positive going forward and
eventually negative going backward, and the argument can be restarted from
such a time.

:::theorem "hyperbolic.semiwave.negative_energy_global_obstruction" (parent := "hyperbolic.nonlinear_wave") (lean := "WaveEquation.not_global_forward_oddPower_of_negative_energy, WaveEquation.not_global_backward_oddPower_of_negative_energy") (uses := "hyperbolic.semiwave.negative_energy_lifespan")
For a globally $`C^2` spacetime field, under the same equation, compact-support,
integrability and differentiation hypotheses on the relevant time half-line,
negative energy implies both

$$`
\neg\bigl(\text{a solution exists for every }t\geq t_0\bigr),
\qquad
\neg\bigl(\text{a solution exists for every }t\leq t_0\bigr).
`

Both theorems derive $`E(t)=E(t_0)<0` from these hypotheses before applying
the concavity obstruction in the forward and backward time directions.
:::

:::proof "hyperbolic.semiwave.negative_energy_global_obstruction" (uses := "hyperbolic.semiwave.negative_energy_lifespan")
Energy conservation keeps the negative sign in either time direction. The
positive virial forcing makes the quadratic momentum strictly positive after
a forward shift and strictly negative after a backward shift when its value
at $`t_0` does not already have the required sign. The corresponding
Riccati estimate then supplies a finite endpoint, contradicting global
continuation in that direction.
:::
