/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.IntegratedSolutions
import PDE.Analysis.Evolution.Compactness.Lp.Basic
import PDE.Analysis.Evolution.Compactness.Lp.Ultrafilter
import PDE.Analysis.Evolution.Core.Gronwall
import PDE.Analysis.Evolution.Galerkin.Existence
import PDE.Analysis.Evolution.Galerkin.Gelfand.Approximation
import PDE.Analysis.Evolution.Galerkin.Gelfand.QuadraticExistence
import PDE.Analysis.Evolution.Galerkin.Hilbert.Existence
import PDE.Analysis.Evolution.Galerkin.Measurable.Existence
import PDE.Analysis.Evolution.Galerkin.Spectral
import PDE.Analysis.Evolution.ODE.FiniteContinuation
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial
import PDE.Analysis.Evolution.Gelfand.QuadraticEquation

/-!
# Galerkin construction for weak evolution

Finite-dimensional pivot-mass systems, measurable Galerkin trajectories,
weak compactness, spectral trial spaces, and the existence and uniqueness
theorems.
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
#doc (Manual) "Galerkin Construction for Weak Evolution" =>

# Finite-dimensional Galerkin equations

:::definition "parabolic.galerkin.restriction" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.restrictFunctional, PDE.Analysis.Evolution.restrictForm") (uses := "parabolic.gelfand_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-378"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a finite-dimensional trial subspace $`S\subseteq V`, dual forcing and
the bilinear form are restricted to tests in $`S`.  These restriction maps
preserve the linear operations used by the evolution equation and satisfy
the expected norm bounds.
:::

Restricting the data is all that is needed to pose the finite-dimensional
problem. In the special case where the mass form is the inner product of
$`V` itself, the restricted problem is solved by the Hilbert-space ODE theory
of the foundations: $`S` is complete, so Riesz representation on
$`S` and variation of constants apply without change.

:::theorem "parabolic.galerkin.hilbert_mass_existence" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.exists_hilbertGalerkin_global, PDE.Analysis.Evolution.exists_hilbertGalerkin_on_Icc, PDE.Analysis.Evolution.exists_hilbertGalerkinOn_Icc, PDE.Analysis.Evolution.exists_hilbertGalerkin_with_uniform_bounds") (uses := "parabolic.galerkin.restriction, parabolic.smooth_weak_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-377"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`V` be a real inner product space, $`S\subseteq V` a complete subspace
(for instance any finite-dimensional trial space), $`B:V\to V^*` a bounded
bilinear form, and $`\ell:\mathbb R\to V^*` continuous. For every
$`t_0\in\mathbb R` and $`u_0\in S` there is a trajectory
$`u:\mathbb R\to S` with $`u(t_0)=u_0` which is differentiable at every time
and solves the restricted weak equation

$$`
(u'(t),w)_V+B(u(t),w)=\ell(t)(w)\qquad(w\in S,\ t\in\mathbb R),
`

its derivative being the Riesz-reduced vector field
$`u'(t)=R_S\ell(t)-A_Su(t)` of the restricted data. If $`\ell` is merely
continuous on $`[a,b]` and $`t_0\in[a,b]`, the same conclusion holds for
$`t\in[a,b]`, and it also gives the interval-level weak evolution
predicate. If moreover $`\lVert\ell(t)\rVert_{V^*}\le M` on $`[a,b]` and
$`B(w,w)\ge C\lVert w\rVert_V^2` for all $`w\in V` with $`C>0`, the
trajectory started at $`u(a)=u_0` satisfies, for $`t\in[a,b]`,

$$`
\tfrac12\lVert u(t)\rVert_V^2
\le\tfrac12\lVert u_0\rVert_V^2+\frac{M^2}{2C}(t-a),
\qquad
\lVert u'(t)\rVert_V\le M+\lVert B\rVert\,\lVert u(t)\rVert_V.
`

These are Evans's Galerkin approximations in the special case where the mass
form is the energy inner product itself, $`H=V`. No smallness or time-step
restriction is needed because the restricted system is affine linear.
:::

:::proof "parabolic.galerkin.hilbert_mass_existence" (uses := "parabolic.hilbert_affine_evolution, parabolic.smooth_weak_energy")
Restriction to $`S` produces a bounded form on the complete space $`S` and a
continuous $`S^*`-valued forcing. Riesz representation on $`S` converts the
restricted weak equation into the affine linear equation
$`u'=R_S\ell(t)-A_Su`, which the variation-of-constants formula solves
globally, or on any closed interval on which $`\ell` is continuous. The energy
inequality is the coercive smooth energy estimate tested with $`u(t)`, using
that restriction does not increase norms. The derivative bound follows from
the Riesz isometry, the contractivity of restriction, and the operator bound
$`\lVert A_Su\rVert\le\lVert B\rVert\lVert u\rVert`.
:::

In a genuine Gelfand triple the time term is $`(u_m'(t),v)_H` rather than
$`(u_m'(t),v)_V`, so the inner product of $`S` alone does not reduce the
restricted equation to an ODE. The pivot inner product restricted to $`S` is
a second nondegenerate form on the trial space.

:::definition "parabolic.galerkin.pivot_mass_system" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.trialPivotForm, PDE.Analysis.Evolution.trialMassOperator, PDE.Analysis.Evolution.trialMassEquiv, PDE.Analysis.Evolution.gelfandGalerkinOperator, PDE.Analysis.Evolution.gelfandGalerkinForcing") (uses := "parabolic.gelfand_triple, parabolic.galerkin.restriction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-376"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

The pivot inner product restricts to a nondegenerate bilinear form on $`S`, giving a map
$`S\to S^*`. Its Riesz representative is the mass operator $`M_S:S\to S`, a continuous
linear equivalence on a finite-dimensional trial space. Applying $`M_S^{-1}` to the Riesz
representative of the restricted residual gives the ODE on $`S`. This is the basis-free
analogue of multiplying a Galerkin matrix equation by the inverse mass
matrix; for an $`L^2`-orthonormal basis that mass matrix is the identity.
:::

Once the mass operator is inverted, the finite-dimensional system may carry
a quadratic term in addition to the linear form. An existence argument for
such a system needs an a priori energy estimate, the passage from an energy
inequality to an invariant region, and a gluing lemma for local solutions.
The estimate comes first,
and it rests on one algebraic fact: a trilinear term that is skew in its
last two arguments vanishes when tested with the state, so the energy
balance of the quadratic equation is that of its linear part.

:::theorem "parabolic.galerkin.skew_quadratic_energy" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.SatisfiesQuadraticGelfandWeakEvolutionAt.energy_equation, PDE.Analysis.Evolution.SatisfiesQuadraticGelfandWeakEvolutionAt.difference_energy_equation, PDE.Analysis.Evolution.gelfandGalerkin_quadratic_energy_bound, PDE.Analysis.Evolution.gelfandGalerkin_quadratic_integrated_energy_bound, PDE.Analysis.Evolution.SatisfiesQuadraticGelfandWeakEvolutionAt") (uses := "parabolic.galerkin.pivot_mass_system, parabolic.trilinear_energy_cancellation") (tags := "provenance:leanpde")
Consider the projected quadratic weak equation

$$`
(u_m'(t),v)_H+A(t;u_m(t),v)
  +N(t;u_m(t),u_m(t),v)=\ell(t)(v).
`

If $`N(t;x,y,z)` is skew in its last two arguments, testing with
$`v=u_m(t)` removes the nonlinear term. For the integrated estimate, assume
the trajectory has the prescribed derivative within $`[a,b]`, that $`A` and
$`\ell` are continuous there, and that $`C>0`, $`M\geq0` satisfy
$`A(t;v,v)\geq C\|v\|_V^2` and $`\|\ell(t)\|_{V^*}\leq M` for all
$`t\in[a,b]` and $`v\in V`. Then, for every $`t\in[a,b]`, the trajectory
satisfies the same estimate as the linear Galerkin equation:

$$`
\frac12\|u_m(t)\|_H^2
+\frac C2\int_a^t\|u_m(s)\|_V^2\,ds
\leq
\frac12\|u_m(a)\|_H^2+\frac{M^2}{2C}(t-a).
`

Two solutions of the quadratic weak equation also satisfy an exact
difference energy identity, used for stability and uniqueness.
:::

:::proof "parabolic.galerkin.skew_quadratic_energy"
Evaluate the projected equation at the state. Skew-symmetry gives
$`N(t;u_m,u_m,u_m)=0`, leaving precisely the state-tested linear energy
identity. Apply the pivot estimate and the integrated coercive estimate.
Subtracting two weak equations and expanding the quadratic term gives the
stated difference identity.
:::

Energy estimates enter a continuation argument as invariant regions. The
simplest case is a damped scalar inequality $`e'+\alpha e\le\beta`, the
shape a coercive estimate takes once the pivot norm is controlled by the
energy norm; such an inequality confines $`e` to a fixed sublevel set, the
time-independent form of an invariant region.

:::theorem "parabolic.galerkin.dissipative_sublevel" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.le_gronwallBound_of_hasDerivWithinAt_le, PDE.Analysis.Evolution.dissipative_energy_bound, PDE.Analysis.Evolution.dissipative_energy_sublevel_invariant") (uses := "parabolic.smooth_weak_energy") (tags := "provenance:leanpde")
Let $`e` be a differentiable scalar energy on $`[a,b]`. If

$$`
e'(t)+\alpha e(t)\leq\beta,\qquad \alpha>0,
`

then

$$`
e(t)\leq e(a)e^{-\alpha(t-a)}
  +\frac{\beta}{\alpha}\bigl(1-e^{-\alpha(t-a)}\bigr).
`

Consequently, every level $`R` satisfying
$`e(a)\leq R` and $`\beta\leq\alpha R` is invariant:
$`e(t)\leq R` throughout the interval. This is the abstract damping step
that turns a coercive energy calculation into a bounded region for
finite-dimensional continuation.
:::

:::proof "parabolic.galerkin.dissipative_sublevel"
Apply differential Grönwall with coefficient $`-\alpha` and forcing
$`\beta`. The explicit bound is a convex combination of $`e(a)` and the
equilibrium level $`\beta/\alpha`, with weights
$`e^{-\alpha(t-a)}` and $`1-e^{-\alpha(t-a)}`. Both endpoints of this
combination are at most $`R`.
:::

An invariant region is exactly what a cellwise continuation argument
consumes: local existence is available on a ball, and the a priori bound
guarantees that the solution never leaves the region where the local theory
applies. The gluing lemma is stated for a time-dependent family of sets
because the integrated coercive estimate produces an envelope growing
linearly in time rather than a fixed ball; the fixed-set and
constant-energy versions are special cases.

:::theorem "parabolic.galerkin.energy_controlled_continuation" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.exists_ode_solution_Icc_of_partition_of_timeDependentInvariant, PDE.Analysis.Evolution.exists_ode_solution_Icc_of_partition_of_invariant, PDE.Analysis.Evolution.exists_ode_solution_Icc_of_partition_of_energy_bound, PDE.Analysis.Evolution.exists_ode_solution_Icc_of_partition_of_energyEnvelope") (uses := "parabolic.galerkin.pivot_mass_system") (tags := "provenance:leanpde")
Fix an initial state $`u_0\in K(a)` and a finite uniform time partition of $`[a,b]`.
Suppose a nonlinear finite-dimensional Galerkin vector field has a local solution on each cell
from every state in $`K` at that cell's initial time, and each such solution remains in
$`K(t)` throughout the cell. Those solutions glue to a trajectory on the whole interval
with $`u(a)=u_0`, remaining in the same moving family.

Taking

$$`
K(t)=\{x:\mathcal E(t,x)\leq B(t,x)\}
`

gives the energy-envelope form. The theorem is independent of the equation.
:::

:::proof "parabolic.galerkin.energy_controlled_continuation"
Choose the first local solution from the prescribed initial state. At each
cell endpoint, the pointwise invariant places its terminal value in the next
allowable set. Start the next solution there, glue adjacent trajectories at
their common value, and induct over the finite partition.
:::

The three pieces combine as follows. Picard–Lindelöf gives a solution of the
mass-inverted quadratic ODE on a short cell whose length depends only on a
coefficient bound; the skew energy estimate supplies a time-dependent
envelope for the pivot norm, and finite-dimensional norm equivalence turns
that envelope into the required coefficient bound on every cell; the
continuation lemma then glues the cells into a trajectory on all of
$`[a,b]`.

:::theorem "parabolic.galerkin.quadratic_finite_interval_existence" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.exists_gelfandGalerkin_quadratic_on_Icc, PDE.Analysis.Evolution.exists_gelfandGalerkin_quadratic_on_Icc_of_bounds, PDE.Analysis.Evolution.gelfandGalerkinQuadraticTerm, PDE.Analysis.Evolution.gelfandGalerkinQuadraticVectorField") (uses := "parabolic.galerkin.skew_quadratic_energy, parabolic.galerkin.energy_controlled_continuation") (tags := "provenance:leanpde")
Let $`V\hookrightarrow H\hookrightarrow V^*` be a Gelfand triple and
$`S\subseteq V` a finite-dimensional trial space. Consider

$$`
(u'(t),v)_H+A(t;u(t),v)+N(t;u(t),u(t),v)=\ell(t)(v),
\qquad v\in S.
`

Assume $`A` and $`\ell` are continuous in time on $`[a,b]`, and that
$`t\mapsto N(t;w,w,\cdot)` is continuous as a dual-valued map for every
fixed $`w\in V`. The latter condition does not require operator-norm
continuity of the full trilinear form.

Restricting the dual residual to $`S`, applying Riesz representation, and
inverting the pivot mass operator produces a quadratic ODE on $`S`. Under
uniform bounds on $`A`, $`N`, and $`\ell`, Picard–Lindelöf gives a solution
from $`u_0\in S` on every interval short enough in terms of those bounds and
$`\|u_0\|`.

Assume in addition that $`A(t;v,v)\geq C\|v\|_V^2` with $`C>0`, that $`N` is
skew in its last two arguments, and that $`M\geq0` bounds
$`\|\ell(t)\|_{V^*}` on $`[a,b]`. Then every $`u_0\in S` starts a classical
Galerkin trajectory on all of $`[a,b]`, with continuous derivative, satisfying
the projected equation at every time and

$$`
\frac12\|u(t)\|_H^2
\leq
\frac12\|u_0\|_H^2+\frac{M^2}{2C}(t-a)
\qquad(t\in[a,b]).
`

The integrated estimate of the skew energy theorem then also holds for this
trajectory. The theorem is abstract in $`N`; a fluid application supplies
the domain, the divergence-free constraint, and the convection form.
:::

:::proof "parabolic.galerkin.quadratic_finite_interval_existence"
The trilinear bound gives
$`\|N(u,u)-N(w,w)\|\lesssim(\|u\|+\|w\|)\|u-w\|`, which yields local
Lipschitz continuity of the mass-inverted vector field on bounded balls.
The stated time-continuity hypotheses give its continuity along continuous
state paths. Apply Picard–Lindelöf on one cell. Testing the projected equation with its
state removes the skew term and gives the pivot-energy envelope. Finite
dimensional norm equivalence converts this into a uniform coefficient bound.
Choose a partition fine enough for the same unit Picard radius on every
cell, preserve the energy envelope locally, and glue the solutions.
:::

Everything so far concerns one trial space. Passing to the limit requires a
sequence of trial spaces, and the convergence argument uses exactly two
properties of it: the spaces eventually approximate every vector of $`V` and
of $`H`, and the pivot-orthogonal projections onto them are uniformly
bounded in the energy norm. Nestedness and a common basis are not needed.

:::definition "parabolic.galerkin.stable_trial_system" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.StableTrialProjection, PDE.Analysis.Evolution.StableTrialSystem") (uses := "parabolic.gelfand_triple")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

A stable trial system is a sequence of finite-dimensional spaces dense in
both $`V` and $`H`, together with pivot-compatible projections uniformly
bounded in the energy norm. The nested spans of one basis orthogonal in both
$`H^1_0(U)` and $`L^2(U)` form such a system.
:::

For each trial space of such a system the object to be constructed is a
trajectory together with its coefficient derivative and the projected weak
equation. The energy estimate is stored alongside, because its constants
$`C` and $`M` do not depend on the trial dimension, and that uniformity is
what the compactness step consumes.

:::definition "parabolic.galerkin.approximation" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.GelfandGalerkinApproximation, PDE.Analysis.Evolution.GelfandGalerkinApproximation.exists_nonauto_sequence_on_Icc") (uses := "parabolic.galerkin.pivot_mass_system, parabolic.galerkin.stable_trial_system, parabolic.gelfand_smooth_energy_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-378"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

A Galerkin approximation consists of a finite-dimensional trajectory, its
coefficient derivative, and the restricted weak equation

$$`
  (u_m'(t),v)_H+B(t;u_m(t),v)=\ell(t)(v)
  \qquad(v\in V_m).
`

For a coercivity constant $`C>0` and a load bound $`M\geq0`, it also records
the dimension-independent estimate

$$`
  \frac12\|u_m(t)\|_H^2
  +\frac C2\int_a^t\|u_m(s)\|_V^2\,ds
  \leq \frac12\|u_m(a)\|_H^2
  +\frac{M^2}{2C}(t-a).
`

For continuous, uniformly coercive time-dependent forms and continuous
bounded loads on a compact time interval, Lean constructs one approximation
in every trial space; the finite ODE partitions are chosen internally.
:::

The classical construction assumes that $`B(t)` and $`\ell(t)` are continuous
in time, which yields $`C^1` trajectories. For measurable, bounded
coefficients the finite-dimensional system is an affine ODE with measurable
coefficients: its natural solution concept is absolutely continuous and
satisfies the equation almost everywhere.

:::definition "parabolic.galerkin.caratheodory_system" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.AffineCaratheodorySolutionOn, PDE.Analysis.Evolution.AffineCaratheodorySolutionOn.exists, PDE.Analysis.Evolution.AffineCaratheodorySolutionOn.trajectory_eq") (uses := "parabolic.galerkin.pivot_mass_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-376"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a Banach space $`S`, an affine Carathéodory solution
of $`u'=A(t)u+f(t)` is absolutely continuous, has the prescribed initial
value, and satisfies the equation almost everywhere. A strongly measurable
operator coefficient uniformly bounded on $`[a,b]` and an integrable forcing
produce a unique trajectory on the whole finite interval. The proof uses a
contracting Picard iterate, so no short-time or smallness hypothesis is
needed.
:::

Applied to the restricted, mass-inverted form and forcing, the Carathéodory
theorem yields the measurable-time analogue of a Galerkin approximation,
whose energy estimate is derived from an equation that holds only almost
everywhere.

:::theorem "parabolic.galerkin.measurable_approximation" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.exists_aeGelfandGalerkinApproximation, PDE.Analysis.Evolution.AEGelfandGalerkinApproximation, PDE.Analysis.Evolution.exists_gelfandGalerkinCaratheodory") (uses := "parabolic.galerkin.caratheodory_system, parabolic.galerkin.stable_trial_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-378"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Restricting a strongly measurable bounded form and forcing to a
finite-dimensional trial space gives a Carathéodory pivot-mass system. Under
strict coercivity, its solution supplies an almost-everywhere Galerkin
approximation with an $`L^2` coefficient derivative, the projected weak
equation, and an energy estimate whose constants are independent of the
trial dimension. It replaces the $`C^1` Galerkin curve when the
coefficients are only measurable in time.
:::

:::proof "parabolic.galerkin.measurable_approximation"
Restrict the form, pivot mass pairing, and forcing to the finite-dimensional
trial space. Strong measurability and uniform bounds pass to the resulting
matrix coefficients, so the Carathéodory theorem gives an absolutely
continuous coefficient trajectory satisfying the projected equation almost
everywhere. Testing that equation with the trajectory, using coercivity, and
applying Young's inequality gives the dimension-independent energy estimate.
The coefficient derivative then belongs to $`L^2` by the finite-dimensional
equation and the uniform coefficient bounds.
:::

The dimension-independent estimate is what makes the limit possible. It
bounds the trajectories in $`L^2(a,b;V)` and, through the projected
equation, their dual derivatives in $`L^2(a,b;V^*)`. These bounds allow weak
compactness. For the integrated limit passage it is enough to extract the
state limit: the time derivative has already been transferred to the scalar
test, and the residual later identifies the weak derivative.

:::theorem "parabolic.galerkin.weak_compactness" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.gelfandGalerkin_integrated_initial_identity_Lp, PDE.Analysis.Evolution.gelfandGalerkin_projected_integrated_initial_identity_Lp, PDE.Analysis.Evolution.tendsto_compLpL_of_tendsto_strongly, PDE.Analysis.Evolution.tendsto_inner_of_tendsto_weak_of_tendsto_strong, PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter, PDE.Analysis.Evolution.integrated_initial_identity_of_weak_L2_limit, PDE.Analysis.Evolution.isGelfandIntegratedWeakSolution_of_projected_weak_L2_limit") (uses := "parabolic.galerkin.measurable_approximation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "377-378"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Uniform $`L^2(a,b;V)` bounds for the states and $`L^2(a,b;V^*)` bounds for
their derivatives have a common weakly convergent ultrafilter refinement.
Strong convergence of the trial projections and the weak–strong pairing
rule then justify passage to the limit in the time-tested Galerkin identity.
When state and derivative limits are both taken, they must be taken along a
common refinement to identify one evolution.
:::

:::proof "parabolic.galerkin.weak_compactness"
Reflexivity of the Bochner $`L^2` spaces makes the bounded families weakly relatively compact.
Extract a weak state limit along an ultrafilter refining the index filter. For each fixed
$`v\in V`, use the projected test $`P_m v` in the integrated Galerkin identity. Strong
convergence $`P_m v\to v`, the uniform state bound, and weak–strong pairing pass the time,
form, and forcing terms to the limit. Strong convergence of the initial projections gives
the prescribed initial boundary term. Since $`v` was arbitrary, the limiting identity holds
for every energy-space test. If a derivative family is also extracted, refine the same
filter before taking that limit.
:::

# Basis-free spectral trial spaces

:::definition "parabolic.galerkin.gram_operator" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.gramOperator")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "731"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    },
    {
      page := "377"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    }
  ]
}
%%%
For a continuous inclusion $`J:V\to H` of Hilbert spaces, its Gram operator is
$`J^*J:V\to V`. Its spectral subspaces take the place of an eigenbasis
chosen in advance.
:::

The spectral construction of trial spaces needs $`J^*J` to be symmetric,
compact, and injective, and each property is inherited from $`J`.

:::theorem "parabolic.galerkin.gram_properties" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.inner_gramOperator_apply, PDE.Analysis.Evolution.isCompactOperator_gramOperator, PDE.Analysis.Evolution.gramOperator_isSymmetric, PDE.Analysis.Evolution.gramOperator_injective") (uses := "parabolic.galerkin.gram_operator, parabolic.gelfand_triple")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "731"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    },
    {
      page := "377"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    }
  ]
}
%%%
The identity

$$`(J^*Ju,v)_V=(Ju,Jv)_H`

makes the Gram operator positive and symmetric. If $`J` is compact, then
$`J^*J` is compact; if $`J` is injective, then $`J^*J` is injective.
:::

:::proof "parabolic.galerkin.gram_properties"
The adjoint identity gives
$`(J^*Ju,v)_V=(Ju,Jv)_H`, which is symmetric in $`u,v` and nonnegative when
$`v=u`. If $`J` is compact, composition with the bounded adjoint $`J^*`
keeps $`J^*J` compact. If $`J^*Ju=0`, pairing with $`u` gives
$`\|Ju\|_H^2=0`; injectivity of $`J` then forces $`u=0`.
:::

For a compact symmetric operator the eigenvalues can accumulate only at
zero, so for each threshold $`1/(m+1)` only finitely many eigenvalues have
magnitude at least the threshold, and the sum of their eigenspaces is
finite-dimensional. Injectivity removes the zero eigenspace, the one part of
the spectral decomposition that no threshold ever reaches.

:::theorem "parabolic.galerkin.spectral_density" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.dense_iSup_thresholdSpace") (uses := "parabolic.galerkin.gram_properties")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "731"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    },
    {
      page := "377"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    }
  ]
}
%%%
For an injective compact symmetric operator, sum all eigenspaces whose
eigenvalues have magnitude at least $`1/(m+1)`. Each threshold space is
finite-dimensional, the spaces increase with $`m`, and their union is dense
in the energy space. Taking whole eigenspaces makes the construction
independent of a basis within each repeated eigenspace: the spectral subspaces
themselves determine the trial spaces.
:::

:::proof "parabolic.galerkin.spectral_density"
The compact self-adjoint spectral theorem decomposes the orthogonal complement
of the kernel into finite-dimensional nonzero eigenspaces, with possible
eigenvalues accumulating only at zero. Injectivity makes the kernel trivial.
For a fixed threshold, only finitely many eigenvalues have magnitude at least
$`1/(m+1)`, so the corresponding sum is finite-dimensional. As the threshold
decreases, every nonzero eigenspace eventually appears; completeness of the
spectral decomposition makes the increasing union dense.
:::

Threshold spaces are sums of eigenspaces of $`J^*J`, hence invariant under
it, and this invariance is what makes the energy-orthogonal projection onto
them pivot-orthogonal as well: for $`w` in the threshold space,
$`(J(v-P_mv),Jw)_H=(v-P_mv,J^*Jw)_V`, and $`J^*Jw` again lies in the
space. A stable trial projection is therefore obtained without any choice of
basis.

:::definition "parabolic.galerkin.stable_spectral_projection" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.stableTrialProjectionThreshold") (uses := "parabolic.galerkin.gram_properties, parabolic.galerkin.spectral_density, parabolic.galerkin.stable_trial_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The energy-orthogonal projection onto each Gram spectral threshold space is
also orthogonal after inclusion into the pivot space. It therefore defines a
Galerkin trial projection $`P_m` with

$$`
  \|P_m v\|_V\leq\|v\|_V
  \qquad\text{and}\qquad
  (J(v-P_m v),Jw)_H=0
  \quad(w\in V_m).
`

Thus its energy stability constant is exactly one.
:::

The abstract construction needs only a compact Gelfand inclusion, and for
the parabolic problem that compactness is the Rellich theorem.

:::definition "parabolic.galerkin.h10_l2_trial_system" (parent := "parabolic.variational") (lean := "SobolevSpace.GraphSpace.h10L2SpectralTrialSystem") (uses := "parabolic.gelfand_triple, parabolic.galerkin.gram_properties, parabolic.galerkin.spectral_density, parabolic.galerkin.stable_spectral_projection")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "731"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    },
    {
      page := "377"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 35, endLine := 39 }
    }
  ]
}
%%%
On every bounded open domain, compactness of
$`H^1_0(\Omega)\hookrightarrow L^2(\Omega)` specializes the abstract spectral
construction to a stable trial system dense in both the energy and pivot
spaces. This provides the finite-dimensional approximation data required by
the weak parabolic existence theorem.
:::

On the interval $`(0,\pi)` the two constructions agree. The sines
$`\sin kx` are orthogonal both in $`L^2` and in $`H^1_0`, so they
diagonalize the Gram operator, and its threshold spaces are the spans of the
first $`N` sines. The Galerkin solution in such a space is the truncated sine
series of the exact solution, and the error in $`L^2` is the tail of the
series. At positive time the factor $`e^{-k^2t}` makes that tail small very
quickly.

{leanpde_figure "galerkin-sine-convergence"}

:::theorem "parabolic.galerkin_existence" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.existsUnique_of_nonauto_galerkin_L2") (uses := "parabolic.integrated_weak_solution, parabolic.galerkin.approximation, parabolic.galerkin.stable_trial_system, parabolic.integrated_garding_uniqueness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`a<b`. For a continuous, uniformly bounded, and uniformly coercive
time-dependent form, stable finite-dimensional trial projections
dense in both $`V` and $`H` produce a unique integrated weak solution for
every forcing in $`L^2(a,b;V^*)` and every initial datum in $`H`.

The theorem contains both stages of Evans's Galerkin argument: solve the
finite-dimensional ODEs for regular forcing, then use uniform energy bounds,
weak compactness, and density to pass to arbitrary Bochner $`L^2` forcing.
:::

:::proof "parabolic.galerkin_existence" (uses := "parabolic.galerkin.approximation, parabolic.integrated_garding_uniqueness")
First take a bounded continuous forcing. Construct the finite-dimensional trajectories,
extract a weak state limit using the uniform energy bound, and pass the projected
time-tested equations to the limit. To reach a prescribed $`L^2(V^*)` forcing, approximate
it by bounded continuous loads. The $`C^{-1}` continuous-dependence estimate makes their
solutions Cauchy in $`L^2(V)`, and strong-limit closure gives the integrated equation for
the prescribed load. The uniqueness theorem identifies the solution.
:::

The unique solution just produced is a Bochner class. The residual theorem
and Lions–Magenes attach to it a continuous pivot representative with the
prescribed initial trace, and for continuous bounded forcing this
representative also satisfies the coercive prefix estimate.

:::theorem "parabolic.galerkin_existence_energy" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.existsUnique_of_nonauto_galerkin_with_energy_bound") (uses := "parabolic.galerkin_existence, parabolic.integrated_energy_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For continuous bounded forcing, the Galerkin theorem returns the unique
integrated weak solution together with its continuous pivot representative,
weak $`L^2(a,b;V^*)` time derivative, initial trace, and the coercive energy
estimate on every prefix $`[a,t]`.
:::

:::proof "parabolic.galerkin_existence_energy"
Apply the Galerkin existence theorem to obtain the unique integrated weak
solution. For continuous bounded forcing, the residual
$`\ell-B(\cdot)u` is an $`L^2(V^*)` weak derivative. Lions–Magenes gives
the continuous pivot representative and its initial trace, and the exact
energy identity combined with coercivity and Young's inequality gives the
prefix estimate. Uniqueness identifies this enriched solution with the one
already constructed.
:::

The measurable-coefficient theorems below remove the time continuity of $`B`
by replacing the classical Galerkin trajectories with the Carathéodory
approximations, and relax coercivity to a Gårding inequality by the
exponential change of variables that turns the mass-shifted form into a
coercive one. Uniqueness in the Gårding case
comes from the integral Grönwall argument, not from nonnegativity of the
unshifted form.

:::theorem "parabolic.measurable_garding_existence" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_L2, PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_garding_L2, PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin_garding_L2_full") (uses := "parabolic.integrated_weak_solution, parabolic.integrated_residual_derivative, parabolic.integrated_garding_uniqueness, parabolic.galerkin.measurable_approximation, parabolic.galerkin.weak_compactness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`a<b` and let $`B(t):V\to V^*` be strongly measurable and uniformly bounded on
$`[a,b]`. Assume the Gårding inequality

$$`\theta\lVert v\rVert_V^2\le
  B(t)(v,v)+\gamma\lVert Jv\rVert_H^2,\qquad \theta>0.`

Given stable finite-dimensional projections dense in both $`V` and $`H`,
every forcing in $`L^2(a,b;V^*)` and every initial datum in $`H` determine a
unique integrated weak solution. The full theorem additionally returns its
$`L^2` weak derivative, the almost-everywhere identity
$`u'=\ell-B(\cdot)u`, a continuous pivot representative with the prescribed
left trace, and the Gårding energy estimate on every prefix $`[a,t]`.
:::

:::proof "parabolic.measurable_garding_existence"
Set $`w(t)=e^{-\gamma(t-a)}u(t)`. The shifted form
$`B_\gamma(t)(v,z)=B(t)(v,z)+\gamma(Jv,Jz)_H` is coercive, and the shifted forcing is
$`e^{-\gamma(t-a)}\ell(t)`. For bounded continuous loads,
solve the measurable finite-dimensional Carathéodory systems and pass their integrated
equations to a weak state limit. Complete this coercive solution operator to arbitrary
$`L^2` loads using the continuous-dependence estimate, and apply it to the shifted forcing.
Multiplication by $`e^{\gamma(t-a)}` returns a solution of the original equation.
The residual theorem and Lions–Magenes give the weak derivative, continuous pivot trace,
and prefix energy estimate; Gårding uniqueness follows from the homogeneous difference
equation and integral Gronwall.
:::
