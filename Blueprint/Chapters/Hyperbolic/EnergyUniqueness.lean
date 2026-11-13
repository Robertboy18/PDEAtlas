/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.WeakWaves
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.Subtraction
import PDE.Hyperbolic.WeakWave.EvansCoefficientIntegrability
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.CanonicalEstimate

/-!
# Wave energy and uniqueness

Energy uniqueness for weak waves in a Gelfand triple.
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
#doc (Manual) "Energy Uniqueness" =>

:::group "hyperbolic.energy_uniqueness"
Wave energy and uniqueness
:::

Uniqueness of weak waves (Evans §7.2.2) follows by testing the homogeneous
equation against a backward time primitive and repeating the estimate on a
finite partition of the time interval. The argument here runs over an
abstract Gelfand triple.

:::theorem "hyperbolic.weak_wave.backward_estimate" (parent := "hyperbolic.energy_uniqueness") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.evans_backward_estimate") (uses := "hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`a<b` and a terminal time $`\sigma\in[a,b]`, set
$`W_\sigma(t)=\int_t^\sigma u(r)\,dr`. Let a homogeneous weak wave have
zero initial displacement and velocity at $`a`. Assume its principal form
$`A` is symmetric, coercive with constant $`c>0`, and absolutely continuous
in time, with coefficient derivative bound $`L_A` and pivot-to-energy
lower-order bound $`L_R\geq0`. Under the scalar integrability hypotheses
for the backward-energy identity, it satisfies

$$`
\frac12\|u(\sigma)\|_H^2+\frac c2\|W_\sigma(a)\|_V^2
\leq
\frac{L_A}{2}\int_a^\sigma\|W_\sigma(t)\|_V^2\,dt
+\frac{L_R}{2}\int_a^\sigma
\bigl(\|u(t)\|_H^2+\|W_\sigma(t)\|_V^2\bigr)\,dt.
`

Here $`u(\sigma)` denotes the continuous pivot-space displacement
representative. Zero initial data remove the initial boundary terms.
:::

:::proof "hyperbolic.weak_wave.backward_estimate"
The weak equation is tested against a backward time primitive. Integration by
parts exposes the endpoint pivot norm and the principal energy. Coercivity
controls the primitive, while the coefficient derivative and lower-order form
are estimated by their stated quadratic bounds.
:::

By itself the estimate is not yet a Grönwall inequality, because
$`W_\sigma(t)=W_\sigma(a)-W_t(a)` ties the right-hand side to the endpoint
quantity $`\|W_\sigma(a)\|_V` with a coefficient of order $`\sigma-a`. On an
interval short enough for that coefficient to be absorbed into the left-hand
side, Grönwall's inequality gives $`u=0` up to $`\sigma`.

:::theorem "hyperbolic.weak_wave.finite_partition_uniqueness" (parent := "hyperbolic.energy_uniqueness") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.continuousDisplacement_eq_zero_of_finite_short_partition") (uses := "hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a=\tau_0<\tau_1<\cdots<\tau_N=b` cover the time interval, with each
$`\tau_{j+1}-\tau_j` short enough to absorb the right-hand side in
{uses "hyperbolic.weak_wave.backward_estimate"}[]. Then a homogeneous
zero-data weak wave has

$$`
u(t)=0\qquad\text{for every }t\in[a,b]
`

for its continuous pivot-space displacement representative.
:::

:::proof "hyperbolic.weak_wave.finite_partition_uniqueness" (uses := "hyperbolic.weak_wave.backward_estimate")
The backward estimate and Grönwall argument give vanishing on the first short
interval. The zero displacement and velocity traces at its right endpoint
restart the same argument on the next interval. Finite induction covers the
whole interval.
:::

Uniqueness for general data follows from the homogeneous zero-data case by
subtraction, which is pure linear algebra on the weak-wave predicate.

:::theorem "hyperbolic.weak_wave.uniqueness_reduction" (parent := "hyperbolic.energy_uniqueness") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.eq_of_homogeneous_eq_zero") (uses := "hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose every homogeneous zero-data weak wave satisfies
$`(w,w_t,w_{tt})=(0,0,0)`. If $`u_1` and $`u_2` have the same operator,
forcing, displacement trace, and velocity trace, then their difference is such
a homogeneous solution, hence

$$`
u_1=u_2,\qquad (u_1)_t=(u_2)_t,\qquad
(u_1)_{tt}=(u_2)_{tt}.
`
:::

:::proof "hyperbolic.weak_wave.uniqueness_reduction"
Subtract the two weak formulations. Linearity cancels the common forcing and
initial traces, so the difference is a homogeneous zero-data weak wave.
Applying homogeneous uniqueness to its displacement, velocity, and
acceleration gives equality of the corresponding components.
:::

Of the three scalar integrability conditions in the backward estimate, two
come from measurability and the coefficient bounds: the coefficient
derivative and lower-order pairings along $`u` and $`W_\sigma`. For the
difference of two solutions, the
homogeneous weak equation identifies $`B(u,W_\sigma)` with the negative
acceleration pairing; $`A=B-R` then gives integrability of the principal
pairing.

:::theorem "hyperbolic.weak_wave.uniqueness" (parent := "hyperbolic.energy_uniqueness") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.eq_of_evans_coefficients_of_operator_measurable") (uses := "hyperbolic.weak_wave.backward_estimate, hyperbolic.weak_wave.finite_partition_uniqueness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In the real Hilbert Gelfand-triple setting, write $`J:V\hookrightarrow H`
for the inclusion and assume $`B=A+R` on $`[a,b]`. Require $`A` to be
absolutely continuous in operator norm, with $`A'(t)=\dot A(t)` for almost
every $`t\in(a,b]`. Both $`\dot A` and $`R` must be almost everywhere
strongly measurable as operator-valued maps. For every $`t\in[a,b]`,
assume $`A(t)` is symmetric and, for all $`v,w\in V`,

$$`
\kappa\|v\|_V^2\leq A(t)(v,v),\qquad
|\dot A(t)(v,v)|\leq L_A\|v\|_V^2,\qquad
|R(t)(v,w)|\leq L_R\|Jv\|_H\|w\|_V,
`

where $`\kappa>0` and $`L_A,L_R\geq0`. Two weak waves for this operator
with equal forcing and initial traces then satisfy

$$`
u_1=u_2\ \text{in }L^2(a,b;V),\qquad
v_1=v_2\ \text{in }L^2(a,b;H),\qquad
a_1=a_2\ \text{in }L^2(a,b;V^*).
`

The scalar integrability conditions inside the backward-energy identity are
derived from the $`L^2` trajectories, the coefficient bounds, and the weak
equation.
:::

:::proof "hyperbolic.weak_wave.uniqueness" (uses := "hyperbolic.weak_wave.backward_estimate")
Subtract the two waves, construct a sufficiently fine uniform finite
partition, apply the backward-energy estimate on each cell, restart from
the zero endpoint traces, and identify the vanishing continuous
representative with all three Bochner classes.
:::
