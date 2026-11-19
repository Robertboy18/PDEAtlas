/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws.Systems
import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.LocalInverse
import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.Breakdown
import PDE.Hyperbolic.ConservationLaw.Scalar.InitialValue

/-!
# Scalar characteristics

The characteristic-foot construction for scalar conservation laws, its
residual identity, and the pre-shock interval detected by the characteristic
Jacobian.
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
#doc (Manual) "Scalar Characteristics" =>

# Classical scalar characteristics

Before shocks form, the scalar conservation law transports the initial value
along curves whose speed depends on that value. The footpoint map asks which
initial position reaches a given spacetime point. Its Jacobian is the precise
quantity that controls whether these characteristic curves still define a
single-valued classical solution.

:::definition "hyperbolic.conservation.scalar_characteristics" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.ConservationFootRelationOn, PDE.Hyperbolic.ConservationLaw.Scalar.conservationSolutionFromFoot, PDE.Hyperbolic.ConservationLaw.Scalar.conservationDenom")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "111-113"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the scalar equation $`u_t+a(u)u_x=0`, a supplied characteristic
footpoint $`\xi(t,x)` on an open spacetime set $`V` satisfies

$$`x=\xi+t\,a(u_0(\xi)),\qquad u(t,x)=u_0(\xi(t,x)).`

The Jacobian denominator is
$`1+t\,a'(u_0(\xi))u_0'(\xi)`.
:::

For differentiable $`a` and $`u_0`, differentiating the footpoint relation
in space gives $`\xi_x(1+t\,a'(u_0(\xi))u_0'(\xi))=1`. Thus a
differentiable local footpoint map already forces the denominator to be
nonzero. We can divide by it and use the chain rule to verify the PDE.

Let us read that denominator geometrically. The forward map is
$`X_t(\xi)=\xi+t\,a(u_0(\xi))`; its derivative tells us how the distance
between neighboring characteristics changes. Along a classical branch,

$$`
\partial_\xi X_t=1+t\,a'(u_0(\xi))u_0'(\xi),
\qquad
u_x(t,X_t(\xi))
=\frac{u_0'(\xi)}{\partial_\xi X_t}.
`

Compression makes the denominator small while the value on each
characteristic remains $`u_0(\xi)`. Thus a nonzero initial slope can become
unbounded without the transported values becoming unbounded. This is loss
of classical regularity through crossing, a different mechanism from the
amplitude growth of the nonlinear heat example.

:::theorem "hyperbolic.conservation.scalar_characteristic_residual" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.ConservationFootRelationOn.partialDeriv_time, PDE.Hyperbolic.ConservationLaw.Scalar.ConservationFootRelationOn.partialDeriv_space, PDE.Hyperbolic.ConservationLaw.Scalar.ConservationFootRelationOn.satisfies_pde_at") (uses := "hyperbolic.conservation.scalar_characteristics")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "111-113"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a,u_0:\mathbb R\to\mathbb R` be differentiable on $`\mathbb R`,
and let $`\xi:\mathbb R^2\to\mathbb R` satisfy the footpoint
relation on an open set $`V`. At each point of $`V` where $`\xi` is
differentiable, the denominator is nonzero and implicit differentiation gives

$$`
\xi_t=-\frac{a(u_0(\xi))}{1+t a'(u_0(\xi))u_0'(\xi)},\qquad
\xi_x=\frac{1}{1+t a'(u_0(\xi))u_0'(\xi)}.
`

Substitution gives $`u_t+a(u)u_x=0` at that point for
$`u=u_0\circ\xi`. The relation and differentiability are needed only
near the point under consideration.
:::

:::proof "hyperbolic.conservation.scalar_characteristic_residual"
Differentiate the footpoint identity in $`t` and $`x`. Solving the resulting
linear equations for $`\xi_t` and $`\xi_x` gives the displayed fractions,
with the nonzero Jacobian denominator permitting division. Applying the
chain rule to $`u=u_0\circ\xi` then factors the PDE residual through
$`\xi_t+a(u)\xi_x=0`.
:::

The residual identity is pointwise. A solution on a whole time strip needs a
single threshold below which no characteristic degenerates, and the infimum
of the degeneracy times is that threshold.

:::theorem "hyperbolic.conservation.scalar_pre_shock" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.conservationDenom_ne_zero_of_lt_shockTime, PDE.Hyperbolic.ConservationLaw.Scalar.conservationShockTime, PDE.Hyperbolic.ConservationLaw.Scalar.exists_local_solution_before_shockTime, PDE.Hyperbolic.ConservationLaw.Scalar.conservationClassicalSolution_satisfies_pde, PDE.Hyperbolic.ConservationLaw.Scalar.contDiffWithinAt_conservationClassicalSolution, PDE.Hyperbolic.ConservationLaw.Scalar.conservationClassicalSolution_initial") (uses := "hyperbolic.conservation.scalar_characteristic_residual")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "112-113"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a,u_0` be $`C^1` on $`\mathbb R`. The formal shock time $`T_*` is the infimum
of nonnegative times at which the characteristic Jacobian vanishes
somewhere; it is $`\infty` if there are none. For every $`0\leq t<T_*`
and label $`\xi_0`, there is an open neighborhood $`V` of
$`(t,\xi_0+t\,a(u_0(\xi_0)))` and a differentiable footpoint map on $`V`
whose value at that point is $`\xi_0`. The resulting $`u=u_0\circ\xi`
satisfies $`u_t+a(u)u_x=0` on $`V` and agrees with $`u_0` on
$`V\cap\{t=0\}`.

These local inverses agree with a global spatial inverse of $`X_t`.
Consequently $`u(t,x)=u_0(X_t^{-1}(x))` is a classical solution on the entire
strip $`0<t<T_*`, is $`C^1` up to time zero from the right when $`T_*>0`,
and has $`u(0,x)=u_0(x)` on the whole initial line. The strip may be empty,
since an infimum of degeneracy times can be zero.
:::

:::proof "hyperbolic.conservation.scalar_pre_shock"
If the denominator vanished at some nonnegative time $`t`, then $`t` would
belong to the set whose infimum defines the shock time. Hence the shock time
would be at most $`t`, contradicting the strict pre-shock assumption. The
nonvanishing denominator makes the derivative of
$`(t,\xi)\mapsto(t,\xi+t\,a(u_0(\xi)))` invertible. The inverse function
theorem supplies a local inverse; its spatial component is the footpoint.
For the global inverse, choose $`t<\tau<T_*`. Positivity of the Jacobian
at $`\tau` implies the uniform bound
$`X_t'(\xi)\ge(\tau-t)/\tau>0`. The mean value theorem makes $`X_t`
strictly increasing with limits $`\pm\infty` at the ends of the line,
so the intermediate value theorem gives surjectivity. Injectivity makes
every local inverse agree with the global inverse. The preceding residual
identity verifies the PDE at positive time, and at time zero the footpoint
relation reduces to $`\xi(0,x)=x`.
:::

## The first loss of classical regularity

The time $`T_*` has two roles. It is a barrier to classical continuation
even when no single label realizes the infimum. A statement that the
derivative diverges along one specified characteristic needs an attained
finite degeneracy.

:::theorem "hyperbolic.conservation.scalar_shock_onset" (parent := "hyperbolic.conservation") (uses := "hyperbolic.conservation.scalar_pre_shock") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.classical_lifespan_le_conservationShockTime, PDE.Hyperbolic.ConservationLaw.Scalar.not_exists_classical_continuation, PDE.Hyperbolic.ConservationLaw.Scalar.tendsto_norm_partialDeriv_space_at_shock")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§3.4.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a,u_0\in C^1(\mathbb R)`. Any solution with the prescribed initial
data that is $`C^1` at every point of the closed strip $`0\le t\le T`
and satisfies $`u_t+a(u)u_x=0` there has $`T\le T_*`. More generally, the
constructed solution has no $`C^1` continuation from a slice
$`0<s<T_*` to any $`T>T_*`.

If $`T_*<\infty` is attained at a label $`\xi`, meaning
$`1+T_*a'(u_0(\xi))u_0'(\xi)=0`, then

$$`\left|u_x\bigl(t,\xi+t\,a(u_0(\xi))\bigr)\right|
\longrightarrow\infty\qquad(t\uparrow T_*).`
:::

:::proof "hyperbolic.conservation.scalar_shock_onset"
A classical solution transports $`u_0(\xi)` along the characteristic of
label $`\xi`. Differentiating that identity gives
$`u_x(t,X_t(\xi))X_t'(\xi)=u_0'(\xi)`. At a degeneracy,
$`X_t'(\xi)=0` forces the left side to vanish, although the degeneracy
identity forces $`u_0'(\xi)\ne0`. A proposed continuation past the
infimum encounters some degeneracy before its final time, giving the
contradiction without choosing a minimizing label.

At an attained first degeneracy, the same derivative identity on the
pre-shock strip gives the quotient
$`u_0'(\xi)/(1+t\,a'(u_0(\xi))u_0'(\xi))`.
Its numerator is nonzero and its denominator tends to zero through positive
values, proving divergence of the norm.
:::

## The value of the shock time

The shock time has a closed form in the data. Write
$`k(\xi)=a'(u_0(\xi))u_0'(\xi)`. The Jacobian $`1+t\,k(\xi)` vanishes at
$`t=-1/k(\xi)` when $`k(\xi)<0`, and never at a nonnegative time when
$`k(\xi)\ge0`.

:::theorem "hyperbolic.conservation.scalar_shock_time_value" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.Scalar.conservationShockTime_eq_of_isGLB, PDE.Hyperbolic.ConservationLaw.Scalar.conservationShockTime_eq_top_of_nonneg") (uses := "hyperbolic.conservation.scalar_pre_shock")
If $`k(\xi)=a'(u_0(\xi))u_0'(\xi)` has infimum $`m<0` over
$`\xi\in\mathbb R`, then

$$`T_*=-\frac1m.`

The infimum need not be attained. If $`k(\xi)\ge0` for every $`\xi`, then
$`T_*=\infty`.
:::

:::proof "hyperbolic.conservation.scalar_shock_time_value"
A degeneracy time $`t\ge0` has $`1+t\,k(\xi)=0` for some label, so
$`k(\xi)<0` and $`t=-1/k(\xi)`. Since $`m\le k(\xi)<0`, this gives
$`t\ge-1/m`, and $`-1/m` is a lower bound of the degeneracy times. Values of
$`k` approaching $`m` from above give degeneracy times approaching $`-1/m`
from above, so no larger number is a lower bound. When $`k\ge0`, the
Jacobian is at least one at every nonnegative time and there is no
degeneracy time.
:::
