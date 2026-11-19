/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.Regularity
import PDE.Elliptic.Regularity.SolutionOperator.H2
import PDE.Elliptic.Regularity.SolutionOperator.HigherOrder

/-!
# Elliptic solution operators

Bounded linear solution operators obtained from elliptic regularity by the closed
graph theorem.
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
#doc (Manual) "Bounded Solution Operators" =>

:::group "elliptic.solution_operators"
Elliptic solution operators
:::

# Regularity as a bounded operator

An existence theorem may say that every forcing $`f` has a solution with two
additional weak derivatives.  For linear PDE, one wants more: the chosen
solution should depend linearly and continuously on $`f`.  Uniqueness of the
underlying weak Dirichlet problem makes the choice canonical, and the closed
graph theorem supplies continuity once qualitative regularity has been
established.

The resulting operators $`S_2:L^2(\Omega)\to H^2(\Omega)` and
$`S_{m+2}:H^m(\Omega)\to H^{m+2}(\Omega)` solve the principal
divergence-form Dirichlet problem, under the boundary-chart, coefficient, and
ellipticity hypotheses of the corresponding global regularity theorems.

:::definition "elliptic.solution_operator.qualitative_lift_data" (parent := "elliptic.solution_operators") (lean := "SobolevSpace.GraphSpace.HasHigherSolutionLift")
For an open domain and a bounded weak Dirichlet solver,
the higher-order lift condition means that every $`H^m` forcing has an
$`H^{m+2}` representative whose base coordinate is the weak solution
$`S f`. Concrete elliptic regularity theorems prove this predicate, and the
generic functional-analytic construction takes it as input.
:::

The predicate is purely qualitative: it asserts the existence of an $`H^{m+2}`
representative for each datum and says nothing about how that representative
depends on the datum. Linearity and continuity are consequences, the former
because a Sobolev field on an open set is determined by its base coordinate,
the latter by the closed graph theorem.

:::definition "elliptic.solution_operator.closed_graph_lift" (parent := "elliptic.solution_operators") (lean := "SobolevSpace.GraphSpace.higherSolutionOperator, SobolevSpace.GraphSpace.higherSolutionOperator_base") (uses := "elliptic.solution_operator.qualitative_lift_data")
Let $`\Omega` be open, let
$`S:L^2(\Omega)\to H^1_0(\Omega)` be a bounded linear weak solver, and
suppose every $`H^m` datum has an $`H^{m+2}` representative whose base
coordinate is the weak solution $`Sf`. Uniqueness of Sobolev fields from
their base coordinate makes this qualitative lift linear. Its graph is
closed because both the Sobolev base-coordinate map and the weak solver are
continuous. The closed graph theorem therefore gives a canonical bounded
linear map

$$`
S_{m+2}:H^m(\Omega)\longrightarrow H^{m+2}(\Omega),
`

whose base coordinate is exactly the original weak solution and whose norm
obeys the usual operator-norm estimate. The construction uses nothing about
the coefficients, which enter only through the lift hypothesis.
:::

The first concrete instance takes $`m=0`. The global $`H^2` theorem supplies
the qualitative lift for the principal divergence-form weak solver, and the
generic construction turns it into a bounded operator from $`L^2(\Omega)` to
$`H^2(\Omega)`.

:::definition "elliptic.solution_operator.h2" (parent := "elliptic.solution_operators") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.globalH2SolveCLM, SobolevSpace.GraphSpace.hasHigherSolutionLift_zero, SobolevSpace.GraphSpace.BoundaryRegularity.globalH2SolveCLM_base_ae, SobolevSpace.GraphSpace.BoundaryRegularity.globalH2SolveCLM_orderOne") (uses := "elliptic.divergence.exists_unique, elliptic.regularity.h2.principal, elliptic.solution_operator.closed_graph_lift")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "334-340"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the hypotheses of the global $`H^2` theorem, the canonical weak
Dirichlet solver lifts to a bounded linear map

$$`S_2:L^2(\Omega)\longrightarrow H^2(\Omega).`

Its value is the unique $`H^2` representative of the weak solution.
:::

Continuity of a linear map between normed spaces is the same as an
operator-norm inequality, so the estimate is a restatement of boundedness.

:::theorem "elliptic.solution_operator.h2_estimate" (parent := "elliptic.solution_operators") (lean := "ContinuousLinearMap.le_opNorm") (uses := "elliptic.solution_operator.h2")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "334-340"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`f\in L^2(\Omega)`, the canonical solution satisfies

$$`\lVert S_2f\rVert_{H^2(\Omega)}
  \le\lVert S_2\rVert_{\mathrm{op}}\,
     \lVert f\rVert_{L^2(\Omega)}.`

The constant is independent of the forcing datum.
:::

:::proof "elliptic.solution_operator.h2_estimate"
The regularity and uniqueness argument has already bundled the solver as a
continuous linear map $`S_2:L^2(\Omega)\to H^2(\Omega)`. The conclusion is
exactly the defining operator-norm inequality
$`\lVert S_2f\rVert\leq\lVert S_2\rVert\lVert f\rVert`.
:::

The all-orders theorem supplies the qualitative lift for every $`m`, under the
correspondingly stronger chart and coefficient hypotheses.

:::definition "elliptic.solution_operator.all_orders" (parent := "elliptic.solution_operators") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.globalHigherSolveCLM, SobolevSpace.GraphSpace.BoundaryRegularity.globalHigherRegularity_hasHigherSolutionLift, SobolevSpace.GraphSpace.BoundaryRegularity.globalHigherSolveCLM_base") (uses := "elliptic.divergence.exists_unique, elliptic.regularity.all_orders, elliptic.solution_operator.closed_graph_lift")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "340-343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`m\in\mathbb N`, the all-orders qualitative theorem and uniqueness
of the weak solution produce a bounded linear map

$$`S_{m+2}:H^m(\Omega)\longrightarrow H^{m+2}(\Omega)`

under the corresponding chart, coefficient, and ellipticity assumptions.
The weak $`H^1_0` solver uses the canonical order-one restriction of the
$`W^{m+1,\infty}` coefficient bundle, while the unreduced bundle supplies
the derivatives used by the regularity theorem. The base-coordinate identity
characterizes the result without unfolding either restriction or the
closed-graph construction.
:::

:::theorem "elliptic.solution_operator.all_orders_estimate" (parent := "elliptic.solution_operators") (lean := "ContinuousLinearMap.le_of_opNorm_le") (uses := "elliptic.solution_operator.all_orders")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "340-343"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The all-orders solution map satisfies, for every $`f\in H^m(\Omega)`,

$$`\lVert S_{m+2}f\rVert_{H^{m+2}(\Omega)}
  \le\lVert S_{m+2}\rVert_{\mathrm{op}}\,
     \lVert f\rVert_{H^m(\Omega)}.`
:::

:::proof "elliptic.solution_operator.all_orders_estimate"
Qualitative regularity gives a unique higher-order representative for each
forcing.  Linearity follows from uniqueness of the base weak solution, and a
closed-graph argument upgrades the resulting linear map to a continuous
linear map.  Its standard operator-norm inequality is the asserted estimate.
:::

Evolution problems apply elliptic regularity at each time to a residual that
depends on time. Given a Bochner trajectory of weak solutions, the stationary
operator can be applied at almost every $`t`, and the questions are
measurability of the result and control of its norm.

:::theorem "elliptic.solution_operator.trajectory_data" (parent := "elliptic.solution_operators") (lean := "SobolevSpace.GraphSpace.exists_higherSolutionTrajectory_of_weak_solution") (uses := "elliptic.solution_operator.closed_graph_lift")
Let the right-hand side belong to $`L^2(\mu;H^m)\cap L^\infty(\mu;H^m)`
and the given weak-solution trajectory belong to $`L^2(\mu;H^1_0)`.
Assume the generic higher-order solver is available and the weak-solution
identity holds almost everywhere. Then there exists a trajectory in
$`L^2(\mu;H^{m+2})\cap L^\infty(\mu;H^{m+2})` whose base coordinate
agrees almost everywhere with the original weak solution and which obeys the
operator-norm estimate. The $`L^2` memberships are separate hypotheses
because the time measure may be infinite.
:::

:::proof "elliptic.solution_operator.trajectory_data"
Apply the stationary higher-order solution operator at almost every time.
The weak-solution identity and uniqueness identify its base coordinate with
the original trajectory. Measurability of the lifted map and the stationary
operator-norm bound give the Bochner representative, its essential-supremum
estimate, and the asserted almost-everywhere compatibility.
:::

The trajectory statement is an existence result. Behind it stands an operator:
the stationary solution operator lifts to a bounded linear map between Bochner
spaces, which is the object that the higher-regularity argument for the wave
equation composes with.

:::theorem "elliptic.solution_operator.bochner_lift" (parent := "elliptic.solution_operators") (lean := "SobolevSpace.GraphSpace.higherSolutionOperatorLp_apply_ae, SobolevSpace.GraphSpace.higherSolutionOperatorLp, SobolevSpace.GraphSpace.higherSolutionOperatorLp_base, SobolevSpace.GraphSpace.higherSolutionOperatorLp_memLp_top") (uses := "elliptic.solution_operator.trajectory_data")
For any measure $`\mu` on time, the generic higher-order solver acts on
Bochner trajectories as a bounded linear map

$$`
L^2(\mu;H^m(\Omega))
\longrightarrow
L^2(\mu;H^{m+2}(\Omega)).
`

It agrees almost everywhere with pointwise application of the stationary
solver, and its Sobolev base coordinate is almost everywhere the
corresponding weak solution. If $`\lVert r(t)\rVert_{H^m}\leq C` almost
everywhere, then the lifted trajectory belongs to
$`L^\infty(\mu;H^{m+2})` and satisfies

$$`
\lVert S_{m+2}r(t)\rVert_{H^{m+2}}
\leq \lVert S_{m+2}\rVert_{\mathrm{op}}\,C
`

almost everywhere.
:::

:::proof "elliptic.solution_operator.bochner_lift"
Lift the stationary continuous linear map pointwise to Bochner $`L^2`.
The standard functorial construction gives boundedness and almost-everywhere
agreement with pointwise application.  Composing with the base-coordinate
map yields the weak solution identity.  Finally, the stationary operator-norm
bound applied almost everywhere preserves the assumed $`L^\infty` envelope.
:::
