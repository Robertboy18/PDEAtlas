/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import PDE.Hyperbolic.Models.ForcedTransport
import PDE.Hyperbolic.Models.Transport
import Verso
import VersoBlueprint
import VersoManual

/-!
# Transport and characteristics

The constant-velocity transport equation, its characteristics,
representation formula, superposition laws, and classical uniqueness
theorem.
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
#doc (Manual) "Transport and Characteristics" =>

We follow Evans, §2.1. A constant velocity $`b` determines
the spacetime direction $`(1,b)`, and the characteristic through $`(t,x)` is
$`s\mapsto x+(s-t)b`. Integrating the source along this line gives the
representation formula; differentiating the formula recovers the equation.

:::group "hyperbolic.transport"
Transport and characteristics
:::

:::definition "hyperbolic.transport.operator" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportOperator") (uses := "foundations.operators.advection")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18-19"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a constant spatial velocity $`b`, the transport operator is the
Fréchet derivative in spacetime direction $`(1,b)`. Its codomain is an
arbitrary real normed space, so the same declaration applies to scalar
unknowns and systems.
:::

:::theorem "hyperbolic.transport.operator_coordinates" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportOperator_eq, TransportEquation.transportOperator_eq_timeDeriv_add_dot_spatialGradient") (uses := "hyperbolic.transport.operator, foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18-19"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The abstract directional derivative equals the familiar coordinate operator
$$`
\partial_t u + \sum_{i=1}^n b_i\,\partial_{x_i}u.
`
The first identity is vector-valued; the second identifies the scalar spatial
sum with $`b\cdot\nabla_xu`.
:::

:::proof "hyperbolic.transport.operator_coordinates"
Decompose the spacetime direction $`(1,b)` into its time basis vector and
spatial coordinate directions. Linearity of the Fréchet derivative gives the
time partial plus the weighted spatial partials; in the scalar case the
finite sum is the Euclidean inner product with the gradient.
:::

The operator by itself fixes only the equation; the Cauchy problem adds a
prescribed value on the hyperplane $`t=0`.

:::definition "hyperbolic.transport.ivp" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportIVP") (uses := "hyperbolic.transport.operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The source-parametric initial-value problem consists of
$`u_t+b\cdot\nabla_xu=f` on $`t>0` and $`u(0,x)=g(x)`. Homogeneous
transport is the specialization $`f=0`.
:::

:::theorem "hyperbolic.transport.problem_interface" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportIVP.residual_eq, TransportEquation.transportIVP.initial_eq, TransportEquation.transportIVP.of_residual_initial, TransportEquation.transportIVP_iff") (uses := "hyperbolic.transport.ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The initial-value problem is equivalent to two clauses: the transport
residual on positive time and the assigned value on $`t=0`.
:::

:::proof "hyperbolic.transport.problem_interface"
Unfold the initial-value predicate. Its two fields are precisely the
positive-time residual equation and the assigned initial value, so projection proves
one direction and pairing the two clauses constructs the converse.
:::

Linearity gives the usual reduction of uniqueness to the homogeneous problem
with zero initial value.

:::theorem "hyperbolic.transport.superposition" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportIVP_zero, TransportEquation.transportIVP_add, TransportEquation.transportIVP_const_mul, TransportEquation.transportIVP_neg, TransportEquation.transportIVP_sub, TransportEquation.transportIVP_linear_combination, TransportEquation.transportIVP_difference_same_initial_homogeneous") (uses := "hyperbolic.transport.problem_interface")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix $`b` and assume $`u` and $`v` are Fréchet differentiable at every
spacetime point with $`t>0`. The residual is linear on positive time, and
initial evaluation respects the same combination:

$$`
L_b(\alpha u+\beta v)=\alpha L_bu+\beta L_bv,\qquad
(\alpha u+\beta v)(0,\cdot)=\alpha g_u+\beta g_v.
`

Consequently zero, addition, scalar multiplication, negation, subtraction,
and arbitrary binary linear combinations preserve the corresponding source
and assigned initial data. In particular, two sufficiently differentiable
solutions with the same source and assigned value have a difference
$`w=u-v` satisfying $`L_bw=0` and $`w(0,\cdot)=0`.
:::

:::proof "hyperbolic.transport.superposition"
At positive-time points, differentiability of the fields justifies applying
the Fréchet derivative to their linear combination. Evaluation at the initial
surface respects the same combination, giving the corresponding sources and
assigned values. Subtracting equal data gives the homogeneous zero-trace
problem. The zero and negation identities also hold without differentiability.
:::

The first explicit solution concerns the homogeneous case $`f=0`. The field
$`u(t,x)=g(x-tb)` is constant along every line of direction $`(1,b)`, so its
time derivative exactly cancels the advection term.

:::theorem "hyperbolic.transport.characteristic_solution" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportFunction_satisfiesPDEProblem") (uses := "hyperbolic.transport.ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18-19"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For differentiable initial data, translation along $`x-tb` solves the
homogeneous specialization of {uses "hyperbolic.transport.ivp"}[], including
its initial trace.
:::

:::proof "hyperbolic.transport.characteristic_solution"
The proof differentiates the affine foot map, applies the chain rule to
$`g(x-tb)`, and cancels the time derivative against the spatial advection.
:::

The translation $`x-tb` in that solution is the point where the line of
direction $`(1,b)` through $`(t,x)` meets the initial hyperplane. Naming this
line, with its parametrization by time, reduces the forced problem to an
ordinary differential equation along it.

:::definition "hyperbolic.transport.characteristic" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportCharacteristic") (uses := "hyperbolic.transport.operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The characteristic through $`(t,x)` is
$`s\mapsto(s,x+(s-t)b)`. It joins the initial foot $`(0,x-tb)` to
$`(t,x)` and has constant spacetime velocity $`(1,b)`.
:::

:::theorem "hyperbolic.transport.characteristic_chain_rule" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportCharacteristic_zero, TransportEquation.transportCharacteristic_self, TransportEquation.hasDerivAt_transportCharacteristic, TransportEquation.hasDerivAt_comp_transportCharacteristic") (uses := "hyperbolic.transport.characteristic, hyperbolic.transport.operator_coordinates")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Along $`\gamma_{t,x}(s)=(s,x+(s-t)b)`, a differentiable profile obeys

$$`
\frac d{ds}u(\gamma_{t,x}(s))
=\partial_tu(\gamma_{t,x}(s))
+b\cdot\nabla_xu(\gamma_{t,x}(s))
=(L_bu)(\gamma_{t,x}(s)).
`

The endpoint identities $`\gamma_{t,x}(0)=(0,x-tb)` and
$`\gamma_{t,x}(t)=(t,x)` are part of the statement.
:::

:::proof "hyperbolic.transport.characteristic_chain_rule"
The affine characteristic has derivative $`(1,b)`. The chain rule evaluates
$`Du` on this direction, which is the transport operator by its coordinate
identity. Substituting $`s=0` and $`s=t` gives the two endpoints.
:::

For a solution of the forced problem the chain rule along a characteristic
reads $`\frac d{ds}u(\gamma_{t,x}(s))=f(\gamma_{t,x}(s))`. Integrating from
$`s=0`, where the curve sits at the initial foot, to $`s=t` produces the
representation formula, which is thus a consequence of the equation rather
than a separate ansatz.

:::theorem "hyperbolic.transport.representation" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportIVP_representation, TransportEquation.transportIVP_representation_of_continuous") (uses := "hyperbolic.transport.problem_interface, hyperbolic.transport.characteristic_chain_rule")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u` satisfy the transport residual and initial-value clauses, and let
$`t\geq0`. Assume $`u` is Fréchet differentiable in spacetime at
$`\gamma_{t,x}(s)` for every $`s\in[0,t]`, including the endpoints, and
$`s\mapsto f(\gamma_{t,x}(s))` is interval integrable on $`[0,t]`. Then
$$`
u(t,x)=g(x-tb)+\int_0^t f(s,x+(s-t)b)\,ds.
`
The continuous-source variant obtains these hypotheses from global
Fréchet differentiability of $`u` and continuity of $`f`.
:::

:::proof "hyperbolic.transport.representation"
Ambient differentiability of $`u` along the closed characteristic segment
gives continuity of its pullback on $`[0,t]`. On $`(0,t)`, the chain rule
and the residual equation give derivative $`f(\gamma_{t,x}(s))`. Its interval
integrability permits the fundamental theorem of calculus; the endpoint
identities and assigned initial value then give the formula.
:::

The right-hand side of the representation depends only on the data $`b`, $`f`,
and $`g`, not on the solution $`u` it was derived from. Detaching it gives an
explicit spacetime field whose properties can be checked directly: that it
solves the problem for differentiable data, and that every sufficiently
regular solution coincides with it.

:::definition "hyperbolic.transport.solution_formula" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportSolutionFormula, TransportEquation.transportSolutionFormula_apply_characteristic, TransportEquation.transportSolutionFormula_eq_coordinates") (uses := "hyperbolic.transport.characteristic")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The explicit spacetime function is

$$`
\mathcal S_{b,f,g}(t,x)
=g(x-tb)+\int_0^t f\bigl(s,x+(s-t)b\bigr)\,ds.
`

Pulling $`\mathcal S_{b,f,g}` back to a characteristic gives
the initial value plus the accumulated source, while the coordinate theorem
separates the footpoint $`x-tb` from time.
:::

:::theorem "hyperbolic.transport.formula_solves" (parent := "hyperbolic.transport") (lean := "TransportEquation.transportSolutionFormula_initial, TransportEquation.hasDerivAt_transportSolutionFormula_characteristic, TransportEquation.transportOperator_transportSolutionFormula, TransportEquation.differentiableAt_transportSolutionFormula, TransportEquation.differentiable_transportSolutionFormula, TransportEquation.transportSolutionFormula_satisfiesPDEProblem_of_differentiable, TransportEquation.transportSolutionFormula_satisfiesPDEProblem") (uses := "hyperbolic.transport.solution_formula, hyperbolic.transport.problem_interface")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For differentiable $`g` and a $`C^1` source, the explicit formula is
differentiable, has initial trace $`g`, and satisfies the forced transport
equation. When the source is only continuous, a variant takes
differentiability of the formula as a hypothesis and reaches the same
conclusion.
:::

:::proof "hyperbolic.transport.formula_solves"
First write the formula in the adapted coordinates $`(t,\xi)=(t,x-tb)`:
$`g(\xi)+\int_0^t f(s,\xi+sb)\,ds`. Since $`f` is $`C^1`, the integrand
and its derivative with respect to $`\xi` are continuous. On a compact
neighborhood of the parameter and time segment, this derivative is uniformly
bounded, so the parametric integral rule proves spacetime differentiability.
Adding differentiable $`g` and composing with the linear coordinate map
preserves it. Restricted to a characteristic, the formula has derivative equal
to the source by the fundamental theorem of calculus. The characteristic
chain rule then identifies that derivative with the transport operator, and
setting $`t=0` gives the assigned initial value.
:::

Uniqueness needs only the representation theorem: global differentiability
lets it be applied along every characteristic at once.

:::theorem "hyperbolic.transport.uniqueness" (parent := "hyperbolic.transport") (lean := "TransportEquation.eq_transportSolutionFormula, TransportEquation.transportIVP_unique") (uses := "hyperbolic.transport.representation, hyperbolic.transport.solution_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "19-20"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every globally differentiable solution with continuous source satisfies, for
$`t\geq0`,

$$`
u(t,x)=\mathcal S_{b,f,g}(t,x)
=g(x-tb)+\int_0^t f\bigl(s,x+(s-t)b\bigr)\,ds.
`

Consequently, if $`u` and $`v` have the same $`b`, $`f`, and $`g`, then
$`u(t,x)=v(t,x)` throughout the nonnegative-time domain.
:::

:::proof "hyperbolic.transport.uniqueness"
The representation theorem identifies every solution with the explicit
formula determined by $`b`, $`f`, and $`g`. Two solutions with the same data
are therefore both equal to that formula and hence equal to each other.
:::
