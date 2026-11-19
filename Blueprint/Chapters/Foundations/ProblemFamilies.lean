/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Verso
import VersoManual
import VersoBlueprint
import Blueprint.Commands.Figures
import PDE.Common.Euclidean
import PDE.FDeriv.SpaceTime.Gradient.Basic
import PDE.Problem.Family.WellPosedness

/-!
# Problem families and Euclidean space

Representative PDE families and their well-posedness vocabulary.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Problem families and Euclidean space" =>

Evans's Chapters 1–2 introduce representative first- and second-order
equations and develop the potential theory of Laplace's equation. We begin
with the distinction between an equation and a well-posed family of problems.

# Problem families and well-posedness

We use one small boundary-value problem to keep the abstract definition of
well-posedness concrete:

$$`
-u''=f\quad\text{on }(0,1),\qquad u(0)=u(1)=0.
`

Take the data space to be $`C([0,1])` with the uniform norm
$`\|f\|_\infty=\max_{[0,1]}|f|`. Take the solution space to be
$`C([0,1])` with the same norm, and admit only twice continuously
differentiable functions satisfying the two endpoint conditions.
These are choices: the equation alone does not specify them.

*Existence* has an explicit answer. Integrating twice and choosing the
integration constants to enforce the endpoints gives

$$`
u_f(x)=(1-x)\int_0^x y f(y)\,dy
       +x\int_x^1(1-y)f(y)\,dy.
`

Differentiating this expression gives $`u_f''=-f`, and substitution gives
both endpoint values. For the constant forcing $`f=1`, it reduces to
$`u_f(x)=x(1-x)/2`: a positive arch whose downward curvature balances the
positive right-hand side. *Uniqueness* is just as concrete. The difference
of two solutions has second derivative zero, so it is affine; an affine
function vanishing at both endpoints is zero.

For *continuous dependence*, write the same formula as
$`u_f(x)=\int_0^1G(x,y)f(y)\,dy`, where
$`G(x,y)=\min(x,y)(1-\max(x,y))\geq0`. Then

$$`
\begin{aligned}
|u_f(x)-u_g(x)|
&\leq \|f-g\|_\infty\int_0^1G(x,y)\,dy\\
&=\frac{x(1-x)}2\|f-g\|_\infty,\\
\|u_f-u_g\|_\infty&\leq\frac18\|f-g\|_\infty.
\end{aligned}
`

{leanpde_figure "interval-green-function"}

Thus the solution map is Lipschitz, hence continuous, in the specified
uniform topologies. The figure draws the tents $`G(x,\cdot)` whose integrals
produce the arch $`x(1-x)/2`, and a difference $`u_f-u_g` confined to the
band that this arch bounds. This estimate measures changes in the values of $`u`;
an estimate in a norm containing derivatives would be a further statement.
The calculation is informal; it illustrates the three clauses of the
definition. Without the endpoint
conditions, arbitrary affine functions could be added and uniqueness would
fail. Without the two topologies, the continuous-dependence clause would
not yet say what is being controlled.

:::group "foundations.well_posedness"
Well-posedness
:::

:::definition "foundations.well_posedness.global" (parent := "foundations.well_posedness") (lean := "PDE.Problem.WellPosed") (uses := "foundations.pde_problems.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "7"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Equip $`\mathcal D` and $`X` with topologies. Global Hadamard well-posedness
for a data-dependent admissible class $`\mathcal S_d\subseteq X` means that
there is a solution operator

$$`
  S:\mathcal D\longrightarrow X
`

with three precise properties:

$$`
\begin{aligned}
&S(d)\in\mathcal S_d
  \text{ and }\operatorname{realize}(S(d))\models P_d
  &&\text{for every }d,\\
&u,v\in\mathcal S_d\text{ and }u,v\text{ solve }P_d
  \Longrightarrow u=v
  &&\text{for every }d,\\
&S:\mathcal D\to X\text{ is continuous}. &&
\end{aligned}
`

The realization map $`X\to(E\to F)` keeps the topology and equality of the
solution space separate from the raw field tested by `PDEProblem`. Thus $`X`
may be a Sobolev, Hölder, energy, quotient, or classical space. Equality in
$`X` must already encode the intended representative convention.

`WellPosed` is a single proposition. Its existential witness is the
continuous solution operator; admissibility, the residual equations, and
uniqueness are clauses of that proposition.
:::

:::theorem "foundations.well_posedness.global_exists" (parent := "foundations.well_posedness") (lean := "PDE.Problem.WellPosed.exists_solution") (uses := "foundations.well_posedness.global")
Every globally well-posed family has an admissible solution for every datum:

$$`
  \operatorname{WellPosed}(P,\mathcal S)
  \quad\Longrightarrow\quad
  \forall d,\ \exists u\in\mathcal S_d,\
  \operatorname{realize}(u)\models P_d.
`
:::

:::proof "foundations.well_posedness.global_exists"
Unpack the continuous solution operator $`S` from the well-posedness
hypothesis and choose $`S(d)`.
:::

Existence uses the solution operator and its admissibility clause but not
its continuity. Uniqueness is the remaining clause, and it applies to
arbitrary admissible solutions $`u,v\in\mathcal S_d`, not only to the value
$`S(d)` supplied by the operator.

:::theorem "foundations.well_posedness.global_unique" (parent := "foundations.well_posedness") (lean := "PDE.Problem.WellPosed.unique") (uses := "foundations.well_posedness.global")
Two admissible solutions for the same datum are equal:

$$`
  u,v\in\mathcal S_d,\quad
  \operatorname{realize}(u)\models P_d,\quad
  \operatorname{realize}(v)\models P_d
  \quad\Longrightarrow\quad
  u=v.
`
:::

:::proof "foundations.well_posedness.global_unique"
Unpack the uniqueness clause of `WellPosed` and apply it to $`u` and $`v`.
:::

:::group "foundations.euclidean_space"
Euclidean and spacetime foundations
:::

:::definition "foundations.euclidean_space.type" (parent := "foundations.euclidean_space") (lean := "EuclideanSpace")
We use Mathlib's Euclidean space directly:

$$`
  \mathbb R^n=\{x:\operatorname{Fin}(n)\to\mathbb R\},
  \qquad
  \lVert x\rVert^2=\sum_{i=1}^n x_i^2.
`

The inner product, topology, measure, and continuous-linear-map structure
all come from Mathlib.
:::

Identifying $`\mathbb R^n` with coordinate functions is an equivalence of
underlying types, not an isometry: the left side carries the Euclidean norm,
while Mathlib equips the product type on the right with the supremum norm.
Coordinate manipulations therefore pass through this equivalence explicitly
rather than by definitional unfolding.

:::definition "foundations.euclidean_space.constructor" (parent := "foundations.euclidean_space") (lean := "WithLp.equiv") (uses := "foundations.euclidean_space.type")
The canonical coordinate equivalence is

$$`
  \mathbb R^n\simeq(\operatorname{Fin}(n)\to\mathbb R),
  \qquad x\longmapsto(i\mapsto x_i).
`

Mathlib provides it as `WithLp.equiv 2 (Fin n → ℝ)`; the inverse
`WithLp.toLp 2` constructs a Euclidean point from its coordinate function.
:::

Evolution equations single out one coordinate for time. Rather than
introducing a product $`\mathbb R\times\mathbb R^n`, we keep
spacetime inside the same Euclidean family as $`\mathbb R^{n+1}`, so that
every coordinate operator defined on Euclidean space applies to spacetime
fields unchanged. Prepending the time coordinate to the spatial ones is done
through the coordinate equivalence just described.

:::definition "foundations.euclidean_space.spacetime" (parent := "foundations.euclidean_space") (lean := "PDE.Common.timeSpaceCons") (uses := "foundations.euclidean_space.constructor")
For $`t\in\mathbb R` and $`x\in\mathbb R^n`, spacetime is assembled as

$$`
  (t,x)\in\mathbb R^{n+1},
  \qquad
  (t,x)_0=t,\quad (t,x)_{i+1}=x_i.
`

`timeSpaceCons t x` implements this convention for the heat, wave, transport,
and conservation-law interfaces.
:::

Assembling a point is half of the convention; the projections that undo it are
what theorem statements use.

:::definition "foundations.euclidean_space.time" (parent := "foundations.euclidean_space") (lean := "PDE.time, PDE.time_apply, PDE.Common.timeSpaceCons_zero") (uses := "foundations.euclidean_space.spacetime")
The time projection is

$$`
  \operatorname{time}(z):=z_0,
  \qquad
  \operatorname{time}(t,x)=t.
`

`time` is an ordinary function on $`\mathbb R^{n+1}`, so theorem statements
use it with no symbolic-expression layer.
:::

:::definition "foundations.euclidean_space.spatial_projection" (parent := "foundations.euclidean_space") (lean := "PDE.Common.spatialPart, PDE.Common.spatialPart_timeSpaceCons, PDE.Common.timeSpaceCons_spatialPart, PDE.Common.spatialPartCLM, PDE.Common.spatialPartCLM_eq_spatialPart") (uses := "foundations.euclidean_space.spacetime")
The spatial projection discards coordinate zero:

$$`
  \operatorname{space}(z)_i:=z_{i+1},
  \qquad
  \operatorname{space}(t,x)=x,
  \qquad
  (\operatorname{time}z,\operatorname{space}z)=z.
`

`spatialPart` is the plain function and `spatialPartCLM` the extensionally
equal continuous linear map; derivative arguments use the bundled map.
:::
