/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Foundations.DifferentialOperators
import PDE.Elliptic.Classical.Poisson.Problem
import PDE.FDeriv.LinearPDE
import PDE.Problem.Equation.Satisfaction

/-!
# PDE problem interfaces

The reusable problem, solution, boundary, and initial-data interfaces.
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
#doc (Manual) "PDE problems" =>

A PDE problem is syntax, and the analytic theorem that solves it is a
separate statement. An equation records an operator, a right-hand side, and the set
on which their values are required to agree. A problem records finite lists of
interior equations and designated initial or boundary equations. Satisfaction
then says that a chosen field obeys each stored identity pointwise.
Regularity, existence, uniqueness, trace interpretations, and weak
formulations are separate propositions.

The residual interface assumes no algebraic structure. Its ambient type $`E`,
value type $`F`, and residual types $`G` are arbitrary types. A concrete
differential operator may require normed spaces, derivatives, measures, or
traces, but those hypotheses belong to that operator and its theorems rather
than to the generic record used to store it. The same problem language
therefore covers classical differential equations, algebraic constraints,
systems, and boundary observations.

The finite-jet interface explains what it means for a differential operator
to have bounded order. For a field $`u:E\to F`, its jet at $`x` is the family
$`(D^j u(x))_{j\geq0}` of continuous multilinear derivatives. An operator has
order at most $`k` when its value at $`x` depends only on the terms with
$`j\leq k`. The `LinearPDE` interface combines this locality law with
linearity on sufficiently regular fields. The lighter `PDEProblem` interface
is used for concrete residual systems and examples.

In one variable, the second jet is simply the local data
$`(u(x),u'(x),u''(x))`. The operator in $`-u''=f` reads its third entry;
the equation compares that value with $`f(x)`. The endpoint conditions read
the first entry at $`0` and $`1`. Storing all three requirements gives a
boundary-value problem. Proving that a particular twice differentiable
function meets them gives a classical solution. Neither the jet nor the
problem record performs that proof.

:::group "foundations.pde_problems"
PDE problem interfaces
:::

:::definition "foundations.pde_problems.jet" (parent := "foundations.pde_problems") (lean := "FormalMultilinearSeries") (uses := "foundations.derivatives.iterated")
For normed spaces $`E` and $`F` over $`\mathbb K`, a formal Fréchet jet is a
sequence

$$`
  J=(J_j)_{j\geq0},
  \qquad J_j\in\mathcal L^j_{\mathbb K}(E;F),
`

where $`\mathcal L^j_{\mathbb K}(E;F)` denotes the continuous $`j`-linear
maps from $`E^j` to $`F`. Mathlib represents this sequence by
`FormalMultilinearSeries`. The totalized jet of $`u:E\to F` at $`x` is
`ftaylorSeries 𝕜 u x`, with

$$`
  J_j=D^j u(x).
`
:::

A differential operator of order $`k` should be blind to the entries $`J_j`
with $`j>k`. Expressing this blindness requires a relation on fields that
compares only the first $`k+1` derivatives at a point.

:::definition "foundations.pde_problems.jet_locality" (parent := "foundations.pde_problems") (lean := "PDE.SameJetUpTo") (uses := "foundations.pde_problems.jet")
Two fields have the same $`k`-jet at $`x` precisely when

$$`
  u\sim_x^k v
  \quad\Longleftrightarrow\quad
  D^j u(x)=D^j v(x)\ \text{ for every }0\leq j\leq k.
`

The predicate `SameJetUpTo` is this relation. It lets an operator state
finite-order locality without choosing coordinates or expanding derivatives
into multi-indices.
:::

The relation becomes the locality field of the linear PDE record.

:::definition "foundations.pde_problems.linear_class" (parent := "foundations.pde_problems") (lean := "PDE.LinearPDE") (uses := "foundations.pde_problems.jet_locality")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "3-6"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A linear PDE of order at most $`k` consists of an operator $`L`, a right-hand side
$`f`, and a domain $`\Omega`, representing

$$`
  Lu=f\qquad\text{on }\Omega.
`

For $`C^k` fields it records the linearity laws

$$`
  L(u+v)=Lu+Lv,
  \qquad L(cu)=c\,Lu,
`

and, for fields that are $`C^k` at $`x`, the locality law

$$`
  u\sim_x^k v\quad\Longrightarrow\quad Lu(x)=Lv(x).
`

The regularity qualification is essential: Mathlib's totalized derivatives
are not linear on arbitrary nondifferentiable functions.

The stored operator and `LinearPDE.residual` are nevertheless total Lean
expressions. Evaluating them does not certify regularity or domain membership;
those hypotheses belong to the classical or weak solution theorem that uses
the expression.
:::

The `LinearPDE` record carries analytic laws that presuppose normed spaces and
a scalar field. Systems, algebraic constraints, and boundary observations need
none of that structure, so the generic equation record stores only an
operator, a right-hand side, and a set, and imposes no laws at all.

:::definition "foundations.pde_problems.equation" (parent := "foundations.pde_problems") (lean := "PDE.PDEEquation")
An equation over fields $`u:E\to F` stores a residual type $`G`, an operator
$`\mathcal P:(E\to F)\to E\to G`, a right-hand side $`g:E\to G`, and a set
$`\Omega\subseteq E`. Its intended assertion is

$$`
  \mathcal P[u](x)=g(x)\qquad(x\in\Omega).
`

The residual type is stored inside each `PDEEquation`. Consequently one
problem can combine scalar, vector, tensor, and proposition-valued residuals
without forcing them into a common codomain.
:::

An equation is a syntactic object, and satisfaction is a separate predicate.

:::definition "foundations.pde_problems.equation_solution" (parent := "foundations.pde_problems") (lean := "Set.EqOn") (uses := "foundations.pde_problems.equation")
A field $`u:E\to F` satisfies an equation $`e` exactly when

$$`
  \forall x\in\Omega_e,\qquad
  \mathcal P_e[u](x)=g_e(x).
`

Lean expresses this directly as
`Set.EqOn (e.operator u) e.rhs e.domain`, a pointwise residual identity on
the stored set. In particular, it does not say that $`u` is differentiable, even when
$`\mathcal P_e` was written using Mathlib's totalized derivative operators; any
required differentiability must appear in a stronger solution class or in a
separate hypothesis.
:::

A single equation cannot express a boundary value problem: the interior
identity and the boundary identity live on different sets and may take values
in different residual types. A bundled problem collects finitely many
equations, each with its own domain and codomain, and keeps the designated
side conditions in a separate list.

:::definition "foundations.pde_problems.problem" (parent := "foundations.pde_problems") (lean := "PDE.PDEProblem") (uses := "foundations.pde_problems.equation")
A bundled problem is a finite system

$$`
  \mathcal P_r[u](x)=g_r(x)
  \quad(x\in\Omega_r,\ 1\leq r\leq m),
`

together with a second finite system of side conditions. `PDEProblem` stores
these systems in the lists `eqns` and `sideConditions`. Write $`\mathcal E_P`
for all the equations in these two lists.

The designation of the second list is organizational rather than semantic.
The same typed equation record occurs in both lists, and its domain need not
literally be a topological boundary or a time slice. Weak, variational,
trace-based, and almost-everywhere interpretations are introduced separately
in the analytic chapters whose solution spaces support them.
:::

Satisfaction of a bundled problem treats interior equations and side
conditions identically.

:::definition "foundations.pde_problems.solution" (parent := "foundations.pde_problems") (lean := "PDE.SatisfiesPDEProblem") (uses := "foundations.pde_problems.equation_solution, foundations.pde_problems.problem")
A field $`u:E\to F` satisfies a bundled problem when every stored equation
holds on its own domain:

$$`
  \operatorname{Solves}(P,u)
  \quad\Longleftrightarrow\quad
  \forall e\in\mathcal E_P,\qquad u\models e.
`

Expanding the equation predicate gives

$$`
  \forall e\in\mathcal E_P,\
  \forall x\in\Omega_e,\qquad
  \mathcal P_e[u](x)=g_e(x).
`

This is exactly `SatisfiesPDEProblem P u`.
:::

Quantifying over the concatenation is convenient for the definition but
awkward in proofs, which typically establish the interior equations and the
side conditions by different arguments. The equivalence with two separate
universal statements restores the two-list structure without altering what
satisfaction means.

:::theorem "foundations.pde_problems.solution_iff" (parent := "foundations.pde_problems") (lean := "PDE.satisfiesPDEProblem_iff_eqns_side_conditions") (uses := "foundations.pde_problems.solution")
The solution predicate splits exactly along the two stored lists:

$$`
  \operatorname{Solves}(P,u)
  \quad\Longleftrightarrow\quad
  \left(\forall e\in P_{\mathrm{eq}},\ u\models e\right)
  \land
  \left(\forall e\in P_{\mathrm{side}},\ u\models e\right).
`

Pointwise PDE examples use this equivalence to establish or to use
satisfaction one list at a time.
:::

:::proof "foundations.pde_problems.solution_iff"
Unfolding the solution predicate says that every equation in the concatenated
equation and boundary-condition lists is satisfied. Membership in this
concatenation splits into membership in either list, yielding the two
universal conditions; conversely the two conditions cover every member of
the concatenation.
:::

# Example: the Poisson equation on a ball

For a concrete solution, take $`f=2n` and $`u(x)=1-|x|^2`.
Each coordinate contributes $`2` to $`\Delta|x|^2`, so
$`-\Delta u=2n` throughout the ball. On the unit sphere,
$`u=1-1=0`. These are the two checks the bundled problem asks for:
the differential equation on the open ball and the value equation on its
boundary. Since $`u` is smooth it is a classical solution; its smoothness is
proved about $`u` directly and is not part of the problem record.

:::definition "foundations.pde_problems.poisson_unit_ball" (parent := "foundations.pde_problems") (lean := "PoissonEquation.unitBallDirichletProblem") (uses := "foundations.pde_problems.problem, foundations.operators.laplacian")
For $`f:\mathbb R^n\to\mathbb R`, the unit-ball homogeneous Dirichlet problem
is the bundled `PDEProblem`

$$`
-\Delta u=f\quad\text{in }B_1(0),
\qquad
u=0\quad\text{on }\partial B_1(0).
`

The equation list contains the residual $`-\Delta u=f` on the open unit
ball. The boundary-condition list contains the identity equation $`u=0` on
the unit sphere.
:::

:::theorem "foundations.pde_problems.poisson_unit_ball_iff" (parent := "foundations.pde_problems") (lean := "PoissonEquation.unitBallDirichletProblem_iff") (uses := "foundations.pde_problems.poisson_unit_ball, foundations.pde_problems.solution")
A field $`u:\mathbb R^n\to\mathbb R` satisfies the bundled problem exactly
when it satisfies both pointwise clauses:

$$`
\operatorname{Satisfies}(P_f,u)
\iff
\left(\forall x\in B_1(0),\ -\Delta u(x)=f(x)\right)
\land
\left(\forall x\in\partial B_1(0),\ u(x)=0\right).
`
:::

:::proof "foundations.pde_problems.poisson_unit_ball_iff"
The forward implication projects the sole interior equation and sole boundary
condition from `SatisfiesPDEProblem`. Conversely, the two pointwise
hypotheses discharge the sole member of each singleton list through the generic
satisfaction constructor.
:::
