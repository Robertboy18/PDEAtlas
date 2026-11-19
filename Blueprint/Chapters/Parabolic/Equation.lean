/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import PDE.Parabolic.Heat.Equation
import PDE.Parabolic.Heat.InitialValueProblem
import Verso
import VersoBlueprint
import VersoManual

/-!
# The heat operator and classical problem interfaces

The heat operator on spacetime and the bundled classical heat problems.
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
#doc (Manual) "The Heat Operator and Classical Problems" =>

The classical heat equation couples a first time derivative to a second
spatial derivative. This asymmetry determines the geometry of the problem:
time has a preferred direction, initial data live on the time-zero face, and
the spatial Laplacian acts on each fixed-time slice. Coordinate zero is time
throughout.

The declarations here state equations and initial traces. Explicit
whole-space solutions come from the Gaussian kernel and Duhamel's formula, and
the variational theory replaces pointwise derivatives by Bochner-space
identities on bounded domains.

# The spacetime operator

:::definition "parabolic.heat_operator" (parent := "parabolic.classical") (lean := "HeatEquation.heatOperator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "44-45"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
With coordinate zero reserved for time, the classical heat operator on
$`\mathbb R\times\mathbb R^n` is

$$`Hu=\partial_tu-\Delta_xu.`

`HeatEquation.heatOperator` is an ordinary function on Euclidean spacetime.
It computes the time-coordinate partial derivative and the Laplacian of the
fixed-time spatial slice. Like Mathlib's Fréchet derivative, it is defined
for every `u`, and the analytic theorems state the regularity they need.
:::

:::theorem "parabolic.heat_operator_linearity" (parent := "parabolic.classical") (lean := "HeatEquation.heatOperator_add, HeatEquation.heatOperator_const_mul") (uses := "parabolic.heat_operator")
Suppose $`u` and $`v` are differentiable at $`z=(t,x)` and their fixed-time
spatial slices are $`C^2` at $`x`. Then the heat operator preserves their
sum at $`z`. It also commutes with multiplication by a real constant:

$$`
  H(u+v)=Hu+Hv,\qquad H(cu)=c\,Hu.
`

The scalar identity holds without regularity assumptions on $`u`, using the
total derivative operators. These two calculus lemmas supply the
superposition results for the homogeneous, forced, and initial-value problems.
:::

:::proof "parabolic.heat_operator_linearity"
Expand $`H=\partial_t-\Delta_x`. For a sum, apply the pointwise sum rules to
the time derivative and to the Laplacian of the fixed-time spatial slices,
then collect terms. For a scalar multiple, pull the constant through both
operators and distribute it across the difference.
:::

# Bundled classical problems

:::definition "parabolic.heat_problem" (parent := "parabolic.classical") (lean := "HeatEquation.heatEquation, HeatEquation.nonhomogeneousHeatEquation") (uses := "parabolic.heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "44-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a spacetime set $`U`, the homogeneous and forced residual problems are

$$`Hu=0\quad\text{and}\quad Hu=f\qquad\text{on }U.`

They are represented by `PDEProblem` values so that explicit formulas and
symbolic calculations can target the same ordinary Lean proposition. The
problem values contain only equations and domains; differentiability,
existence, uniqueness, and boundary regularity belong to separate theorems.
:::

The calculus lemmas for $`H` reach the bundled problems through a
characterization of satisfaction.

:::theorem "parabolic.heat_problem_characterization" (parent := "parabolic.classical") (lean := "HeatEquation.heatEquation_iff, HeatEquation.nonhomogeneousHeatEquation_iff") (uses := "parabolic.heat_problem")
Satisfaction of either bundled problem is equivalent to its pointwise heat
operator identity:

$$`
  u\models\operatorname{Heat}(f,U)
  \quad\Longleftrightarrow\quad
  \forall z\in U,\ H u(z)=f(z),
`

with $`f=0` for the homogeneous problem. The forward and reverse directions
are also exposed as projection and constructor theorems.
:::

:::proof "parabolic.heat_problem_characterization"
Unfold satisfaction of the bundled `PDEProblem`. Its equation field is
defined pointwise as $`Hu(z)=f(z)` on the stored domain $`U`, so a witness of
satisfaction immediately projects to the displayed identity. Conversely,
the pointwise identity fills the sole equation field of the problem witness.
The homogeneous statement is the specialization $`f=0`.
:::

Through that equivalence, linearity of $`H` becomes closure of the solution
sets.

:::theorem "parabolic.heat_superposition" (parent := "parabolic.classical") (lean := "HeatEquation.heatEquation_const, HeatEquation.heatEquation_add, HeatEquation.heatEquation_const_mul, HeatEquation.heatEquation_sub, HeatEquation.heatEquation_linear_combination, HeatEquation.nonhomogeneousHeatEquation_add, HeatEquation.nonhomogeneousHeatEquation_const_mul, HeatEquation.nonhomogeneousHeatEquation_sub, HeatEquation.nonhomogeneousHeatEquation_linear_combination") (uses := "parabolic.heat_problem")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "44-45"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Constant functions solve the homogeneous equation. Under the regularity
assumptions of {bpref "parabolic.heat_operator_linearity"}[] at every point of
$`U`, sums, differences, and real linear combinations of homogeneous solutions
are again solutions. More generally, if
$`H u=f` and $`H v=g`, then
$$`
  H(au+bv)=af+bg.
`
Multiplication of a solution by a constant needs no additional regularity.
:::

:::proof "parabolic.heat_superposition" (uses := "parabolic.heat_operator_linearity")
Apply the pointwise linearity of the heat operator and then substitute the
residual equations for the two solutions. The homogeneous results are the
zero-forcing specializations.
:::

Cauchy data add a condition on the time-zero slice.

:::definition "parabolic.heat_ivp" (parent := "parabolic.classical") (lean := "HeatEquation.heatResidualAssignedInitialValueProblem, HeatEquation.forcedHeatResidualAssignedInitialValueProblem") (uses := "parabolic.heat_problem")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-51"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The homogeneous and forced residual problems combine the positive-time
equation with an assigned value on the time-zero hyperplane:

$$`Hu=0\ \text{or}\ f\quad(t>0),\qquad u(0,x)=g(x).`

The second clause is an equality on the time-zero slice. Continuity up to
time zero and convergence of a representation formula to $`g` are separate
analytic conclusions, proved for the kernel and Duhamel solutions.
:::

:::theorem "parabolic.heat_ivp_characterization" (parent := "parabolic.classical") (lean := "HeatEquation.heatResidualAssignedInitialValueProblem_iff, HeatEquation.forcedHeatResidualAssignedInitialValueProblem_iff") (uses := "parabolic.heat_ivp")
Each bundled problem is equivalent to the conjunction of its heat-operator
identity at positive times and its assigned time-zero value:

$$`
  u\models\operatorname{HeatResidualAssigned}(f,g)
  \quad\Longleftrightarrow\quad
  \bigl(\forall t>0,\ \forall x,\ Hu(t,x)=f(t,x)\bigr)
  \ \land\
  \bigl(\forall x,\ u(0,x)=g(x)\bigr).
`
:::

:::proof "parabolic.heat_ivp_characterization"
Unfold the bundled initial-value problem. Satisfaction consists of exactly two
fields: satisfaction of the positive-time heat problem and satisfaction of
the time-zero initial condition. Apply the heat-problem characterization to
the first field and unfold the second to obtain the conjunction. Conversely,
the two conjuncts construct those two fields and hence the bundled IVP
witness.
:::

For sums and general linear combinations of Cauchy problems, the
differentiability and spatial $`C^2` assumptions are needed only on the
half-space $`t>0`, where the residual lives.

:::theorem "parabolic.heat_ivp_superposition" (parent := "parabolic.classical") (lean := "HeatEquation.heatResidualAssignedInitialValueProblem_add, HeatEquation.heatResidualAssignedInitialValueProblem_const_mul, HeatEquation.heatResidualAssignedInitialValueProblem_sub, HeatEquation.heatResidualAssignedInitialValueProblem_linear_combination, HeatEquation.forcedHeatResidualAssignedInitialValueProblem_add, HeatEquation.forcedHeatResidualAssignedInitialValueProblem_const_mul, HeatEquation.forcedHeatResidualAssignedInitialValueProblem_sub, HeatEquation.forcedHeatResidualAssignedInitialValueProblem_linear_combination") (uses := "parabolic.heat_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-51"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Superposition also preserves the Cauchy data. If $`u` and $`v` have source
terms $`f,g` and initial values $`u_0,v_0`, then $`au+bv` has source
$`af+bg` and initial value $`au_0+bv_0`. The theorem family includes the
homogeneous and forced equations, with addition, subtraction, scalar
multiplication, and general real linear combinations.
:::

:::proof "parabolic.heat_ivp_superposition" (uses := "parabolic.heat_operator_linearity")
Use heat-operator linearity on positive time and ordinary pointwise linearity
on the time-zero hyperplane. The bundled Cauchy-problem constructor then joins
the two clauses.
:::
