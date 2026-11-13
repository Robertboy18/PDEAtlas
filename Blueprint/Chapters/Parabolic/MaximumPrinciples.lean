/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.Duhamel
import PDE.Parabolic.ComparisonPrinciple
import PDE.Parabolic.Heat.MaximumPrinciple
import PDE.Parabolic.MaximumPrinciple.FactoredOperator
import PDE.Parabolic.MaximumPrinciple.WithPotential
import PDE.Parabolic.MaximumPrinciple.MatrixOperator
import PDE.Parabolic.MaximumPrinciple.Strong.Maximum
import PDE.Parabolic.Heat.MaximumPrinciple.Strong
import PDE.Parabolic.Heat.MaximumPrinciple.Positivity
import PDE.Parabolic.Heat.GaussianGrowth
import PDE.Parabolic.Harnack.Classical

/-!
# Parabolic maximum principles

Maximum, comparison, and uniqueness principles for heat flow: the weak
principles on bounded cylinders, the whole-space principle under Gaussian
growth, the strong principle, positivity, and the Harnack inequality.
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
#doc (Manual) "Maximum, Comparison, and Uniqueness" =>

Parabolic equations propagate information forward from the initial face and
inward from the spatial boundary. Their natural boundary is therefore not the
entire boundary of a spacetime cylinder: the spatial interior of the
terminal-time face is excluded, while its lateral boundary points remain.
The parabolic boundary encodes this causal geometry.

The maximum principle rules out a new positive maximum in the positive-time
interior. A small perturbation by $`-\varepsilon t` makes the differential
inequality strict, compactness supplies a maximizer, and the spatial
second-derivative test conflicts with the time derivative at that point.
Applying the same result to differences yields comparison and uniqueness.

:::definition "parabolic.closed_cylinder" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.closedCylinder")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "52"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For an open spatial domain $`\Omega` and $`T>0`, the closed spacetime
cylinder is $`\overline\Omega\times[0,T]`.
:::

Boundary data are prescribed on only part of the boundary of this cylinder.
The maximum-principle argument finds a maximizer over the whole closed set
and must then be able to exclude it from the region where the differential
inequality holds, and that region is $`\Omega\times(0,T]`, terminal face
included.

:::definition "parabolic.parabolic_boundary" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.parabolicBoundary")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "52"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The parabolic boundary consists of the initial face
$`\overline\Omega\times\{0\}` and the lateral boundary
$`\partial\Omega\times[0,T]`. The terminal face
$`\Omega\times\{T\}` is excluded.
:::

The operator to which the argument applies need not be the Laplacian. What
the second-derivative test uses at a spatial maximum is only that each
principal term is a second derivative in a fixed direction. The directions
may vary with the point, but they are held fixed while differentiating the
spatial slice; no derivatives of the coefficient fields enter.

:::definition "parabolic.factored_operator" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.factoredParabolicOperator, ParabolicMaximum.factoredParabolicOperatorWithPotential")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "389"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a scalar field $`u(x,t)` on a real normed space, finitely many direction
fields $`\sigma_k(x,t)`, and a drift $`b(x,t)`, define

$$`Pu=u_t-\sum_k D_x^2u[\sigma_k,\sigma_k]+D_xu[b].`

The potential variant is $`P_cu=Pu+c(x,t)u(x,t)`. The definitions impose
no sign condition on $`c`; {bpref "parabolic.maximum_principle_with_potential"}[]
assumes $`c\geq0`.

Writing $`\sigma_{ki}` for coordinate $`i` of direction $`\sigma_k`, the
principal matrix has entries $`A_{ij}=\sum_k\sigma_{ki}\sigma_{kj}`.
Every symmetric positive-semidefinite matrix has such a factorization. The theorems use
only this semidefinite sign.
:::

For the heat equation itself the factorization is the standard basis:
$`\sigma_k=e_k` gives $`\sum_kD^2u[e_k,e_k]=\Delta u`, and $`b=0`.

:::definition "parabolic.classical_heat_operator" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.heatParabolicOperator") (uses := "foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "50-52"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a field written with separate spatial and time arguments, the classical
heat operator is $`u_t-\Delta u`. The heat maximum, comparison, and
uniqueness statements use this operator directly.
:::

The first principle is stated for the factored operator without zeroth-order
term, and only the semidefinite sign of the principal part enters. Its
hypotheses are the template for the other maximum principles:
continuity on the closed cylinder, classical differentiability at each point
of $`\Omega\times(0,T]`, the differential inequality there, and a bound on
the parabolic boundary.

:::theorem "parabolic.factored_weak_maximum_principle" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.subsolution_le_of_boundary_le") (uses := "parabolic.closed_cylinder, parabolic.parabolic_boundary, parabolic.factored_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "389-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be nonempty and open with compact closure, and let $`T>0`.
Assume $`u` is continuous on the closed cylinder. At every
$`(x,t)\in\Omega\times(0,T]`, assume its spatial slice is $`C^2` at $`x`,
its time slice is differentiable at $`t`, and $`Pu\leq0`.
If $`u\leq M` on the parabolic boundary, then
$`u\leq M` throughout the closed cylinder.

The time derivative is required at $`T` even at spatial interior points,
where terminal boundary data are not prescribed. It is the two-sided
derivative on the real line, not a one-sided derivative within $`[0,T]`. The
potential variants use the same hypotheses; the heat versions ask for less at
the terminal face.
:::

:::proof "parabolic.factored_weak_maximum_principle"
For $`\varepsilon>0`, the perturbation $`u_\varepsilon=u-\varepsilon t`
satisfies $`Pu_\varepsilon<0` and retains the boundary upper bound.
If its maximum on the compact cylinder exceeded $`M`, a maximizer would
lie in $`\Omega\times(0,T]`. There the spatial gradient vanishes and every
directional second derivative is nonpositive. The time derivative is
nonnegative, including at $`t=T`, where comparison with earlier times gives
the same sign. Thus $`Pu_\varepsilon\geq0`, a contradiction. Let
$`\varepsilon\downarrow0` to recover the bound for $`u`.
:::

A zeroth-order term $`cu` with $`c\geq0` does not disturb the argument
provided the bound $`M` is nonnegative. At a point where $`u>M\geq0` the
term $`cu` is nonnegative, so it only makes the inequality $`Pu+cu\leq0`
harder to satisfy. This is where the sign restriction on $`M` enters.

:::theorem "parabolic.maximum_principle_with_potential" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.subsolution_with_potential_le_of_boundary_le") (uses := "parabolic.closed_cylinder, parabolic.parabolic_boundary, parabolic.factored_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "390-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`c\geq0`, $`M\geq0`, $`Pu+cu\leq0`, and $`u\leq M` on the
parabolic boundary, then $`u\leq M` throughout the closed cylinder. Taking
$`M` to be the maximum of the positive part of the boundary data gives
Evans's Theorem 9(i).
:::

:::proof "parabolic.maximum_principle_with_potential"
The same perturbation $`u_\varepsilon=u-\varepsilon t` produces the additional
term $`-c\varepsilon t`, which has the favorable sign because
$`c,\varepsilon,t\geq0`. At a positive maximum the zeroth-order term is also
nonnegative.
:::

Replacing $`u` by $`-u` turns subsolutions into supersolutions and upper
bounds into lower bounds. The sign condition on $`M` flips with it: the
minimum principle requires $`M\leq0`, precisely so that $`-M` is an
admissible upper bound for $`-u`.

:::theorem "parabolic.minimum_principle_with_potential" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.boundary_le_supersolution_with_potential") (uses := "parabolic.maximum_principle_with_potential")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "390-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`c\geq0`, $`M\leq0`, $`Pu+cu\geq0`, and $`u\geq M` on the
parabolic boundary, then $`u\geq M` throughout the closed cylinder. This is
the dual minimum statement in Evans's Theorem 9(ii), with the sign restriction
on $`M` required by the nonnegative zeroth-order coefficient.
:::

:::proof "parabolic.minimum_principle_with_potential" (uses := "parabolic.maximum_principle_with_potential")
Apply the maximum principle with potential to $`-u` and the nonnegative upper
bound $`-M`, then negate the resulting inequality.
:::

For the heat operator, $`c=0` and the principal part is the full Laplacian,
so the sign restriction on $`M` disappears. The statement is repeated for
the heat operator so that no factorization of the
identity matrix has to be supplied when it is invoked. It is also sharper at
the top of the cylinder: derivatives and the differential inequality are
needed only on the open slab $`\Omega\times(0,T)`. Continuity carries the
bound from every shorter cylinder up to the terminal face.

:::theorem "parabolic.weak_maximum_principle" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.heat_subsolution_le_of_boundary_le") (uses := "parabolic.closed_cylinder, parabolic.parabolic_boundary, parabolic.classical_heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "389-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be nonempty and open with compact closure, $`T>0`, and $`u`
continuous on the closed cylinder. Suppose that at every
$`(x,t)\in\Omega\times(0,T)` the spatial slice is $`C^2`, the time slice is
differentiable, and $`u_t-\Delta u\leq0`. If $`u\leq M` on the parabolic
boundary, then $`u\leq M` throughout the closed cylinder.
:::

:::proof "parabolic.weak_maximum_principle"
At a spatial maximum $`\Delta u\leq0`, while at a positive-time maximum on
$`[0,s]` one has $`u_t\geq0`. The perturbation
$`u_\varepsilon=u-\varepsilon t` reduces the non-strict case to this strict
contradiction on each cylinder $`\overline\Omega\times[0,s]` with $`s<T`,
where the hypotheses hold up to the top face. Every point of
$`\Omega\times(0,T)` lies in such a cylinder, and the closed cylinder is the
closure of this open slab, so continuity gives the bound everywhere.
:::

Negating a supersolution of the heat equation produces a subsolution with the
negated bound.

:::theorem "parabolic.weak_minimum_principle" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.boundary_le_heat_supersolution") (uses := "parabolic.weak_maximum_principle")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "389-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the heat operator, if $`u_t-\Delta u\geq0` on $`\Omega\times(0,T)`
and $`u\geq M` on the parabolic boundary, then $`u\geq M` on the closed
cylinder. Unlike the potential case, no sign condition on $`M` is needed.
:::

:::proof "parabolic.weak_minimum_principle" (uses := "parabolic.weak_maximum_principle")
Set $`w=-u`. Then $`w_t-\Delta w=-(u_t-\Delta u)\leq0`, while the boundary
hypothesis $`u\geq M` becomes $`w\leq-M`. The weak maximum principle gives
$`w\leq-M` throughout the cylinder, which is equivalent to $`u\geq M`.
:::

Applied to a difference $`w=u-v`, the maximum principle compares two
functions instead of bounding one.

:::theorem "parabolic.comparison_principle" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.heat_comparison_of_boundary_le") (uses := "parabolic.closed_cylinder, parabolic.parabolic_boundary, parabolic.classical_heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "389-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`u_t-\Delta u\leq v_t-\Delta v` on $`\Omega\times(0,T]` and $`u\leq v` on the
parabolic boundary, with the classical regularity required by the maximum
principle, then $`u\leq v` on the entire closed cylinder.
:::

:::proof "parabolic.comparison_principle" (uses := "parabolic.weak_maximum_principle")
Set $`w=u-v`. Linearity of the heat operator gives
$`w_t-\Delta w\leq0`, and the boundary assumption gives $`w\leq0` on the
parabolic boundary. The weak maximum principle therefore yields $`w\leq0`
on the closed cylinder, which is exactly $`u\leq v`.
:::

Uniqueness is comparison applied twice.

Compactness of $`\overline\Omega` supplies the point where the perturbed
solution attains its maximum. On an unbounded domain, behavior at infinity
needs a separate argument.

:::theorem "parabolic.classical_uniqueness" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.heat_solution_unique") (uses := "parabolic.closed_cylinder, parabolic.parabolic_boundary, parabolic.classical_heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "389-391"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be nonempty and open with compact closure, and $`T>0`. Under the
regularity hypotheses of {bpref "parabolic.comparison_principle"}[], two
classical heat solutions with equal residual on $`\Omega\times(0,T]` and equal
parabolic boundary data agree throughout the closed cylinder:

$$`
  Hu=Hv\ \text{ on }\Omega\times(0,T],\qquad
  u=v\ \text{ on }\partial_pQ
  \quad\Longrightarrow\quad
  u=v\ \text{ on }\overline Q.
`
:::

:::proof "parabolic.classical_uniqueness" (uses := "parabolic.comparison_principle")
The two solutions have the same heat residual and the same parabolic boundary
data. Comparison first gives $`u\leq v`; exchanging the two solutions gives
$`v\leq u`. Pointwise antisymmetry of the real order then gives $`u=v` on the
whole closed cylinder.
:::

On all of $`\mathbb R^n` there is no compact cylinder, and uniqueness fails
without some control at infinity: Tychonoff's classical example is a nonzero
solution with zero initial data that grows faster than any Gaussian. The
remedy in {Informal.citet "evans-2010"}[] is a growth bound of the form
$`u(x,t)\leq Ae^{a|x|^2}`. Any fixed Gaussian rate $`a` is allowed, however
large, and the time horizon $`T` is arbitrary.

:::theorem "parabolic.whole_space_maximum_principle" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.iSup_eq_initial_of_gaussian_growth, HeatEquation.iSup_Ioc_eq_initial_of_gaussian_growth, HeatEquation.heat_subsolution_le_of_gaussian_growth") (uses := "parabolic.classical_heat_operator, parabolic.weak_maximum_principle")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`T>0` and $`a\geq0`. Let $`u` be continuous on $`\mathbb R^n\times[0,T]`,
with $`C^2` spatial slices and differentiable time slices on
$`\mathbb R^n\times(0,T)`, and suppose $`u_t-\Delta u=0` there. If
$`u(x,t)\leq Ae^{a|x|^2}` for $`0<t<T`, then

$$`\sup_{\mathbb R^n\times[0,T]}u=\sup_{x\in\mathbb R^n}u(x,0),`

with suprema in the extended reals. The same equality holds with $`[0,T]`
replaced by $`(0,T]`.
:::

:::proof "parabolic.whole_space_maximum_principle" (uses := "parabolic.weak_maximum_principle")
Only the upper bound needs work, and the extended-real formulation makes the
case of initial data unbounded above trivial. So fix $`M` with
$`u(\cdot,0)\leq M`. On a short time interval, of length fixed by $`a`,
compare $`u` on a large ball with $`M` plus a small multiple of the growing
Gaussian $`(T_1-t)^{-n/2}\exp\bigl(|x-y|^2/4(T_1-t)\bigr)`. This barrier
solves the heat equation, and on the sphere $`|x-y|=r` it outgrows
$`Ae^{a|x|^2}` once $`r` is large. The weak maximum principle on the ball
gives $`u(y,t)\leq M` plus the small multiple, and letting the multiple tend
to zero gives $`u(y,t)\leq M`. The short intervals are then concatenated up
to $`T`. The equality with the positive-time supremum uses continuity at
$`t=0`.
:::

The growth bound is needed only for $`0<t<T`, and the equation only at
interior times.

:::theorem "parabolic.whole_space_uniqueness" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.eq_of_gaussian_growth") (uses := "parabolic.whole_space_maximum_principle")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u` and $`v` satisfy the regularity hypotheses of
{bpref "parabolic.whole_space_maximum_principle"}[] and solve the same
forced equation $`u_t-\Delta u=f=v_t-\Delta v` on $`\mathbb R^n\times(0,T)`.
If $`|u|\leq A_1e^{a_1|x|^2}` and $`|v|\leq A_2e^{a_2|x|^2}` for $`0<t<T`,
and $`u(\cdot,0)=v(\cdot,0)`, then $`u=v` on $`\mathbb R^n\times[0,T]`.
:::

:::proof "parabolic.whole_space_uniqueness" (uses := "parabolic.whole_space_maximum_principle")
The difference $`w=u-v` solves the homogeneous equation, vanishes at
$`t=0`, and satisfies $`|w|\leq(A_1+A_2)e^{\max(a_1,a_2)|x|^2}`. The
maximum principle applied to $`w` and to $`-w` gives $`\sup w\leq0` and
$`\sup(-w)\leq0`.
:::

The weak principle says the maximum is attained on the parabolic boundary. It
does not rule out an interior maximum as well. The strong principle says that
an interior maximum at a positive time $`t_0` forces the solution to be
constant on the whole cylinder below $`t_0`. The statement is only about the
past. Boundary values imposed after $`t_0` can still change the solution
there.

The strong principle is proved for a general operator in nondivergence form.
The coefficients multiply second derivatives directly and are never
differentiated.

:::definition "parabolic.matrix_operator" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.matrixParabolicOperator") (uses := "parabolic.factored_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a matrix field $`a(x,t)`, a drift $`b(x,t)`, and a potential $`c(x,t)`,

$$`Lu=u_t-\sum_{i,j}a_{ij}(x,t)\,\partial_i\partial_ju+Du\cdot b+c\,u.`

When $`a_{ij}=\sum_k\sigma_{ki}\sigma_{kj}` and the spatial slice is
$`C^2` at the point, this agrees with the factored operator.
:::

:::theorem "parabolic.strong_maximum_principle" (parent := "parabolic.maximum_principles") (lean := "ParabolicMaximum.matrix_strong_maximum_zero_potential, ParabolicMaximum.matrix_strong_minimum_zero_potential, ParabolicMaximum.matrix_strong_maximum_nonnegative_potential, ParabolicMaximum.matrix_strong_minimum_nonnegative_potential") (uses := "parabolic.matrix_operator, parabolic.closed_cylinder")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U` be open and connected. Let $`a`, $`b`, $`c` be continuous on
$`U\times(0,T]`, with $`a` symmetric and
$`\sum a_{ij}\xi_i\xi_j\geq\theta|\xi|^2` for some $`\theta>0`. Let $`u` be
continuous on $`\overline U\times[0,T]`, with $`C^2` spatial slices and
differentiable time slices on $`U\times(0,T)`. Suppose $`Lu\leq0` there and
$`u` attains its maximum over the closed cylinder at $`(x_0,t_0)` with
$`x_0\in U` and $`0<t_0\leq T`. If $`c=0`, or if $`c\geq0` and
$`u(x_0,t_0)\geq0`, then $`u\equiv u(x_0,t_0)` on
$`\overline U\times[0,t_0]`. The minimum versions hold for $`Lu\geq0`, with
$`u(x_0,t_0)\leq0` in the case $`c\geq0`.
:::

:::proof "parabolic.strong_maximum_principle"
Put $`M=u(x_0,t_0)` and $`v=M-u\geq0`. The sign conditions ensure that
$`v` is a supersolution. The argument proves that positivity of $`v` moves
forward in time. If $`v(y,s)>0`, a small cubic bump centred at $`y` lies
below $`v` at time $`s`. Moved along a segment and damped exponentially
in time, the bump remains a subsolution: uniform ellipticity and bounds on
the continuous coefficients over a compact piece of the cylinder fix the
damping rate. Comparison on the moving ball then keeps $`v>0` at the end of
the segment. Any two points of the connected set $`U` are joined by a finite
chain of overlapping balls inside $`U`. So if $`v(y,s)>0` for some $`s<t_0`,
then $`v(x_0,t_0)>0`, which is false. Hence $`v=0` on $`U\times(0,t_0)`,
and continuity extends this to $`\overline U\times[0,t_0]`.

The proof uses only comparison with explicit barriers. It needs neither boundedness of
$`U` nor derivatives of the coefficients. It also uses derivatives only
strictly before $`T`, so a maximum at $`t_0=T` is covered.
:::

For the heat equation, $`a` is the identity matrix, $`b=0`, $`c=0`, and
$`\theta=1`. The strong principle then holds for extrema of either sign.

:::theorem "parabolic.heat_strong_maximum_principle" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.eqOn_const_of_isMaxOn, HeatEquation.eqOn_const_of_isMinOn") (uses := "parabolic.strong_maximum_principle, parabolic.classical_heat_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U` be open and connected, and let $`u` be continuous on
$`\overline U\times[0,T]`, with $`C^2` spatial slices and differentiable time
slices on $`U\times(0,T)`. If $`u_t-\Delta u\leq0` and $`u` attains its maximum over
the closed cylinder at an interior point $`(x_0,t_0)` with $`0<t_0\leq T`,
then $`u` is constant on $`\overline U\times[0,t_0]`. The same holds for a
minimum of a supersolution.
:::

:::proof "parabolic.heat_strong_maximum_principle" (uses := "parabolic.strong_maximum_principle")
The heat operator equals the matrix operator with coefficients
$`(I,0,0)`, identically in $`u`. The identity matrix is symmetric with
ellipticity constant one, and constant coefficients are continuous.
:::

The heat case also follows from the mean value formula on heat balls
({bpref "parabolic.heat_ball_mean_value"}[]), a route specific to the
Laplacian.

A consequence is infinite speed of propagation on bounded domains. With zero
boundary values, a nonnegative initial temperature that is positive
somewhere makes the temperature strictly positive everywhere inside at every
positive time.

:::theorem "parabolic.heat_positivity" (parent := "parabolic.maximum_principles") (lean := "HeatEquation.heat_supersolution_pos_of_initial_pos") (uses := "parabolic.weak_minimum_principle, parabolic.heat_strong_maximum_principle")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.3.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U` be open and connected with compact closure. Let $`u` be a
classical supersolution, $`u_t-\Delta u\geq0` on $`U\times(0,T)`, with
$`u\geq0` on the parabolic boundary and $`u(y,0)>0` for some
$`y\in\overline U`. Then $`u(x,t)>0` for every $`x\in U` and
$`0<t\leq T`.
:::

:::proof "parabolic.heat_positivity" (uses := "parabolic.weak_minimum_principle, parabolic.heat_strong_maximum_principle")
By the weak minimum principle $`u\geq0` on the closed cylinder. If
$`u(x,t)=0` for some $`x\in U` and $`t>0`, then $`(x,t)` is an interior
minimum, and the strong principle makes $`u` identically zero on
$`\overline U\times[0,t]`. This contradicts $`u(y,0)>0`.
:::

On the whole line the same fact is visible in the kernel formula
({bpref "parabolic.infinite_propagation"}[]), since the Gaussian is positive. On a
bounded interval, the figure computes the zero-boundary solution from its
sine series.

{leanpde_figure "heat-positivity"}

The Harnack inequality is a quantitative form of the strong principle. It
compares a nonnegative solution at an earlier time with the same solution at
a later time, uniformly over a compact subregion. The constant depends on the
geometry and the coefficients. It is chosen before the solution.

:::theorem "parabolic.harnack" (parent := "parabolic.maximum_principles") (lean := "ParabolicHarnack.exists_harnack_constant_of_space_time_derivatives") (uses := "parabolic.matrix_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U` be open, and let $`V` be connected with compact closure
$`\overline V\subseteq U`. Let $`0<s<t\leq T`. Let $`a`, $`b`, $`c` be
continuous on $`U\times(0,T]`, with $`a` symmetric and uniformly elliptic;
$`c` may have either sign. Then there is $`C>0` with the following
property. Let $`u\geq0` be continuous on $`U\times(0,T]`. Suppose $`u` has
continuous spatial first and second derivatives and a continuous time
derivative on $`U\times(0,T)`, and $`Lu=0` there. Then

$$`u(x,s)\leq C\,u(y,t)\quad(x,y\in\overline V),\qquad
  \sup_V u(\cdot,s)\leq C\inf_V u(\cdot,t).`
:::

:::proof "parabolic.harnack"
The proof uses the contact-set method of Krylov and Safonov, in the form
presented by Imbert and Silvestre. Suppose a supersolution is small at some
point at a later time. Slide a family of paraboloids up from below until
they first touch the graph at earlier times. At each contact point the
spatial Hessian of the solution is bounded below by that of the paraboloid.
The supersolution inequality then bounds the Jacobian of the contact map,
using only ellipticity and bounds on the trace and the drift. The change of
variables formula turns this into a lower bound on the measure of the set
where the solution was small earlier. An expanding barrier and an iteration
of this growth step give a measure estimate on nested cylinders. The upper
side comes from propagating almost-maximal values forward to later balls.
Together they give the comparison on small cylinders, and a finite covering
of $`\overline V` gives the constant. A potential of either sign is
absorbed by adding one spatial variable $`z` and multiplying by an
exponential in $`z`. The potential then becomes a drift in $`z`. The
contact argument needs a jointly $`C^2` gradient. The classical hypotheses
stated here are reached by averaging forward in time and letting the width
tend to zero.

The coefficients are only assumed continuous.
:::
