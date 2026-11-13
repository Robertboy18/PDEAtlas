/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod
import PDE.CalculusOfVariations.NullLagrangian.Determinant
import PDE.CalculusOfVariations.NullLagrangian.BoundaryAction
import PDE.CalculusOfVariations.Polyconvexity.Determinant.Classical
import PDE.CalculusOfVariations.Polyconvexity.Determinant.Existence
import PDE.CalculusOfVariations.Constraints.Multiplier
import PDE.CalculusOfVariations.Constraints.Determinant.Existence
import PDE.CalculusOfVariations.Constraints.Sphere.Existence
import PDE.Elliptic.Regularity.Obstacle.ClassicalData

/-!
# Null Lagrangians, polyconvexity, and constraints

The determinant as a null Lagrangian, polyconvex energies that depend on it,
and minimization under the constraints `|u| = 1` and `det Du = 1`.
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
#doc (Manual) "Null Lagrangians and Constraints" =>

:::group "methods.constraints"
Null Lagrangians, polyconvexity, and constrained minimization
:::

Convexity in the full gradient is too restrictive for many elastic energies.
An energy that penalizes compression can depend on $`\det Du`, which is
not convex as a function of matrices in dimension at least two. The
polyconvex densities treated here depend convexly on the gradient and its
determinant as separate variables. To pass to a weak limit, we must then identify the limiting
determinant: for $`q>n` the determinant is
{bpref "sobolev.jacobian_determinant_weak_continuity"}[continuous from the weak topology of
$`W^{1,q}` to the weak topology of $`L^{q/n}`]. Its null-Lagrangian
structure supplies this fact.

Constraints require a separate weak-closedness argument. The same determinant
continuity preserves $`\det Du=1`; strong $`L^2` compactness preserves
$`|u|=1`. Neither admissible class is generally convex. These are the
constrained variational problems developed in Evans
{Informal.citet "evans-2010"}[], Chapter 8.

# Null Lagrangians

For a density $`L(P,z,x)` of a map $`u:\mathbb R^n\to\mathbb R^m`, with
$`P` standing for $`Du` and $`z` for $`u`, the Euler–Lagrange expression in
component $`k` is

$$`-\sum_{i=1}^n\partial_i\Bigl(\frac{\partial L}{\partial P_{ki}}(Du,u,x)\Bigr)
  +\frac{\partial L}{\partial z_k}(Du,u,x).`

Usually this expression vanishes only for the critical points of the action
$`\int_\Omega L(Du,u,x)\,dx`. A null Lagrangian is a density for which it
vanishes for every map.

:::definition "methods.null_lagrangian" (parent := "methods.constraints") (lean := "PDE.CalculusOfVariations.IsNullLagrangianOn, PDE.CalculusOfVariations.classicalEulerLagrange, PDE.CalculusOfVariations.determinantLagrangian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A density $`L:\mathbb R^{m\times n}\times\mathbb R^m\times\mathbb R^n\to\mathbb R`
is a null Lagrangian on $`\Omega` if every smooth map $`u` on $`\Omega`
satisfies the Euler–Lagrange system, with classical derivatives, at every
point of $`\Omega`. The determinant density is $`L(P,z,x)=\det P` on square
matrices.
:::

:::theorem "methods.null_lagrangian.determinant" (parent := "methods.constraints") (uses := "methods.null_lagrangian") (lean := "PDE.CalculusOfVariations.isNullLagrangianOn_determinant, PDE.CalculusOfVariations.classicalEulerLagrange_determinant_eq_zero, PDE.CalculusOfVariations.classicalEulerLagrange_determinant_eq_zero_on")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every dimension $`n`, the Euler–Lagrange expression of the determinant
vanishes at every point where $`u:\mathbb R^n\to\mathbb R^n` is $`C^2`. In
particular the determinant is a null Lagrangian on every open set.
:::

:::proof "methods.null_lagrangian.determinant"
The derivative of $`\det` in the entry $`(k,i)` is the cofactor
$`(\operatorname{cof}P)_{ki}`, at singular matrices as well, and the density
does not depend on $`z`. The Euler–Lagrange expression is therefore
$`-\sum_i\partial_i(\operatorname{cof}Du)_{ki}`, and the rows of the cofactor
matrix of a $`C^2` map are divergence free. This is the Piola identity. Each
cofactor is a sum of products of first derivatives, and after
differentiation the mixed second derivatives cancel in pairs.
:::

The name is explained by what the action does. If the Euler–Lagrange
expression vanishes identically, the derivative of the action along any path
of maps with fixed boundary values is zero, so the action depends only on the
boundary values.

:::theorem "methods.null_lagrangian.boundary_action" (parent := "methods.constraints") (uses := "methods.null_lagrangian") (lean := "PDE.CalculusOfVariations.IsNullLagrangianOn.lagrangianAction_eq_of_eqOn_frontier, PDE.CalculusOfVariations.IsNullLagrangianOn.lagrangianAction_eq_of_contDiff, PDE.CalculusOfVariations.IsNullLagrangianOn.classicalEulerLagrange_eq_zero_of_contDiffOn")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`L` be a null Lagrangian on an open set $`\Omega` with $`C^2` joint
dependence on its arguments. Then every $`C^2` map on $`\Omega` also
satisfies its Euler–Lagrange system. If $`\Omega` is bounded with $`C^2`
graph boundary and $`L` has a continuous second jet, then two maps that are
$`C^2` up to the boundary, continuous on $`\overline\Omega`, and equal on
$`\partial\Omega` have the same action

$$`\int_\Omega L(Du,u,x)\,dx=\int_\Omega L(Dv,v,x)\,dx.`
:::

:::proof "methods.null_lagrangian.boundary_action"
The Euler–Lagrange expression at a point depends only on the second jet of
the map there, and every second jet is realized by a polynomial map, which is
smooth. This passes the null property from smooth maps to $`C^2` maps.
For the action, extend $`u` and $`v` across the boundary to $`C^2` maps on
the whole space, using reflection in the graph charts, and consider
$`w_t=(1-t)u+tv`. The first-variation identity writes
$`\frac{d}{dt}\int_\Omega L(Dw_t,w_t,x)\,dx` as the integral of the
Euler–Lagrange expression of $`w_t` against $`v-u`, plus a boundary term that
vanishes because $`v-u=0` on $`\partial\Omega`. The Euler–Lagrange expression
is zero, so the action is constant in $`t`.
:::

# Polyconvex energies

Write $`W^{1,q}(\Omega;\mathbb R^n)` for maps whose $`n` components lie in
$`W^{1,q}(\Omega)`. A polyconvex density of the kind proved here has the form
$`L(Du,u,x)=F(x,u,Du,\det Du)`, where $`F(x,s,P,d)` is convex in the pair
$`(P,d)` jointly but can be far from convex in $`P` alone. The standard
example is $`|P|^q+\varphi(\det P)` with $`\varphi` convex. The integral is
taken in the extended sense, so it may be $`+\infty`, and only a lower bound
on the graph $`d=\det P` is required.

Lower semicontinuity comes from separating the two arguments. When
$`u_k\rightharpoonup u` weakly in $`W^{1,q}` with $`q>n`, the gradients
converge weakly in $`L^q`, and by the null-Lagrangian structure the
determinants converge weakly in $`L^{q/n}`. The pair
$`(Du_k,\det Du_k)` therefore converges weakly to $`(Du,\det Du)`, and a
functional that is convex in a weakly converging variable is weakly lower
semicontinuous.

:::theorem "methods.polyconvex.lower_semicontinuity" (parent := "methods.constraints") (uses := "methods.null_lagrangian.determinant, methods.sobolev.integral_weak_lsc") (lean := "PDE.CalculusOfVariations.vectorWkpIntegral_le_liminf_of_contDiffOn_convex_determinant, PDE.CalculusOfVariations.lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_convex_determinant, PDE.CalculusOfVariations.determinantDensity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n`, $`n\ge1`, be bounded and open with $`C^1`
graph boundary, and let $`q>n` be real. Let
$`F(x,s,P,d)` be $`C^1` on $`\Omega\times\mathbb R^n\times\mathbb
R^{n\times n}\times\mathbb R`, convex in $`(P,d)` for each $`x\in\Omega` and
$`s`, and bounded below by $`-\beta` on the graph $`d=\det P`. If
$`u_k\rightharpoonup u` weakly in $`W^{1,q}(\Omega;\mathbb R^n)`, then

$$`\int_\Omega F(x,u,Du,\det Du)\,dx
  \le\liminf_{k\to\infty}\int_\Omega F(x,u_k,Du_k,\det Du_k)\,dx.`
:::

:::proof "methods.polyconvex.lower_semicontinuity"
Lift each map to the pair $`(Du_k,\det Du_k)`, with values in
$`\mathbb R^{n\times n+1}`. Weak convergence of the determinants, from
$`W^{1,q}` to $`L^{q/n}`, makes the lifted sequence converge weakly. The
mixed convex lower semicontinuity theorem for integrands convex in a weakly
converging variable and continuous in a strongly converging one then applies,
with the values $`u_k` converging strongly by compact embedding.
:::

With lower semicontinuity in hand, the direct method goes through.

:::theorem "methods.polyconvex.minimizer" (parent := "methods.constraints") (uses := "methods.polyconvex.lower_semicontinuity, methods.sobolev.integral_minimizer") (lean := "PDE.CalculusOfVariations.exists_minimizer_determinantWkpIntegral_of_nonempty_trace, PDE.CalculusOfVariations.exists_minimizer_determinantWkpIntegral_prescribed_boundary, PDE.CalculusOfVariations.exists_minimizer_determinantWkpIntegral_of_finite_competitor")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.2.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the hypotheses of the lower semicontinuity theorem, suppose also that
$`\alpha|P|^q-\beta\le F(x,s,P,\det P)` with $`\alpha>0` and $`\beta` of
either sign. For every boundary datum $`\gamma` whose trace class

$$`
A=\{u\in W^{1,q}(\Omega;\mathbb R^n):
u=\gamma\text{ on }\partial\Omega\text{ in the trace sense}\}
`

is nonempty, the extended energy $`\int_\Omega F(x,u,Du,\det Du)\,dx` attains
its minimum on $`A`. The same holds for an affine class $`g+W^{1,q}_0`. If
some member of $`A` has finite energy, the minimizer's density is integrable
and its energy is an ordinary real integral.
:::

:::proof "methods.polyconvex.minimizer"
A nonempty trace class is the affine class $`g+W^{1,q}_0` of any of its
members. If every competitor has infinite energy, any member minimizes.
Otherwise the coercivity bound makes a minimizing sequence bounded in
$`W^{1,q}`, reflexivity extracts a weakly convergent subsequence, the affine
class is weakly closed, and lower semicontinuity shows that the limit
minimizes.
:::

# Constrained minimization

A constraint $`J(u)=c` given by a differentiable functional is the simplest
case, and the finite-dimensional rule survives in a Banach space: at a
constrained extremum the derivative of the energy is a multiple of the
derivative of the constraint, provided that the constraint derivative is
nonzero and both functionals have the strict differentiability required below.

:::theorem "methods.constraints.multiplier" (parent := "methods.constraints") (uses := "methods.euler_lagrange.first_variation") (lean := "PDE.CalculusOfVariations.exists_multiplier_of_hasStrictFDerivAt")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.4.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`E` be a real Banach space and $`F,J:E\to\mathbb R` strictly
differentiable at $`u`, with $`J'(u)\ne0`. If $`u` is a local extremum of
$`F` on the level set $`\{v:J(v)=J(u)\}`, then $`F'(u)=\lambda J'(u)` for
some $`\lambda\in\mathbb R`.
:::

:::proof "methods.constraints.multiplier"
The implicit function argument gives coefficients $`(a,b)\ne(0,0)` with
$`aJ'(u)+bF'(u)=0`. If $`b` were zero then $`a\ne0` and $`J'(u)=0`, which
is excluded. Take $`\lambda=-a/b`.
:::

The incompressibility constraint $`\det Du=1` is pointwise, not a single
level set, and no multiplier rule is needed for existence. Weak continuity of
the determinant does the work: if $`\det Du_k=1` almost everywhere and
$`u_k\rightharpoonup u` in $`W^{1,q}`, $`q>n`, then $`\det Du_k\rightharpoonup\det Du`
in $`L^{q/n}`, and a weak limit of the constant function $`1` is $`1`. The
admissible class is weakly closed although it is not convex.

:::theorem "methods.constraints.det_one" (parent := "methods.constraints") (uses := "methods.polyconvex.minimizer") (lean := "PDE.CalculusOfVariations.exists_minimizer_matrixWkpIntegral_of_nonempty_trace_det_eq_one, PDE.CalculusOfVariations.exists_minimizer_matrixWkpIntegral_prescribed_boundary_det_eq_one, PDE.CalculusOfVariations.exists_minimizer_matrixWkpIntegral_det_eq_one_of_finite_competitor")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.4.4"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n`, $`n\ge1`, be bounded and open with $`C^1`
graph boundary, let $`q>n`, and let $`L(x,s,P)` be $`C^1`, convex in $`P`,
with $`\alpha|P|^q-\beta\le L(x,s,P)` for some $`\alpha>0`. If
$`g\in W^{1,q}(\Omega;\mathbb R^n)` has $`\det Dg=1` almost everywhere, the
extended energy $`\int_\Omega L(x,u,Du)\,dx` attains its minimum among maps
$`u\in g+W^{1,q}_0` with $`\det Du=1` almost everywhere. When $`L=L(x,P)`
does not depend on the value, the same holds in the class of maps with trace
$`\gamma` and $`\det Du=1`, for every boundary datum $`\gamma` for which that
class is nonempty; if one admissible map has finite energy, the minimizer's
density is integrable and its energy is finite.
:::

:::proof "methods.constraints.det_one"
Run the direct method in the affine class of the given admissible map. The
constraint set is weakly sequentially closed by the weak continuity of the
determinant, and the energy is weakly lower semicontinuous because it is
convex in $`Du`. A bounded minimizing sequence in the constraint set has a
weak limit that stays in it.
:::

The sphere constraint $`|u|=1` is the other classical example. Strong
$`L^2` compactness preserves unit length and gives a minimizer when the
admissible class is nonempty. Deriving its equation needs a different
argument. A variation $`U+tV` leaves the sphere, so it
is projected back: the variation is $`G(U+tV)`, where $`G` is a smooth map
that agrees with $`z\mapsto z/|z|` on the annulus $`\tfrac12\le|z|\le2`.
For a bounded direction $`V` and small $`|t|`, $`U+tV` stays in that annulus
and the projected map again has unit length and the same boundary values.

:::theorem "methods.constraints.sphere_variation" (parent := "methods.constraints") (lean := "PDE.CalculusOfVariations.hasDerivAt_vectorDirichletEnergy_normalizedVariation, PDE.CalculusOfVariations.normalizedVariation_norm_values_eq_one_ae, PDE.CalculusOfVariations.normalizedVariation_sub_mem_H10") (uses := "methods.constraints.multiplier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.4.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^{n+1}` be bounded and open with $`C^1` graph
boundary. Choose a smooth compactly supported map
$`G:\mathbb R^m\to\mathbb R^m` agreeing with $`z/|z|` on
$`\tfrac12\le|z|\le2`. Let $`U\in H^1(\Omega;\mathbb R^m)` have
$`|U|=1` almost everywhere and let
$`V\in H^1(\Omega;\mathbb R^m)` be bounded by $`M`. For $`|t|M<\tfrac12` the
projected variation $`G(U+tV)` has unit length almost everywhere, and if
$`V\in H^1_0` it has the boundary values of $`U`. The Dirichlet energy
$`E(W)=\tfrac12\int_\Omega|DW|^2` of the projected variation is differentiable at
$`t=0` with derivative

$$`\frac{d}{dt}\Big|_{t=0}E\bigl(G(U+tV)\bigr)
  =\int_\Omega\Bigl(DU:DV-|DU|^2\,U\cdot V\Bigr)\,dx.`
:::

:::proof "methods.constraints.sphere_variation"
The graph-domain hypotheses supply the Sobolev extension operator and inward
partition used for composition and preservation of the boundary values.
The smooth compactly supported cutoff has bounded derivative and Lipschitz
$`DG`.
Since $`|U|=1`, the chain rule gives
$`D(G(U+tV))=DG(U+tV)\,(DU+tDV)`, and at $`t=0` the derivative of the
normalization $`z\mapsto z/|z|` at a unit vector is the projection
$`I-z\otimes z`. Differentiating $`|U|^2=1` gives $`(DU)^TU=0`, which turns
the projected term into $`-|DU|^2U\cdot V`. Differentiation under the integral
sign is justified by an integrable bound built from the Lipschitz bound on
$`DG`.
:::

:::theorem "methods.constraints.harmonic_map" (parent := "methods.constraints") (uses := "methods.constraints.sphere_variation") (lean := "PDE.CalculusOfVariations.exists_sphere_dirichlet_minimizer_weak_equation, PDE.CalculusOfVariations.integral_inner_derivatives_eq_of_sphere_minimizer_of_local_graph, PDE.CalculusOfVariations.integral_inner_derivatives_eq_of_sphere_minimizer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.4.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^{n+1}` be bounded and open with $`C^1` graph
boundary, and let $`g\in H^1(\Omega;\mathbb R^m)`. Assume the class

$$`\mathcal A_g=\{W\in H^1(\Omega;\mathbb R^m):
|W|=1\text{ a.e.},\ W-g\in H^1_0(\Omega;\mathbb R^m)\}`

is nonempty. Then the Dirichlet energy attains its minimum on
$`\mathcal A_g`. Every such minimizer $`U` satisfies

$$`\int_\Omega DU:DV\,dx=\int_\Omega|DU|^2\,U\cdot V\,dx
  \qquad\text{for every }V\in H^1_0(\Omega;\mathbb R^m)\cap L^\infty.`

This is the weak form of the harmonic map equation
$`-\Delta U=|DU|^2U`. Nonemptiness of $`\mathcal A_g` is a hypothesis.
:::

:::proof "methods.constraints.harmonic_map"
For existence, an energy-bounded minimizing sequence has bounded gradients.
Poincaré's inequality controls the zero-boundary differences from $`g`,
so weak compactness gives an $`H^1` limit with the same boundary values.
Rellich compactness gives strong $`L^2` convergence, preserving unit length
almost everywhere, and weak lower semicontinuity gives minimality.
This existence argument itself needs only a bounded open domain of positive
dimension.

For the equation, the projected variations are admissible competitors, so the energy along
them has a minimum at $`t=0` and its derivative there vanishes. The previous
theorem computes that derivative. An essentially bounded test field has an
almost-everywhere bound $`M`, which is all the variation theorem asks for,
and the graph boundary supplies the Sobolev extension that the composition
with $`G` needs.
:::

The multiplier in the harmonic map equation is $`|DU|^2`, a function rather
than a number. Formally it is the multiplier for a constraint imposed at
every point; here it comes out of the projected variation directly.

# Contact with an obstacle

An inequality constraint changes the Euler equation precisely where the
minimizer touches the obstacle. Consider

$$`J(v)=\frac12\int_\Omega |Dv|^2\,dx-\int_\Omega fv\,dx,
\qquad v\in H^1_0(\Omega),\quad v\ge\psi\text{ a.e.}`

Upward variations are admissible at contact, while downward ones may not be.
The resulting reaction $`r=-\Delta u-f` is nonnegative. Away from contact
both directions become available and the Poisson equation is recovered.
Starting from a constrained minimizer, the regularity theorem supplies the
extra differentiability needed to express this description almost everywhere.

:::theorem "methods.constraints.obstacle_regularity" (parent := "methods.constraints") (lean := "PDE.Elliptic.Obstacle.exists_h2_dirichletObstacle_minimizer_of_classical") (uses := "elliptic.dirichlet.energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.4 (obstacle problem)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n`, $`n>0`, be bounded and open with $`C^2`
graph boundary. Let $`f\in L^2(\Omega)` and let the obstacle $`\psi` be
$`C^2` up to the boundary, continuous on $`\overline\Omega`, and nonpositive
on $`\partial\Omega`. If $`u\in H^1_0(\Omega)` minimizes $`J` among fields
above $`\psi`, then $`u` has an $`H^2` representative $`U`. Its reaction obeys

$$`0\le r=-\Delta U-f\le(-\Delta\psi-f)^+,\qquad r(U-\psi)=0
\quad\text{a.e. in }\Omega.`

On the contact set $`U=\psi`, one has $`\Delta U=\Delta\psi` almost
everywhere; on $`U>\psi`, one has $`-\Delta U=f` almost everywhere.
:::

:::proof "methods.constraints.obstacle_regularity" (uses := "sobolev.trace_classical")
The graph boundary supplies the extension and trace infrastructure.
The classical obstacle defines an $`H^2` field whose Sobolev trace agrees
with its boundary values, so the boundary sign becomes the sign condition
needed by the obstacle regularity theorem. The constrained variational
inequality and its reaction estimate then give the $`H^2` lift and
$`0\le r\le(-\Delta\psi-f)^+`. Complementarity sets the reaction to zero
off contact. On contact, the Sobolev derivatives of $`U-\psi` vanish
almost everywhere on its zero set, giving equality of the Laplacians.
:::
