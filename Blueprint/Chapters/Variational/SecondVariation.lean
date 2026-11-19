/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod
import PDE.Elliptic.Variational.DirichletSecondVariation
import PDE.CalculusOfVariations.SecondVariation.Legendre

/-!
# Second variations

Second-variation formulas and their application to
Dirichlet energy.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PDE.CalculusOfVariations
open SobolevSpace.GraphSpace

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Second Variations and Dirichlet Energy" =>

:::group "methods.second_variation"
Second variations and necessary positivity
:::

Evans derives first- and second-variation tests for integral functionals on
pp. 454–459 by restricting the energy to affine lines.

The first variation detects a critical point. It cannot distinguish a minimum
from a maximum or saddle. The second variation supplies the next test. If $`u`
is a local minimizer and $`\varphi` is an admissible direction, the
one-dimensional function

$$`
g(t)=J(u+t\varphi)
`

has a local minimum at $`t=0`. Therefore $`g'(0)=0` and
$`g''(0)\geq0`. Fréchet differentiation identifies these derivatives with
$`DJ(u)[\varphi]` and $`D^2J(u)[\varphi,\varphi]`.

Nonnegativity is only a necessary test in this generality: both $`J(s)=s^4`
and $`J(s)=-s^4` have zero first and second derivatives at zero, although
one has a minimum and the other a maximum. Quadratic energies are more
informative because their expansion has no unexamined higher-order remainder.

# Second-Order Necessary Conditions

:::theorem "methods.second_variation.hessian_nonnegative_at_local_minimum" (parent := "methods.second_variation") (lean := "IsLocalMin.fderiv_fderiv_apply_self_nonneg")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "458"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If a $`C^2` real-valued functional on a real normed space has a local minimum
at $`u`, then

$$`
D^2F(u)[v,v]\geq0\qquad\text{for every }v.
`
:::

:::proof "methods.second_variation.hessian_nonnegative_at_local_minimum"
Restrict the functional to the affine line $`t\mapsto u+tv`. The restriction
has a local minimum at zero, so its second derivative is nonnegative there;
the chain rule identifies that derivative with `D²F(u)[v,v]`.
:::

Diagonal nonnegativity is a statement about the quadratic form
$`v\mapsto D^2F(u)[v,v]`. Since the second Fréchet derivative of a $`C^2`
functional is symmetric, it is equivalently a statement about the bilinear
form itself.

:::theorem "methods.second_variation.hessian_positive_semidefinite_at_local_minimum" (parent := "methods.second_variation") (lean := "IsLocalMin.isPosSemidef_fderiv_fderiv") (uses := "methods.second_variation.hessian_nonnegative_at_local_minimum")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "458"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The bilinear form underlying the Hessian at a local minimum is symmetric and
positive semidefinite:

$$`
D^2F(u)[v,w]=D^2F(u)[w,v],\qquad D^2F(u)[v,v]\geq0\qquad(v,w\in E).
`
:::

:::proof "methods.second_variation.hessian_positive_semidefinite_at_local_minimum" (uses := "methods.second_variation.hessian_nonnegative_at_local_minimum")
Mathlib's symmetry theorem for second Fréchet derivatives supplies symmetry,
and diagonal nonnegativity supplies the remaining positive-semidefinite
condition.
:::

# Nonlinear integral functionals

For $`J(u)=\int_\Omega L(Du,u,x)\,dx`, the second variation has gradient,
field, and mixed terms. The gradient term can be isolated by variations
that oscillate rapidly in a fixed direction. This tests the matrix
Hessian only on rank-one matrices, the matrices produced by differentiating
one scalar oscillation times one vector amplitude.

:::theorem "methods.second_variation.legendre_hadamard" (parent := "methods.second_variation") (uses := "methods.second_variation.hessian_nonnegative_at_local_minimum") (lean := "PDE.CalculusOfVariations.integral_lagrangian_secondVariation_nonneg_of_isLocalMin, PDE.CalculusOfVariations.lagrangian_hessian_rankOne_nonneg_of_isLocalMin")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n` be bounded and open and
$`u\in C^2(\mathbb R^n;\mathbb R^m)`. Assume $`L(P,z,x)` is jointly
$`C^2` for $`x\in\Omega`, with its values and first two derivatives
extending continuously to $`x\in\overline\Omega`.
If $`t\mapsto J(u+tv)` has a local minimum at zero for a globally
$`C^2` variation $`v`, then

$$`\delta^2J(u)[v,v]=\int_\Omega
D^2L(Du,u,x)[(Dv,v,0),(Dv,v,0)]\,dx\ge0.`

If this local-minimum condition holds for every smooth compactly supported
vector variation in $`\Omega`, then at every $`x\in\Omega`,

$$`D^2_{PP}L(Du(x),u(x),x)[a\otimes\xi,a\otimes\xi]\ge0
\qquad(a\in\mathbb R^m,\ \xi\in(\mathbb R^n)^*).`

The domain needs no boundary regularity. The pointwise condition tests the
matrix Hessian on rank-one directions only, and it is necessary for a minimum
but not sufficient.
:::

:::proof "methods.second_variation.legendre_hadamard"
Differentiate $`J(u+tv)` twice under the integral using the continuous
second jet. The scalar second-derivative test gives the integral inequality.
Next fix a smooth cutoff $`g` supported in $`\Omega` and use the pair
$`v_s(y)=g(y)a\sin(\lambda\xi(y))` and
$`v_c(y)=g(y)a\cos(\lambda\xi(y))`.
Adding their second variations cancels the mixed oscillatory terms and
gives $`A+\lambda^2 B\ge0` for every real $`\lambda`, where

$$`B=\int_\Omega g^2
D^2_{PP}L(Du,u,y)[a\otimes\xi,a\otimes\xi]\,dy.`

Hence $`B\ge0`. If the continuous rank-one Hessian were negative at an
interior point, a nonzero cutoff in a neighborhood where it stays negative
would give $`B<0`. This local contradiction proves the pointwise condition.
:::

# Quadratic Energies

:::theorem "methods.second_variation.quadratic_energy_exact_expansion" (parent := "methods.second_variation") (lean := "PDE.CalculusOfVariations.quadraticEnergy_add_eq")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "454-459"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a symmetric bounded bilinear form $`B` and continuous load $`\ell`, the
energy

$$`
J(u)=\frac12B(u,u)-\ell(u)
`

satisfies the exact expansion

$$`
J(u+v)=J(u)+B(u,v)-\ell(v)+\frac12B(v,v).
`
:::

:::proof "methods.second_variation.quadratic_energy_exact_expansion"
Expand both bilinear arguments and the linear load, use symmetry on the two
mixed terms, and collect coefficients.
:::

The expansion is an exact Taylor formula: the term linear in $`v` is
$`B(u,v)-\ell(v)`, the quadratic term is $`\frac12B(v,v)`, and there is no
higher-order remainder. The Fréchet derivative and the second variation can
therefore be read off directly.

:::theorem "methods.second_variation.quadratic_energy_first_variation" (parent := "methods.second_variation") (lean := "PDE.CalculusOfVariations.quadraticEnergy_fderiv")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "454-457"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Fréchet derivative of the quadratic energy at $`u` is

$$`
DJ(u)[v]=B(u,v)-\ell(v),
`

or equivalently $`DJ(u)=B(u,-)-\ell` as a continuous linear functional.
:::

:::proof "methods.second_variation.quadratic_energy_first_variation" (uses := "methods.second_variation.quadratic_energy_exact_expansion")
Mathlib's bilinear derivative rule differentiates `B(u,u)`. Symmetry combines
the two resulting terms, while the load differentiates to itself.
:::

At a local minimizer the derivative vanishes by Fermat's theorem, and the
derivative formula turns that vanishing into an identity in every direction.
Because the energy is quadratic in $`u`, no separate differentiability
hypothesis is needed here, in contrast to the semilinear energies, where
differentiability of the potential has to be supplied before a minimizer can
be called a weak solution.

:::theorem "methods.second_variation.quadratic_energy_euler_equation" (parent := "methods.second_variation") (lean := "PDE.CalculusOfVariations.quadraticEnergy_isWeakSolution_of_isLocalMin")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "454-457"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every unconstrained local minimizer satisfies the weak Euler equation

$$`
B(u,v)=\ell(v)\qquad\text{for every test direction }v.
`
:::

:::proof "methods.second_variation.quadratic_energy_euler_equation" (uses := "methods.second_variation.quadratic_energy_first_variation")
Fermat's theorem makes the derivative vanish at a local minimum. Substituting
the derivative formula and evaluating the zero functional gives the weak
equation.
:::

The Euler equation used only the first derivative. The second derivative is
where the quadratic structure pays off: because $`DJ(u)` depends affinely on
$`u`, the Hessian does not depend on the base point at all, and the
second-variation test can be evaluated without knowing the minimizer.

:::theorem "methods.second_variation.quadratic_energy_second_variation" (parent := "methods.second_variation") (lean := "PDE.CalculusOfVariations.quadraticEnergy_secondVariation_eq")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "458-459"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The second Fréchet derivative of the quadratic energy is independent of the
base point:

$$`
D^2J(u)[v,w]=B(v,w).
`
:::

:::proof "methods.second_variation.quadratic_energy_second_variation" (uses := "methods.second_variation.quadratic_energy_first_variation")
The first-variation map is the affine map $`u\mapsto B(u,\mathbin\cdot)-\ell`; its derivative
is therefore the continuous linear map `B`.
:::

Combining the abstract second-order necessary condition with the base-point
independence of the Hessian gives a condition on $`B` alone: a quadratic
energy can have a local minimizer only if $`B` is positive semidefinite.
Coercive forms satisfy this automatically.

:::theorem "methods.second_variation.quadratic_energy_second_variation_nonnegative" (parent := "methods.second_variation") (lean := "PDE.CalculusOfVariations.quadraticEnergy_secondVariation_nonneg_of_isLocalMin") (uses := "methods.second_variation.hessian_nonnegative_at_local_minimum, methods.second_variation.quadratic_energy_second_variation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "458-459"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At a local minimum, the second variation obeys the necessary condition

$$`
B(v,v)=D^2J(u)[v,v]\geq0
\qquad\text{for every }v.
`
:::

:::proof "methods.second_variation.quadratic_energy_second_variation_nonnegative" (uses := "methods.second_variation.hessian_nonnegative_at_local_minimum, methods.second_variation.quadratic_energy_second_variation")
Identify the Hessian of the quadratic energy with `B`, then apply the abstract
diagonal nonnegativity theorem at the local minimum.
:::

# Dirichlet Energy and Poisson's Equation

For the symmetric quadratic energy
$`J(w)=\frac12B(w,w)-\ell(w)`, stationarity at $`u` gives
$`B(u,v)=\ell(v)`. Expanding at that point therefore yields

$$`
J(u+v)-J(u)=\frac12B(v,v).
`

If $`B(v,v)\geq c\|v\|^2` with $`c>0`, an energy gap bounds the squared
distance to the minimizer by $`2/c` times that gap. This is a useful
connection to certified computation: a certified energy estimate becomes a
field-error estimate once coercivity and admissibility in the same space
have been established.

For $`f\in L^2(\Omega)`, the Poisson Dirichlet energy on $`H^1_0(\Omega)`
is the quadratic energy built from the Dirichlet form and the load
functional of $`f`. The abstract Hessian formula specializes to it without
any new computation.

:::theorem "methods.second_variation.dirichlet_energy_second_variation" (parent := "methods.second_variation") (lean := "SobolevSpace.GraphSpace.dirichletEnergy_secondVariation_eq, SobolevSpace.GraphSpace.dirichletEnergy_secondVariation_apply")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "455-459"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the Poisson Dirichlet energy on $`H^1_0(\Omega)`,

$$`
D^2J(u)[v,w]
=\sum_{i=1}^n\int_\Omega \partial_i v\,\partial_i w\,dx.
`
:::

:::proof "methods.second_variation.dirichlet_energy_second_variation" (uses := "methods.second_variation.quadratic_energy_second_variation")
Specialize the quadratic Hessian formula to the symmetric Dirichlet form and
the continuous load induced by the forcing term.
:::

On the diagonal the Dirichlet form is a sum of squared $`L^2` norms of weak
derivatives, so the necessary condition $`D^2J(u)[v,v]\geq0` holds for every
$`v` whether or not $`u` is a minimizer. The second-variation test never
rules out a critical point of the Dirichlet energy.

:::theorem "methods.second_variation.dirichlet_energy_second_variation_self" (parent := "methods.second_variation") (lean := "SobolevSpace.GraphSpace.dirichletEnergy_secondVariation_self_eq")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "455-459"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The diagonal Dirichlet Hessian is

$$`
D^2J(u)[v,v]
=\sum_{i=1}^n\lVert\partial_i v\rVert_{L^2(\Omega)}^2,
`

expressed through the canonical weak-derivative maps.
:::

:::proof "methods.second_variation.dirichlet_energy_second_variation_self" (uses := "methods.second_variation.dirichlet_energy_second_variation")
Evaluate the Hessian as the Dirichlet form and use its diagonal
identity in terms of the squared $`L^2` norms of the weak derivatives.
:::

A nonnegative Hessian is only a necessary condition in general. For the
Dirichlet energy the first variation is also sufficient.

:::theorem "methods.second_variation.dirichlet_energy_local_minimum_iff_weak_poisson" (parent := "methods.second_variation") (lean := "SobolevSpace.GraphSpace.dirichletEnergy_isLocalMin_iff_isWeakSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "455-459"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`u\in H^1_0(\Omega)`,

$$`
u\text{ is a local minimizer of }J
\quad\Longleftrightarrow\quad
\sum_i\int_\Omega\partial_i u\,\partial_i v\,dx
=\int_\Omega fv\,dx
\quad(v\in H^1_0(\Omega)).
`
:::

:::proof "methods.second_variation.dirichlet_energy_local_minimum_iff_weak_poisson" (uses := "methods.second_variation.quadratic_energy_euler_equation")
The forward direction is the local first-variation condition. Conversely, the
Dirichlet principle makes every weak solution a global minimizer,
hence a local minimizer.
:::
