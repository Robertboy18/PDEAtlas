/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod.QuadraticModel
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PDE.CalculusOfVariations.SobolevIntegral
import PDE.CalculusOfVariations.EulerLagrange.PartialDerivatives
import PDE.CalculusOfVariations.EulerLagrange.Systems
import PDE.CalculusOfVariations.EulerLagrange.Convex
import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Dirichlet
import PDE.CalculusOfVariations.FirstVariation.UniformLocalMinimizer
import PDE.CalculusOfVariations.Noether.InducedConservation

/-!
# Sobolev integral functionals

The first-order Sobolev jet, convex integral energies, their
weak lower semicontinuity and minimizers, and the first-variation bridge to
Euler–Lagrange equations.
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
#doc (Manual) "Sobolev Integral Functionals" =>

# Convex integral functionals on Sobolev space

## Finding a field by minimizing its energy

For integral functionals there are two existence results. The Hilbert-space
criterion treats the whole space. The mixed-energy theorem constructs a
minimizer in a fixed affine class $`g+W^{1,p}_0(\Omega)`; it allows infinite
energies and starts from one finite-energy competitor.

Finding a minimizer and identifying its equation are separate steps. For a
differentiable functional, the first derivative vanishes along a variation
when both signs of that variation are admissible. Computing that derivative
gives the weak Poisson equation in our example. For mixed densities, the
first-variation theorem derives the directional formula from growth of the
supplied full density derivative.

## The concrete picture

Here $`H^1(\Omega)` is the weak-derivative graph space. On an open domain it
is the Sobolev space used by Evans; on an arbitrary set the theorems are
statements about the graph space, and open-domain Sobolev results keep their
openness hypothesis.

:::definition "methods.sobolev.jet" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.firstOrderSobolevJet")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-466"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a scalar field $`u\in H^1(\Omega)`, the first-order Sobolev jet bundles its
canonical $`L^2` representative and all canonical first weak derivatives:

$$`
j^1u(x)=(u(x),Du(x))\in\mathbb R\times\mathbb R^n.
`

Its values are the arguments of Evans's Lagrangian.
:::

The jet is exactly the argument that a first-order density $`F(x,z,p)`
takes, with $`z=u(x)` and $`p=Du(x)`. Integrating the composite over
$`\Omega` against the domain measure defines the functional whose minimizers
are sought.

:::definition "methods.sobolev.integral_energy" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.firstOrderSobolevIntegralEnergy") (uses := "methods.sobolev.jet")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-466"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Given a density $`F(x,z,p)`, the functional is the integral

$$`
J_F(u)=\int_\Omega F(x,u(x),Du(x))\,dx.
`
:::

Mathlib's Bochner integral assigns zero to a nonintegrable density. Before
using $`J_F` as an energy, we therefore need integrability for the fields
under consideration.

A quadratic-growth theorem gives one way to prove this. Suppose
$`F` is jointly measurable and, for almost every $`x` and every $`(z,p)`,

$$`
|F(x,z,p)|\leq a(x)+C\max\{|z|,\|p\|\}^2,
\qquad a\in L^1(\Omega),\quad C\geq0.
`

The maximum is the product norm on $`\mathbb R\times\mathbb R^n`. Since its
square is at most $`|z|^2+\|p\|^2`, evaluating this bound at
$`(u(x),Du(x))` gives an integrable majorant for every $`u\in H^1(\Omega)`.
The canonical representatives agree with the $`L^2` coordinates almost
everywhere, which suffices for this integral estimate.

This establishes finiteness of the energy without convexity or a bounded
domain. Convexity is the next input: it passes from $`F(x,-,-)` to the
integral because the jet map respects affine combinations almost everywhere.
The convexity theorem keeps integrability as a hypothesis so that other growth
conditions can supply it too.

:::theorem "methods.sobolev.integral_convex" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.convexOn_firstOrderSobolevIntegralEnergy") (uses := "methods.sobolev.integral_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "467-470"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Almost-everywhere compatibility of canonical Sobolev representatives with
affine combinations, pointwise joint convexity in $`(z,p)`, and integrability
of every admissible density imply

$$`
J_F((1-t)u+tv)\leq(1-t)J_F(u)+tJ_F(v)
\qquad(0\leq t\leq1).
`

Joint convexity is a clean sufficient condition for this theorem.
:::

:::proof "methods.sobolev.integral_convex"
The canonical representatives of $`(1-t)u+tv` agree almost everywhere with
the same affine combination of the representatives of $`u` and $`v`, both in
the base coordinate and every weak-derivative coordinate. Apply pointwise
convexity of $`F(x,-,-)` to these jets for almost every $`x`, then integrate
the resulting inequality. Linearity of the integral gives the stated convex
combination of energies.
:::

Convexity is what connects the integral functional to the weak topology.

:::theorem "methods.sobolev.integral_weak_lsc" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.lowerSemicontinuous_weakSpace_firstOrderSobolevIntegralEnergy, PDE.CalculusOfVariations.lintegral_le_liminf_of_tendsto_strong_weak_of_convex_gradient") (uses := "methods.sobolev.integral_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "468-470"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose $`F(x,-,-)` is jointly convex for almost every $`x`, every
admissible density $`F(x,u(x),Du(x))` is integrable, and the resulting
functional is lower semicontinuous in the strong $`H^1` topology. Then

$$`
u_\alpha\rightharpoonup u\ \text{in }H^1(\Omega)
\quad\Longrightarrow\quad
J_F(u)\leq\liminf_\alpha J_F(u_\alpha).
`

This Hilbert-space criterion takes strong lower semicontinuity as an input.
A second result derives sequential lower semicontinuity from convexity in the
gradient variable, using strong convergence of the values.

On a finite measure space, let $`1<p<\infty` and write the density as
$`F(x,s,z)`, with $`s\in\mathbb R` and $`z\in\mathbb R^n`. Assume that
$`F`, its gradient derivative $`D=\partial_zF`, and a spatial lower bound
$`a(x)` are measurable in their indicated variables. For almost every $`x`,
assume that $`F(x,s,z)` and $`D(x,s,z)` are continuous in $`s` for each fixed
$`z`, that $`F(x,s,\cdot)` is convex and differentiable for every $`s`, and
that $`F(x,s,z)\geq a(x)` for all $`s,z`.

If $`v_j\to v` strongly in $`L^p`, while $`z_j\rightharpoonup z` weakly in
$`L^p` with $`\sup_j\|z_j\|_p<\infty`, then

$$`
\int \bigl(F(x,v,z)-a(x)\bigr)\,d\mu
\leq\liminf_j\int \bigl(F(x,v_j,z_j)-a(x)\bigr)\,d\mu.
`

These are nonnegative Lebesgue integrals with values in $`[0,\infty]`.
There is no upper growth bound on $`F` or $`D`, and $`a` need only be
measurable. An integrable $`a` makes this a finite constant shift of the
original energy. The Lean theorem also permits the values to converge
strongly in a different $`L^r` space, $`1\leq r\leq\infty`.
:::

:::proof "methods.sobolev.integral_weak_lsc" (uses := "methods.direct_method.convex_weak_lsc, methods.sobolev.integral_convex")
For the Hilbert-space criterion, pointwise convexity and integrability give
convexity of the integral functional. Closed convex sublevel sets then
upgrade strong lower semicontinuity to weak lower semicontinuity.

For the sequential result, first choose indices tending to infinity along
which the energies tend to their liminf. Strong convergence of the values
allows a further selection converging almost everywhere. Convexity in $`z` gives a
supporting affine function at the limiting gradient. Restrict to measurable
sets on which these supporting densities and fields are uniformly bounded.
Continuity in $`s` and dominated convergence give strong $`L^{p'}` convergence
of the restricted fields, where $`p'=p/(p-1)<\infty`. Pairing them with the
bounded, weakly convergent gradients passes the affine inequality to the
limit. Fatou's lemma removes the restriction to those sets. The proof never
requires a global integrable bound on the supporting field.
:::

The Hilbert-space criterion assumes coercivity. For a mixed density with a
positive lower bound in the gradient, Poincaré derives the corresponding bound
on the admissible sublevel.

:::theorem "methods.sobolev.integral_minimizer" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.exists_global_minimizer_firstOrderSobolevIntegralEnergy, PDE.CalculusOfVariations.exists_minimizer_mixedWkpLIntegral_prescribed_boundary") (uses := "methods.sobolev.integral_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "470-471"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Pointwise convexity, density integrability, strong lower semicontinuity, and
coercivity give

$$`
\exists u\in H^1(\Omega),\qquad
J_F(u)=\inf_{v\in H^1(\Omega)}J_F(v).
`

This first conclusion is unconstrained. The mixed-energy result works in a
prescribed affine class. Let $`n\geq1`, let $`\Omega\subseteq\mathbb R^n` be
bounded and measurable, and let $`1<p<\infty`. Assume the measurability,
value-continuity, and gradient convexity and differentiability hypotheses of
the sequential lower-semicontinuity theorem, with Lebesgue measure restricted
to $`\Omega`. Suppose that $`b:\mathbb R^n\to\mathbb R` is measurable and that,
for some $`c>0`, almost every $`x` satisfies

$$`
F(x,s,z)\geq c|z|^p-b(x)\qquad\text{for every }s\in\mathbb R,\ z\in\mathbb R^n.
`

For $`g\in W^{1,p}(\Omega)`, set $`\mathcal A=g+W^{1,p}_0(\Omega)` and define

$$`
J_b^+(u)=\int_\Omega\bigl(F(x,u(x),\nabla u(x))+b(x)\bigr)\,dx
\in[0,\infty].
`

If one $`v_0\in\mathcal A` has $`J_b^+(v_0)<\infty`, there is a
$`u\in\mathcal A` such that

$$`
J_b^+(u)<\infty,\qquad J_b^+(u)\leq J_b^+(v)\quad\text{for every }v\in\mathcal A.
`

The lower bound is uniform in the value $`s`. It makes the shifted density
nonnegative, so the energy is a nonnegative Lebesgue integral even when some
competitors have infinite energy. No upper growth bound is required. If
$`b` is integrable, this also minimizes the original extended energy after
subtracting the finite constant $`\int_\Omega b`. On measurable sets,
$`W^{1,p}_0` means the supported smooth-core closure; on open sets it is the
usual zero-boundary space. No boundary atlas is assumed.
:::

:::proof "methods.sobolev.integral_minimizer" (uses := "methods.direct_method.coercive, methods.sobolev.integral_weak_lsc, sobolev.rellich_zero_trace")
For the unconstrained Hilbert result, the Sobolev integral theorem supplies
weak lower semicontinuity, and the coercive direct method attains the infimum.

For the affine result, write each competitor as $`g+w` with
$`w\in W^{1,p}_0(\Omega)`. The gradient lower bound and Poincaré control the
$`W^{1,p}` norm of corrections in the sublevel below the finite competitor.
Reflexivity and separability give a weakly convergent subsequence of a
minimizing sequence in this closed Sobolev subspace. Compactness of its base
coordinate gives strong $`L^p` convergence of the values; adding the fixed
field $`g` preserves that convergence. The gradients remain bounded and
converge weakly along the same subsequence. Apply the preceding sequential
inequality with $`a=-b`. The limit stays in the affine class and its energy
is no larger than the infimum approached by the sequence, hence it minimizes.
Comparison with the finite competitor makes its energy finite.
:::

The exponential-energy example gives a different reason to use the extended
integral. On a bounded measurable $`\Omega\subseteq\mathbb R^n`, $`n\geq1`,
consider

$$`
E(u)=\int_\Omega\left(e^{|\nabla u|^2}+(u-1)^2\right)\,dx,
\qquad u\in W^{1,2}_0(\Omega).
`

Square-integrability of the gradient does not itself give an integrable
exponential. We therefore let $`E` take values in $`[0,\infty]`. The zero
function has energy $`2|\Omega|`, so there is a finite starting point. The
inequality $`e^r\geq r` for $`r\geq0` controls the gradient, while convexity
of $`z\mapsto e^{|z|^2}` supplies lower semicontinuity. The direct method
therefore gives a finite-energy minimizer among all fields in the same
zero-boundary class, without a polynomial upper growth bound on the density.

The Sobolev counterpart of the quadratic $`L^2` model shows how these
analytic inputs are discharged in practice: convexity, coercivity, and weak
lower semicontinuity all follow from one identity.

:::theorem "methods.sobolev.quadratic_unique" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.existsUnique_global_minimizer_quadraticSobolevIntegralEnergy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the concrete energy

$$`
J_g(u)=\int_\Omega\left(
|u-g|^2+\sum_i|\partial_i u-\partial_i g|^2
\right)\,dx
=\lVert u-g\rVert_{H^1(\Omega)}^2,
`

the library proves integrability, identifies the energy with squared $`H^1`
distance, proves coercivity and weak lower semicontinuity, and obtains the
prescribed field $`g` as the unique global minimizer. This elementary quadratic model runs
through the whole direct-method chain.
:::

:::proof "methods.sobolev.quadratic_unique" (uses := "methods.direct_method.coercive")
The concrete integral equals the squared $`H^1` distance to $`g`. Its weak lower
semicontinuity and coercivity give a minimizer by the direct method; comparison
with `g` forces the squared distance to vanish and hence proves uniqueness.
:::

# Scope of the integral theorem

The boundary condition of the affine theorem is $`u-g\in W^{1,p}_0(\Omega)`
for a given Sobolev field $`g`. Because its compactness step uses only
zero-boundary corrections, the theorem holds on every bounded measurable set
in positive dimension, including dimension one.

Energies of vector-valued maps that depend on $`\det Du` are not convex in
the gradient. For them the lower-semicontinuity step goes through the weak
continuity of the determinant instead, giving the
{bpref "methods.polyconvex.minimizer"}[polyconvex existence theorem], and
the same continuity makes the pointwise constraint $`\det Du=1` weakly
closed. Each further constraint needs its own proof that the admissible set
is nonempty and weakly closed.

## Example: the Dirichlet energy

The prototypical application of the direct method is the Dirichlet energy

$$`
J(u)=\frac{1}{2}\int_\Omega|\nabla u|^2\,dx-\int_\Omega f\,u\,dx,
\qquad u\in H^1_0(\Omega),
`

where $`\Omega\subset\mathbb R^n`, $`n\ge1`, is a bounded open set and
$`f\in L^2(\Omega)`. This energy governs the Poisson equation
$`-\Delta u=f` with Dirichlet boundary conditions. Its load term $`-f(x)s`
does not in general satisfy the pointwise lower bound uniform in $`s` used
by the extended mixed-energy theorem. Here Poincaré controls that term after
integration. Let us trace the direct-method argument on $`H^1_0` through its
four steps.

*Step 1: Coercivity.* The Poincaré inequality on $`H^1_0(\Omega)` gives a
constant $`C_P>0` with $`\|u\|_{L^2}\leq C_P\|\nabla u\|_{L^2}`. Together
with Cauchy–Schwarz and Young's inequality,

$$`
J(u)\geq\frac{1}{2}\|\nabla u\|_{L^2}^2
-\|f\|_{L^2}\|u\|_{L^2}
\geq\frac{1}{2}\|\nabla u\|_{L^2}^2
-C_P\|f\|_{L^2}\|\nabla u\|_{L^2}
\geq\frac{1}{4}\|\nabla u\|_{L^2}^2-C_P^2\|f\|_{L^2}^2.
`

Thus $`J(u)\to+\infty` as $`\|\nabla u\|_{L^2}\to\infty`, confirming
coercivity.

*Step 2: Bounded minimizing sequence.* Let $`(u_k)` be a minimizing
sequence: $`J(u_k)\to\inf J`. By coercivity, $`\|\nabla u_k\|_{L^2}` is
bounded. The Poincaré inequality then bounds $`\|u_k\|_{H^1_0}`.

*Step 3: Weak convergence and compactness.* Since $`H^1_0(\Omega)` is a
reflexive Hilbert space, the Eberlein–Šmulian theorem extracts a subsequence
$`u_{k_j}\rightharpoonup u` weakly in $`H^1_0(\Omega)`. The gradient map is
bounded and linear, so the gradients converge weakly in $`L^2` as well.
These weak limits suffice for the two terms of this energy.

*Step 4: Lower semicontinuity.* The gradient term is convex and continuous
in the strong $`H^1` norm, hence weakly lower semicontinuous:

$$`
\frac{1}{2}\int_\Omega|\nabla u|^2\,dx
\leq\liminf_{j\to\infty}\frac{1}{2}\int_\Omega|\nabla u_{k_j}|^2\,dx.
`

For the load term, Cauchy–Schwarz and Poincaré give
$`|\int_\Omega f v|\leq C_P\|f\|_{L^2}\|\nabla v\|_{L^2}`.
Thus $`v\mapsto\int_\Omega f v` is a bounded linear functional on
$`H^1_0(\Omega)` and is continuous for weak convergence. Therefore

$$`
J(u)\leq\liminf_{j\to\infty}J(u_{k_j})=\inf J.
`

Since $`u` is admissible, $`J(u)=\inf J`, and $`u` is a minimizer.

*Uniqueness.* The energy $`J` is strictly convex (the Hessian in direction
$`v` is $`\int|\nabla v|^2>0` for $`v\neq 0`), so the minimizer is unique.

*Euler–Lagrange equation.* Stationarity $`DJ(u)[v]=0` for all
$`v\in H^1_0` gives

$$`
\int_\Omega\nabla u\cdot\nabla v\,dx=\int_\Omega f\,v\,dx
\qquad\text{for all }v\in H^1_0(\Omega),
`

which is the weak form of $`-\Delta u=f` with $`u=0` on $`\partial\Omega`.
In the library, the zero-boundary Sobolev space, Dirichlet form, and load
functional of this example come from the
{bpref "elliptic.dirichlet.energy"}[Poisson Dirichlet energy] rather than
from the integral-functional minimizer theorem.

# First variation and the Euler-Lagrange bridge

:::theorem "methods.euler_lagrange.first_variation" (parent := "methods.direct_method") (lean := "IsLocalMin.hasFDerivAt_eq_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "454-456"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At an unconstrained global minimizer of a Fréchet-differentiable real
functional,

$$`
u\in\operatorname*{arg\,min}J
\quad\Longrightarrow\quad
DJ(u)=0\in H^*.
`

This is the Banach-space form of Evans's directional first-variation
calculation.
Variations that preserve boundary values need a constrained version, such as
the mixed-density first-variation theorem.
:::

:::proof "methods.euler_lagrange.first_variation"
Mathlib proves this for a local minimum, which every global minimum supplies.
Its proof moves away from the minimizer along a fixed direction. Near a local
minimum the difference quotients of the energy are nonnegative, and they
converge to the first variation applied to that direction, so this value is
nonnegative. The same bound for the opposite direction makes it zero. Since
the direction was arbitrary, the first variation is the zero continuous linear map.
:::

:::theorem "methods.euler_lagrange.sobolev_minimum" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.integral_firstVariation_eq_zero_of_mixedWkpLIntegral_minimizer, PDE.CalculusOfVariations.integral_eulerLagrange_eq_zero_of_mixedWkpLIntegral_minimizer")
Let $`1\leq p<\infty` and let $`q` be its Hölder conjugate. The theorem takes
the full derivative $`dF(x,z)` in the product state $`z=(s,\xi)`, with
$`\|dF(x,z)\|\leq h(x)+C\|z\|^{p-1}` and $`h\in L^q`.
Differentiability and the bound hold for every state outside a fixed null
set. The density and the evaluated derivative $`(x,z,w)\mapsto dF(x,z)[w]`
are jointly measurable.

Suppose $`u\in W^{1,p}(\Omega)` minimizes the nonnegative extended integral of
$`F(x,u,\nabla u)+b(x)` in the prescribed affine class and has finite energy.
Here $`b` is measurable and $`F(x,z)+b(x)\geq0` for every state outside a
fixed null set. For every variation $`v` in the supported smooth-core
closure, the first-variation integrand
$`dF(x,(u,\nabla u))[(v,\nabla v)]` is integrable and has integral zero.
On open sets this variation space is $`W^{1,p}_0(\Omega)`.

This necessary condition includes $`p=1,\ q=\infty`, starting from a given
finite minimum. The existence theorem uses $`p>1`.

To see the differential equation inside this identity, write
$`A=\partial_sF` and $`D=\nabla_\xi F`. Assume joint measurability and, almost
everywhere in $`x`, joint continuity of these partial derivatives in
$`(s,\xi)`. Suppose they satisfy the conjugate growth bound
with $`|A|+\|D\|` in place of $`\|dF\|`. Mathlib's product differentiation
theorem assembles the full derivative:

$$`
dF(x,s,\xi)[r,z]=A(x,s,\xi)r+\langle D(x,s,\xi),z\rangle.
`

Substituting this expression into the first variation gives

$$`
\int_\Omega
\left(A(x,u,\nabla u)v+
\langle D(x,u,\nabla u),\nabla v\rangle\right)\,dx=0.
`

This is the weak equation $`-\operatorname{div}D+A=0`.
The integral is finite for every admissible variation; no derivative of the
integral functional is assumed.
:::

:::proof "methods.euler_lagrange.sobolev_minimum"
A common Hölder bound controls the line derivative for $`-1\leq t\leq1`. The mean value theorem gives
integrability of the shifted density along $`u+tv` from its integrability
at $`u`. The nearby extended integrals can therefore be compared as real
integrals and differentiated at $`t=0`; minimality makes that derivative
zero. This uses no separate upper growth bound on the density and does
not require $`b` itself to be integrable.
:::

:::theorem "methods.euler_lagrange.vector_sobolev_minimum" (parent := "methods.direct_method") (uses := "methods.euler_lagrange.sobolev_minimum") (lean := "PDE.CalculusOfVariations.integral_firstVariation_eq_zero_of_vectorWkpLIntegral_minimizer")
Under the same measurability, differentiability, shifted lower bound, finite-energy
minimum, and finite-exponent growth hypotheses, collect the component states in
$`Ju(x)=((u_k(x),\nabla u_k(x)))_k` and allow $`F(x,Ju)` to couple them.
A shared minimum theorem gives
$`\int_\Omega dF(x,Ju)[Jv]\,dx=0` for every vector variation in the
zero-boundary class. The growth bound uses the maximum norm on the finite
family of states.
:::

:::proof "methods.euler_lagrange.vector_sobolev_minimum"
The finite family of value-gradient pairs is in $`L^p`. Apply the same
dominated integral-differentiation argument to this product state. Every
line $`u+tv` remains in the componentwise affine class, so minimality makes
the derivative vanish.
:::

:::theorem "methods.euler_lagrange.convex_converse" (parent := "methods.direct_method") (uses := "methods.euler_lagrange.sobolev_minimum") (lean := "PDE.CalculusOfVariations.mixedWkpLIntegral_le_of_convex_of_weak_eulerLagrange")
Let $`1\le p\le\infty`. Retain the measurable density and shift with
$`F(x,z)+b(x)\ge0` almost everywhere for every state, and the same affine
variation class. Write $`Ju=(u,\nabla u)` for a member $`u` of that class.
Assume $`F(x,s,\xi)` is jointly convex in $`(s,\xi)` almost everywhere
and has its actual derivative at $`Ju`. Suppose the tested derivative is
integrable and has integral zero for every admissible variation. Then $`u`
minimizes the shifted extended energy in that affine class. This follows from
the tangent-plane inequality:

$$`
F(x,Jw)-F(x,Ju)\geq dF(x,Ju)[Jw-Ju].
`
:::

:::proof "methods.euler_lagrange.convex_converse"
For a competitor in the same affine class, $`w-u` is an admissible variation.
The weak equation makes the integral on the right zero, giving the
extended-energy comparison. An infinite-energy competitor is immediate; a
finite-energy competitor also forces the solution's energy to be finite.
This converse needs integrability of the tested derivative, but no power
growth or coercivity, and it includes $`p=\infty` with the supported-closure
boundary class. Joint convexity matters here: the earlier existence argument
only required convexity in the gradient.
:::

Passing from the integrated identity $`DJ(u)[\varphi]=0` for all test
directions to a pointwise Euler–Lagrange equation requires a localization
principle.

:::theorem "methods.euler_lagrange.fundamental_lemma" (parent := "methods.direct_method") (lean := "IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero") (uses := "foundations.distributions.test_function")
Let $`U\subseteq\mathbb R^n` be open and let $`f:\mathbb R^n\to\mathbb R` be
locally integrable on $`U` for Lebesgue measure. If

$$`
\int_U f\,\varphi\,dx=0
`

for every smooth compactly supported $`\varphi:\mathbb R^n\to\mathbb R`
whose support lies in $`U`, then $`f` vanishes almost everywhere on $`U`:

$$`
f(x)=0\qquad\text{for almost every }x\in U.
`

Only the behavior of $`f` inside $`U` matters: each test function vanishes
near the boundary and outside the domain. This is the
localization step of Evans's Euler–Lagrange derivation in §8.1.2, which
passes from the vanishing first variation to the almost-everywhere equation.
:::

There is a regularity step before applying this lemma to an energy density
$`F(x,u,\nabla u)`. The first variation initially says

$$`
\int_U\bigl(D_pF(x,u,\nabla u)\cdot\nabla\varphi
             +D_uF(x,u,\nabla u)\varphi\bigr)=0.
`

If the flux $`D_pF` has a weak divergence represented by a locally
integrable function, and $`D_uF` is locally integrable, integration by parts
produces the locally integrable residual
$`r=-\nabla\cdot D_pF+D_uF`. The fundamental lemma then gives $`r=0`
almost everywhere. Without that extra divergence regularity the displayed
test identity still defines the distributional equation. Further regularity,
such as continuity of $`r`, is needed to conclude equality at every point.

:::proof "methods.euler_lagrange.fundamental_lemma"
Because every admissible $`\varphi` is supported in $`U`, the integral over
$`U` equals the integral over $`\mathbb R^n`, so the hypothesis says that
$`f` integrates to zero against every smooth compactly supported function
with support in the open set $`U`. Mathlib's theorem for such functions
then applies: smooth cutoffs supported in $`U` approximate indicator
functions of compact subsets of $`U`, dominated convergence passes the
vanishing integrals to those indicators, and a locally integrable function
whose integral over every compact subset of $`U` vanishes is zero almost
everywhere on $`U`.
:::

## A classical local minimum gives a pointwise equation

The smooth version carries out each step of this bridge. It uses a
neighborhood of the field in the uniform $`C^1` topology, rather than
assuming that the first variation or the Euler–Lagrange residual vanishes.
Write

$$`J(u)=\int_\Omega L(Du(x),u(x),x)\,dx,
\qquad u:\mathbb R^n\to\mathbb R^m.`

Here the matrix variable is first in the density $`L(P,z,x)`, unlike the
earlier scalar notation $`F(x,s,p)`.

:::theorem "methods.euler_lagrange.classical_local_minimum" (parent := "methods.direct_method") (uses := "methods.euler_lagrange.fundamental_lemma") (lean := "PDE.CalculusOfVariations.IsC1LocalMinimizer.classicalEulerLagrange_eq_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§8.1.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n`, $`n>0`, be bounded and open with $`C^1`
graph boundary, and let $`u\in C^2(\mathbb R^n;\mathbb R^m)`.
Assume $`L` is jointly $`C^2` for $`x\in\Omega`, with its values and its
first two derivatives extending continuously to $`x\in\overline\Omega`.
Suppose some $`\varepsilon>0` satisfies

$$`J(u)\le J(u+v)`

for every globally $`C^2` perturbation $`v` that vanishes on
$`\partial\Omega` and obeys
$`\|v(x)\|+\|Dv(x)\|<\varepsilon` on $`\overline\Omega`.
The Jacobian norm here is the elementwise supremum norm. Then at every
$`x\in\Omega` and for every component $`k`,

$$`-\sum_{i=1}^n\partial_i
\left(L_{P_{ki}}(Du,u,x)\right)+L_{z_k}(Du,u,x)=0.`

The minimizer is assumed to be $`C^2`, and the equation is a necessary
condition for it.
:::

:::proof "methods.euler_lagrange.classical_local_minimum"
Fix a smooth compactly supported variation $`v` in $`\Omega`.
Compactness of $`\overline\Omega` bounds both $`v` and $`Dv`, so
$`u+tv` lies in the minimizing neighborhood for sufficiently small
$`|t|`. The function $`t\mapsto J(u+tv)` therefore has derivative zero at
zero. The continuous second jet supplies the bounds needed to differentiate
under the integral. Integration by parts transfers the derivatives of
$`v` to the flux, with no boundary term. The fundamental lemma makes
each Euler–Lagrange component zero almost everywhere; its continuity
upgrades this to every interior point.
:::

## From a variational symmetry to a conserved current

A symmetry can move the field and the spatial coordinates together.
Let $`\Phi_t(y)` move space and let $`\Psi_t(y,z)` transform field values.
The transformed field is defined near a point by its graph,

$$`U_t(\Phi_t(y))=\Psi_t(y,u(y)).`

The Jacobian determinant in a change of variables matters: invariance of
the action density means invariance of
$`L(DU_t,U_t,\cdot)\det D\Phi_t`, not merely of $`L` at the original
coordinates. The theorem constructs $`U_t` by local inversion of
$`\Phi_t` and differentiates this finite invariance.

:::theorem "methods.euler_lagrange.noether" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.Noether.noether_of_field_space_maps") (uses := "foundations.operators.divergence")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 8 (invariant variational problems)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix $`x`. Assume $`u` is $`C^2` at $`x`, $`L` is jointly $`C^2` at
$`(Du(x),u(x),x)`, and the maps $`(t,y)\mapsto\Phi_t(y)` and
$`(t,y,z)\mapsto\Psi_t(y,z)` are jointly $`C^2` at $`(0,x)` and
$`(0,x,u(x))`, respectively. Near $`x`, suppose
$`\Phi_0(y)=y` and $`\Psi_0(y,u(y))=u(y)`.
For the locally induced field $`U_t`, assume that for all sufficiently
small $`t`,

$$`L(DU_t(\Phi_t(x)),\Psi_t(x,u(x)),\Phi_t(x))\det D\Phi_t(x)
=L(Du(x),u(x),x).`

If $`u` satisfies the Euler–Lagrange system at $`x`, define
$`X(y)=\partial_t\Phi_t(y)|_{t=0}` and
$`\eta(y)=\partial_t\Psi_t(y,u(y))|_{t=0}`. Then the current

$$`J_i=\sum_k L_{P_{ki}}(Du,u,y)\bigl(\eta-Du\,X\bigr)_k
+L(Du,u,y)X_i`

satisfies $`\operatorname{div}J(x)=0`. All hypotheses are local at the
specified points; a global inverse or a transformation group is not required.
:::

:::proof "methods.euler_lagrange.noether"
At parameter zero, $`D\Phi_0(x)=I`. The inverse function theorem
constructs a jointly $`C^2` induced field satisfying the graph identity.
Differentiating that identity at fixed spatial coordinates gives the field
variation $`\eta-Du\,X`. Differentiating the finite density invariance
also gives the volume term $`L\operatorname{div}X`. The product and chain
rules assemble these terms into the divergence of the displayed current,
plus the Euler–Lagrange residual paired with the field variation.
That residual vanishes at $`x`, leaving conservation of the current.
:::
