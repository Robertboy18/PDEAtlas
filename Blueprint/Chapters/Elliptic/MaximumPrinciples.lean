/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Elliptic.FundamentalSolutions.Planar
import Blueprint.Commands.Figures
import PDE.Elliptic.Classical.Harmonic.Harnack
import PDE.Elliptic.Classical.Harmonic.StrongMaximumPrinciple
import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple
import PDE.Elliptic.Classical.Harnack.Harnack
import PDE.Elliptic.Classical.Harnack.Local.Density
import PDE.Elliptic.Classical.Harnack.Local.LevelDecay
import PDE.Elliptic.Classical.MaximumPrinciple.MatrixHopf
import PDE.Elliptic.Classical.MaximumPrinciple.MatrixSymmetrization

/-!
# Maximum principles

Weak and strong maximum principles, the Hopf lemma, and Harnack inequalities,
first for the Laplacian and then for operators with variable coefficients.
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
#doc (Manual) "Maximum, Minimum, Comparison, and Uniqueness for Harmonic Functions" =>

# From mean values to rigidity

Maximum principles turn local harmonicity into global order information.  The
weak principle says that a harmonic function continuous up to the boundary of
a ball cannot rise above its boundary values.  Applying it to a difference
gives comparison, and applying comparison in both directions gives uniqueness
for the ball Dirichlet problem.

The strong principle has a different conclusion.  On an open preconnected
domain, an interior point at which a harmonic function attains its
domain-wide maximum forces the function to be constant.  The proof uses the
spherical mean-value identity: an average can equal a pointwise upper bound
only when the surrounding values also equal that bound.  The maximum set is
therefore both open and closed.

:::theorem "elliptic.maximum.weak_ball" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.le_of_boundary_le") (uses := "elliptic.harmonicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "26-27"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`r>0`. If $`u` is harmonic in $`B(x_0,r)`,
continuous on its closure, and $`u\le M` on $`\partial B(x_0,r)`, then

$$`u(x)\le M\qquad(x\in\overline{B(x_0,r)}).`

This is the harmonic case on a ball. The
{bpref "elliptic.maximum.matrix_weak"}[variable-coefficient weak principle]
holds on every open set with compact closure.
:::

:::proof "elliptic.maximum.weak_ball"
Add a small positive quadratic perturbation to make the Laplacian strictly
positive.  Compactness supplies a maximum on the closed ball, while the
second-derivative test rules out an interior maximum above the boundary
bound.  Letting the perturbation vanish gives the weak inequality.
:::

The minimum principle is the maximum principle applied to $`-u`, which is
harmonic whenever $`u` is. Together the two bounds say that a harmonic function
continuous on the closed ball takes its values in the interval spanned by its
boundary values.

:::theorem "elliptic.minimum.weak_ball" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.ge_of_boundary_ge") (uses := "elliptic.harmonicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "27"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`r>0`. If $`u` is harmonic in $`B(x_0,r)`,
continuous on its closure, and $`m\le u` on $`\partial B(x_0,r)`, then

$$`m\le u(x)\qquad(x\in\overline{B(x_0,r)}).`
:::

:::proof "elliptic.minimum.weak_ball" (uses := "elliptic.maximum.weak_ball")
The function $`-u` is harmonic whenever $`u` is. The boundary inequality
$`m\leq u` is equivalent to $`-u\leq-m`, so the weak maximum principle gives
$`-u(x)\leq-m` throughout the closed ball. Negating this inequality yields
$`m\leq u(x)`.
:::

Comparison is the weak maximum principle for the difference $`u-v`: harmonicity
is preserved under subtraction, and the boundary inequality $`u\le v` is the
boundary bound $`u-v\le0`. This is the form in which the principle is applied to
two candidate solutions of the same Dirichlet problem.

:::theorem "elliptic.maximum.comparison_ball" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.le_of_boundary_le_function") (uses := "elliptic.harmonicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "27-28"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`u` and $`v` be harmonic in the same ball
$`B(x_0,r)`, with $`r>0`, and continuous on its closure. If $`u\le v` on
the sphere, then

$$`u(x)\le v(x)\qquad(x\in\overline{B(x_0,r)}).`
:::

:::proof "elliptic.maximum.comparison_ball" (uses := "elliptic.maximum.weak_ball")
The difference $`u-v` is harmonic and continuous on the closed ball. Apply
the weak maximum principle with boundary upper bound zero.
:::

Two-sided comparison is uniqueness: if $`u=v` on the sphere, comparison in both
directions gives $`u\le v` and $`v\le u` on the closed ball. The Green-kernel
theory uses this statement to identify any solution of the ball
Dirichlet problem with the Poisson integral of its boundary data.

:::theorem "elliptic.maximum.uniqueness_ball" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.eq_of_boundary_eq") (uses := "elliptic.harmonicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "27-28"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`r>0`. If $`u` and $`v` are harmonic in
$`B(x_0,r)`, continuous on $`\overline{B(x_0,r)}`, and satisfy $`u=v` on
the sphere, then

$$`u=v\qquad\text{on }\overline{B(x_0,r)}.`

This is the homogeneous, ball-domain case of Evans's Dirichlet uniqueness
theorem.
:::

:::proof "elliptic.maximum.uniqueness_ball" (uses := "elliptic.maximum.comparison_ball")
Because the two harmonic functions agree on the boundary, the comparison
principle applied to $`u` and $`v` gives $`u\leq v` on the closed ball.
Applying it again with the functions exchanged gives $`v\leq u`; pointwise
antisymmetry then gives $`u=v`.
:::

The strong principle replaces the ball by an arbitrary open preconnected set and
the boundary hypothesis by an interior maximum. Its proof uses the spherical
mean-value identity instead of the second-derivative test. Our proof of the
mean-value formula goes through the ball Poisson theory, so the strong
principle also depends on the weak one.

:::theorem "elliptic.maximum.strong_harmonic" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.eqOn_const_of_isPreconnected_of_forall_le") (uses := "elliptic.harmonicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "27-28"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`U` be open and preconnected. If a harmonic
function $`u` attains a domain-wide maximum at some $`x_0\in U`, then

$$`u(x)=u(x_0)\qquad\text{for every }x\in U.`
:::

:::proof "elliptic.maximum.strong_harmonic" (uses := "elliptic.mean_value.from_harmonicity")
At a maximum point, the spherical mean-value identity says that the continuous
nonnegative gap $`u(x_0)-u` has integral zero on every sufficiently small
centered sphere. Positivity of surface measure on open patches forces the
gap to vanish on each sphere. Varying the radius fills a ball, so the maximum
set is open in $`U`. It is also relatively closed by continuity and contains
$`x_0`; preconnectedness makes it all of $`U`.
:::

With its minimum counterpart, the strong principle says that a nonconstant
harmonic function on a preconnected open set attains neither its maximum nor
its minimum over the set.

:::theorem "elliptic.minimum.strong_harmonic" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.eqOn_const_of_isPreconnected_of_forall_ge") (uses := "elliptic.harmonicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "27"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`U` be open and preconnected. If a harmonic
function $`u` attains a domain-wide minimum at some $`x_0\in U`, then

$$`u(x)=u(x_0)\qquad\text{for every }x\in U.`
:::

:::proof "elliptic.minimum.strong_harmonic" (uses := "elliptic.maximum.strong_harmonic")
Negation preserves harmonicity. If $`u` attains its minimum at $`x_0`, then
$`-u` attains its maximum there. The strong maximum principle makes $`-u`
constant on the preconnected domain, and multiplying the resulting identity
by $`-1` makes $`u` constant as well.
:::

# Operators with variable coefficients

The Laplacian is the simplest of the operators

$$`Lu=-\sum_{i,j=1}^n a^{ij}(x)\,\partial_i\partial_j u+\sum_{i=1}^n b^i(x)\,\partial_i u+c(x)\,u`

studied in {Informal.citet "evans-2010"}[] §6.4. The mean-value identity is
lost as soon as the coefficients vary, so these principles need a different
argument. Both proofs perturb $`u` by an explicit function whose image under
$`L` has a known sign, and then look at a maximum point with the
second-derivative test. The sign conventions follow Evans, so $`-\Delta` is
the case $`a=I`, $`b=0`, $`c=0`, and a subsolution is a function with
$`Lu\le0`.

The matrix $`a(x)` may be any real matrix. Only its quadratic form enters the
hypotheses, and that form depends only on the symmetric part of $`a(x)`. The
Lean proofs first replace $`a` by its symmetric part, which changes neither
$`Lu` (the Hessian of a $`C^2` function is symmetric) nor the quadratic form.
The weak and strong principles and the Hopf lemma assume no continuity of the
coefficients.

:::definition "elliptic.maximum.matrix_operator" (parent := "elliptic.representation") (lean := "EllipticMaximum.matrixOperator")
For $`a:\mathbb R^n\to\mathbb R^{n\times n}`, $`b:\mathbb R^n\to\mathbb R^n`,
and $`c:\mathbb R^n\to\mathbb R`, the operator in nondivergence form is

$$`Lu(x)=-\sum_{i,j}a_{ij}(x)\,\partial_i\partial_j u(x)+Du(x)\,b(x)+c(x)\,u(x).`

The second derivatives are those of the Fréchet derivative, so the formula is
defined for every function and is meaningful where $`u` is $`C^2`.
:::

The weak principle only needs one direction in which $`L` is uniformly
elliptic. If $`a_{ii}\ge\alpha>0` for a fixed index $`i` and $`b^i\le B`, then
$`v(x)=e^{\lambda x_i}` satisfies $`Lv<0` once $`\lambda` is large, and
$`u+\varepsilon v` cannot have an interior maximum. The other directions only
need a nonnegative quadratic form.

:::theorem "elliptic.maximum.matrix_weak" (parent := "elliptic.representation") (lean := "EllipticMaximum.matrix_subsolution_le_of_boundary_le_of_nonneg_quadratic") (uses := "elliptic.maximum.matrix_operator, elliptic.maximum.weak_ball")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.4.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open with compact closure. Suppose that
on $`\Omega` the quadratic form of $`a(x)` is nonnegative, that for one fixed
index $`i` we have $`a_{ii}\ge\alpha>0` and $`b^i\le B`, and that $`c\ge0`.
Let $`u` be continuous on $`\overline\Omega`, $`C^2` in $`\Omega`, with
$`Lu\le0` in $`\Omega` and $`u\le M` on $`\partial\Omega`, where $`cM\ge0`.
Then

$$`u\le M\qquad\text{on }\overline\Omega.`

When $`c=0` the bound $`M` may have either sign. When $`c\ge0` is nonzero
somewhere, $`M` must be nonnegative there, which is the form
$`u\le\max_{\partial\Omega}u^+` of Evans's statement.
:::

:::proof "elliptic.maximum.matrix_weak" (uses := "elliptic.maximum.matrix_operator")
Replace $`a` by its symmetric part. Put $`e(x)=e^{\lambda x_i}` and let
$`E` be its maximum over the compact set $`\overline\Omega`. Without the
potential, $`e` has residual $`(-\lambda^2a_{ii}+\lambda b^i)e\le(-\lambda^2\alpha+\lambda B)e`,
which is negative once $`\lambda\alpha>B`. The shifted barrier $`e-E` is
nonpositive, so the potential adds $`c(e-E)\le0` and $`L(e-E)<0`. For
$`\varepsilon>0` the function $`u_\varepsilon=u+\varepsilon(e-E)` is a strict
subsolution with $`u_\varepsilon\le M` on the boundary. At an interior maximum
above $`M` its gradient would vanish, its Hessian would be negative
semidefinite, and $`c\,u_\varepsilon\ge cM\ge0`, which together give
$`Lu_\varepsilon\ge0`. Hence $`u_\varepsilon\le M`, and letting $`\varepsilon\to0` gives the claim.
:::

The strong principle needs to know how $`u` leaves a boundary maximum. The
Hopf lemma answers that it leaves at a definite rate. At a point of an
interior tangent ball where $`u` attains a strict maximum, the outward normal
derivative is strictly positive. A plain maximum only gives
$`\partial_\nu u\ge0`.

{leanpde_figure "hopf-lemma"}

In the figure the gap $`u(x^0)-u` along the inner radius stays above a
multiple of the barrier $`v=e^{-\lambda|x|^2}-e^{-\lambda}`. The barrier
vanishes on the outer sphere with a nonzero slope, so the gap has a nonzero
slope too. A function whose gap grows only quadratically would cross the
barrier, and the comparison principle on the annulus rules that out.

:::theorem "elliptic.maximum.hopf" (parent := "elliptic.representation") (lean := "EllipticMaximum.matrix_hopf_normal_fderiv_pos, EllipticMaximum.matrix_hopf_inward_deriv_neg") (uses := "elliptic.maximum.matrix_operator, elliptic.maximum.matrix_weak")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.4.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`R>0` and $`\lVert x^0-z\rVert=R`. On the annulus
$`R/2<\lVert x-z\rVert<R` assume the quadratic form of $`a` is at least
$`\kappa|v|^2` with $`\kappa>0`, $`\operatorname{tr}a\le A`,
$`\lVert b\rVert\le B`, $`0\le c\le C`, $`c\,u(x^0)\ge0`, and $`Lu\le0`. Let
$`u` be continuous on $`\overline B(z,R)`, $`C^2` in $`B(z,R)`, differentiable
at $`x^0`, and suppose $`u(x)<u(x^0)` for every $`x\in B(z,R)`. Then

$$`Du(x^0)\,\nu>0,\qquad \nu=\frac{x^0-z}{R}.`

The second Lean statement gives the same conclusion as a one-sided inward
derivative along the segment from $`x^0` to $`z`, and does not need
differentiability of $`u` at $`x^0`.
:::

:::proof "elliptic.maximum.hopf" (uses := "elliptic.maximum.matrix_weak")
Set $`v(x)=e^{-\lambda\lVert x-z\rVert^2}-e^{-\lambda R^2}`. For $`\lambda`
large, depending on $`\kappa`, $`A`, $`B`, $`C`, and $`R`, the barrier
satisfies $`Lv\le0` on the annulus. On the inner sphere $`u<u(x^0)` holds
with a positive gap by compactness, so for small $`\varepsilon` the function
$`u+\varepsilon v-u(x^0)` is at most $`0` on both boundary spheres. The weak
principle on the annulus gives $`u(x^0)-u\ge\varepsilon v`. Differentiating
this at $`x^0` along the inward radius yields a derivative at most
$`\varepsilon\,\partial_\nu v(x^0)<0`.
:::

The strong principle follows. If $`u` attains its maximum over a connected
open set at an interior point and is not constant, some ball inside the set
touches the maximum set at a boundary point. At that point $`Du=0`
because it is an interior maximum, while Hopf's lemma makes a directional
derivative positive.

:::theorem "elliptic.maximum.matrix_strong" (parent := "elliptic.representation") (lean := "EllipticMaximum.matrix_eqOn_const_of_isPreconnected_of_isMaxOn_of_elliptic") (uses := "elliptic.maximum.matrix_operator, elliptic.maximum.hopf")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.4.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be open and preconnected. Assume that each point of $`\Omega`
has a closed ball in $`\Omega` on which the quadratic form of $`a` is at
least $`\kappa|v|^2` with $`\kappa>0`, and $`\operatorname{tr}a`,
$`\lVert b\rVert`, and $`c\ge0` are bounded above. If $`u` is $`C^2` in
$`\Omega`, $`Lu\le0`, $`u` attains its maximum over $`\Omega` at
$`x^0\in\Omega`, and $`c\,u(x^0)\ge0`, then $`u\equiv u(x^0)` on $`\Omega`.

The constants may change from ball to ball; bounded continuous coefficients
on a connected domain, with $`c\ge0` and a nonnegative maximum, are a special
case.
:::

:::proof "elliptic.maximum.matrix_strong" (uses := "elliptic.maximum.hopf")
Replace $`a` by its symmetric part. The set where $`u=u(x^0)` is closed in
$`\Omega` and nonempty. If it were not all of $`\Omega`, there would be a
point of the complement closer to the maximum set than to $`\partial\Omega`,
and a ball around it, inside $`\Omega` and in the set $`u<u(x^0)`, touching the
maximum set at a boundary point $`y`. At $`y` the derivative vanishes, since
$`y` is an interior maximum. The Hopf lemma on this ball, with the local
constants, says a normal derivative is positive. The contradiction shows the
maximum set is open as well.
:::

# Harnack comparison

The maximum principle compares an interior value with boundary data. Harnack
compares two interior values using positivity. If $`\lVert x-y\rVert\le r`,
then $`B(y,r)\subset B(x,2r)`, and mean values and $`u\ge0` give

$$`
u(y)=\frac{1}{|B(y,r)|}\int_{B(y,r)}u
\le\frac{1}{|B(y,r)|}\int_{B(x,2r)}u
=2^n u(x).
`

Positivity is the step that permits enlarging the integration region.
A function that changes sign can lose mass by cancellation, so the same
argument would fail. This also explains why a nonnegative harmonic function
cannot vanish at an interior point and be positive just beside it.

On the unit disc the Poisson kernel makes the comparison exact. Every
positive harmonic function is an average of the kernels $`P(\cdot,\zeta)`
over boundary points $`\zeta`, and each kernel satisfies

$$`\frac{1-r}{1+r}\le\frac{P(x,\zeta)}{P(0,\zeta)}\le\frac{1+r}{1-r}\qquad(|x|=r<1).`

{leanpde_figure "harnack-disc"}

The figure plots these ratios along one radius. The band is the whole of the
Harnack inequality on the disc. On $`|x|\le\tfrac12` it gives
$`\sup u\le9\inf u`, and the constant blows up like $`(1-r)^{-2}` as the
smaller disc grows toward the boundary. The formal proof chains mean-value
balls instead of using the Poisson kernel, which gives a worse constant on any
compact set but works in every domain.

:::theorem "elliptic.harnack.local_ball" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.le_two_pow_mul_of_dist_le") (uses := "elliptic.mean_value.sphere_and_ball")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "29-30"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0`, $`r>0`, and suppose $`u` is nonnegative and harmonic on a set
containing $`\overline B(x,2r)`. If $`\lVert x-y\rVert\leq r`, then

$$`u(y)\leq 2^n u(x).`

The ambient harmonicity set need not be open: the explicit closed-ball
containment supplies every mean-value ball used in the proof.
:::

:::proof "elliptic.harnack.local_ball" (uses := "elliptic.mean_value.sphere_and_ball")
The ball $`B(y,r)` lies inside $`B(x,2r)`. Nonnegativity makes the integral
over the smaller ball no larger than the integral over the larger one.
Applying the ball mean-value formula at $`y` and $`x`, then using
$`|B(x,2r)|=2^n|B(y,r)|`, gives the stated factor.
:::

To compare distant points, we pass through a chain of overlapping balls, each
link costing a factor $`2^n`. The constant can deteriorate as the compact set
approaches the boundary or as the connecting geometry forces more links.

:::theorem "elliptic.harnack.compact_comparison" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.exists_harnack_constant_on_isCompact") (uses := "elliptic.harnack.local_ball")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "30"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge 1`, let $`U\subseteq\mathbb R^n` be open and preconnected, and let
$`K\subseteq U` be compact. There is a constant $`C>0`, depending only on
$`n`, $`K`, and $`U`, such that every nonnegative harmonic function on
$`U` satisfies

$$`u(x)\leq C\,u(y)\qquad(x,y\in K).`
:::

:::proof "elliptic.harnack.compact_comparison" (uses := "elliptic.harnack.local_ball")
Join points of the connected domain by chains of overlapping admissible
balls. Each link contributes the local factor $`2^n`. Compactness gives a
finite subcover of $`K` and hence a uniform bound on the number of links
needed from a fixed base point. Comparing both $`x` and $`y` with that base
point produces one constant valid for every pair in $`K`.
:::

The same inequality holds for nonnegative solutions of $`Lu=0` with variable
coefficients, which is Theorem 5 of {Informal.citet "evans-2010"}[] §6.4.3.
There is no mean-value formula in this setting. The Lean proof uses the
contact-set method, with the monotone envelope, contact Jacobian, and basic
measure estimate following Imbert and Silvestre's lecture notes on fully
nonlinear equations (§§4.1 to 4.2 of the 2013 HAL version). No derivative of
a coefficient is taken anywhere.

The first step is a quantitative form of the strong principle: a nonnegative
supersolution without potential that is small at one point is small on a set
of definite measure.

:::theorem "elliptic.harnack.contact_measure" (parent := "elliptic.representation") (lean := "EllipticHarnack.measure_vertexBall_le_mul_measure_sublevel") (uses := "elliptic.maximum.matrix_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.4.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose that on $`B(0,1)` the quadratic form of $`a` is at least
$`\alpha|v|^2` with $`\alpha>0`, $`\operatorname{tr}a\le\tau`, and
$`\lVert b\rVert\le B`. Let $`u\ge0` be continuous on $`\overline B(0,1)`,
$`C^2` in $`B(0,1)`, and satisfy $`Lu\ge0` there with $`c=0`. If
$`u(x^0)\le1` for some $`x^0\in\overline B(0,\tfrac12)`, then

$$`
\bigl|\overline B(x^0,\tfrac18)\bigr|
\le\Bigl(\frac{\tau+2B}{\alpha}\Bigr)^n\,\bigl|B(0,1)\cap\{u\le\tfrac54\}\bigr|.
`
:::

:::proof "elliptic.harnack.contact_measure"
Slide each paraboloid with vertex $`y\in\overline B(x^0,\tfrac18)` up until
it touches $`u` from below on $`\overline B(0,\tfrac{15}{16})`. Because
$`u(x^0)\le1` and $`u\ge0` on the unit ball, the touching happens at an
interior point where $`u\le\tfrac54`. The contact set is compact and the map
sending a contact point to its vertex covers the vertex ball. At a contact point
the contact Jacobian $`J` is positive semidefinite, and $`Lu\ge0` together with
the gradient identity at contact gives
$`\alpha\operatorname{tr}J\le\operatorname{tr}(aJ)\le\tau+2B`. This bounds
$`\det J` by $`((\tau+2B)/\alpha)^n`, and the area formula gives the estimate.
:::

Covering the unit cube by dyadic subcubes and applying this estimate at every
scale turns one point of smallness into geometric decay of the superlevel sets.
This is the $`L^\varepsilon` estimate, and it controls $`\inf u` from below.

:::theorem "elliptic.harnack.level_decay" (parent := "elliptic.representation") (lean := "EllipticHarnack.exists_superlevel_geometric_decay") (uses := "elliptic.harnack.contact_measure")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.4.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\alpha>0`, $`\tau\ge0`, and $`B\ge0`. There are $`M\ge2` and
$`0<\delta<1` such that the following holds for all coefficients with
ellipticity $`\alpha`, $`\operatorname{tr}a\le\tau`, and
$`\lVert b\rVert\le B` on the ball of radius $`16(n+1)`. If $`u\ge0` is
$`C^2` there, satisfies $`Lu\ge0` with $`c=0`, and $`u(x^0)\le1` at some
point of the closed unit cube $`Q`, then for every $`k\ge0`

$$`\bigl|\{x\in Q:\ u(x)>M^k\}\bigr|\le\delta^k\,|Q|.`
:::

:::proof "elliptic.harnack.level_decay" (uses := "elliptic.harnack.contact_measure")
The contact estimate, rescaled to cubes, says that $`u\le M` on a fixed
fraction $`\eta` of a cube whenever $`u\le1` at a point of a slightly larger
cube. Apply it to $`u/M^k`. A dyadic child in which $`\{u>M^{k+1}\}` has
density above $`1-\eta` cannot contain a point of its parent where
$`u\le M^k`. Mathlib's subbox partition theorem turns this into the induction
that loses the factor $`\delta=1-\eta` at each level.
:::

A matching upper estimate for subsolutions and a chain of cubes across the
domain finish the proof. The signed potential is absorbed by multiplying $`u` by an
exponential in an added coordinate, which turns $`c` into a drift in one more
dimension.

:::theorem "elliptic.harnack.variable_coefficients" (parent := "elliptic.representation") (lean := "EllipticHarnack.exists_harnack_constant, EllipticHarnack.exists_harnack_constant_of_ae_bounds") (uses := "elliptic.maximum.matrix_operator, elliptic.harnack.level_decay, elliptic.harnack.compact_comparison")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.4.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U` be open and bounded and let $`V` be preconnected with
$`\overline V\subseteq U`. Let $`a`, $`b`, $`c` be continuous on $`U` with
bounded ranges, with $`a` symmetric and
$`\sum_{i,j}a_{ij}(x)v_iv_j\ge\alpha|v|^2` for almost every $`x\in U`, where
$`\alpha>0`. There is $`C>0` such that every $`u\in C^2(U)` with $`u\ge0`
and $`Lu=0` in $`U` satisfies

$$`\sup_V u\le C\,\inf_V u.`

The potential $`c` may have either sign. The second Lean statement replaces
the bounded ranges by essential bounds.
:::

:::proof "elliptic.harnack.variable_coefficients" (uses := "elliptic.harnack.level_decay")
Continuity turns the almost-everywhere bounds and ellipticity into pointwise
ones on the open set $`U`. Compactness of $`\overline V` and connectedness of
$`V` give a finite chain of small balls in $`U`. On each ball the level decay
bounds the infimum from below and the upper estimate bounds the supremum, with
constants fixed by $`\alpha`, the coefficient bounds, and the radius. Multiplying
along the chain gives one constant for all pairs of points of $`V`.
:::
