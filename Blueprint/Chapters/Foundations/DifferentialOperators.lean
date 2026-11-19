/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Foundations.ProblemFamilies
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian
import PDE.FDeriv.Laplacian.Isometry
import PDE.FDeriv.Laplacian.Product

/-!
# Differential operators

The coordinate derivatives and linear operators used
throughout the book.
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
#doc (Manual) "Coordinate derivatives and vector operators" =>

PDE formulas are written with gradients, divergences, Laplacians, and
transport derivatives, while Mathlib's calculus is organized around the
Fréchet derivative. We set up the dictionary between those two
languages. Coordinate derivatives are obtained by evaluating the Fréchet
derivative on Euclidean basis vectors; the vector operators are then assembled
from those coordinates.

# Why the Fréchet derivative

The Fréchet derivative requires one continuous linear map $`L` giving the
uniform approximation $`f(x+h)=f(x)+Lh+o(\|h\|)` as $`\|h\|\to0`.
Existence of a derivative along every line is weaker, even in finite
dimensions: all directional derivatives can vanish at a point where the
function is not continuous. Even linearity and continuity of the resulting
map of directions do not replace the uniform remainder estimate.
Continuous partial derivatives on a neighborhood are a sufficient
finite-dimensional condition for Fréchet differentiability. Using the
Fréchet derivative gives the same chain-rule framework for Euclidean fields
and for maps between the function spaces used in PDE existence theory.

Here $`o(\|h\|)` means that the norm of the error, divided by $`\|h\|`,
tends to zero in every direction at once. For the running polynomial
$`f(x,y)=x^2-y^2`, the calculation is exact:

$$`
f(x+a,y+b)-f(x,y)=2xa-2yb+(a^2-b^2).
`

The linear part is $`L(a,b)=2xa-2yb`. Since
$`|a^2-b^2|\leq a^2+b^2`, the error divided by
$`\sqrt{a^2+b^2}` is at most $`\sqrt{a^2+b^2}`, which tends to zero.
Evaluating $`L` on the two basis vectors gives $`2x` and $`-2y`;
these are the entries of the gradient. Differentiating them once more gives
the Laplacian $`2-2=0`.

The cost of this uniformity is that many natural PDE objects (solutions with
corners, shock profiles, and distributional fields) are not Fréchet
differentiable. When that happens, the derivative is replaced by a
distributional or weak surrogate from the distribution theory or the Sobolev
theory. Regularity theorems then supply conditions under which these weak
derivatives agree with classical derivatives.

Evans (2010, Appendices A.3–A.4) fixes the finite-dimensional notation;
the infinite-dimensional theory originates with Fréchet (1906) and is treated
systematically in Cartan (1971) and Lang (1995).

# Conventions

One convention matters throughout the book: `fderiv`, and hence each operator
defined from it, is a total Lean function. At a point where the field is not
differentiable it still has a formal value, normally zero. The definitions
therefore describe operator expressions, while theorems that interpret
them analytically carry differentiability or $`C^k` hypotheses explicitly.
This separation lets the same operators appear in classical equations,
symbolic residuals, and weak-form bridges without storing regularity inside
every expression.

Several locality statements refer to the *germ* of a function at $`x`.
This means its values on some neighborhood of $`x`, with functions identified
when they agree on a possibly smaller neighborhood. A derivative can depend
on these nearby values without depending on the function far away.

:::group "foundations.derivatives"
Differential operators
:::

:::definition "foundations.derivatives.partial" (parent := "foundations.derivatives") (lean := "PDE.partialDeriv") (uses := "foundations.euclidean_space.type")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "701"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the $`i`th Euclidean basis vector $`e_i`, the coordinate derivative is

$$`
  \partial_i f(x):=Df(x)[e_i].
`

The implementation `partialDeriv i f x` evaluates Mathlib's total Fréchet
derivative on $`e_i`. It is therefore a total expression even when $`f` is
not differentiable, and denotes the classical partial derivative only under
the corresponding differentiability hypothesis.
:::

Higher derivatives are iterated coordinate derivatives, indexed by a finite word
of coordinates rather than by a multi-index. Words keep the order of application
explicit, which matters until enough regularity is available to commute
derivatives.

:::definition "foundations.derivatives.iterated" (parent := "foundations.derivatives") (lean := "PDE.iteratedPartialDeriv") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "701"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A derivative word $`\alpha=[i_1,\ldots,i_m]` and a field
$`f:\mathbb R^n\to E`, where $`E` is any real normed vector space, determine
the recursion

$$`
  D_{[]}f:=f,\qquad
  D_{i::\alpha}f:=\partial_i(D_\alpha f).
`

Consequently,

$$`
  D_{[i_1,\ldots,i_m]}f
  =\partial_{i_1}\bigl(\partial_{i_2}(\cdots\partial_{i_m}f)\bigr).
`

The head of the Lean list is the outermost derivative, while the final list
entry is the derivative applied to $`f` first.

The construction does not require a scalar codomain. Every recursive stage
still maps $`\mathbb R^n` to the same normed space $`E`, so coordinate
differentiation can be iterated for vector-, matrix-, or function-space-valued
fields without introducing a second definition. Statements that interpret
the totalized expression analytically supply the regularity needed at every
iteration.
:::

The recursion peels off the head of the word, so the first check concerns the
other end.

:::theorem "foundations.derivatives.iterated_append" (parent := "foundations.derivatives") (lean := "PDE.iteratedPartialDeriv_append_single") (uses := "foundations.derivatives.iterated")
Appending a coordinate to the right of a derivative word means that this new
coordinate derivative acts on the original field first:

$$`
  D_{\alpha\mathbin{+\!\!+}[i]}f
  =D_\alpha(\partial_i f).
`

This theorem pins down the list-order convention. It holds for fields with
arbitrary real normed-space codomain and is an identity between totalized
derivative expressions, with no smoothness assumption.
:::

:::proof "foundations.derivatives.iterated_append"
Induct on the list $`\alpha`. For the empty list, both sides reduce to
$`\partial_i f`. For $`\alpha=j::\beta`, unfold one recursive layer on each
side. Both expressions become $`\partial_j` applied to the induction
hypothesis for $`\beta`, so they agree definitionally after rewriting.
:::

Repeating a single coordinate connects the word calculus with Mathlib's
multilinear iterated Fréchet derivative. This identification is the route by
which symmetry and locality results for `iteratedFDeriv` are transferred to
coordinate derivatives.

:::theorem "foundations.derivatives.repeated_as_frechet" (parent := "foundations.derivatives") (lean := "PDE.iterate_partialDeriv_eq_iteratedFDeriv_single") (uses := "foundations.derivatives.iterated")
Let $`D_i` denote coordinate differentiation in direction $`e_i`. If
$`f:\mathbb R^n\to E` is $`C^m` at $`x`, then

$$`
  (D_i^m f)(x)
  =D^m f(x)[e_i,\ldots,e_i].
`

Here the right side is Mathlib's $`m`-linear iterated Fréchet derivative
evaluated on $`m` copies of the same coordinate vector. The codomain $`E` is
an arbitrary real normed vector space. The theorem is local: `ContDiffAt` at
$`x` suffices, and no global smoothness is required.
:::

:::proof "foundations.derivatives.repeated_as_frechet"
Induct on $`m`. At order zero both sides are $`f(x)`. At the successor step,
apply the induction hypothesis to the first coordinate derivative. Evaluation of a
continuous linear map at $`e_i` is itself a continuous linear map, so it can
be moved through the iterated Fréchet derivative. Mathlib's successor formula
for `iteratedFDeriv` then identifies the result with the next multilinear
derivative evaluated on one additional copy of $`e_i`.
:::

Each coordinate derivative costs one order of differentiability. This
bookkeeping is needed whenever a derivative of a derivative must still be
differentiated, for instance in the block-commutation law.

:::theorem "foundations.derivatives.regularity_budget" (parent := "foundations.derivatives") (lean := "PDE.contDiffAt_iterate_partialDeriv") (uses := "foundations.derivatives.repeated_as_frechet")
Coordinate differentiation uses exactly the expected finite regularity
budget. If $`f:\mathbb R^n\to E` is $`C^{m+k}` at $`x`, then

$$`
  D_i^k f\quad\text{is }C^m\text{ at }x.
`

The statement is vector-valued and point-local. Setting $`m=0` says that
$`D_i^kf` is $`C^0` at $`x`, while larger $`m` keeps smoothness in reserve
for later chain or product rules.
:::

:::proof "foundations.derivatives.regularity_budget"
Induct on $`k`. The zero case is the original regularity hypothesis. For a
successor, view one coordinate derivative as evaluation of `fderiv` on the
constant vector $`e_i`. Taking `fderiv` lowers the differentiability order by
one, and continuous-linear-map evaluation preserves the remaining order.
Apply the induction hypothesis to the resulting field.
:::

Totalized coordinate derivatives depend only on the germ of the field.

:::theorem "foundations.derivatives.germ_locality" (parent := "foundations.derivatives") (lean := "PDE.iterate_partialDeriv_congr_nhds, PDE.iterate_partialDeriv_eventuallyEq, PDE.mixed_iterate_partialDeriv_congr_nhds") (uses := "foundations.derivatives.partial")
Repeated coordinate derivatives are local operators. Suppose
$`f,g:\mathbb R^n\to E` agree on a neighborhood of $`x`.

* The repeated derivatives $`D_i^m f` and $`D_i^m g` agree on a neighborhood
  of $`x`, and in particular $`D_i^m f(x)=D_i^m g(x)`.
* The same holds after a block of $`b` derivatives in coordinate $`j`
  followed by a block of $`a` derivatives in coordinate $`i`.

No differentiability hypothesis enters, because the coordinate derivatives
are those of the totalized Fréchet derivative.
:::

:::proof "foundations.derivatives.germ_locality"
Equality of $`f` and $`g` near $`x` gives equality of their Fréchet derivatives
near $`x`, hence of each coordinate derivative. Induction on the number of
derivatives gives the first claim, and applying it to the $`j`-block and then
to the $`i`-block gives the second.
:::

The same first derivative also has a one-dimensional characterization.
Differentiability at $`x` is needed, since the totalized `fderiv` and the
one-variable `deriv` need not agree otherwise.

:::theorem "foundations.derivatives.coordinate_line" (parent := "foundations.derivatives") (lean := "PDE.partialDeriv_eq_deriv_coordinateLine") (uses := "foundations.derivatives.partial")
If $`f` is differentiable at $`x`, the coordinate derivative is the ordinary
derivative along the $`i`th coordinate line:

$$`
  \partial_i f(x)
  =\left.\frac{d}{dt}f\bigl(x+(t-x_i)e_i\bigr)\right|_{t=x_i}.
`

This connects the Fréchet definition with one-variable directional
calculations.
:::

:::proof "foundations.derivatives.coordinate_line"
Differentiate the composition of $`f` with the affine coordinate line.
The line has derivative equal to the $`i`th Euclidean basis vector and passes
through $`x` at parameter $`x_i`, so the chain rule gives exactly the
Fréchet derivative of $`f` applied to that basis vector.
:::

Linearity of $`\partial_i` is inherited from linearity of the Fréchet
derivative.

:::theorem "foundations.derivatives.linearity" (parent := "foundations.derivatives") (lean := "PDE.partialDeriv_add, PDE.partialDeriv_const_smul, PDE.partialDeriv_neg, PDE.partialDeriv_sub") (uses := "foundations.derivatives.partial")
Coordinate differentiation obeys the usual linearity identities:

$$`
  \partial_i(f+g)=\partial_i f+\partial_i g,\qquad
  \partial_i(cf)=c\,\partial_i f,
`

and hence $`\partial_i(-f)=-\partial_i f` and
$`\partial_i(f-g)=\partial_i f-\partial_i g`. The sum and difference
identities assume that $`f` and $`g` are differentiable at the point;
constant scaling and negation hold for the totalized derivative with no
hypothesis.
:::

:::proof "foundations.derivatives.linearity"
Unfold `partialDeriv` as the total Fréchet derivative evaluated on a basis
vector. Apply Mathlib's derivative rules for addition, subtraction, negation,
and constant scalar multiplication, then evaluate the resulting continuous
linear maps on that vector. The sum and difference rules use the stated
differentiability hypotheses.
:::

The iterated version has the same shape; for sums, differentiability must hold
at every stage of the word.

:::theorem "foundations.derivatives.iterated_linearity" (parent := "foundations.derivatives") (lean := "PDE.iteratedPartialDeriv_zero, PDE.iteratedPartialDeriv_add_of_contDiff, PDE.iteratedPartialDeriv_sub_of_contDiff, PDE.iteratedPartialDeriv_const_smul") (uses := "foundations.derivatives.iterated, foundations.derivatives.linearity")
For a derivative word $`\alpha` and fields
$`f,g:\mathbb R^n\to E`,

$$`
  D_\alpha 0=0,\qquad
  D_\alpha(cf)=cD_\alpha f.
`

These two identities are unconditional because the total Fréchet derivative
commutes with zero and constant scalar multiplication even at
nondifferentiability points. If $`f` and $`g` are globally $`C^m`, where
$`m` is the length of $`\alpha`, then

$$`
  D_\alpha(f+g)=D_\alpha f+D_\alpha g,\qquad
  D_\alpha(f-g)=D_\alpha f-D_\alpha g.
`

All four statements allow an arbitrary real normed-space codomain $`E`.
:::

:::proof "foundations.derivatives.iterated_linearity"
Induct on $`\alpha`. The empty word reduces to the corresponding pointwise
algebra identity. At a successor word, unfold the outer coordinate
derivative. Zero and scalar multiplication use their unconditional
single-derivative rules. For addition and subtraction, global $`C^m`
regularity makes every derivative along a proper tail of the word
differentiable, so the
single-coordinate sum or difference rule applies at the next step.
:::

Commuting two different coordinates is the first place where second-order
regularity is essential.

:::theorem "foundations.derivatives.mixed_commutation" (parent := "foundations.derivatives") (lean := "PDE.partialDeriv_partialDeriv_comm_at, PDE.partialDeriv_partialDeriv_comm_of_contDiff, PDE.partialDeriv_iterate_partialDeriv_comm, PDE.iterate_partialDeriv_comm") (uses := "foundations.derivatives.iterated, foundations.derivatives.regularity_budget")
For a $`C^2` field $`f:\mathbb R^n\to E` with arbitrary real normed-space
codomain, mixed coordinate derivatives commute:

$$`
  \partial_i\partial_j f=\partial_j\partial_i f.
`

The pointwise theorem requires only `ContDiffAt ℝ 2 f x`; its global
function-valued form assumes `ContDiff ℝ 2 f`. For a globally $`C^{a+b}`
field we also have the finite-block law

$$`
  D_i^a(D_j^b f)=D_j^b(D_i^a f).
`
:::

:::proof "foundations.derivatives.mixed_commutation"
The $`C^2` hypothesis gives symmetry of the second Fréchet derivative.
Evaluate that symmetric bilinear map on the two coordinate basis vectors,
identify the evaluations with the two iterated partial derivatives, and use
function extensionality for the global form. For finite blocks, induct on one
block length, commute one outer derivative past the other block, and use the
regularity-budget theorem to retain the smoothness needed by the induction
hypothesis.
:::

The vector operators are assembled from coordinate derivatives.

:::definition "foundations.operators.gradient" (parent := "foundations.derivatives") (lean := "gradient") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "701"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Euclidean gradient is the vector characterized by

$$`
  \bigl(\nabla f(x)\bigr)_i=\partial_i f(x)
  \qquad(0\leq i<n).
`

Mathlib constructs it as the Riesz representative of the totalized Fréchet
derivative, so it carries the same regularity caveat as `partialDeriv`.
:::

Divergence is the trace of the Jacobian. Composed with the gradient it gives the
Laplacian, so both definitions are made from the same `partialDeriv`.

:::definition "foundations.operators.divergence" (parent := "foundations.derivatives") (lean := "PDE.divergence") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "703"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a vector field $`F=(F_1,\ldots,F_n)`, divergence is

$$`
  \operatorname{div}F(x)
  :=\sum_{i=1}^n\partial_iF_i(x).
`

Differentiability of the component functions is supplied by the theorem using
the operator rather than hidden in the definition.
:::

The Laplacian is defined directly as the sum of the second same-coordinate
derivatives rather than as $`\operatorname{div}\nabla`, so that it is a
totalized expression in its own right.

:::definition "foundations.operators.laplacian" (parent := "foundations.derivatives") (lean := "PDE.laplacian") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "701"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Euclidean Laplacian is the coordinate trace of the second derivative:

$$`
  \Delta f(x):=\sum_{i=1}^n\partial_i^2f(x).
`

For scalar fields this gives the operator in the classical Laplace and Poisson
equations of Evans Chapter 2. The same sum makes sense for vector fields and
complex-valued functions, so we use one definition, `PDE.laplacian`, for all of
them. Mathlib's canonical `Laplacian.laplacian` instead traces the totalized second
Fréchet derivative. The two agree under local $`C^2` regularity; for a nonsmooth
function, their totalized expressions can differ.
:::

Locality of the Laplacian is inherited from the locality of `fderiv`. It is the
germ statement behind the radial computations, where a first-derivative
identity valid near $`x` is differentiated again at $`x`.

:::theorem "foundations.operators.laplacian_locality" (parent := "foundations.derivatives") (lean := "EuclideanLaplacian.laplacian_congr_nhds") (uses := "foundations.operators.laplacian, foundations.derivatives.germ_locality")
The Laplacian depends only on the germ of a field with values in a real normed space. If
$`f=g` throughout a neighborhood of $`x`, then

$$`
  \Delta f(x)=\Delta g(x).
`

The theorem is stated for the totalized coordinate Laplacian and has no
differentiability hypothesis; its content is locality of the totalized Fréchet
derivatives.
:::

:::proof "foundations.operators.laplacian_locality"
Unfold the Laplacian as a finite sum of same-coordinate second derivatives.
Neighborhood equality is preserved by the first coordinate derivative on a
possibly smaller neighborhood, and locality of the second derivative gives
equality of each summand at $`x`. Sum these coordinatewise equalities.
:::

The first explicit computation is the squared norm. It is smooth everywhere,
including the origin, so its identities hold with no hypothesis.

:::theorem "foundations.operators.laplacian_norm_sq" (parent := "foundations.derivatives") (lean := "EuclideanLaplacian.partialDeriv_norm_sq, EuclideanLaplacian.laplacian_norm_sq") (uses := "foundations.derivatives.partial, foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`x\in\mathbb R^n`,
$$`
  \partial_i\lVert x\rVert^2=2x_i,
  \qquad
  \Delta\lVert x\rVert^2=2n.
`
:::

:::proof "foundations.operators.laplacian_norm_sq"
Differentiate the squared norm using the inner-product formula to obtain
$`\partial_i\lVert x\rVert^2=2x_i`. Differentiating once more gives $`2` in
each coordinate. The Laplacian is therefore the sum of $`n` copies of $`2`,
namely $`2n`.
:::

Composing a one-variable profile with the squared norm gives the first radial
chain rule for the Laplacian.

:::theorem "foundations.operators.laplacian_comp_norm_sq" (parent := "foundations.derivatives") (lean := "EuclideanLaplacian.laplacian_comp_norm_sq") (uses := "foundations.operators.laplacian_norm_sq, foundations.operators.laplacian_locality")
Let $`q(x)=\lVert x\rVert^2`. If
$`f:\mathbb R\to\mathbb R` is $`C^2` at $`q(x)`, then

$$`
  \Delta(f\circ q)(x)
  =4\lVert x\rVert^2 f''(\lVert x\rVert^2)
   +2n f'(\lVert x\rVert^2).
`

In Lean, $`f'` and $`f''` are written `deriv f` and
`deriv (deriv f)`. This squared-radius formulation is valid at $`x=0`;
there is no division by $`\lVert x\rVert`. It is therefore the preferred
chain rule for Gaussian profiles, heat kernels, and other radial expressions
that are naturally smooth functions of $`\lVert x\rVert^2`.
:::

:::proof "foundations.operators.laplacian_comp_norm_sq"
For every coordinate $`i`, the first chain rule gives

$$`
  \partial_i(f\circ q)(y)=2y_i f'(q(y))
`

on a neighborhood of $`x` where the local $`C^2` hypothesis propagates.
Differentiate this product once more in coordinate $`i`:

$$`
  \partial_i^2(f\circ q)(x)
  =2f'(q(x))+4x_i^2 f''(q(x)).
`

Sum over $`i`. The constant term contributes $`2n f'(q(x))`, while
$`\sum_i x_i^2=\lVert x\rVert^2` converts the second term to
$`4\lVert x\rVert^2f''(q(x))`.
:::

Composing instead with the norm itself gives the classical radial formula away
from the origin. The one-variable expression on the right is the
{bpref "foundations.coordinates.radial_laplacian"}[radial Laplacian].

:::theorem "foundations.operators.laplacian_radial" (parent := "foundations.derivatives") (lean := "EuclideanLaplacian.laplacian_radial") (uses := "foundations.operators.laplacian, foundations.operators.laplacian_locality")
Let $`x\ne0` and let $`f:\mathbb R\to\mathbb R` be $`C^2` at
$`r=\lVert x\rVert`. Then the Laplacian of the radial field
$`y\mapsto f(\lVert y\rVert)` is

$$`
  \Delta(f\circ\lVert\cdot\rVert)(x)
  =f''(r)+\frac{n-1}{r}f'(r).
`

The formal coefficient in Lean is
$`((n:\mathbb R)-1)/r`. The nonzero hypothesis is essential: the norm is not
Fréchet differentiable at the origin, and the displayed formula contains
$`1/r`. At the origin one should instead use a theorem tailored to the
profile's parity or rewrite the field through the squared radius when
possible.
:::

:::proof "foundations.operators.laplacian_radial"
Away from zero, the derivative of the norm is the linear functional
$`v\mapsto\langle x/r,v\rangle`, hence

$$`
  \partial_i(f\circ\lVert\cdot\rVert)(x)
  =f'(r)\frac{x_i}{r}.
`

Use neighborhood locality so that this first-derivative identity may be
differentiated at $`x`. The product and quotient rules give

$$`
  \partial_i^2(f\circ\lVert\cdot\rVert)(x)
  =\frac{f'(r)}r-\frac{f'(r)x_i^2}{r^3}
    +\frac{f''(r)x_i^2}{r^2}.
`

After summing, use $`\sum_i x_i^2=r^2`. The second sum becomes
$`f'(r)/r`, the third becomes $`f''(r)`, and the first consists of
$`n` copies of $`f'(r)/r`; collecting terms yields the stated
$`f''(r)+(n-1)f'(r)/r`.
:::

The same computation for an inverse power of the distance to a fixed point
produces the kernels of potential theory.

:::theorem "foundations.operators.laplacian_inverse_distance" (parent := "foundations.derivatives") (lean := "EuclideanLaplacian.laplacian_inv_dist_pow, EuclideanLaplacian.secondPartial_inv_dist_pow") (uses := "foundations.operators.laplacian")
Let $`y\in\mathbb R^n`, $`k\in\mathbb N` and $`x\ne y`. Then

$$`
\Delta_x\,\lvert x-y\rvert^{-k}=k\,(k+2-n)\,\lvert x-y\rvert^{-k-2}.
`
:::

:::proof "foundations.operators.laplacian_inverse_distance"
Write $`r=\lvert x-y\rvert`. Away from the pole,
$`\partial_i r^{-k}=-k\,r^{-k-2}(x-y)_i`, and differentiating again in the
same coordinate gives

$$`
\partial_i^2r^{-k}=-k\,r^{-k-2}+k(k+2)\,r^{-k-4}(x-y)_i^2 .
`

Summing over $`i` and using $`\sum_i(x-y)_i^2=r^2` gives
$`-nk\,r^{-k-2}+k(k+2)\,r^{-k-2}`. The derivative formulas come from a
closed-form Fréchet derivative of $`z\mapsto\operatorname{dist}(z,y)^{-k}`,
valid on the open set $`z\ne y`.
:::

For $`n\ge3` the choice $`k=n-2` makes the right side zero, so
$`\lvert x-y\rvert^{2-n}` is harmonic away from $`y`. This is the Newtonian
kernel behind the fundamental solution of Laplace's equation. The choice
$`k=n` gives $`\Delta_x\lvert x-y\rvert^{-n}=2n\,\lvert x-y\rvert^{-n-2}`, which
is used in the computations with Poisson kernels.

The radial formulas rest on a symmetry that the coordinate definition hides.
The sum $`\sum_i\partial_i^2` is written in one basis, yet it does not depend on
which orthonormal basis is chosen, so rotations, reflections and translations
of the argument commute with $`\Delta`. This is why a rotation-invariant
equation such as $`\Delta u=0` has radial solutions to look for in the first
place.

:::theorem "foundations.operators.laplacian_isometry" (parent := "foundations.derivatives") (lean := "PDE.laplacian_comp_isometry_add_at, PDE.laplacian_comp_linearIsometryEquiv_at, InnerProductSpace.laplacian_comp_linearIsometryEquiv") (uses := "foundations.operators.laplacian")
Let $`A` be a linear isometry of $`\mathbb R^n`, let $`b\in\mathbb R^n`, and
let $`f` be $`C^2` at $`Ax+b`. Then

$$`
\Delta\bigl(f(A\,\cdot+b)\bigr)(x)=(\Delta f)(Ax+b).
`

For Mathlib's basis-free Laplacian on finite-dimensional inner product
spaces the identity $`\Delta(f\circ A)=(\Delta f)\circ A` holds for any
linear isometric equivalence and needs no regularity.
:::

:::proof "foundations.operators.laplacian_isometry"
Mathlib's Laplacian is the trace of the second derivative, and that trace
can be computed in any orthonormal basis. Computing
$`\Delta(f\circ A)` in the standard basis $`(e_i)` is the same as computing
$`\Delta f` at $`Ax` in the orthonormal basis $`(Ae_i)`. Where $`f` is
$`C^2`, the coordinate Laplacian agrees with Mathlib's, which gives the
linear case, and the translation $`y\mapsto y+b` does not change second
derivatives.
:::

Products obey the Leibniz rule with one cross term, which is the gradient
pairing counted twice.

:::theorem "foundations.operators.laplacian_product" (parent := "foundations.derivatives") (lean := "PDE.laplacian_mul, PDE.secondPartialDeriv_mul") (uses := "foundations.operators.laplacian, foundations.derivatives.partial")
If $`f` and $`g` are $`C^2` at $`x`, then

$$`
\Delta(fg)(x)=\Delta f(x)\,g(x)+2\sum_{i=1}^n\partial_if(x)\,\partial_ig(x)+f(x)\,\Delta g(x),
`

and each mixed second derivative satisfies
$`\partial_i\partial_j(fg)=\partial_i\partial_jf\,g+\partial_jf\,\partial_ig
+\partial_if\,\partial_jg+f\,\partial_i\partial_jg` at $`x`.
:::

:::proof "foundations.operators.laplacian_product"
Apply the product rule to $`\partial_j(fg)=\partial_jf\,g+f\,\partial_jg` on a
neighbourhood of $`x`, where both factors are differentiable, and
differentiate once more in direction $`i`. Setting $`i=j` and summing over
$`i` collects the two cross terms into $`2\sum_i\partial_if\,\partial_ig`.
:::

Returning to the vector operators, the only input needed to compare the
Laplacian with $`\operatorname{div}\nabla` is the
{bpref "foundations.operators.gradient_agreement"}[coordinate law for the gradient].

:::theorem "foundations.operators.laplacian_as_div_gradient" (parent := "foundations.derivatives") (lean := "PDE.laplacian_eq_divergence_gradient") (uses := "foundations.operators.gradient,foundations.operators.divergence,foundations.operators.laplacian")
The coordinate Laplacian agrees with the divergence of the canonical
gradient:

$$`
  \Delta f=\operatorname{div}(\nabla f).
`

Both sides use the same totalized Fréchet-calculus convention.
:::

:::proof "foundations.operators.laplacian_as_div_gradient"
By definition, $`\operatorname{div}(\nabla f)=\sum_i\partial_i(\nabla f)_i`. The gradient
agreement theorem identifies $`(\nabla f)_i=\partial_i f`, so each summand
becomes $`\partial_i(\partial_i f)=\partial_i^2 f`. The resulting sum
$`\sum_i\partial_i^2 f` is the coordinate definition of $`\Delta f`. The
identity is purely algebraic in the totalized expressions; no
differentiability hypothesis is used.
:::

Mathlib defines the gradient as a Riesz representative, so its coordinate law is
a theorem rather than a definition.

:::theorem "foundations.operators.gradient_agreement" (parent := "foundations.derivatives") (lean := "PDE.gradient_apply_eq_partialDeriv") (uses := "foundations.operators.gradient")
For every coordinate $`i`,

$$`
  \bigl(\nabla f(x)\bigr)_i=\partial_i f(x).
`

This is an identity between totalized expressions, because both sides use the
same Fréchet derivative.
:::

:::proof "foundations.operators.gradient_agreement"
Write the $`i`th gradient coordinate as its inner product with the $`i`th
Euclidean basis vector. Mathlib's defining gradient identity turns this into
the Fréchet derivative applied to that vector, which is the definition of
`partialDeriv`.
:::

The coordinate law is the case $`v=e_i` of the defining property of the
gradient.

:::theorem "foundations.operators.fderiv_gradient_pairing" (parent := "foundations.derivatives") (lean := "inner_gradient_left") (uses := "foundations.operators.gradient_agreement")
For every scalar field and direction $`v`, Mathlib's totalized gradient pairing satisfies
$$`
  \langle \nabla f(x),v\rangle=Df(x)[v].
`
This is an unconditional identity between totalized Lean expressions.
:::

:::proof "foundations.operators.fderiv_gradient_pairing"
Mathlib defines the Euclidean gradient as the Riesz representative of the
Fréchet derivative. The Riesz representation identity evaluated at $`v`
is precisely $`\langle\nabla f(x),v\rangle=Df(x)[v]`.
:::

The coordinate expansion of the Fréchet derivative is the common lemma behind
scalar advection and vector-valued transport.

:::theorem "foundations.operators.fderiv_coordinates" (parent := "foundations.derivatives") (lean := "PDE.fderiv_apply_eq_sum_smul_partialDeriv, PDE.fderiv_apply_eq_sum_partialDeriv_mul") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "701"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a field $`f : \mathbb R^n\to E` with arbitrary real normed-space codomain,
the Fréchet derivative expands in the Euclidean basis as
$$`
  Df(x)[v]=\sum_i v_i\,\partial_i f(x).
`
The scalar specialization rewrites scalar multiplication as ordinary real
multiplication. Both identities hold for the totalized derivative.
:::

:::proof "foundations.operators.fderiv_coordinates"
Expand $`v` in the standard Euclidean basis and use linearity of
$`Df(x)`. Each basis-vector evaluation is the corresponding `partialDeriv`,
which gives the vector-valued sum. In the scalar case, rewrite real scalar
multiplication as ordinary multiplication and commute the factors.
:::

The advective derivative is the Fréchet derivative evaluated along the velocity
field itself. Defining it this way, rather than through the coordinate formula,
keeps scalar and vector-valued transport under one definition.

:::definition "foundations.operators.advection" (parent := "foundations.derivatives") (lean := "PDE.advectiveDerivative") (uses := "foundations.operators.fderiv_coordinates")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a velocity field $`u` and a field $`f` with arbitrary normed-space
codomain, the advective derivative is
$$`
  (u\mathbin{\cdot}D)f(x)=Df(x)[u(x)].
`
:::

:::theorem "foundations.operators.scalar_advection_coordinates" (parent := "foundations.derivatives") (lean := "PDE.advectiveDerivative_eq_sum_mul_partialDeriv") (uses := "foundations.operators.advection, foundations.operators.fderiv_coordinates")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "18"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a scalar field, the Fréchet definition expands exactly to the familiar
coordinate expression
$$`
  (u\mathbin{\cdot}D)f(x)=\sum_i u_i(x)\,\partial_i f(x).
`
This equality is algebraic in the totalized Fréchet derivative.
:::

:::proof "foundations.operators.scalar_advection_coordinates" (uses := "foundations.operators.fderiv_coordinates")
Unfold advection as $`Df(x)[u(x)]` and apply the scalar coordinate expansion
of the Fréchet derivative with direction $`u(x)`. Commutativity of real
multiplication puts each summand in the conventional order
$`u_i(x)\partial_i f(x)`.
:::
