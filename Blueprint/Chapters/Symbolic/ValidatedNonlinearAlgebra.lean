/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.CertificateWorkflows
import CAS.Continuum.IntervalEval.Affine
import CAS.Continuum.Krawczyk.Interval
import CAS.Continuum.MatrixVerification.Expression
import CAS.Continuum.MatrixVerification.RowSum
import CAS.Polynomial.RealRoot.IntervalNewton

/-!
## Validated nonlinear algebra

The affine-arithmetic, interval-Newton, and finite-matrix
verification kernels used by checked numerical planners.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Validated Nonlinear Algebra" =>

Validated numerical work often begins with data that is useful but not yet a
proof: an affine approximation, a narrow interval around a suspected root, or
a floating-point approximation to a matrix inverse. Each kernel comes with
the small mathematical obligation that turns such a proposal into an ordinary
Lean theorem: an enclosure, a uniqueness claim, or an invertibility theorem.

:::definition "symbolic.affine_model" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "CAS.Continuum.AffineModel.Represents, CAS.Continuum.AffineModel.range")
An affine model consists of an exact rational affine form $`A(\varepsilon)`
and a rational interval $`R` for the terms not retained in that form. It
represents a real value $`x` when

$$`x-A(\varepsilon)\in R.`

The reported range is the interval sum of the affine range and $`R`. The noise
variables are shared between occurrences of the same input coordinate, so the
model retains dependencies that ordinary interval substitution would forget.
:::

:::theorem "symbolic.affine_model_multiplication" (parent := "symbolic.cega") (uses := "symbolic.affine_model") (lean := "CAS.Continuum.AffineModel.Represents.mul")
Suppose affine models $`M_A` and $`M_B` represent $`x` and $`y` at a common
noise assignment satisfying $`|\varepsilon_i|\leq1`. The checked product model
represents $`xy` at the same assignment.

Its affine part retains the constant and linear terms. Its interval remainder
contains the quadratic noise product, the two affine-remainder cross terms,
and the product of the old remainders.
:::

:::proof "symbolic.affine_model_multiplication"
Write $`x=A+r` and $`y=B+s`. Expand
$`xy=AB+As+Br+rs`, separate the constant-linear part of $`AB`, and enclose
the discarded quadratic term using $`\varepsilon_i^2\in[0,1]` on the diagonal
and $`\varepsilon_i\varepsilon_j\in[-1,1]` off the diagonal. The existing
rational interval addition and multiplication theorems enclose the remaining
three terms.
:::

:::theorem "symbolic.affine_box_compiler" (parent := "symbolic.cega") (uses := "symbolic.affine_model_multiplication, symbolic.finite_box_queries") (lean := "CAS.Continuum.RationalInterval.represents_unitNoise_of_compileAffine?_eq_some, CAS.Continuum.RationalInterval.affineRange?, CAS.Continuum.RationalInterval.mem_affineRange_of_memBox")
The affine compiler accepts rational constants, variables, addition,
subtraction, negation, multiplication, and natural powers. If it returns a
model for an expression on a rational box, every point of that box evaluates
inside the model's reported range.

Each input interval is recentered as $`c_i+r_i\varepsilon_i`. For any boxed
point, the recovered noise lies in $`[-1,1]` and recenters to the original
point. On unsupported expression constructors the compiler fails.
:::

:::proof "symbolic.affine_box_compiler"
Induct on the reflected expression, using the affine semantic theorem for each
accepted constructor. Recover one unit noise per input coordinate from the
boxed point, prove its magnitude is at most one, and rewrite the recentered
coordinates back to the original point. The model-range theorem then supplies
the ordinary enclosure.
:::

:::theorem "symbolic.interval_newton_certificate" (parent := "symbolic.cega") (uses := "symbolic.unique_root_bracket, symbolic.polynomial_interval_evaluation") (lean := "CAS.Polynomial.RealRoot.IntervalNewtonCertificate.root_mem_image, CAS.Polynomial.RealRoot.IntervalNewtonCertificate.existsUnique_root, CAS.Polynomial.RealRoot.IntervalNewtonCertificate.nonzeroOn_of_excludesRoots_eq_true")
A checked interval-Newton step for a rational univariate polynomial uses a nondegenerate input
interval and a sign-definite interval enclosure of the derivative. It checks
the proposed image against the exact Newton image computed from the midpoint.
Every input root lies in that image.

For the checked Newton image $`N(I)`, the localization contract is

$$`x\in I\ \land\ p(x)=0\quad\Longrightarrow\quad x\in N(I).`

If endpoint signs bracket a root, derivative nonvanishing gives exactly one
root in the input interval. If the checked image is disjoint from the input,
the input interval contains no root:

$$`N(I)\cap I=\varnothing
  \quad\Longrightarrow\quad
  \forall x\in I,\ p(x)\ne0.`

Both conclusions are local to the stated interval.
:::

:::proof "symbolic.interval_newton_certificate"
The mean value theorem expresses a root relative to the interval midpoint.
The derivative enclosure and its sign select a valid reciprocal interval, so
interval arithmetic places the root in the proposed Newton image. Endpoint
signs give existence by the intermediate value theorem and strict monotonicity
gives uniqueness. Disjointness contradicts image membership and therefore
proves root exclusion.
:::

For $`p(x)=x^2-2` on $`I=[1,2]`, take the midpoint $`m=3/2`.
Then $`p(m)=1/4` and $`p'(I)\subseteq[2,4]`. Any root $`z\in I`
satisfies $`0=p(m)+p'(\xi)(z-m)` for some intermediate $`\xi`, hence

$$`
z\in m-\frac{p(m)}{[2,4]}
=\frac32-\left[\frac1{16},\frac18\right]
=\left[\frac{11}{8},\frac{23}{16}\right].
`

This narrows a width-one bracket to width $`1/16`. The endpoint signs
$`p(1)<0<p(2)` establish existence, and $`p'>0` establishes uniqueness.
The Newton-image calculation localizes that root; its localization
implication alone would also be true if there were no root.

:::definition "symbolic.approximate_inverse_candidate" (parent := "symbolic.cega") (lean := "CAS.Continuum.MatrixVerification.ApproximateInverseCandidate, CAS.Continuum.MatrixVerification.ApproximateInverseCandidate.IsCertified")
For finite square matrices, an approximate-inverse candidate stores a target
matrix $`A`, a proposed inverse $`B`, and a nonnegative residual bound
$`\eta`. The
proposal contains no proof. Certification requires

$$`\lVert I-BA\rVert\leq\eta<1`

in Mathlib's Euclidean matrix operator norm.
:::

:::theorem "symbolic.approximate_inverse_neumann" (parent := "symbolic.cega") (uses := "symbolic.approximate_inverse_candidate") (lean := "CAS.Continuum.MatrixVerification.ApproximateInverseCandidate.matrix_isUnit, CAS.Continuum.MatrixVerification.ApproximateInverseCandidate.toEuclideanCLM_bijective, CAS.Continuum.MatrixVerification.ApproximateInverseCandidate.inverse_sub_proposedInverse_norm_le")
Every certified approximate inverse proves that $`A` is a unit and that its
Euclidean continuous linear operator is bijective. It also gives the
a posteriori estimate

$$`\lVert A^{-1}-B\rVert
  \leq \eta\,\lVert A^{-1}\rVert.`

The proposed inverse need not equal $`A^{-1}`.
:::

:::proof "symbolic.approximate_inverse_neumann"
The strict residual bound makes $`I-(I-BA)=BA` a unit by Mathlib's Neumann
theorem. Direct finiteness of the square matrix algebra then implies that both
factors $`B` and $`A` are units. Mapping the matrix unit into continuous linear
maps gives bijectivity. Finally,
$`A^{-1}-B=(I-BA)A^{-1}` and norm submultiplicativity give the error bound.
:::

:::theorem "symbolic.approximate_inverse_row_sum" (parent := "symbolic.cega") (uses := "symbolic.approximate_inverse_neumann") (lean := "CAS.Continuum.MatrixVerification.ResidualEntryBounds.row_norm_sum_le, CAS.Continuum.MatrixVerification.ResidualEntryBounds.residual_norm_lt_one, CAS.Continuum.MatrixVerification.ResidualEntryBounds.matrix_isUnit")
An alternative checker accepts exact rational upper bounds $`u_{ij}` for the
absolute values of the entries of $`I-BA`. If every row sum of these bounds
is at most $`\eta<1`, then the
matrix infinity norm of the residual is below one and $`A` is invertible.

This route matches the output of entrywise interval evaluation. Its conclusion
is algebraic invertibility, so later Euclidean arguments do not need to
identify the infinity norm with the Euclidean operator norm.
:::

:::proof "symbolic.approximate_inverse_row_sum"
Sum the checked entry bounds along each row and use Mathlib's formula for the
matrix infinity norm as the maximum absolute row sum. The strict row-sum bound
allows the same Neumann argument for $`BA`; direct finiteness again projects
invertibility to $`A`.
:::

:::theorem "symbolic.approximate_inverse_expression_compiler" (parent := "symbolic.cega") (uses := "symbolic.approximate_inverse_row_sum, symbolic.interval_evaluator_sound") (lean := "CAS.Continuum.MatrixVerification.Expression.evalMatrix_leftResidual, CAS.Continuum.MatrixVerification.Expression.ApproximateInverseData.certify?, CAS.Continuum.MatrixVerification.Expression.ApproximateInverseData.matrix_isUnitAt")
Let $`A(x)` and the proposed inverse $`B(x)` be square matrices of reflected
real expressions. A constant rational matrix is one possible choice of $`B`.
The compiler forms $`I-B(x)A(x)`, evaluates every entry through one checked
interval context, replaces each interval by its exact endpoint absolute
maximum, and computes the largest rational row sum $`q`.

If every entry compiles and $`q<1`, then for every parameter point $`x` in
the context domain the real matrix $`A(x)` is invertible. Failure of any entry
or of the strict comparison returns `none`.
:::

:::proof "symbolic.approximate_inverse_expression_compiler"
Expression evaluation commutes with matrix multiplication, so the generated
symbolic matrix denotes the actual residual $`I-B(x)A(x)`. Interval soundness
bounds each residual entry. Summing endpoint absolute maxima bounds every row,
and taking the finite maximum gives the advertised $`q`. The checked row-sum
Neumann theorem then proves invertibility pointwise.
:::

:::definition "symbolic.krawczyk_ball_certificate" (parent := "symbolic.cega") (uses := "symbolic.approximate_inverse_candidate, symbolic.interval_newton_certificate") (lean := "CAS.Continuum.Krawczyk.Certificate, CAS.Continuum.Krawczyk.Certificate.IsCertified, CAS.Continuum.Krawczyk.residualBounds, CAS.Continuum.Krawczyk.certifyFrobenius")
For a real map $`F:\mathbb R^n\to\mathbb R^n`, a
ball-form Krawczyk proposal stores a center $`x_0`, nonnegative radius $`r`,
real approximate-inverse matrix $`B`, and nonnegative contraction bound $`q`.
Certification requires
an actual Fréchet Jacobian $`J(x)` on the closed ball together with

$$`\lVert I-BJ(x)\rVert_2\leq q<1,
\qquad
\lVert BF(x_0)\rVert_2+qr\leq r.`

For a fixed rational matrix $`B`, the interval layer encloses the entries
of $`J(x)` and compiles those bounds to $`I-BJ(x)`. Its Frobenius checker
computes the sum of squared endpoint absolute bounds in exact
nonnegative-rational arithmetic. The certificate is stated for a closed
Euclidean ball rather than for the rectangular boxes of the classical Krawczyk
operator.
:::

The two inequalities have different jobs. For $`T(x)=x-BF(x)`, the
Jacobian bound contracts distances throughout the ball. Writing
$`\eta=\|BF(x_0)\|`, the center moves by $`\eta`, so

$$`
\|T(x)-x_0\|
\leq\|T(x)-T(x_0)\|+\|T(x_0)-x_0\|
\leq qr+\eta.
`

Thus $`\eta+qr\leq r` keeps the entire image inside the ball. Equivalently,
the radius must absorb the amplified center defect $`\eta/(1-q)`. This is
the local finite-dimensional version of the defect estimate in the
{bpref "methods.semilinear.contraction"}[fixed-point chapter], with the
self-map condition checked explicitly.

:::theorem "symbolic.krawczyk_unique_zero" (parent := "symbolic.cega") (uses := "symbolic.krawczyk_ball_certificate, symbolic.approximate_inverse_neumann") (lean := "CAS.Continuum.Krawczyk.certifyFrobenius_sound, CAS.Continuum.Krawczyk.isCertified_of_intervals, CAS.Continuum.Krawczyk.Certificate.existsUnique_zero")
Every certified ball-form Krawczyk proposal proves

$$`\exists!x\in\overline B(x_0,r),\qquad F(x)=0.`

Uniqueness is local to the certified ball. The proof derives the
invertibility of $`B` from the contraction bound.
:::

:::proof "symbolic.krawczyk_unique_zero"
The map $`T(x)=x-BF(x)` has derivative $`I-BJ(x)`, hence is $`q`-Lipschitz
on the convex ball. The self-map inequality sends that ball into itself, so
Banach's fixed-point theorem gives a unique fixed point. At the center, the
same strict residual estimate proves $`BJ(x_0)` and then $`B` invertible by
the Neumann argument. Thus $`T(x)=x` implies $`BF(x)=0` and hence $`F(x)=0`.
Conversely every zero is a fixed point, which transfers fixed-point
uniqueness to zero uniqueness.
:::
