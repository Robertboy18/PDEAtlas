/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.Asymptotics
import PDE.Analysis.Approximation.Splines.CoxDeBoor
import PDE.Analysis.Approximation.Splines.NormalizedBasis
import PDE.Analysis.Approximation.Splines.SchoenbergWhitney
import PDE.Analysis.Approximation.Splines.SchoenbergWhitneyRefinement

/-!
# B-splines and Schoenberg–Whitney collocation

The Cox–de Boor recursion on nondecreasing knot
sequences, its support and positivity theorems, the collocation matrix, the
Schoenberg–Whitney interlacing theorem, and the positive `LDU` certificate
through which a validated backend proves collocation nonsingularity.
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
#doc (Manual) "B-Splines and Schoenberg–Whitney Collocation" =>

:::group "methods.splines"
Spline approximation
:::

# Cox–de Boor B-splines

B-splines are the standard basis for certified piecewise-polynomial
approximation. A collocation matrix with a checked positive determinant
certifies that a finite family is linearly independent. Tensor products of these one-dimensional
families provide profile representations on rectangles.

:::definition "methods.splines.knot_sequence" (parent := "methods.splines") (lean := "CAS.Splines.KnotSequence")
A knot sequence is a nondecreasing map

$$`
t:\mathbb N\to\mathbb R,\qquad i\le j\ \Longrightarrow\ t_i\le t_j,
`

bundled as an order homomorphism. Repeated knots are allowed, and a finite
knot vector is represented by repeating its final knot with the desired
endpoint multiplicity.
:::

Monotonicity of the knots is the only structure the recursion needs. The
blending weights divide by the knot differences $`t_{i+p+1}-t_i` and
$`t_{i+p+2}-t_{i+1}`, which are nonnegative because the sequence is
nondecreasing and may vanish when knots repeat.

:::definition "methods.splines.cox_de_boor_basis" (parent := "methods.splines") (lean := "CAS.Splines.coxDeBoorBasis, CAS.Splines.leftBlendWeight, CAS.Splines.rightBlendWeight, CAS.Splines.finiteCoxDeBoorBasis") (uses := "methods.splines.knot_sequence")
The degree-zero B-spline with index $`i` is the indicator of the half-open
knot cell $`[t_i,t_{i+1})`, and the recursion

$$`
N_{i,p+1}(x)
=\frac{x-t_i}{t_{i+p+1}-t_i}\,N_{i,p}(x)
+\frac{t_{i+p+2}-x}{t_{i+p+2}-t_{i+1}}\,N_{i+1,p}(x)
`

defines the higher degrees, with the convention that a quotient with zero
denominator equals zero. That convention is Lean's totalized division, and it
is exactly the standard treatment of repeated knots. A finite family selects
the indices $`0\le i<m` of a fixed degree.
:::

With knots $`t_0=0`, $`t_1=1`, and $`t_2=2`, one step of the recursion
produces the familiar degree-one hat:

$$`
N_{0,1}(x)=
\begin{cases}
x,&0\leq x<1,\\
2-x,&1\leq x<2,\\
0,&\text{otherwise}.
\end{cases}
`

Only the two adjacent cells contribute. In a linear combination of such
basis functions, changing one coefficient changes the function only near
that coefficient's knot interval. The support theorem states this
locality. Whether specified sample values determine the coefficients
uniquely is a different question, answered by the collocation theorem.

The recursion combines $`N_{i,p}` and $`N_{i+1,p}` with weights that are
nonnegative on the supports $`[t_i,t_{i+p+1})` and $`[t_{i+1},t_{i+p+2})` of
those two children, and both supports lie inside $`[t_i,t_{i+p+2})`.
Induction on the degree therefore propagates support and sign information
from the degree-zero indicators, and the strict positivity statement is what
the Schoenberg–Whitney diagonal condition later relies on.

:::theorem "methods.splines.cox_de_boor_support" (parent := "methods.splines") (lean := "CAS.Splines.coxDeBoorBasis_mem_support, CAS.Splines.coxDeBoorBasis_eq_zero_of_lt_left, CAS.Splines.coxDeBoorBasis_eq_zero_of_right_le, CAS.Splines.coxDeBoorBasis_nonneg, CAS.Splines.coxDeBoorBasis_pos_of_mem_support_interior") (uses := "methods.splines.cox_de_boor_basis")
For every nondecreasing knot sequence, degree $`p`, and index $`i`,

$$`
N_{i,p}(x)\ne0\ \Longrightarrow\ x\in[t_i,t_{i+p+1}),
\qquad
N_{i,p}\ge0,
`

so the B-spline vanishes for $`x<t_i` and for $`x\ge t_{i+p+1}`. Moreover
it is strictly positive on the open interior of its canonical support,

$$`
t_i<x<t_{i+p+1}\ \Longrightarrow\ N_{i,p}(x)>0,
`

including when interior knots are repeated.
:::

:::proof "methods.splines.cox_de_boor_support"
All statements are proved by induction on the degree. At degree zero they
are properties of the indicator of a half-open cell. In the recursion, a
nonzero value requires one of the two child B-splines to be nonzero, and the
child supports $`[t_i,t_{i+p+1})` and $`[t_{i+1},t_{i+p+2})` lie inside
$`[t_i,t_{i+p+2})`. On those supports both blending weights are
nonnegative, giving nonnegativity. For strict positivity, away from a
repeated knot block one of the two children is positive by induction and its
weight is positive; when the point coincides with an entire block of equal
knots, the left-clamped identity $`N=1` resolves the right-continuous
convention.
:::

Nonnegativity and local support describe individual B-splines; linear
independence of a finite family is a statement about all of them at once,
and the cleanest certificate for it is a matrix. Evaluating $`m` functions at
$`m` points gives a square matrix whose nonsingularity forces any vanishing
linear combination to have zero coefficients, so independence is transferred
to the question of a nonzero determinant.

:::definition "methods.splines.collocation_matrix" (parent := "methods.splines") (lean := "CAS.Splines.collocationMatrix, CAS.Splines.linearIndependent_of_collocation_det_ne_zero")
For a finite family of functions $`B_j:X\to\Bbbk` and matching points
$`x_i\in X`, indexed by the same finite type, the collocation matrix is

$$`
A_{ij}=B_j(x_i).
`

If $`\Bbbk` is a field and $`\det A\ne0`, the family $`(B_j)` is linearly
independent as $`\Bbbk`-valued functions: a vanishing combination evaluated
at the points gives a vanishing product with $`A`, and invertibility forces
the coefficients to vanish.
:::

# Schoenberg–Whitney collocation

The Schoenberg–Whitney inequalities place each point $`x_i` strictly inside
the canonical support of $`N_{i,p}`, with the points increasing strictly. The
positivity theorem then gives a positive diagonal, although that alone does
not establish nonsingularity.

:::definition "methods.splines.schoenberg_whitney_condition" (parent := "methods.splines") (lean := "CAS.Splines.SchoenbergWhitneyCondition, CAS.Splines.SchoenbergWhitneyCondition.diagonal_pos, CAS.Splines.SchoenbergWhitneyCondition.mem_support_interior, CAS.Splines.SchoenbergWhitneyCondition.strictMono") (uses := "methods.splines.knot_sequence, methods.splines.cox_de_boor_basis, methods.splines.collocation_matrix")
A family of sample points $`x_0<x_1<\dots<x_{m-1}` satisfies the
Schoenberg–Whitney condition for the degree-$`p` B-splines
$`N_{0,p},\dots,N_{m-1,p}` when it is strictly increasing and

$$`
t_i<x_i<t_{i+p+1}\qquad(0\le i<m).
`

Each sample point then lies in the open interior of the canonical support of
its own B-spline, so every diagonal entry $`N_{i,p}(x_i)` of the collocation
matrix is strictly positive, including at repeated interior knots.
:::

The interlacing inequalities are sufficient for a positive determinant. They
are not necessary under the half-open endpoint convention: a left-clamped
B-spline can take value one at its left endpoint.

:::theorem "methods.splines.schoenberg_whitney" (parent := "methods.splines") (lean := "CAS.Splines.SchoenbergWhitneyCondition.det_collocation_pos, CAS.Splines.SchoenbergWhitneyCondition.det_collocation_ne_zero, CAS.Splines.SchoenbergWhitneyCondition.linearIndependent") (uses := "methods.splines.schoenberg_whitney_condition, methods.splines.collocation_matrix")
If the points $`x_0<\dots<x_{m-1}` satisfy the Schoenberg–Whitney condition
for an arbitrary nondecreasing knot sequence, repeated knots included, then

$$`
\det\bigl[N_{j,p}(x_i)\bigr]_{0\le i,j<m}>0.
`

In particular the collocation matrix is nonsingular and the B-splines
$`N_{0,p},\dots,N_{m-1,p}` are linearly independent real functions.
:::

:::proof "methods.splines.schoenberg_whitney" (uses := "methods.splines.cox_de_boor_support")
Insert $`p+1` copies of each sample point so that its tracked refined
support begins with $`p+1` equal knots and ends strictly to their right.
Boehm's knot-insertion formula expresses every
coarse B-spline as a nonnegative combination of two adjacent refined
B-splines, so each insertion factors the coarse collocation matrix as the
refined collocation matrix times a bidiagonal matrix with nonnegative
entries, and such matrices are totally nonnegative on ordered minors. At a
fully clamped knot the refined B-splines evaluate as a Kronecker delta, so
after all insertions the refined collocation rows selected by the sample
points form an identity minor. The rectangular Cauchy–Binet formula writes
the coarse determinant as a sum of products of ordered minors, all
nonnegative; tracking one strictly positive ordered minor through every
insertion, which the interlacing inequalities guarantee, makes the sum
strictly positive. Nonsingularity and the collocation criterion then give
linear independence.
:::

The geometric theorem certifies collocation for B-splines at interlaced
points. A numerical backend often holds a concrete matrix and a computed
factorization instead, and wants nonsingularity without invoking any theory
of the basis; for that purpose the factorization itself, with unit-triangular
factors and positive pivots, is the certificate, since its determinant is
the product of the pivots.

:::definition "methods.splines.positive_ldu_certificate" (parent := "methods.splines") (lean := "CAS.Splines.PositiveLDUCertificate")
For a square matrix $`A` over a linearly ordered commutative ring with
strictly ordered multiplication, a positive $`LDU` certificate consists of
matrices $`L`, $`U` and pivots $`d_i>0` with

$$`
A=L\,\operatorname{diag}(d)\,U,
`

where $`L` is lower triangular with unit diagonal and $`U` is upper
triangular with unit diagonal. The certificate stores no determinant
assertion; a validated backend supplies the factors, and Lean checks the
product, the triangular structure, the unit diagonals, and the positivity of
every pivot.
:::

Checking a certificate is exact arithmetic: multiply the three factors,
compare with $`A`, and inspect the diagonals and the signs of the pivots. The
family behind $`A` need not consist of B-splines.

:::theorem "methods.splines.positive_ldu_det_pos" (parent := "methods.splines") (lean := "CAS.Splines.PositiveLDUCertificate.det_pos, CAS.Splines.PositiveLDUCertificate.det_ne_zero, CAS.Splines.PositiveLDUCertificate.linearIndependent") (uses := "methods.splines.positive_ldu_certificate, methods.splines.collocation_matrix")
A valid positive $`LDU` certificate for $`A` proves

$$`
\det A>0,
`

hence $`\det A\ne0`. When $`A` is the collocation matrix of a finite family
of functions at matching points over a linearly ordered field, the family is
therefore linearly independent.
:::

:::proof "methods.splines.positive_ldu_det_pos"
The determinant is multiplicative, the determinant of a triangular matrix is
the product of its diagonal entries, which are all one, and the determinant
of the diagonal factor is the product of the pivots, a product of strictly
positive elements. The collocation criterion converts nonvanishing of the
determinant into linear independence.
:::
