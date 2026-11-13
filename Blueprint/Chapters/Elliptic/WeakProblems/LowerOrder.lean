/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.WeakProblems.DivergenceForm
import PDE.Elliptic.Variational.LowerOrderForm
import PDE.Elliptic.Variational.ShiftedDivergenceForm
import PDE.Elliptic.Semilinear.SubSupersolution.Classical

/-!
# Lower-order divergence-form problems

The full divergence-form bilinear form, generalized loads, the Gårding shift, and
the resulting shifted solver and energy estimate.
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
#doc (Manual) "Lower-Order Divergence-Form Problems" =>

# Lower-order terms and coercive shifts

First- and zeroth-order terms need not preserve coercivity, even when the
principal coefficient matrix is uniformly elliptic. The replacement is a
Gårding inequality: the full form controls the gradient up to a multiple of
the $`L^2` norm. Adding a sufficiently large positive mass term absorbs that
loss and restores a coercive problem. This is the content of Gårding's
inequality (1953), which Evans (2010, pp. 318–319) states for $`L^\infty`
coefficients and {Informal.citet "brezis-2011"}[] (Proposition 9.22) places in the
functional-analytic framework of compact perturbations of coercive operators.

We make the threshold explicit. Bounds for the first-order
operators are combined with Young's inequality, the zeroth-order operator is
controlled by its norm, and the resulting constants determine
the coercive shift. Every larger shift gives the same uniform coercivity lower
bound and therefore a unique Lax–Milgram solution.

The forcing is written in the standard $`H^{-1}` form
$`f_0-\sum_iD_i f^i`. In Lean this is a continuous functional assembled from
one base $`L^2` component and one component for each weak derivative.

A one-dimensional model shows why a shift can be needed. Let $`L>0`.
On $`\Omega=(0,L)`, consider the operator $`-u''-cu=f` in weak form:

$$`
B_c(u,v)=\int_0^L u'v'\,dx-c\int_0^L uv\,dx.
`

Take $`\phi(x)=\sin(\pi x/L)`, the first Dirichlet eigenfunction of
$`-d^2/dx^2` on $`(0,L)` with eigenvalue $`\lambda_1=(\pi/L)^2`. Then

$$`
B_c(\phi,\phi)=\lambda_1\lVert\phi\rVert_2^2-c\lVert\phi\rVert_2^2
=(\lambda_1-c)\lVert\phi\rVert_2^2.
`

When $`c<\lambda_1`, the form is positive on every eigenspace and hence
coercive on all of $`H^1_0(0,L)`. When $`c=\lambda_1`, the form vanishes on
the one-dimensional eigenspace of $`\phi`; coercivity fails, and the equation
$`-u''-\lambda_1 u=f` has no solution unless $`f\perp\phi` (the Fredholm
alternative). When $`c>\lambda_1`, the form is negative on that eigenspace.

Adding the mass shift $`\mu\int_0^L uv` replaces $`B_c` by

$$`
B_c^\mu(u,v)=\int_0^L u'v'-c\int_0^L uv+\mu\int_0^L uv
=\int_0^L u'v'+(\mu-c)\int_0^L uv.
`

On the eigenspace of $`\phi`,
$`B_c^\mu(\phi,\phi)=(\lambda_1-c+\mu)\lVert\phi\rVert_2^2`. Thus any
$`\mu>c-\lambda_1` restores positivity in this
eigendirection, and since higher eigenvalues are larger, coercivity holds on
all of $`H^1_0`. The general Gårding estimate below performs the same
correction without diagonalizing the operator. It uses only Young's
inequality and the coefficient bounds to find an explicit $`\mu_0` that works
uniformly (Evans, 2010, pp. 318–319; {Informal.citet "gilbarg-trudinger-2001"}[], Section 8.1).

:::definition "elliptic.divergence.full_form" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.fullDivergenceForm") (uses := "elliptic.divergence.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The full bounded divergence-form bilinear form adds the first-order terms
$`\sum_i (b_iD_i u,v)_{L^2}` and the zeroth-order term
$`(cu,v)_{L^2}` to the principal form.  At the operator-valued level the
coefficients are bounded maps on $`L^2`; multiplication operators give the
local $`L^\infty` coefficient fields.
:::

Lower-order terms also change what should count as forcing. The natural dual
of $`H^1_0(\Omega)` is $`H^{-1}(\Omega)`, whose elements need not be
functions, so the loads are allowed to contain first derivatives of $`L^2`
functions from the start.

:::definition "elliptic.divergence.generalized_load" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.generalizedLoad") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "299-300"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "314-315"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
Data $`f_0,f_1,\ldots,f_n\in L^2(\Omega)` define the continuous functional

$$`v\longmapsto (f_0,v)_{L^2}+\sum_i(f_i,D_i v)_{L^2},`

which represents the distribution $`f_0-\sum_iD_i f_i` in
$`H^{-1}(\Omega)`.
:::

Whether such loads exhaust the dual space is a question about the Riesz
representation on the graph space. The answer is affirmative: the coordinates
of a Riesz representative are exactly data $`f_0,f_1,\ldots,f_n`, so nothing
is lost by stating the shifted problem only for generalized loads.

:::theorem "elliptic.divergence.generalized_load_representation" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.exists_generalizedLoad_representation") (uses := "elliptic.divergence.generalized_load")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "299-300"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every continuous functional on our $`H^1_0(\Omega)` graph space has a
representation $`f_0-\sum_iD_i f_i` with all components in $`L^2(\Omega)`.
The chosen components additionally satisfy an exact squared-norm identity
with the dual norm.  The components are coordinates of a Riesz representative
and need not be derivatives of one another.
:::

:::proof "elliptic.divergence.generalized_load_representation"
Extend the functional isometrically to the ambient base-gradient product,
take its Riesz representative, and read the base and first-derivative
coordinates as $`f_0,f_1,\ldots,f_n`.  The product-space norm decomposition
gives the squared-norm identity.
:::

The predicate below combines the full form, the generalized load, and a mass
shift $`\mu` into one distributional equation. The shift is the parameter that
will be adjusted to restore coercivity; $`\mu=0` is the original unshifted
problem, whose solvability is the Fredholm question.

:::definition "elliptic.divergence.shifted_weak_solution" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.IsWeakShiftedFullDivergenceSolution") (uses := "elliptic.divergence.full_form, elliptic.divergence.generalized_load")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314-315"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a measurable domain, $`L^\infty` coefficients $`a`, $`b`, and $`c`, a
shift $`\mu`, standard $`H^{-1}` data $`(f_0,f^1,\ldots,f^n)`, and
$`u\in H^1_0(\Omega)`, the predicate requires $`\Omega` to be open and
records

$$`
\int_\Omega a^{ij}D_j uD_i\varphi
+\int_\Omega b^iD_i u\,\varphi
+\int_\Omega(c+\mu)u\varphi
=\int_\Omega f_0\varphi+\int_\Omega f^iD_i\varphi
`

for every $`\varphi\in C_c^\infty(\Omega)`. This is the weak form of
$`-D_i(a^{ij}D_j u)+b^iD_i u+cu+\mu u=f_0-D_i f^i`.
:::

Whether the shifted form is coercive depends on the size of $`\mu`, and
Gårding's inequality quantifies the loss caused by the lower-order terms. It
bounds the full quadratic form from below by half the principal ellipticity,
minus an explicit multiple of the $`L^2` norm.

:::theorem "elliptic.divergence.garding" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.fullDivergenceForm_garding") (uses := "elliptic.divergence.full_form, elliptic.divergence.integrated_ellipticity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "318-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If the principal form has ellipticity constant $`\alpha>0`, the constants
$`\beta,\gamma` are nonnegative, each first-order operator has norm at most
$`\beta`, and the zeroth-order operator has norm at most $`\gamma`, then

$$`\frac{\alpha}{2}B_0(u,u)
\le B(u,u)+\left(\frac{n\beta^2}{2\alpha}+\gamma\right)
\lVert u\rVert_{L^2}^2.`

Here $`B_0(u,u)=\sum_i\lVert D_i u\rVert_2^2` is the Dirichlet form. This is
Gårding's estimate (Evans, 2010, pp. 318–319) for operator-valued coefficients.
:::

:::proof "elliptic.divergence.garding"
Bound each first-order pairing by Cauchy–Schwarz and Young's inequality,
sum over coordinates, bound the zeroth-order pairing by its operator norm,
and combine the result with principal ellipticity.
:::

Read with the mass term moved to the left, Gårding's inequality says that
$`B(u,u)+\mu\lVert u\rVert_{L^2}^2` dominates $`(\alpha/2)B_0(u,u)` together
with
$`\bigl(\mu-\tfrac{n\beta^2}{2\alpha}-\gamma\bigr)\lVert u\rVert_{L^2}^2`.
Choosing the shift so that the second coefficient equals $`\alpha/2` makes
both graph-space coordinates appear with the same constant.

:::definition "elliptic.divergence.coercive_shift" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.coerciveShift") (uses := "elliptic.divergence.garding")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
We choose the explicit mass shift

$$`\mu_0=\frac{n\beta^2}{2\alpha}+\gamma+\frac\alpha2.`

This choice records exactly which estimates were used and leaves coercivity
constant $`\alpha/2`.
:::

Since a larger shift only adds a nonnegative multiple of
$`\lVert u\rVert_{L^2}^2`, the same lower bound persists for every
$`\mu\ge\mu_0`. The graph-space norm squared is the sum of the base and
gradient contributions, which is why the constant $`\alpha/2` needs no
Poincaré inequality and no bounded domain.

:::theorem "elliptic.divergence.shifted_coercive" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.shiftedDivergenceForm_isCoercive_of_coerciveShift_le") (uses := "elliptic.divergence.garding, elliptic.divergence.coercive_shift")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every $`\mu\ge\mu_0` makes the shifted full form coercive on the graph-space
$`H^1_0(\Omega)`, with coercivity constant $`\alpha/2`.
:::

:::proof "elliptic.divergence.shifted_coercive"
Add the mass shift to Gårding's inequality, decompose the graph-space norm
into its $`L^2` and gradient components, and use monotonicity in $`\mu`.
:::

Coercivity of the shifted form is exactly the hypothesis of Lax–Milgram, so
the shifted problem is uniquely solvable for every generalized load. For
pointwise $`L^\infty` coefficients the operator bounds $`\beta,\gamma` are the
$`L^\infty` norms of $`b^i` and $`c`, and boundedness of $`\Omega` is not
required, in contrast with the unshifted principal problem.

:::theorem "elliptic.divergence.shifted_exists_unique" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic_of_coerciveShift_le") (uses := "elliptic.lax_milgram, elliptic.divergence.shifted_weak_solution, elliptic.divergence.ae_implies_integrated, elliptic.divergence.shifted_coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be open and measurable. Suppose the principal
$`L^\infty` coefficient matrix has ellipticity constant $`\alpha>0`, while
$`\beta,\gamma\ge0`, every coordinate satisfies
$`\lVert b^i\rVert_{L^\infty}\le\beta`, and
$`\lVert c\rVert_{L^\infty}\le\gamma`.
For

$$`\mu\ge\mu_0=
  \frac{n\beta^2}{2\alpha}+\gamma+\frac{\alpha}{2},`

every standard $`H^{-1}` load $`f_0-D_i f^i` has a unique weak solution
$`u\in H^1_0(\Omega)`.
:::

:::proof "elliptic.divergence.shifted_exists_unique" (uses := "elliptic.lax_milgram, elliptic.divergence.shifted_weak_solution, elliptic.divergence.ae_implies_integrated, elliptic.divergence.shifted_coercive")
The Gårding estimate at the explicit threshold is strengthened by the
nonnegative extra mass term when $`\mu` is larger. Lax–Milgram then gives the
unique Hilbert-space solution, and the smooth-test density bridge identifies it
with the concrete shifted divergence-form weak equation.
:::

Uniqueness makes the solution a function of the data, and at the canonical
shift $`\mu_0` that function can be named. The definition lives at the
operator-valued level, where only integrated ellipticity and the operator-norm
bounds are available.

:::definition "elliptic.divergence.shifted_solver" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.shiftedDivergenceSolve") (uses := "elliptic.divergence.shifted_exists_unique")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "319-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`A_{ij}`, $`b_i`, and $`c` be bounded operators on $`L^2(\Omega)`.
Given integrated ellipticity for $`A` and the nonnegative lower-order bounds
used above, the canonical coercive shift determines a named Lax–Milgram
solution in $`H^1_0(\Omega)` for every standard graph-space load
$`f_0-D_i f^i`. This definition is operator-valued and needs only
measurability of $`\Omega`; the pointwise multiplication specialization and
openness enter in the distributional-PDE theorem.
:::

The named solver is characterized by the variational identity it satisfies
against every $`v\in H^1_0(\Omega)`, not only against smooth tests.

:::theorem "elliptic.divergence.shifted_solver_equation" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.shiftedDivergenceSolve_equation") (uses := "elliptic.divergence.shifted_solver, elliptic.divergence.shifted_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`v\in H^1_0(\Omega)`, the named solution satisfies the full
shifted variational identity, with right-hand side
$`(f_0,v)+\sum_i(f^i,D_i v)`. The identity explicitly expands the
graph-space load but still permits bounded, possibly nonlocal coefficient
operators. After specialization to multiplication operators on an open
domain, the smooth-test bridge gives Evans's local distributional equation.
:::

:::proof "elliptic.divergence.shifted_solver_equation"
Apply the weak equation for the named Lax–Milgram solver to $`v`, then expand
the generalized load. This gives the mass-shifted bilinear form on the left
and $`(f_0,v)+\sum_i(f^i,D_i v)` on the right.
:::

Testing this identity with $`v=u` and using the coercivity constant
$`\alpha/2` at the canonical shift yields an a priori bound with a fully
explicit constant.

:::theorem "elliptic.divergence.shifted_solver_estimate" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.norm_shiftedDivergenceSolve_le") (uses := "elliptic.divergence.shifted_solver_equation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under integrated ellipticity with constant $`\alpha>0` and the stated
nonnegative lower-order operator bounds, the canonical operator-valued
solution obeys the explicit estimate

$$`\lVert u\rVert_{H^1_0}\le
\frac{2}{\alpha}\left(\lVert f_0\rVert_2+
\sum_i\lVert f^i\rVert_2\right).`

The constant is explicit for the chosen graph-space norm.
:::

:::proof "elliptic.divergence.shifted_solver_estimate"
Test the solver equation with $`v=u`. Coercivity at the canonical shift gives
$`(\alpha/2)\lVert u\rVert_{H^1_0}^2` on the left, while Cauchy–Schwarz
bounds the generalized load by
$`(\lVert f_0\rVert_2+\sum_i\lVert f^i\rVert_2)
\lVert u\rVert_{H^1_0}`. Cancel the solution norm to obtain the displayed
factor $`2/\alpha`.
:::

For local $`L^\infty` multiplication coefficients the shifted problem also
satisfies weak comparison
(weak comparison). Under the integrated
ellipticity and lower-order bounds above, fix the same coefficients and shift
$`\mu\geq\mu_0` for two weak solutions $`u,v\in H^1_0(\Omega)`. If their dual
loads obey
$`\ell_1(t)\leq\ell_2(t)` for every almost-everywhere nonnegative
$`t\in H^1_0(\Omega)`, then $`u\leq v` almost everywhere on $`\Omega`.

Test the difference equation with $`w=(u-v)^+`. The supported Sobolev
closure is preserved by this operation, and
$`D_iw=\mathbf{1}_{\{u>v\}}D_i(u-v)` almost everywhere, including on
$`\{u=v\}`. Local multiplication then gives
$`B_\mu(u-v,w)=B_\mu(w,w)`. Load order makes this quantity nonpositive;
coercivity forces $`w=0`. This localization is why comparison uses
multiplication coefficients even though the solver permits nonlocal operators.

At the canonical shift, the scalar-load comparison theorem specializes this
argument to ordered scalar $`L^2` loads with the divergence forcing held
fixed. Comparison needs only measurable $`\Omega`: here the zero-boundary
space means the closure of supported smooth functions. On open domains this
is the usual $`H^1_0(\Omega)`. Neither boundedness nor a boundary atlas is
required; the conclusion is an almost-everywhere inequality between weak
solutions.

Comparison also gives a route to a nonlinear equation. Let $`\Omega` now be
bounded and measurable, and suppose ordered weak lower and upper solutions
$`\underline u,\overline u\in H^1_0(\Omega)` are given for $`Lu=g(u)`.
Suppose $`g` is continuous, has at most linear growth, and
$`s\mapsto g(s)+Ms` is increasing for some real $`M`. Choose
$`\mu=\max\{\mu_0,M\}`. The shifted reaction $`s\mapsto g(s)+\mu s` is
then increasing, so the map

$$`
T(w)=(L+\mu)^{-1}\bigl(g(w)+\mu w\bigr)
`

preserves order. Weak comparison and the barrier inequalities give
$`\underline u\leq T(\underline u)` and
$`T(\overline u)\leq\overline u`. Starting at the lower barrier produces

$$`
\underline u=u_0\leq u_1\leq u_2\leq\cdots\leq\overline u,
\qquad u_{k+1}=T(u_k).
`

The barriers bound this sequence in $`L^2`, and the linear growth estimate bounds
the shifted loads there. The linear solver bounds the iterates in $`H^1_0`;
Rellich compactness then supplies an $`L^2` limit. Monotonicity makes the
whole sequence converge, and continuity of the solver also gives convergence
in $`H^1_0`. At the fixed point the two mass terms cancel, leaving
$`Lu=g(u)`.

The monotone iteration theorem
carries out this construction with the same rough multiplication coefficients
as comparison. Consider $`g(s)=1+\sqrt{\max\{s,0\}}`. It is increasing, so we
can take $`M=0`; the estimate $`|g(s)|\leq 2+|s|` supplies linear growth.
Its slope becomes unbounded near zero, but continuity is enough to pass to
the limit in $`L^2`. Zero is a lower barrier, and any nonnegative weak upper
barrier encloses a solution. Globally Lipschitz reactions, including
$`g(s)=1+|s|`, are special cases with $`M` equal to the Lipschitz constant.

Often the barriers give a bounded range $`[a,b]` for every iterate. Then we
only need continuity of $`g` and monotonicity of $`g(s)+Ms` on that interval.
Let $`P(s)=\min\{\max\{s,a\},b\}` and extend the reaction by

$$`
\widetilde g(s)=g(P(s))+M P(s)-Ms.
`

On $`[a,b]` this is exactly $`g`. The shifted function
$`\widetilde g(s)+Ms` is increasing and bounded, so $`\widetilde g` has
linear growth on the whole line. The preceding construction applies, and the
barriers keep its solution where the extension agrees with $`g`.
The interval-reaction existence theorem
formalizes this argument. For instance, it handles $`1+s^3` on $`[0,R]`
without a global growth bound for the cubic. Both barriers belong to the
zero-boundary space throughout this construction.


# From signed-trace barriers to a classical solution

For smooth coefficients and boundary, the barriers can instead lie in
$`H^1(\Omega)`: their traces need only bracket the prescribed zero boundary
value. The solution still belongs to $`H^1_0(\Omega)`. Keeping its values
between fixed constants makes local smoothness of the reaction sufficient
for the regularity argument.

:::theorem "elliptic.divergence.classical_between_barriers" (parent := "elliptic.weak_theory") (lean := "PDE.Elliptic.Semilinear.exists_classical_solution_between_H1_barriers_of_contDiffOn") (uses := "elliptic.divergence.full_form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 9, subsolutions and supersolutions"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
Let $`\Omega\subset\mathbb R^n`, $`n>0`, be bounded and open with smooth
boundary. Suppose the coefficients $`a^{ij},b^i,c` are smooth up to the
boundary and $`a` is uniformly elliptic. Let $`f` be smooth on an open
neighborhood of $`[\ell,r]`. Assume ordered weak barriers
$`\underline u,\overline u\in H^1(\Omega)` satisfy

$$`
\ell\leq\underline u\leq\overline u\leq r
\quad\text{almost everywhere},\qquad
\operatorname{Tr}\underline u\leq0\leq\operatorname{Tr}\overline u
\quad\text{surface-almost everywhere},
`

and the subsolution and supersolution inequalities for every nonnegative
$`H^1_0` test function, using the full divergence-form operator below. Then
there are $`u\in H^1_0(\Omega)` and a representative $`z=u` almost everywhere,
smooth on $`\overline\Omega`, such that

$$`
-\sum_{i,j}\partial_i(a^{ij}\partial_jz)
  +\sum_i b^i\partial_i z+cz=f(z)\quad\text{in }\Omega,
\qquad z=0\quad\text{on }\partial\Omega.
`

The representative lies in $`[\ell,r]` at every interior point and between
the two Sobolev barriers almost everywhere. The principal matrix need not be
symmetric, and the potential need not have a fixed sign.
:::

:::proof "elliptic.divergence.classical_between_barriers"
The signed-trace comparison argument constructs a weak zero-boundary solution
between the barriers. Its bounded range controls the derivatives of the
reaction needed at each stage of Sobolev composition. Global elliptic
regularity then bootstraps the solution through every finite Sobolev order.
Morrey regularity supplies one smooth representative on the closure. The
trace-kernel identity makes that representative zero at every boundary point.
Finally, the weak equation gives the full divergence-form identity almost
everywhere; continuity promotes it to a pointwise equation in the interior.
:::
