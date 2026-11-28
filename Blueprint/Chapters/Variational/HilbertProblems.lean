/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

import Blueprint.Chapters.Variational.DirectMethod
import PDE.Elliptic.Variational.DirichletData
import PDE.HilbertProblems.Nineteenth
import PDE.HilbertProblems.Twentieth
import PDE.HilbertProblems.TwentyThird
import PDE.CalculusOfVariations.ExtremalFamily.Comparison
import PDE.CalculusOfVariations.LocalMinimizer.Classical

/-!
# Hilbert's problems

The problems of Hilbert's 1900 list that concern the calculus of variations, as the folder
`PDE/HilbertProblems` states them, with the general theorems that answer them.
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
#doc (Manual) "Hilbert's Problems" =>

:::group "methods.hilbert"
Hilbert's problems on the calculus of variations
:::

Three problems of the list that Hilbert presented in Paris in 1900
{Informal.citet "hilbert-1902"}[] concern the calculus of variations: the 19th, the 20th and the
23rd. The folder `PDE/HilbertProblems` is for them. A file there quotes the problem as Hilbert
asked it and proves an answer for a stated class from the general theory, which stays under its
own subject. The
folder holds the 19th problem for one unknown and uniformly regular integrands, the 20th
problem for convex integrands of growth $`p`, and the 23rd problem for the simple integral
and, for a field given by a family of extremals, for the multiple integral.

# The 19th Problem: Analyticity

Hilbert calls a variational problem $`\iint F(p,q,z;x,y)\,dx\,dy=\text{Minimum}` regular when
$`F` is analytic and $`F_{pp}F_{qq}-F_{pq}^2>0`, and asks whether the solutions of regular
problems are always analytic, also when the boundary values are continuous but not analytic.

:::theorem "methods.hilbert.analytic" (parent := "methods.hilbert") (lean := "PDE.HilbertProblems.Nineteenth.IsRegular.exists_analytic, PDE.HilbertProblems.Nineteenth.IsRegular.analyticOnNhd_of_contDiffOn, PDE.HilbertProblems.Nineteenth.IsRegular.hilbert_inequality, PDE.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn, PDE.CalculusOfVariations.analyticOnNhd_of_contDiffOn_two")
Let $`\Omega\subseteq\mathbb R^n` be open and let $`F:\mathbb R^n\to\mathbb R` be real-analytic
with

$$`\theta|\xi|^2\leq D^2F(p)(\xi,\xi)\leq\Lambda|\xi|^2\qquad(\theta>0)`

for all $`p` and $`\xi`. Then every local minimizer of $`\int F(\nabla u)` in
$`W^{1,2}_{\mathrm{loc}}(\Omega)` has a representative that is real-analytic in $`\Omega` and
solves $`\operatorname{div}\nabla F(\nabla v)=0` at every point. A function with two
continuous derivatives that solves this equation at every point of $`\Omega` is real-analytic.
For $`n=2` such an $`F` satisfies $`F_{pp}>0` and $`F_{pp}F_{qq}-F_{pq}^2>0`.
:::

:::proof "methods.hilbert.analytic"
This is the regularity theorem for local minimizers. A solution of class $`C^2` is a local
minimizer because $`F` is convex, and it is continuous, so it is the analytic representative
of itself. For the inequality, the lower bound gives
$`(F_{pp}-\theta)s^2+2F_{pq}st+(F_{qq}-\theta)t^2\geq0` for all $`s`, $`t`, hence
$`F_{pq}^2\leq(F_{pp}-\theta)(F_{qq}-\theta)` and
$`F_{pp}F_{qq}-F_{pq}^2\geq\theta^2`.
:::

:::theorem "methods.hilbert.analytic_boundary" (parent := "methods.hilbert") (uses := "methods.hilbert.analytic, methods.hilbert.existence") (lean := "PDE.HilbertProblems.Nineteenth.exists_analytic_solution, PDE.HilbertProblems.Nineteenth.exists_analytic_of_isSolution, PDE.CalculusOfVariations.forall_integral_oneUnknownDensity_le_iff")
Let $`\Omega` be bounded and open, $`n\geq1`, and $`F` as above. For every
$`g\in W^{1,2}(\Omega)` the integral $`\int_\Omega F(\nabla u)\,dx` has a minimizer among the
$`u` with $`u-g\in W^{1,2}_0(\Omega)`, and every such minimizer has a representative that is
real-analytic in $`\Omega`. The datum need not be continuous, and the boundary condition is
this weak one.
:::

:::proof "methods.hilbert.analytic_boundary"
The bounds on $`D^2F` make $`F` convex with quadratic growth and coercivity, so the existence
theorem of the 20th problem applies to the system of one unknown. A minimizer in the boundary
class is a local minimizer, and the previous theorem applies.
:::

Integrands that depend on $`x` or $`u`, regular problems that are not uniformly regular, such
as the area integrand, uniqueness, and analyticity up to the boundary are not formalized.
Hilbert asks about continuous boundary values. A continuous function on the boundary need not
have an extension in $`W^{1,2}(\Omega)`, and it is not proved that the solution takes
continuous boundary values at every boundary point. For several unknown functions the answer
is no.

# The 20th Problem: Boundary Values

Hilbert asks whether every regular variation problem has a solution, "provided certain
assumptions regarding the given boundary conditions are satisfied" and "provided also if need
be that the notion of a solution shall be suitably extended". He expects a proof by a general
principle of the kind of Dirichlet's principle. For integrands that are convex in the
derivatives and of growth $`p` the answer is yes: the extended solution is a Sobolev function,
and the principle is the direct method. This is a sufficient condition, not a statement about
every regular problem.

Let $`\Omega\subseteq\mathbb R^n` be bounded and measurable, $`n\geq1`, and $`1<p<\infty`.
The unknown is a system $`u=(u_1,\dots,u_m)` in $`W^{1,p}(\Omega)`, and

$$`J(u)=\int_\Omega F(x,u,Du)\,dx.`

A system $`u` has the boundary values of $`g` when $`u_i-g_i\in W^{1,p}_0(\Omega)` for every
$`i`.

:::theorem "methods.hilbert.existence" (parent := "methods.hilbert") (lean := "PDE.HilbertProblems.Twentieth.exists_solution, PDE.HilbertProblems.Twentieth.exists_solution_of_contDiffUpToBoundary, PDE.CalculusOfVariations.exists_minimizer_integral_vectorWkp_prescribed_boundary, PDE.CalculusOfVariations.lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient")
Let $`F(x,s,\xi)` be measurable, continuous in $`s` and convex in $`\xi` for almost every
$`x`, with

$$`c|\xi|^p-b(x)\leq F(x,s,\xi)\leq a(x)+D\,|(s,\xi)|^p`

for some $`c>0` and integrable $`a`, $`b`. Then for every $`g\in W^{1,p}(\Omega)^m` there is a
system $`u` with the boundary values of $`g` such that $`J(u)\leq J(v)` for every system $`v`
with these boundary values. On a bounded open set the datum may be given by functions that are
continuously differentiable up to the boundary.
:::

:::proof "methods.hilbert.existence"
The lower bound and Poincaré's inequality bound a minimizing sequence in $`W^{1,p}`. A
subsequence of the corrections $`u_j-g` converges weakly in $`W^{1,p}_0`, and the values
converge strongly in $`L^p` because the set is bounded. The integral is lower semicontinuous
along such a sequence because $`F` is convex in the gradient. The upper bound makes $`J` finite,
so the minimizer of the extended energy minimizes $`J`.
:::

Hilbert's condition $`F_{pp}F_{qq}-F_{pq}^2>0`, together with $`F_{pp}>0`, makes $`F`
strictly convex in the derivatives. The theorem uses convexity only; it need not be strict, and
$`F` need not be differentiable.

:::theorem "methods.hilbert.euler_lagrange" (parent := "methods.hilbert") (uses := "methods.hilbert.existence") (lean := "PDE.HilbertProblems.Twentieth.exists_isWeakSolution, PDE.HilbertProblems.Twentieth.IsSolution.isWeakSolution, PDE.HilbertProblems.Twentieth.dirichlet_principle, PDE.CalculusOfVariations.integral_firstVariation_eq_zero_of_integral_vectorWkp_le")
Suppose in addition that, for almost every $`x`, $`F(x,\cdot,\cdot)` has a derivative
$`dF(x,z)` at every $`z=(s,\xi)`, jointly measurable, with
$`|dF(x,z)|\leq h(x)+C|z|^{p-1}`, $`h\in L^{p'}(\Omega)`. Then every solution $`u` of the
variational problem satisfies

$$`\int_\Omega dF(x,u,Du)(\varphi,D\varphi)\,dx=0`

for every system $`\varphi` with components in $`W^{1,p}_0(\Omega)`. This is the weak form of
the Euler–Lagrange system $`\operatorname{div}F_\xi(x,u,Du)=F_s(x,u,Du)`. For $`F=|\xi|^p`
every hypothesis holds: the integral $`\int|Du|^p` has a minimizer with given boundary values,
and it solves $`\operatorname{div}(|Du|^{p-2}Du)=0` weakly. For $`p=2` this is Dirichlet's
principle.
:::

:::proof "methods.hilbert.euler_lagrange"
The growth of the derivative makes $`t\mapsto J(u+t\varphi)` differentiable at $`t=0`, with
the displayed integral as its derivative. The function has a minimum there.
:::

For a linear equation the solution comes from the Lax–Milgram theorem and is unique.

:::theorem "methods.hilbert.linear" (parent := "methods.hilbert") (lean := "SobolevSpace.GraphSpace.existsUnique_isInteriorWeakFullDivergenceSolution_prescribed_boundary, SobolevSpace.GraphSpace.existsUnique_interiorVariableCoeffForm_prescribed_boundary, SobolevSpace.GraphSpace.existsUnique_weak_harmonic_extension, PDE.Analysis.Variational.existsUnique_eq_add_and_forall_eq")
Let $`\Omega\subseteq\mathbb R^n` be bounded and open, $`n\geq1`, let $`a` be a bounded
measurable matrix with $`a(x)\xi\cdot\xi\geq\alpha|\xi|^2` almost everywhere, $`\alpha>0`, and
let $`c\geq0` be bounded and measurable. For every $`f\in L^2(\Omega)` and every
$`g\in H^1(\Omega)` there is exactly one $`u\in H^1(\Omega)` with $`u-g\in H^1_0(\Omega)` and

$$`\int_\Omega\bigl(a\nabla u\cdot\nabla v+c\,uv\bigr)\,dx=\int_\Omega fv\,dx
\qquad\text{for every }v\in H^1_0(\Omega).`
:::

:::proof "methods.hilbert.linear"
Write $`u=g+w`. The correction $`w\in H^1_0(\Omega)` solves the problem with zero boundary
values and the load $`v\mapsto\int fv-\int(a\nabla g\cdot\nabla v+c\,gv)`, which is
continuous on $`H^1_0(\Omega)`. The form is coercive there by Poincaré's inequality, so the
Lax–Milgram theorem gives exactly one $`w`.
:::

Attainment of the boundary values in the classical sense, regularity up to the boundary, data
that are differentiable in sections and integrands of linear growth, such as the area
integrand, are not formalized.

# The 23rd Problem: Slope Fields and Weierstrass's Formula

The last problem is not one question. Hilbert asks for further work on the calculus of
variations and adds a short justification, in which he develops two theorems. For the integral

$$`J(y)=\int_a^bF(y_x,y;x)\,dx`

and a function $`p(x,y)` he considers

$$`J^*(y)=\int_a^b\bigl\{F+(y_x-p)F_p\bigr\}\,dx,`

with $`F` and $`F_p` taken at the slope $`p=p(x,y)`, and asks how $`p` is to be chosen so
that $`J^*` is independent of the path of integration. Since $`J^*=\int\{A\,y_x-B\}\,dx` with
$`A=F_p` and $`B=pF_p-F`, the integral $`J^*` is the integral of the form $`A\,dy-B\,dx`
over the graph of $`y`. His answer is that the form must be closed:

$$`\frac{\partial F_p}{\partial x}+\frac{\partial(pF_p-F)}{\partial y}=0.`

:::theorem "methods.hilbert.independence" (parent := "methods.hilbert") (lean := "PDE.HilbertProblems.TwentyThird.independence, PDE.HilbertProblems.TwentyThird.fieldEquation_iff_eulerLagrange, PDE.CalculusOfVariations.SlopeField.IsEikonal.invariantIntegral_eq_of_endpoints, PDE.CalculusOfVariations.SlopeField.exists_isEikonal_of_convex")
Let $`D` be a convex open region of the plane on which $`F` is differentiable in the slope at
$`p`, the functions $`A=F_p` and $`B=pF_p-F` are differentiable, and $`p` solves the equation
above. Then $`J^*` has the same value on any two
curves in $`D` over $`[a,b]` with the same endpoints, along which its integrand is integrable.
A curve is continuous and has a derivative off a countable set. Moreover, at a point where
$`F`, $`p` and $`F_p(p)` are differentiable, the equation holds exactly when a solution of
$`y_x=p(x,y)` through the point satisfies the Euler–Lagrange equation
$`\frac{d}{dx}F_{y_x}=F_y` there.
:::

:::proof "methods.hilbert.independence"
A closed form on a convex open set is the differential of a function $`S`, by the Poincaré
lemma. Along a curve, $`\frac{d}{dx}S(x,y(x))` is the integrand of $`J^*`, so
$`J^*=S(b,y(b))-S(a,y(a))`. For the second statement, differentiate $`B=pA-F(p)` in $`y`:
the terms with $`p_y` cancel because $`A=F_p`, and
$`\partial_xA+\partial_yB=\partial_xA+p\,\partial_yA-F_y`, which is
$`\frac{d}{dx}A(x,y(x))-F_y` along a curve of the field.
:::

The general theorem takes the function $`S` as its premise and needs nothing of the region.
It holds for an unknown with values in a real normed space; then closedness is the equation
above together with the symmetry of the derivative of $`F_p` in $`y`. The function $`S` is
differentiable with differential $`A\,dy-B\,dx`. Where $`F` is convex in the slope and
differentiable at the slope $`p`, it solves the Hamilton–Jacobi equation
$`S_x+\sup_q\{S_yq-F(q,y;x)\}=0`.

:::theorem "methods.hilbert.weierstrass" (parent := "methods.hilbert") (uses := "methods.hilbert.independence") (lean := "PDE.HilbertProblems.TwentyThird.weierstrass_formula, PDE.HilbertProblems.TwentyThird.integral_le_of_weierstrassE_nonneg, PDE.CalculusOfVariations.SlopeField.IsEikonal.integral_sub_integral_eq_integral_weierstrassExcess, PDE.CalculusOfVariations.SlopeField.IsEikonal.hamiltonJacobi")
Under the hypotheses of the independence theorem, let $`\bar y` be a curve of the field,
$`\bar y_x=p(x,\bar y)`, and let $`y` be any curve in $`D` with the endpoints of $`\bar y`,
with $`F(y_x)`, $`F(\bar y_x)` and the integrand of $`J^*` along $`y` integrable. Then

$$`J(y)-J(\bar y)=\int_a^bE(y_x,p)\,dx,\qquad
E(y_x,p)=F(y_x)-F(p)-(y_x-p)F_p(p).`

In particular, if $`E\geq0` on $`D` for every slope $`y_x`, then $`J(\bar y)\leq J(y)`.
:::

:::proof "methods.hilbert.weierstrass"
Along $`\bar y` the integrand of $`J^*` is $`F`, so $`J^*(\bar y)=J(\bar y)`. By
independence $`J^*(y)=J^*(\bar y)`, and $`F(y_x)` minus the integrand of $`J^*` is
$`E(y_x,p)`.
:::

The lines through the origin, $`p=y/x` on the half plane $`x>0`, are a field for
$`F=y_x^2/2`: they are an instance of the hypotheses on the field, and the theorem says that
a straight line minimizes $`\int y_x^2/2\,dx` among the curves in the half plane with its
endpoints, an integrable $`y_x^2` and an integrable integrand of $`J^*`.

For a double integral $`J(z)=\int F(z_x,z_y,z;x,y)\,d\omega` Hilbert considers

$$`J^*(z)=\int\bigl\{F+(z_x-p)F_p+(z_y-q)F_q\bigr\}\,d\omega`

with $`F`, $`F_p`, $`F_q` taken at slopes $`p(x,y,z)`, $`q(x,y,z)` whose integral surfaces
are extremals. Here the field is given by these surfaces, a family $`z=Z_t` of solutions of
the Euler–Lagrange equation with one real parameter, and the surfaces that are compared are
the parameter graphs $`z(x)=Z_{\theta(x)}(x)`; the slopes used at the point $`(x,z(x))` are
the derivatives of $`Z_{\theta(x)}` at $`x`. The family is not assumed to cover a region
simply, so slope functions of the point are not used.

:::theorem "methods.hilbert.multiple" (parent := "methods.hilbert") (lean := "PDE.HilbertProblems.TwentyThird.multipleIntegral_independence, PDE.HilbertProblems.TwentyThird.multipleIntegral_independence_of_injOn, PDE.HilbertProblems.TwentyThird.integrableOn_fieldIntegrand, PDE.HilbertProblems.TwentyThird.multipleIntegral_eq_lagrangianAction, PDE.HilbertProblems.TwentyThird.multipleIntegral_weierstrass_formula, PDE.HilbertProblems.TwentyThird.multipleIntegral_le_of_fieldE_nonneg, PDE.CalculusOfVariations.ExtremalFamily.integral_invariant_eq_of_eqOn_frontier, PDE.CalculusOfVariations.ExtremalFamily.lagrangianAction_parameter_graph_sub_eq_integral_graphExcess, PDE.CalculusOfVariations.ExtremalFamily.lagrangianAction_le_parameter_graph_of_graphExcess_nonneg")
Let $`\Omega` be a bounded open set with $`C^1` graph boundary, in any number of variables,
and let $`Z_t`, $`t` in an open interval containing $`0`, be solutions of the Euler–Lagrange
system on $`\Omega`, for any number of unknown functions. Let $`F` and the family be twice
continuously differentiable, with values and derivatives up to order two that extend
continuously to the closure. Let $`\theta` and $`\theta'` be $`C^1` with values in the
parameter interval on $`\overline\Omega`, and $`z(x)=Z_{\theta(x)}(x)`,
$`z'(x)=Z_{\theta'(x)}(x)`. The integrand of $`J^*` along such a surface is integrable. If
$`\theta=\theta'` on $`\partial\Omega`, then

$$`J^*(z)=J^*(z').`

The same holds if $`z=z'` on $`\partial\Omega` and $`t\mapsto Z_t(x)` is injective for every
$`x\in\partial\Omega`.

If $`\theta=0` on $`\partial\Omega` and $`\bar z=Z_0`, then

$$`J^*(z)=J(\bar z),\qquad J(z)-J(\bar z)=\int_\Omega E\,d\omega,`

where $`E=F(Dz)-F(P)-(Dz-P)F_P(P)` and $`P` is the matrix of derivatives of
$`Z_{\theta(x)}` at $`x`. If $`E\geq0`, then $`J(\bar z)\leq J(z)`.
:::

:::proof "methods.hilbert.multiple"
The integral of the flux of the family from $`0` to $`\theta(x)` is a vector field $`B`
whose value at a boundary point depends on the value of $`\theta` there only. Its divergence
is the pairing of the flux with $`D\theta` plus $`F(DZ_{\theta(x)})-F(D\bar z)`, because
each $`Z_t` is an extremal. The integrand of $`J^*` is $`F(DZ_{\theta(x)})` plus that
pairing, so it is $`F(D\bar z)+\operatorname{div}B`, and by the divergence theorem
$`J^*(z)` is $`J(\bar z)` plus the flux of $`B` through the boundary. This flux is the same
for $`\theta` and $`\theta'`, and it is zero when $`\theta=0` on the boundary. The last
formula follows since $`F(Dz)` is the integrand of $`J^*` plus $`E`.
:::

The family has one real parameter and no field condition is assumed. Two parameter graphs
through one boundary curve whose parameters differ on the boundary are not compared, and for
them $`J^*` can differ. For more than one unknown function the parameter graphs are a thin
class of surfaces.

Jacobi's condition, the necessity of the conditions, regions that are not convex for the
simple integral, and the description of the field of a multiple integral by the slope
functions $`p`, $`q` with Hilbert's first-order equation are not formalized.
