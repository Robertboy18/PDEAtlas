/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Foundations.PDEProblems
import Blueprint.Commands.Figures
import PDE.Analytic.CauchyKovalevskaya.Solution.Existence
import PDE.Analytic.CauchyKovalevskaya.Majorant.CoefficientBounds
import PDE.Analytic.CauchyKovalevskaya.Solution.Uniqueness
import PDE.Cauchy.CoordinateChange.Equation
import PDE.Cauchy.CoordinateChange.Uniqueness
import PDE.Cauchy.Formal.Convergence
import PDE.Cauchy.Formal.Recursion
import PDE.Cauchy.InitialData.Existence
import PDE.Cauchy.InitialData.Uniqueness
import PDE.Cauchy.Noncharacteristic
import PDE.Cauchy.NormalForm.Existence
import PDE.Cauchy.NormalForm.Uniqueness

/-!
# Cauchy problems

Noncharacteristic Cauchy data, the formal power-series solution of a first-order
Cauchy system, and the majorant argument behind the Cauchy–Kovalevskaya theorem.
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
#doc (Manual) "Cauchy problems" =>

A Cauchy problem prescribes a solution and some of its derivatives on a
hypersurface $`\Gamma` and asks the equation to do the rest. For an equation
of order $`k` the natural data are the values of $`u` and its first $`k-1`
normal derivatives along $`\Gamma`. Two questions come before any existence
theorem. Do these data, together with the equation, pin down every derivative
of $`u` on $`\Gamma`? And if they do, does the resulting Taylor series
converge?

The one-dimensional wave equation $`u_{tt}=u_{xx}` shows how the first
question can fail. On the line $`t=0` the data are $`u(0,x)` and
$`u_t(0,x)`. Differentiating them in $`x` gives $`u_x`, $`u_{xx}`, and
$`u_{tx}` on the line, and the equation then supplies the one missing
second derivative, $`u_{tt}=u_{xx}`. On the line $`t=x` the same procedure
breaks down. Differentiating the first derivatives along the line gives
$`u_{tt}+u_{tx}` and $`u_{tx}+u_{xx}`, hence their difference
$`u_{tt}-u_{xx}`. The equation prescribes exactly that difference, so it
either repeats what the data already say or contradicts them, and in neither
case does it determine the three second derivatives.
The difference is visible in the principal symbol: for a normal
$`\nu=(\nu_t,\nu_x)` it is $`\nu_t^2-\nu_x^2`, which equals $`1` for
$`\nu=(1,0)` and vanishes for $`\nu=(1,-1)/\sqrt2`. A hypersurface is
*noncharacteristic* when the principal symbol is nonzero on its normals.

Even when every derivative is determined, the Taylor series need not
converge. Kovalevskaya's example is the heat equation $`u_t=u_{xx}` with
$`u(0,x)=g(x)=1/(1+x^2)`. The line $`t=0` is characteristic for the heat
operator, whose principal symbol $`\nu_x^2` vanishes at $`\nu=(1,0)`, but
the equation is solved for $`u_t`, so every time derivative is still
determined formally: $`\partial_t^ku=\partial_x^{2k}u`. At the origin
$`\partial_x^{2k}g(0)=(-1)^k(2k)!`, so the formal solution is

$$`
u(t,0)\sim\sum_{k\ge0}(-1)^k\frac{(2k)!}{k!}\,t^k ,
`

whose terms grow roughly like $`(4t)^k k!` and diverge for every $`t\ne0`, although
$`g` is analytic on the whole real line. The wave equation with the same
datum and $`u_t(0,x)=0` has the solution
$`u(t,x)=\tfrac12\bigl(g(x+t)+g(x-t)\bigr)`, and at $`x=0` its series
$`\sum_k(-1)^kt^{2k}` converges for $`|t|<1`.

{leanpde_figure "kovalevskaya-series"}

The figure plots both series. The wave partial sums settle onto
$`1/(1+t^2)` inside the unit interval, while at each plotted time the size of
the $`k`-th term of the heat series first shrinks and then grows without
bound. The Cauchy–Kovalevskaya theorem says that the divergence cannot happen
for a first-order system solved for its time derivative with analytic
coefficients and data. {Informal.citet "evans-2010"}[] treats
noncharacteristic surfaces in §4.6.1 and the analytic theorem in §4.6.3.
The determination of derivatives is proved for smooth solutions of a
quasilinear scalar equation, with no analyticity assumption. The convergence
proof runs on
Mathlib's multivariable formal power series, with the formal solution
constructed by recursion in the time degree, over any commutative
$`\mathbb Q`-algebra, before any estimate is made.

# Noncharacteristic data determine the jet

:::group "foundations.cauchy"
Cauchy problems and the Cauchy–Kovalevskaya theorem
:::

For a scalar equation of order $`k` on $`\Omega\subseteq\mathbb R^n`, write
$`J_{<k}u(x)` for the coordinate derivatives of $`u` of order below $`k`
at $`x`, and consider

$$`
\sum_{|\alpha|=k}a_\alpha\bigl(x,J_{<k}u(x)\bigr)\,\partial^\alpha u(x)
 = b\bigl(x,J_{<k}u(x)\bigr).
`

The hypersurface $`\Gamma` enters only through a nonzero conormal field
$`\nu` and local parametrizations. The normal data are ordinary directional
derivatives along the fixed vector $`\nu(x)`,

$$`
D_\nu^j u(x)=D^ju(x)[\nu(x),\ldots,\nu(x)],
`

so no derivative of the field $`\nu` appears. The vector need not be a unit
vector, because the symbol condition is homogeneous in $`\nu`.

:::theorem "foundations.cauchy.noncharacteristic_jets" (parent := "foundations.cauchy") (lean := "PDE.Cauchy.Quasilinear.iteratedFDeriv_eq_on_of_cauchy_data, PDE.Cauchy.Quasilinear.iteratedFDeriv_eq_on_of_cauchy_data_of_symbol_at_jet") (uses := "foundations.pde_problems.jet, foundations.derivatives.iterated")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "233"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    }
  ]
}
%%%
Let $`k>0`, let $`\Omega\subseteq\mathbb R^n` be open and
$`\Gamma\subseteq\Omega`, and let the coefficients $`a_\alpha(x,p)` and
$`b(x,p)` be $`C^\infty` on $`\Omega` times the space of lower jets. Let
$`\nu` be nonzero along $`\Gamma`, and let $`\Gamma` have local
parametrizations whose differential at each point has image
$`\ker\langle\nu(x),\cdot\rangle`. Suppose $`u,v\in C^\infty(\Omega)` both solve the equation in
$`\Omega`, their lower normal data agree,

$$`
D_\nu^ju=D_\nu^jv\quad\text{on }\Gamma\text{ for }0\le j<k,
`

and the principal symbol at the jet of $`u` does not vanish:

$$`
\sum_{|\alpha|=k}a_\alpha\bigl(x,J_{<k}u(x)\bigr)\,\nu(x)^\alpha\ne0
\qquad(x\in\Gamma).
`

Then $`D^ju=D^jv` on $`\Gamma` for every $`j\ge0`. The first Lean form
asks instead that the symbol be nonzero at every lower jet $`p`, which is how
the condition is usually stated for linear equations; the second evaluates it
only at the jet of $`u`.
:::

:::proof "foundations.cauchy.noncharacteristic_jets"
Below order $`k`, differentiate the equal normal data along the
parametrizations of $`\Gamma`. Tangential derivatives of an identity on
$`\Gamma` give equality of $`D^ju` and $`D^jv` on any list of $`j` vectors, each
tangent to $`\Gamma` or equal to $`\nu`, and for $`j<k` such lists span
all of $`D^ju`. In particular $`J_{<k}u=J_{<k}v` on $`\Gamma`, so the two
equations have the same coefficients there.

At order $`k+i` induct on $`i`. Tangential differentiation of the previous
step fixes every component of $`D^{k+i}u` except the one with all $`k+i`
slots filled by $`\nu`. Differentiating the equation $`i` times along
$`\nu` produces that component multiplied by the principal symbol, plus terms
already known to agree. Since the symbol is nonzero, the pure normal
derivative agrees as well. The Lean proof carries out this argument once, for
conormal tensors, and the quasilinear statement instantiates it with the
coordinate monomials $`\nu^\alpha`; their mixed-partial multiplicities are
part of the coordinate expansion and not of the coefficients.
:::

The conclusion is only about derivatives on $`\Gamma`: two smooth solutions
with the same Cauchy data can still differ off $`\Gamma`. Recovering the solution from its jet needs
convergence of the Taylor series, which is where analyticity enters.

# The formal solution

The analytic theorem is proved for a first-order system in normal form. Time
is the coordinate $`t=x_0`, the unknown is $`u=(u_1,\ldots,u_m)` of
$`(t,x)\in\mathbb R^{1+d}`, and

$$`
\partial_tu_i=\sum_{j=1}^d\sum_{k=1}^mB_{jik}(u,x)\,\partial_{x_j}u_k+c_i(u,x),
\qquad u(0,x)=0.
`

A general analytic Cauchy problem reduces to this one by subtracting the
initial datum and adjoining time as an extra unknown; the
{bpref "methods.power_series.analytic_evolution"}[analytic evolution theorem]
performs that reduction. Here the coefficients $`B_{jik}` and $`c_i` are
formal power series in the $`m+d` variables $`(z,x)`, and the unknown is a
tuple of formal series in $`(t,x)`.

:::theorem "foundations.cauchy.formal_solution" (parent := "foundations.cauchy") (lean := "PDE.Analytic.CauchyKovalevskaya.existsUnique_formal_solution, PDE.Analytic.CauchyKovalevskaya.existsUnique_iterate_pderiv_eq_of_coeff_depend_lt") (uses := "foundations.pde_problems.jet")
Over any commutative ring $`R` containing $`\mathbb Q`, and for any formal coefficient series
$`B_{jik}` and $`c_i`, there is exactly one tuple of formal series
$`u_i\in R[[t,x_1,\ldots,x_d]]` with zero coefficient of $`t^0` and

$$`
\partial_tu_i=\sum_{j,k}B_{jik}(u,x)\,\partial_{x_j}u_k+c_i(u,x)
\qquad(1\le i\le m),
`

where $`B_{jik}(u,x)` substitutes the series $`u` for the state variables.
The underlying recursion is stated for any order $`k` and any index set: if
the coefficients of $`G(u)` up to time degree $`n` depend only on the
coefficients of $`u` below time degree $`n+k`, then
$`\partial_t^ku=G(u)` has a unique solution whose first $`k` time
coefficients vanish.
:::

:::proof "foundations.cauchy.formal_solution"
Group the coefficients of a series by their power of $`t`. Since the unknowns
vanish at $`t=0`, substitution into the coefficient series is admissible,
and the coefficient of $`t^n` on the right depends only on the coefficients
of $`u` of time degree at most $`n`, spatial derivatives included, because
$`\partial_{x_j}` does not change the power of $`t`. The equation therefore
defines the coefficient of $`t^{n+1}` in $`u` from those already chosen.
Strong induction on the time degree gives existence, and the same induction
shows that any two solutions agree degree by degree.
:::

The recursion is where the order of the equation in time matters. For the
heat equation the right-hand side $`u_{xx}` takes two spatial derivatives,
yet it uses only lower time degrees, so a unique formal solution exists
there too; it simply fails to converge. Existence of a formal solution is
therefore cheap, and everything depends on estimating its coefficients.

# Majorants and convergence

A real series $`V` *majorizes* $`U` when $`|U_\beta|\le V_\beta` for every
multi-index $`\beta`. If the coefficients of one Cauchy system are majorized by
those of another, the recursion transfers the bound to the solutions, because
every step builds the new coefficient from sums and products of old ones with
nonnegative combinatorial weights.

:::theorem "foundations.cauchy.majorant_comparison" (parent := "foundations.cauchy") (lean := "PDE.Analytic.CauchyKovalevskaya.formal_solution_isMajorizedOn, PDE.Analytic.CauchyKovalevskaya.formalRightHandSide_isMajorizedOn") (uses := "foundations.cauchy.formal_solution")
Let $`u` solve the formal system with coefficients $`(B,c)` and $`v` solve
it with coefficients $`(D,e)`, both with zero coefficient of $`t^0`. If
$`B_{jik}` is majorized by $`D_{jik}` and $`c_i` by $`e_i` for all indices,
then every $`u_i` is majorized by $`v_i`. The comparison of right-hand sides
holds degree by degree: if $`u` is majorized by $`v` through time degree
$`n`, the two right-hand sides are majorized through the same degree.
:::

:::proof "foundations.cauchy.majorant_comparison"
Induct on the time degree. At degree zero both solutions vanish. Majorization
is preserved by sums, products, substitution into a majorized series, and
spatial differentiation, all on sets of multi-indices closed under going down
in the time degree. So a bound through degree $`n` for the unknowns gives one
for the right-hand sides, and the equation
$`\partial_tu=\text{right-hand side}` moves it up to degree $`n+1`.
:::

It remains to exhibit one majorizing system that can be solved in closed
form. Any analytic coefficient near the origin is majorized by a geometric
series $`\alpha/(\rho-\sum_i z_i-\sum_j x_j)`. Put that same series in every
entry of $`B` and $`c`. By symmetry the majorizing system then has a solution
with equal components depending on $`t` and $`\sum_jx_j` only, and it
reduces to the scalar quadratic equation

$$`
\Bigl(\rho-\sum_{j=1}^dx_j\Bigr)v=\alpha t+\kappa v^2,
\qquad 2\kappa=m(d+1).
`

:::definition "foundations.cauchy.scalar_majorant" (parent := "foundations.cauchy") (lean := "PDE.Analytic.CauchyKovalevskaya.scalarMajorant, PDE.Analytic.CauchyKovalevskaya.spatialDenominator, PDE.Analytic.CauchyKovalevskaya.coefficientMajorant") (uses := "foundations.cauchy.majorant_comparison")
For $`\rho,\alpha,\kappa\in\mathbb R`, the spatial denominator is
$`\rho-\sum_{j=1}^dx_j` and the scalar majorant is the root of
$`(\rho-\sum_jx_j)v=\alpha t+\kappa v^2` with zero trace at $`t=0`,

$$`
v=\operatorname{root}\Bigl(\frac{\alpha t}{\rho-\sum_jx_j},\ \frac{\kappa}{\rho-\sum_jx_j}\Bigr),
`

where $`\operatorname{root}(a,b)` is the formal series solving $`w=a+bw^2`
built from the Catalan numbers, $`w=\sum_{n\ge0}C_n\,b^n a^{n+1}`. The
coefficient majorant is $`\alpha/(\rho-\sum_iz_i-\sum_jx_j)` in the $`m`
state and $`d` spatial variables.
:::

:::theorem "foundations.cauchy.scalar_majorant_system" (parent := "foundations.cauchy") (lean := "PDE.Analytic.CauchyKovalevskaya.scalarMajorant_formal_eq, PDE.Analytic.CauchyKovalevskaya.radius_pos_scalarMajorant") (uses := "foundations.cauchy.scalar_majorant")
If $`\rho\ne0` and $`2\kappa=m(d+1)`, the tuple whose $`m` components all
equal the scalar majorant solves the formal Cauchy system in which every
matrix entry and every forcing component is the coefficient majorant. If
$`\rho>0` and $`\alpha,\kappa\ge0`, the scalar majorant has nonnegative
coefficients and a positive radius of convergence.
:::

:::proof "foundations.cauchy.scalar_majorant_system"
Differentiating the quadratic identity in $`t` and in each $`x_j` gives
equations for $`\partial_tv` and $`\partial_{x_j}v` with the common
invertible factor $`\rho-\sum_jx_j-2\kappa v`. Substituting $`v` into the
coefficient majorant turns its denominator into $`\rho-\sum_jx_j-mv`, and
the choice $`2\kappa=m(d+1)` makes the two sides of the system agree after
cancelling that factor. For convergence, collapse all variables to one: the
coefficients are nonnegative, so the radius of the multivariable series is
controlled by that of a one-variable quadratic root with nonzero constant
term in its denominator, and such a root is analytic near zero.
:::

A closed-form root of the quadratic can also be written with a square root.
The Catalan construction gives the
same function as a power series whose coefficients are visibly nonnegative,
which is what the comparison theorem consumes.

:::theorem "foundations.cauchy.convergent_formal_solution" (parent := "foundations.cauchy") (lean := "PDE.Analytic.CauchyKovalevskaya.exists_convergent_formal_solution, PDE.Analytic.CauchyKovalevskaya.radius_pos_formal_solution") (uses := "foundations.cauchy.majorant_comparison, foundations.cauchy.scalar_majorant_system")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "240"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    }
  ]
}
%%%
If every coefficient series $`B_{jik}` and $`c_i` has positive radius of
convergence, the formal solution of the reduced system has zero coefficient
of $`t^0` and each component has positive radius of convergence. More
precisely, whenever all coefficients are majorized by the coefficient majorant
with $`\rho>0` and $`\alpha\ge0`, the formal solution converges.
:::

:::proof "foundations.cauchy.convergent_formal_solution"
Finitely many series of positive radius admit one common geometric majorant
$`\alpha/(\rho-\sum_iz_i-\sum_jx_j)`. Take $`\kappa=m(d+1)/2`. The
comparison theorem bounds each component of the formal solution by the
scalar majorant, which converges, and a series dominated coefficientwise by a
convergent one converges on the same polydisc.
:::

Summing the convergent series gives a function, and the remaining work is to
check that this function solves the equation. Compatibility of convergent
power series with products, substitution, and differentiation does that.

:::theorem "foundations.cauchy.analytic_zero_data" (parent := "foundations.cauchy") (lean := "PDE.Analytic.CauchyKovalevskaya.exists_analytic_solution_zero, PDE.Analytic.CauchyKovalevskaya.eventuallyEq_of_analytic_solutions_zero") (uses := "foundations.cauchy.convergent_formal_solution, foundations.cauchy.formal_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "240"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    }
  ]
}
%%%
Suppose every $`B_{jik}` and $`c_i` is a real function of $`(z,x)` analytic
at the origin. Then for some $`r>0` there is a field $`u` analytic on the
ball of radius $`r` about the origin in $`\mathbb R^{1+d}` with $`u(0,x)=0`
for $`|x|<r` and

$$`
\partial_tu_i=\sum_{j,k}B_{jik}(u,x)\,\partial_{x_j}u_k+c_i(u,x)
`

on that ball. Two fields analytic at the origin that satisfy the equation and
have zero initial trace near the origin agree on a neighborhood of the origin.
:::

:::proof "foundations.cauchy.analytic_zero_data"
Take the Taylor series of the coefficients and apply the convergence theorem.
The sum of the formal solution is analytic on its ball of convergence, its
trace at $`t=0` vanishes because the $`t^0` coefficient does, and the
power-series identities for the equation hold after summation. For
uniqueness, the Taylor series at the origin of any analytic solution with
zero trace solves the formal system, so by the uniqueness of formal
solutions both Taylor series coincide, and analytic functions with the same
Taylor series agree near their center.
:::

The radius $`r` is not given by a formula. The
{bpref "methods.power_series.analytic_evolution"}[analytic evolution theorem]
restores general analytic initial data and time-dependent coefficients, and
the {bpref "methods.power_series.analytic_hypersurface"}[hypersurface version]
combines it with noncharacteristic jet determination: at a noncharacteristic point of
an analytic hypersurface, analytic normal data have a unique analytic
solution germ.

# Scalar equations of higher order

The hypersurface theorem is stated for one scalar quasilinear equation of
order $`k\ge1`,

$$`
\sum_{|\alpha|=k}a_\alpha\bigl(x,J_{<k}u(x)\bigr)\,\partial^\alpha u(x)
=b\bigl(x,J_{<k}u(x)\bigr),
`

where $`J_{<k}u` is the list of all derivatives of order below $`k`. It is
proved in four steps. The first two work in the flat picture, with Cauchy
data on $`\{x_0=0\}`. The third straightens a curved hypersurface with an
analytic chart, and the fourth recovers flat Cauchy data from normal data.

The flat normal form solves for the pure time derivative:

$$`
\partial_0^ku=\sum_{\substack{|\alpha|=k\\\alpha\ne(k,0,\ldots,0)}}a_\alpha\bigl(J_{<k}u,x\bigr)\,\partial^\alpha u
+b\bigl(J_{<k}u,x\bigr),
\qquad \partial_0^ju=0\text{ on }\{x_0=0\}\ (j<k).
`

Each term on the right has at least one spatial derivative among its $`k`.

:::theorem "foundations.cauchy.scalar_formal_solution" (parent := "foundations.cauchy") (lean := "PDE.Cauchy.Quasilinear.Analytic.existsUnique_formal_solution, PDE.Cauchy.Quasilinear.Analytic.exists_convergent_formal_solution") (uses := "foundations.cauchy.formal_solution, foundations.cauchy.convergent_formal_solution")
Over any commutative $`\mathbb Q`-algebra and for any formal coefficient
series, the normal form has exactly one formal solution whose first $`k`
time coefficients vanish. Over $`\mathbb R`, if every coefficient series has
positive radius of convergence, this formal solution has positive radius of
convergence.
:::

:::proof "foundations.cauchy.scalar_formal_solution"
The time-degree recursion of the formal solution theorem applies with one
unknown and order $`k`. The coefficient of $`t^n` on the right uses only
time coefficients of $`u` below $`n+k`, because every term has fewer than
$`k` time derivatives. For convergence, the lower jet
$`U=(\partial^\beta u)_{\lvert\beta\rvert<k}` satisfies a first-order
system. The time derivative of a component of order below $`k-1` is
another component. A top-order derivative with a spatial index $`i` is
$`\partial_{x_i}` of a lower component, and the pure time derivative of top
order is given by the equation. One extra clock component absorbs the
explicit dependence on $`x_0`. The system is in the normal form of the
convergence theorem, so its formal solution converges. By formal uniqueness,
its first component is the scalar formal solution.
:::

:::theorem "foundations.cauchy.scalar_zero_data" (parent := "foundations.cauchy") (lean := "PDE.Cauchy.Quasilinear.Analytic.exists_analytic_solution_zero, PDE.Cauchy.Quasilinear.Analytic.eventuallyEq_of_analytic_solution_zero") (uses := "foundations.cauchy.scalar_formal_solution")
If the coefficients $`a_\alpha` and $`b` are analytic at the origin, the
normal form has a solution analytic on a ball about the origin in
$`\mathbb R^{1+d}` whose whole lower jet vanishes on $`\{x_0=0\}`. Two
solutions analytic at the origin whose pure time derivatives of order below
$`k` vanish on $`\{x_0=0\}` near the origin agree near the origin.
:::

:::proof "foundations.cauchy.scalar_zero_data"
The sum of the convergent formal solution is analytic on its ball, and the
power-series form of the equation turns into the pointwise equation after
summation. The vanishing time coefficients give the zero lower jet on the
initial plane. For uniqueness, the Taylor series of either solution satisfies
the formal equation with zero initial coefficients, so both Taylor series
equal the unique formal solution.
:::

General flat data reduce to zero data by subtraction. If $`G` is analytic
and carries the prescribed data, then $`w=u-G` solves an equation whose
coefficients are those of the original, evaluated at $`J_{<k}(w+G)`.
Dividing by the pure time coefficient puts it in normal form, so only that
coefficient needs to be nonzero.

:::theorem "foundations.cauchy.scalar_data_extension" (parent := "foundations.cauchy") (lean := "PDE.Cauchy.Quasilinear.Analytic.exists_analytic_solution_of_data_extension, PDE.Cauchy.Quasilinear.Analytic.eventuallyEq_of_analytic_solution_of_lower_jet") (uses := "foundations.cauchy.scalar_zero_data")
Let $`G` be analytic at the origin, let $`a_\alpha` and $`b` be analytic at
$`(0,J_{<k}G(0))`, and suppose
$`a_{(0,\ldots,0)}(0,J_{<k}G(0))\ne0`. Then on some ball about the origin
there is an analytic solution $`u` of the equation with
$`J_{<k}u=J_{<k}G` on $`\{x_0=0\}`. Two analytic solutions with the same
lower jet on $`\{x_0=0\}` near the origin agree near the origin, provided the
pure time coefficient is nonzero at their common initial jet.
:::

:::proof "foundations.cauchy.scalar_data_extension"
Shift by $`G` and divide by the pure time coefficient, which stays nonzero
on a neighbourhood by continuity. The normalized coefficients are analytic,
and the zero-data theorem solves the shifted equation. Adding $`G` back
gives $`u` on a ball small enough for the division to be valid. For
uniqueness, use the solution $`u` itself as the data extension. Then
$`0` and $`v-u` solve the same normalized equation, both with zero pure time
traces, and zero-data uniqueness gives $`v-u=0` near the origin.
:::

A curved hypersurface $`\Gamma=\{\varphi=0\}` with $`\nabla\varphi(p)\ne0`
is flattened by an analytic chart whose first coordinate is $`\varphi`.
The equation transforms by the chain rule, and noncharacteristicity
transforms with it.

:::theorem "foundations.cauchy.coordinate_change" (parent := "foundations.cauchy") (lean := "PDE.Cauchy.Quasilinear.Analytic.equation_comp_iff, PDE.Cauchy.Quasilinear.Analytic.transformedCoefficients_replicate, PDE.Cauchy.Quasilinear.Analytic.transformedCoefficients_replicate_ne_zero, PDE.Cauchy.Quasilinear.Analytic.analyticAt_transformed_of_level_chart") (uses := "foundations.cauchy.noncharacteristic_jets")
Let $`c` be analytic with inverse $`\psi`. Pulling back by $`c` gives
transformed coefficients and forcing, analytic where the originals are, such
that $`u\circ c` solves the original equation at $`\psi(y)` exactly when
$`u` solves the transformed equation at $`y`. If the $`i`-th component of
$`c` is $`\varphi` near $`\psi(y)` and $`\nabla\varphi\ne0` there, the
transformed coefficient of $`\partial_i^k` is

$$`
\lvert\nabla\varphi\rvert^k\sum_{\lvert\alpha\rvert=k}a_\alpha\,\nu^\alpha,
\qquad \nu=\frac{\nabla\varphi}{\lvert\nabla\varphi\rvert},
`

with the original coefficients evaluated at the transported lower jet. It is
nonzero exactly when $`\Gamma` is noncharacteristic at that point.
:::

:::proof "foundations.cauchy.coordinate_change"
Write $`\partial^\alpha(u\circ c)` by the finite chain rule for
compositions. The derivatives of $`u` of order $`k` appear linearly, with
coefficients built from first derivatives of $`c`, and everything else
depends only on lower derivatives of $`u`. Collecting terms defines the
transformed coefficients and the forcing. The coefficient of the pure
derivative $`\partial_i^k` collects the products of the $`i`-th component
of the first derivative of $`c` in each slot. That component is
$`\nabla\varphi=\lvert\nabla\varphi\rvert\,\nu`, so the coefficient is
$`\lvert\nabla\varphi\rvert^k` times the principal symbol at $`\nu`.
:::

:::theorem "foundations.cauchy.level_chart_uniqueness" (parent := "foundations.cauchy") (lean := "PDE.Cauchy.Quasilinear.Analytic.eventuallyEq_of_analytic_solution_of_level_chart") (uses := "foundations.cauchy.coordinate_change, foundations.cauchy.scalar_data_extension, foundations.cauchy.noncharacteristic_jets")
Let $`c` be an analytic chart at $`p` with analytic inverse, $`c(p)=0`,
and first component $`\varphi`, with $`\nabla\varphi(p)\ne0`. Suppose
the coefficients are analytic at the lower jet of $`u` at $`p`, and the
principal symbol at the unit normal is nonzero there. Two solutions analytic
at $`p` with the same normal derivatives $`D_\nu^ju` for $`j<k` on
$`\{\varphi=0\}` near $`p` agree near $`p`.
:::

:::proof "foundations.cauchy.level_chart_uniqueness"
Differentiating the equal normal data tangentially gives equal lower jets
on the hypersurface, as in the first step of the jet theorem. Transport
these through the chart to equal lower jets on $`\{y_0=0\}`. The transformed
equation has a nonzero pure transverse coefficient by the coordinate-change
theorem, so flat uniqueness applies to the two pulled-back solutions.
:::

The {bpref "methods.power_series.analytic_hypersurface"}[hypersurface theorem]
puts these steps together. For existence, it builds one analytic function
whose normal derivatives on $`\Gamma` are the prescribed $`g_j`, solves the
transformed problem with that function as data extension, and pulls the
solution back. The data are ordinary normal derivatives with the unit
normal held fixed.
