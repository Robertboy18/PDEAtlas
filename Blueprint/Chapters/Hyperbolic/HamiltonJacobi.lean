/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.NonlinearFirstOrder
import PDE.Hyperbolic.HamiltonJacobi.Characteristics
import PDE.Hyperbolic.HamiltonJacobi.Control.TerminalValue
import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Path.Hamiltonian
import PDE.Hyperbolic.HamiltonJacobi.Equation
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.InitialValue
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Viscosity
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Comparison
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Control.Viscosity
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.FinitePropagation
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.InitialValue
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Quadratic
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Regularity
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Semiconcavity
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Variational
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Viscosity

/-!
# Hamilton-Jacobi equations

Hamilton–Jacobi equations: characteristics, the Hopf–Lax formula, optimal
control, and viscosity solutions.
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
#doc (Manual) "Hamilton–Jacobi and Hopf–Lax" =>

:::group "hyperbolic.hamilton_jacobi"
Hamilton–Jacobi and Hopf–Lax
:::

# The equation and its characteristics

The formal Hamilton–Jacobi equation has a Hamiltonian that may depend on
time, and the characteristic theory specializes the general first-order characteristic system of the
previous chapter to this particular nonlinearity.

:::definition "hyperbolic.hj.equation" (parent := "hyperbolic.hamilton_jacobi") (lean := "NonlinearFirstOrder.hamiltonJacobiEquation, NonlinearFirstOrder.hjF") (uses := "foundations.pde_problems.problem, foundations.coordinates.spatial_gradient, foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-115"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a Hamiltonian $`H=H(p,t,x)` on
$`\mathbb R^n\times\mathbb R\times\mathbb R^n` and a spacetime domain
$`U\subseteq\mathbb R^{n+1}`, with time in coordinate zero, the Hamilton–Jacobi
equation is the single-equation problem

$$`
\partial_tu+H(D_xu,t,x)=0\quad\text{on }U
`

with no side conditions; $`D_xu` is the spatial gradient. In the fully
nonlinear form $`F(Du,u,(t,x))=0` the same equation uses

$$`
F(p,z,(t,x))=p_0+H(p_x,t,x),
`

where $`p_0` is the time component of the spacetime gradient and $`p_x` its
spatial part; the value argument $`z` does not enter. The autonomous
equation $`u_t+H(Du,x)=0` is the special case of a time-independent
Hamiltonian.
:::

:::theorem "hyperbolic.hj.characteristic_equations" (parent := "hyperbolic.hamilton_jacobi") (lean := "NonlinearFirstOrder.hamiltonJacobi_characteristic_equations_at") (uses := "hyperbolic.hj.equation, hyperbolic.first_order.characteristic_system, foundations.operators.gradient")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-119"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`U\subseteq\mathbb R^{n+1}` be open, let the phase function
$`F(p,z,(t,x))=p_0+H(p_x,t,x)` be $`C^1` in all of its arguments, and let
$`u\in C^2(U)` satisfy $`F(Du,u,(t,x))=0` on $`U`, that is,
$`u_t+H(D_xu,t,x)=0`. Let $`\gamma\colon\mathbb R\to\mathbb R^{n+1}` be
differentiable at $`s` with $`\gamma(s)\in U` and

$$`
\dot\gamma(s)=D_pF\bigl(Du(\gamma(s)),u(\gamma(s)),\gamma(s)\bigr),
`

and assume that $`H` is differentiable in its momentum argument and jointly
differentiable in its time and space arguments at the point determined by
$`\gamma(s)`. Write $`\gamma=(t,x)`, let $`p=Du\circ\gamma=(p_0,p_x)` be
the spacetime gradient along the curve, and let $`z=u\circ\gamma`. Then at
the parameter value $`s`

$$`
\dot t=1,\qquad
\dot x=D_pH(p_x,t,x),\qquad
\dot p_0=-H_t(p_x,t,x),
`

$$`
\dot p_x=-D_xH(p_x,t,x),\qquad
\dot z=D_pH(p_x,t,x)\cdot p_x-H(p_x,t,x).
`

These are Hamilton's equations for $`(x,p_x)` with the curve parameter
identified with time; the last identity is the classical
$`\dot z=p\cdot\dot x-H`.
:::

:::proof "hyperbolic.hj.characteristic_equations" (uses := "hyperbolic.first_order.characteristics_local")
Apply the general characteristic identities for $`F(Du,u,\cdot)=0` to this
$`F`. Since $`F` is affine in $`p_0` with unit coefficient, the momentum
gradient $`D_pF` has time component $`1` and spatial part $`D_pH`, which
gives $`\dot t=1` and $`\dot x=D_pH`. The general equation
$`\dot p=-D_{(t,x)}F-F_z\,p` has $`F_z=0`, and the spacetime gradient of
$`F` splits into the time derivative $`H_t` and the spatial gradient
$`D_xH`. Finally $`\dot z=D_pF\cdot p=p_0+D_pH\cdot p_x`, and the equation
$`p_0=-H` along the solution turns this into $`\dot z=D_pH\cdot p_x-H`.
:::

# The Hopf–Lax formula

The Hopf–Lax formula is built from convex duality. Given a Hamiltonian
$`H`, its Legendre–Fenchel transform is the Lagrangian

$$`
L(q)=\sup_{p\in\mathbb R}\{pq-H(p)\}.
`

The value at time $`t>0` then minimizes the initial value plus the action of
the constant-speed path joining a spatial footpoint to the observation point.
Each analytic stage below is used in the proof that this value is a viscosity
solution.

:::definition "hyperbolic.hj.legendre_transform" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.legendreTransform, HopfLax1D.LegendreFinite")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The one-dimensional Legendre–Fenchel transform is

$$`
L(q)=H^*(q)=\sup_{p\in\mathbb R}\bigl(pq-H(p)\bigr).
`

`LegendreFinite H` states that this defining supremum is bounded above for
every $`q`, so $`L\colon\mathbb R\to\mathbb R` is well defined without
introducing extended-real arithmetic into the interface.
:::

The transform and Hopf–Lax results below assume `LegendreFinite H`.
Without this hypothesis, Lean still assigns a real value to the supremum,
but it need not represent a finite convex conjugate.

:::theorem "hyperbolic.hj.legendre_convex_continuous" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.legendre_transform") (lean := "HopfLax1D.convexOn_legendreTransform, HopfLax1D.continuous_legendreTransform")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`0\leq\theta\leq1`,

$$`
L\bigl(\theta q_1+(1-\theta)q_2\bigr)
\leq\theta L(q_1)+(1-\theta)L(q_2).
`

The finite Legendre transform is convex because it is a supremum of affine
functions. In one dimension, finite convexity on all of $`\mathbb R` also
gives continuity $`L\in C(\mathbb R)`, which permits the Hopf–Lax integrand
to attain its minimum after coercive localization.
:::

:::proof "hyperbolic.hj.legendre_convex_continuous"
For each fixed $`p`, the map $`q\mapsto pq-H(p)` is affine. Its value at a
convex combination is the same convex combination of its endpoint values;
taking the supremum over $`p` gives the convexity inequality. Finiteness on
the open interval $`\mathbb R` then invokes the standard theorem that a
finite convex real function is continuous on the interior of its domain.
:::

Convexity of $`L` is one half of duality. The other half is that the transform
loses no information about a convex Hamiltonian: applying it twice returns
$`H`, which is how the Hamiltonian re-enters the viscosity argument after the
variational formula has been analyzed in terms of $`L`.

:::theorem "hyperbolic.hj.legendre_biconjugate" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.legendre_transform") (lean := "HopfLax1D.biconjugate_eq_of_convex_of_differentiable")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a differentiable convex Hamiltonian with finite Legendre transform,
$`H^{**}=H` pointwise. No separate finiteness assumption on the biconjugate
is required. The proof evaluates the first conjugate at $`H'(p)` and combines
the convex supporting-line inequality with the reverse Fenchel bound.
:::

:::proof "hyperbolic.hj.legendre_biconjugate"
Fenchel's inequality gives $`H^{**}(p)\leq H(p)`. For the reverse inequality,
convex differentiability supplies the supporting line
$`H(r)\geq H(p)+H'(p)(r-p)`. Rearranging shows that the supremum defining
$`H^*(H'(p))` equals $`pH'(p)-H(p)`. Testing the second conjugate at
$`H'(p)` therefore gives $`H^{**}(p)\geq H(p)`.
:::

Convexity of $`L` also has a dynamic consequence: the cost of a straight
displacement over time $`t+s` never exceeds the total cost of two straight
displacements through any intermediate point. This inequality is what makes
the Hopf–Lax operators compose.

:::theorem "hyperbolic.hj.legendre_time_split" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.legendre_convex_continuous") (lean := "HopfLax1D.legendreTransform_time_split_le")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "119-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`L=H^*` be finite. For $`s,t>0` and any $`x,y,z\in\mathbb R`,

$$`
(t+s)L\!\left(\frac{x-y}{t+s}\right)
\leq sL\!\left(\frac{z-y}{s}\right)
     +tL\!\left(\frac{x-z}{t}\right).
`

Travel from $`y` to $`z` takes time $`s`, and from $`z` to $`x` time
$`t`. The direct path costs no more than this two-segment path.
:::

:::proof "hyperbolic.hj.legendre_time_split"
The single-step velocity is the weighted average of the two segment
velocities, with weights $`t/(t+s)` and $`s/(t+s)`. Apply convexity of $`L`
to that average and multiply by $`t+s`. The resulting right-hand side is
exactly the sum of the two segment costs.
:::

The Lagrangian enters the solution formula as the cost of straight-line
motion: the value at $`(t,x)` is the cheapest way of arriving at $`x` from
some footpoint $`y`, paying the initial value at $`y` plus the action of
constant-speed travel.

:::definition "hyperbolic.hj.hopf_lax_formula" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.legendre_transform") (lean := "HopfLax1D.hopfLax")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`t>0`, the Hopf–Lax operator is

$$`
(Q_tg)(x)=
\inf_{y\in\mathbb R}
\left\{g(y)+tL\!\left(\frac{x-y}{t}\right)\right\}.
`

Thus the optimization variable is the initial footpoint $`y`, and the
Lagrangian is evaluated at the constant speed from $`y` to $`x`.
:::

The infimum ranges over all of $`\mathbb R`, so neither its finiteness nor its
attainment is automatic. Lipschitz data cannot decrease faster than linearly,
while a finite Legendre transform lies above affine functions of every slope,
and this is what makes the integrand coercive.

:::theorem "hyperbolic.hj.hopf_lax_attainment" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.hopf_lax_formula, hyperbolic.hj.legendre_convex_continuous") (lean := "HopfLax1D.exists_isMinOn_hopfLaxIntegrand_of_lipschitz")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a finite Legendre transform, positive time, and Lipschitz initial data,
there exists a minimizing footpoint $`y_*` with

$$`
(Q_tg)(x)
=g(y_*)+tL\!\left(\frac{x-y_*}{t}\right).
`

The integrand is bounded below. The proof derives a linear coercive lower
bound from the dual supremum, minimizes on a sufficiently large compact
interval, and excludes every point outside that interval.
:::

:::proof "hyperbolic.hj.hopf_lax_attainment"
Let $`K` be a Lipschitz constant for $`g`. Test the supremum defining $`L`
at both slopes $`K+1` and $`-(K+1)`. These two bounds control the two tails:
the action grows at least as $`(K+1)|x-y|` minus a constant, while the
datum can decrease by at most $`K|x-y|`. Thus the integrand tends to
$`+\infty` as $`|y|\to\infty`. Continuity gives a minimum on a large compact
interval, and the coercive bound excludes every point outside it.
:::

The coercivity estimate is quantitative: it confines every minimizing
footpoint to an explicit ball around $`x` whose radius grows linearly with
$`t`, which is the one-dimensional form of finite propagation speed.

:::definition "hyperbolic.hj.hopf_lax_propagation_radius" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.hopf_lax_attainment") (lean := "HopfLax1D.propagationRadius, HopfLax1D.dist_le_propagationRadius_of_isMinOn_hopfLaxIntegrand, HopfLax1D.exists_hopfLax_eq_integrand_and_dist_le")
Let $`L=H^*` be finite and let $`g` be $`K`-Lipschitz, with $`K\geq0`.
Set

$$`
C_H(K)=\max\{H(K+1),H(-(K+1))\},\qquad
R_{H,K}(t)=\max\{0,\ t(C_H(K)+L(0))\}.
`

For $`t>0`, every minimizing footpoint $`y_*` for $`(Q_tg)(x)` satisfies
$`|x-y_*|\leq R_{H,K}(t)`. Such a minimizer exists. Indeed, the coercive
lower bound is $`g(x)+|x-y|-tC_H(K)`, while the competitor $`y=x`
has cost $`g(x)+tL(0)`; comparison gives the radius.
:::

Since only footpoints inside the propagation ball matter, two equally
Lipschitz data that are close on that ball have close values at $`(t,x)`,
however much they differ elsewhere.

:::theorem "hyperbolic.hj.hopf_lax_local_nonexpansive" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.hopf_lax_attainment, hyperbolic.hj.hopf_lax_propagation_radius") (lean := "HopfLax1D.dist_hopfLax_le_of_dist_le_on_closedBall")
Let $`L=H^*` be finite, let $`g,\tilde g` both be $`K`-Lipschitz, and fix
$`t>0` and $`x\in\mathbb R`. If

$$`
|g(y)-\tilde g(y)|\leq C
\qquad\text{whenever }|y-x|\leq R_{H,K}(t),
`

then $`|(Q_tg)(x)-(Q_t\tilde g)(x)|\leq C`. Only values on this closed
ball enter the comparison.
:::

:::proof "hyperbolic.hj.hopf_lax_local_nonexpansive"
Choose a minimizing footpoint for each datum. Localization places both
footpoints in the common closed ball. Testing each Hopf–Lax infimum at the
other datum's minimizer gives the two one-sided inequalities whose
combination is the distance estimate.
:::

The case of distance zero is the domain-of-dependence statement: the value at
$`(t,x)` is determined by the data on the propagation ball alone.

:::theorem "hyperbolic.hj.hopf_lax_finite_domain" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.hopf_lax_local_nonexpansive") (lean := "HopfLax1D.hopfLax_eq_of_eqOn_closedBall")
Let $`L=H^*` be finite, let $`g,\tilde g` both be $`K`-Lipschitz, and
let $`t>0`. Then

$$`
\left(g=\tilde g\ \text{on }\overline B(x,R_{H,K}(t))\right)
\quad\Longrightarrow\quad
(Q_tg)(x)=(Q_t\tilde g)(x).
`
:::

:::proof "hyperbolic.hj.hopf_lax_finite_domain"
Apply local nonexpansiveness with distance bound zero. Agreement of the
initial data on the propagation ball makes the required local supremum
distance vanish, so the distance between the two Hopf–Lax values is zero
and the values are equal.
:::

A different one-sided estimate concerns second differences. Semiconcavity of
the datum is inherited by the Hopf–Lax profile with the same constant.

:::theorem "hyperbolic.hj.hopf_lax_semiconcavity" (parent := "hyperbolic.hamilton_jacobi") (uses := "hyperbolic.hj.hopf_lax_attainment") (lean := "HopfLax1D.hopfLax_semiconcave_of_semiconcave_phi")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If the initial datum is globally Lipschitz and satisfies

$$`
g(x+h)+g(x-h)-2g(x)\leq C h^2,
`

then for every $`t>0` its Hopf–Lax profile satisfies the same estimate:

$$`
(Q_tg)(x+h)+(Q_tg)(x-h)-2(Q_tg)(x)\leq C h^2.
`

A minimizer for the central point supplies translated competitors at the two
neighboring points, and the common Lagrangian terms cancel.
:::

:::proof "hyperbolic.hj.hopf_lax_semiconcavity"
Let $`y_*` minimize the value at $`x`. Use $`y_*+h` and $`y_*-h` as
competitors for the values at $`x+h` and $`x-h`. Both competitors have the
same displacement $`x-y_*`, so their two Lagrangian terms cancel against
twice the central one. What remains is precisely the assumed semiconcavity
inequality for $`g` at $`y_*`.
:::

The time-splitting inequality for $`L` becomes, at the level of the operators,
the semigroup law. The formal version assumes that the relevant infima are
bounded below, an assumption discharged later by the Lipschitz estimates.

:::theorem "hyperbolic.hj.hopf_lax_semigroup" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.hopfLax_semigroup") (uses := "hyperbolic.hj.hopf_lax_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "119-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`L=H^*` be finite and fix $`s,t>0` and $`x\in\mathbb R`. Assume
the sets of competitor costs defining $`Q_{t+s}g(x)`,
$`Q_t(Q_sg)(x)`, and $`Q_sg(z)` for every $`z\in\mathbb R` are bounded
below. Then

$$`
(Q_t(Q_sg))(x)=(Q_{t+s}g)(x).
`

This is the dynamic-programming semigroup identity for the autonomous
Hamiltonian.
:::

:::proof "hyperbolic.hj.hopf_lax_semigroup" (uses := "hyperbolic.hj.legendre_time_split")
The time-splitting inequality gives a lower bound for every two-segment cost;
taking the two infima yields $`Q_{t+s}g(x)\leq Q_t(Q_sg)(x)`. Conversely,
for each footpoint $`y`, choose $`z=(sx+ty)/(t+s)`. Both segment velocities
then equal $`(x-y)/(t+s)`, so the two-segment cost equals the direct cost.
Testing the nested infima at $`z` and $`y` and then taking the infimum over
$`y` proves the reverse inequality.
:::

Restricting to straight paths loses nothing. By Jensen's inequality any
absolutely continuous path with integrable action ending at $`x` costs at
least the straight path from its own starting point. The footpoint infimum
therefore equals the infimum over these admissible paths.

:::theorem "hyperbolic.hj.hopf_lax_path_formula" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.hopfLax_eq_variationalValue_of_lipschitz, HamiltonJacobi.HopfLax.value_hamiltonian_eq_variationalValue, HamiltonJacobi.HopfLax.exists_isMinOn_pathCost_hamiltonian") (uses := "hyperbolic.hj.hopf_lax_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "114-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In one dimension, for positive time, a finite Legendre transform, and Lipschitz
initial data,

$$`
(Q_tg)(x)=
\inf_{\substack{\gamma\in AC([0,t]),\ \gamma(t)=x\\L(\dot\gamma)\in L^1(0,t)}}
\left\{
g(\gamma(0))+\int_0^tL(\dot\gamma(s))\,ds
\right\}.
`

Thus the pointwise footpoint infimum equals Evans's variational infimum over
finite-action absolutely continuous paths ending at $`x`.

The path representation also holds on any finite-dimensional real inner-product
space $`E`. Assume $`H:E\to\mathbb R` is convex and superlinear and
$`g:E\to\mathbb R` is Lipschitz. With the inner product identifying the dual
space and $`L=H^*`, for every $`t>0` and $`x\in E`,

$$`Q_tg(x)=\min_{y\in E}\left\{g(y)+tL\left(\frac{x-y}{t}\right)\right\}
=\min_{\substack{\gamma\in AC([0,t];E),\ \gamma(t)=x\\
L(\dot\gamma)\in L^1(0,t)}}
\left\{g(\gamma(0))+\int_0^t L(\dot\gamma(s))\,ds\right\}.`

Both minima are attained: a minimizing footpoint $`y` gives the minimizing
path $`\gamma(s)=y+s(x-y)/t`. The finite-dimensional statement uses the
convex, superlinear Hamiltonian hypotheses; the subsequent one-dimensional
comparison and viscosity theorems retain their own stated assumptions.
:::

:::proof "hyperbolic.hj.hopf_lax_path_formula"
Jensen's inequality and the absolutely-continuous fundamental theorem bound
every path action below by the pointwise Hopf–Lax integrand at its initial
point. Constant-speed affine paths give the reverse inequality for every
possible initial point. In finite dimension the Hamiltonian assumptions
give a finite, continuous, convex, superlinear conjugate. Its superlinear
growth dominates the possible linear decrease of $`g`, making the
footpoint cost coercive. A continuous coercive function on a
finite-dimensional space attains its minimum, and the corresponding straight
path has finite action and attains the path minimum as well.
:::

# Comparison, Lipschitz estimates, and the closed-time evolution

:::theorem "hyperbolic.hj.hopf_lax_nonexpansive" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.dist_hopfLax_le_of_lipschitz, HopfLax1D.hopfLax_mono_phi_of_lipschitz") (uses := "hyperbolic.hj.hopf_lax_formula")
For a finite Legendre transform, $`t>0`, and a $`K`-Lipschitz datum $`g`, the
Hopf–Lax operator preserves order and is nonexpansive in the uniform distance
against an arbitrary second datum $`\tilde g`:

$$`
g\le\tilde g\ \text{pointwise}\ \Longrightarrow\ Q_tg\le Q_t\tilde g,
\qquad
\left(\forall y,\ |g(y)-\tilde g(y)|\le C\right)\ \Longrightarrow\
|(Q_tg)(x)-(Q_t\tilde g)(x)|\le C .
`

Only the datum $`g` is assumed Lipschitz, and in the first statement it is
the smaller one. This hypothesis makes its Hopf–Lax infimum bounded below;
the second datum needs no regularity of its own.
:::

:::proof "hyperbolic.hj.hopf_lax_nonexpansive" (uses := "hyperbolic.hj.hopf_lax_attainment")
Lipschitz data give a coercive lower bound for the Hopf–Lax integrand, so
the infimum for $`g` is finite. If $`g\le\tilde g`, every competitor value
for $`\tilde g` dominates the corresponding competitor value for $`g`, which
gives monotonicity. For the distance bound, the pointwise inequalities
$`g\le\tilde g+C` and $`\tilde g\le g+C` transfer to the infima because
adding a constant to the datum adds the same constant to the Hopf–Lax value;
the two one-sided inequalities combine to the distance estimate.
:::

Comparison controls the dependence on the datum; the next estimates control
the dependence on $`(t,x)`. Translating a minimizing footpoint shows that the
spatial Lipschitz constant of the datum is not increased, and the semigroup
law converts the estimate against the datum into an estimate in time with a
constant depending only on $`H` and $`K`.

:::theorem "hyperbolic.hj.hopf_lax_lipschitz" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.hopfLax_lipschitzWith_space_of_lipschitz, HopfLax1D.abs_sub_hopfLax_le_lipschitz_time, HopfLax1D.abs_sub_hopfLax_le_initial_mul, HopfLax1D.abs_sub_hopfLax_le_lipschitz_spacetime, HopfLax1D.timeLipschitzConstant") (uses := "hyperbolic.hj.hopf_lax_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "120-128"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`H` have a finite Legendre transform $`L` and let $`g` be
$`K`-Lipschitz. Set

$$`
C_{H,K}=\max\bigl\{|L(0)|,\ |\max\{H(K),H(-K)\}|\bigr\}.
`

Then for all $`t,s>0` and $`x,y\in\mathbb R`,

$$`
|(Q_tg)(x)-(Q_tg)(y)|\le K|x-y|,\qquad
|(Q_tg)(x)-g(x)|\le C_{H,K}\,t,
`

$$`
|(Q_tg)(x)-(Q_sg)(x)|\le C_{H,K}|t-s|,\qquad
|(Q_tg)(x)-(Q_sg)(y)|\le K|x-y|+C_{H,K}|t-s|.
`

Thus $`x\mapsto(Q_tg)(x)` is $`K`-Lipschitz with the constant of the datum,
and the profile is Lipschitz in time with an explicit constant depending only
on $`H` and $`K`. These are the estimates of Lemma 2 of Evans, §3.3.2.
:::

:::proof "hyperbolic.hj.hopf_lax_lipschitz" (uses := "hyperbolic.hj.hopf_lax_attainment, hyperbolic.hj.hopf_lax_semigroup")
For the spatial estimate, let $`y_*` be a minimizing footpoint for the value
at $`x`. Translating it by $`y-x` gives a competitor for the value at $`y`
with the same Lagrangian term, so the difference of the two values is bounded
by $`|g(y_*+y-x)-g(y_*)|\le K|x-y|`; exchanging the roles of $`x` and $`y`
gives the reverse bound. For the estimate against the datum, the stationary
footpoint $`y=x` gives $`(Q_tg)(x)\le g(x)+tL(0)`, while the Fenchel bound
$`L(q)\ge K|q|-\max\{H(K),H(-K)\}` together with the Lipschitz bound on
$`g` gives the matching lower bound. The time estimate restarts the
evolution at time $`s` through the semigroup law and applies the previous
bound to the $`K`-Lipschitz profile $`Q_sg`; the spacetime estimate is the
triangle inequality.
:::

The Hopf–Lax operator is defined for $`t>0`; the evolution on the closed
half-plane, the candidate solution of Evans §3.3.2, equals $`g` at $`t=0`. The
estimate $`|(Q_tg)(x)-g(x)|\le C_{H,K}\,t` is what makes inserting the datum
at time zero a continuous extension.

:::definition "hyperbolic.hj.hopf_lax_evolution" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.hopfLaxEvolution, HamiltonJacobi1D.hopfLaxEvolutionSpacetime") (uses := "hyperbolic.hj.hopf_lax_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "120-128"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The closed-time Hopf–Lax evolution inserts the datum at time zero:

$$`
(S_tg)(x)=
\begin{cases}
g(x), & t=0,\\
(Q_tg)(x), & t\neq0.
\end{cases}
`

Its spacetime form is $`u(z)=(S_{z_0}g)(z_1)` on $`\mathbb R^2` with time in
coordinate zero. This is Evans's candidate solution in §3.3.2, defined on
$`\mathbb R\times[0,\infty)` with $`u=g` on $`\{t=0\}`. The definitions
are total; every theorem about them below carries the hypothesis $`t\ge0`.
:::

On the closed half-line the semigroup law can be stated without bounded-below
side conditions, because $`Q_sg` is again $`K`-Lipschitz and the Lipschitz
estimates supply every needed lower bound.

:::theorem "hyperbolic.hj.hopf_lax_evolution_dynamic_programming" (parent := "hyperbolic.hamilton_jacobi") (lean := "HamiltonJacobi1D.hopfLaxEvolutionSpacetime_dynamic_programming, HopfLax1D.hopfLaxEvolution_semigroup_of_lipschitz, HopfLax1D.hopfLaxEvolution_dynamic_programming_of_lipschitz") (uses := "hyperbolic.hj.hopf_lax_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "119-124"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a finite Legendre transform and a $`K`-Lipschitz datum $`g`, the
closed-time operators form a semigroup on the closed half-line: for
$`t,s\ge0`,

$$`
S_{t+s}g=S_t(S_sg).
`

Equivalently, the profile $`u(t,x)=(S_tg)(x)` can be restarted from any
intermediate time: if $`0\le s\le t`, then

$$`
u(t,x)=\bigl(S_{t-s}\,u(s,\cdot)\bigr)(x).
`

Unlike the positive-time semigroup law, no bounded-below hypotheses appear:
the Lipschitz datum supplies them, and the time-zero cases reduce to
$`S_0=\mathrm{id}`.
:::

:::proof "hyperbolic.hj.hopf_lax_evolution_dynamic_programming" (uses := "hyperbolic.hj.hopf_lax_semigroup, hyperbolic.hj.hopf_lax_lipschitz")
If $`t=0` or $`s=0`, both sides agree because $`S_0` is the identity. For
$`t,s>0`, the Lipschitz datum makes all three Hopf–Lax infima bounded below,
and the spatial Lipschitz estimate shows that $`Q_sg` is again
$`K`-Lipschitz, so the positive-time semigroup identity applies. The restart
form substitutes $`t=(t-s)+s`.
:::

Comparison likewise extends to the initial slice, where it reduces to the
hypotheses on the data themselves.

:::theorem "hyperbolic.hj.hopf_lax_evolution_nonexpansive" (parent := "hyperbolic.hamilton_jacobi") (lean := "HamiltonJacobi1D.dist_hopfLaxEvolutionSpacetime_le_of_initial_dist_le, HamiltonJacobi1D.hopfLaxEvolutionSpacetime_le_of_initial_le, HopfLax1D.dist_hopfLaxEvolution_le_of_lipschitz, HopfLax1D.hopfLaxEvolution_mono_phi_of_lipschitz") (uses := "hyperbolic.hj.hopf_lax_evolution")
Let $`H` have a finite Legendre transform, let $`g` be $`K`-Lipschitz, and
let $`\tilde g` be arbitrary. Write $`u_g` for the closed-time Hopf–Lax
profile of $`g`. At every spacetime point $`z` with $`z_0\ge0`,

$$`
g\le\tilde g\ \text{pointwise}\ \Longrightarrow\ u_g(z)\le u_{\tilde g}(z),
\qquad
\left(\forall y,\ |g(y)-\tilde g(y)|\le C\right)
\ \Longrightarrow\ |u_g(z)-u_{\tilde g}(z)|\le C.
`

Thus the evolution preserves order and is nonexpansive in the uniform
distance on the closed forward half-plane, including the initial slice.
:::

:::proof "hyperbolic.hj.hopf_lax_evolution_nonexpansive" (uses := "hyperbolic.hj.hopf_lax_nonexpansive")
At time zero both profiles reduce to the data, and the claims are the
hypotheses. At positive time the profiles are the Hopf–Lax values, and the
positive-time comparison theorem applies verbatim.
:::

# The quadratic Hamiltonian

:::definition "hyperbolic.hj.quadratic_hamiltonian" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.quadraticHamiltonian, HopfLax1D.hasDerivAt_quadraticHamiltonian, HopfLax1D.strongConvexOn_quadraticHamiltonian")
The normalized quadratic Hamiltonian is

$$`
H(p)=\frac{p^2}{2}.
`

It is the model case of the one-dimensional theory: differentiable with
$`H'(p)=p`, and strongly convex on $`\mathbb R` with constant one.
:::

:::theorem "hyperbolic.hj.quadratic_legendre_self_dual" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.legendreTransform_quadraticHamiltonian, HopfLax1D.legendreFinite_quadraticHamiltonian, HopfLax1D.hopfLax_quadraticHamiltonian") (uses := "hyperbolic.hj.quadratic_hamiltonian, hyperbolic.hj.legendre_transform, hyperbolic.hj.hopf_lax_formula")
The quadratic Hamiltonian has a finite Legendre transform and is self-dual:

$$`
L(q)=\sup_{p\in\mathbb R}\Bigl(pq-\frac{p^2}2\Bigr)=\frac{q^2}2=H(q).
`

Consequently, for every $`t\neq0` and every datum $`g`, the Hopf–Lax value is
the infimum of the Moreau cost

$$`
(Q_tg)(x)=\inf_{y\in\mathbb R}\Bigl\{g(y)+\frac{(x-y)^2}{2t}\Bigr\}.
`

For $`t>0` this is the Moreau envelope of $`g` with parameter $`t`.
:::

:::proof "hyperbolic.hj.quadratic_legendre_self_dual"
Completing the square gives $`pq-p^2/2=q^2/2-(p-q)^2/2`. The right-hand
side is at most $`q^2/2`, which bounds the defining supremum and proves
finiteness, and the choice $`p=q` attains the bound. Substituting $`L=H`
into the Hopf–Lax integrand and simplifying $`t\,(x-y)^2/(2t^2)` gives the
Moreau cost.
:::

The minimization can preserve a corner. As a teaching calculation, take the
Lipschitz datum $`g(y)=-|y|` and $`t>0`. Minimizing separately on the two
half-lines gives

$$`
\inf_y\left\{-|y|+\frac{(x-y)^2}{2t}\right\}
=-|x|-\frac t2.
`

For $`x>0` the minimizing footpoint is $`y=x+t`; for $`x<0` it is
$`y=x-t`. At $`x=0` both $`y=t` and $`y=-t` minimize. The value remains
continuous, but switching between minimizing paths leaves it
nondifferentiable at the origin.

We can still test the equation there. A smooth function touching this value
from above at $`(t,0)` has $`\varphi_t=-1/2` and a spatial slope
$`p=\varphi_x\in[-1,1]`, hence

$$`
\varphi_t+H(\varphi_x)=-\frac12+\frac{p^2}{2}\le0.
`

No differentiable function touches this downward corner from below: its
slope would have to be at least $`1` on the left and at most $`-1` on the
right. The supersolution test is therefore vacuous at the corner, while
away from it the classical equation holds. This illustrates the
{bpref "hyperbolic.hj.viscosity_solution"}[touching-test definition] used
below. The calculation is done by hand; its datum is unbounded, so it lies
outside the bounded-slab initial-value class.

In every dimension, the quadratic value is also the limit of the
viscous Cauchy solutions. For bounded uniformly continuous
$`g\colon\mathbb R^n\to\mathbb R` and $`\nu>0`, evolve
$`\exp(-g/(2\nu))` by heat flow for time $`\nu t` and apply $`-2\nu\log`.
The resulting $`u^\nu` solves $`u_t^\nu+\|D_xu^\nu\|^2/2=\nu\Delta u^\nu`
for $`t>0`. As $`\nu\downarrow0`, it converges uniformly on
$`\mathbb R^n\times[0,T]` for every finite $`T\geq0` to the quadratic
Hopf–Lax value $`\inf_y\{g(y)+\|x-y\|^2/(2t)\}` for $`t>0`, extended by
$`g` at time zero.

The heat integral is controlled from both sides using the quadratic minimum:
a Gaussian bound controls its tail, and a ball around a minimizing footpoint
provides positive mass. The continuity modulus controls the cost on that
ball. Parabolic rescaling makes these bounds uniform in both space and time
on the slab. Comparison identifies the limit as the unique quadratic
viscosity IVP solution in the class bounded and uniformly continuous on every
finite slab, using locally $`C^1` tests.

# Autonomous optimal control

:::definition "hyperbolic.hj.autonomous_control_value" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.IsAdmissibleControl, HopfLax1D.controlValue")
Starting from $`z`, an admissible control $`a` is an integrable velocity with
integrable Lagrangian cost and terminal constraint

$$`
x=z+\int_0^t a(s)\,ds.
`

The autonomous value is

$$`
V(t,x)=
\inf_{(z,a)\,\mathrm{admissible}}
\left\{g(z)+\int_0^tL(a(s))\,ds\right\}.
`

Admissibility is a predicate on the initial state and the control.
:::

Constant controls with velocity $`(x-z)/t` are admissible and cost exactly the
Hopf–Lax integrand at the footpoint $`z`, so the control value is at most the
Hopf–Lax value; convexity of $`L` supplies the reverse inequality.

:::theorem "hyperbolic.hj.control_hopf_lax" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.hopfLax_eq_controlValue_of_lipschitz") (uses := "hyperbolic.hj.autonomous_control_value, hyperbolic.hj.hopf_lax_formula")
For a finite Legendre transform, positive time, and Lipschitz initial data,

$$`
V(t,x)=(Q_tg)(x).
`

Jensen's inequality shows that every admissible control costs at least the
constant control $`a(s)=(x-z)/t` with the same displacement, while constant
controls give the reverse bound.
:::

:::proof "hyperbolic.hj.control_hopf_lax"
For an admissible control starting at $`z`, the terminal constraint says that
its mean velocity is $`(x-z)/t`. Jensen's inequality bounds its integral
cost below by $`tL((x-z)/t)`, so taking infima gives the Hopf–Lax lower
bound. Conversely, every footpoint $`z` defines the constant admissible
control with that velocity and exactly that cost, giving the reverse bound.
:::

Once the two values agree, the Hopf–Lax semigroup law is Bellman's principle
for the control problem, with the intermediate value function playing the role
of the restarted datum.

:::theorem "hyperbolic.hj.control_dynamic_programming" (parent := "hyperbolic.hamilton_jacobi") (lean := "HopfLax1D.controlValue_dynamic_programming_of_lipschitz") (uses := "hyperbolic.hj.control_hopf_lax, hyperbolic.hj.hopf_lax_semigroup")
Under the same finite-conjugate and Lipschitz-data hypotheses, if $`0<s<t`,
Bellman's principle holds:

$$`
V(t,x)=V_{t-s}\bigl(x;\,z\mapsto V(s,z)\bigr).
`
:::

:::proof "hyperbolic.hj.control_dynamic_programming"
Replace each control value by its equal Hopf–Lax expression. Splitting the
total time as $`s+(t-s)` turns the right-hand side into the composition
$`Q_{t-s}(Q_sg)`. The Hopf–Lax semigroup law identifies this composition
with $`Q_tg`, which is the original control value.
:::

:::group "hyperbolic.viscosity"
Viscosity solutions
:::

:::definition "hyperbolic.hj.viscosity_solution" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.IsContinuousDifferentiableTestSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "582-583"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A continuous candidate is tested against differentiable functions touching
it from above or below relative to an open spacetime domain. The resulting
inequalities encode $`u_t+H(u_x)=0` without requiring derivatives of $`u`.
This is the domain-relative definition specialized to $`H=H(p)`.
:::

The interior notion says nothing about initial data or growth. Evans's
initial-value formulation adds a pointwise trace at $`t=0` and boundedness
with uniform continuity on every time slab, the regularity class in which he
proves uniqueness.

:::definition "hyperbolic.hj.viscosity_ivp" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.IsDifferentiableTestInitialSolution") (uses := "hyperbolic.hj.viscosity_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "579-606"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a one-dimensional spatially dependent Hamiltonian $`H(p,x)` and initial
datum $`g`, the formal initial-value predicate requires boundedness and
uniform continuity on every slab $`[0,T]\times\mathbb R`, the domain-relative
sub- and supersolution inequalities on $`t>0` for tests differentiable at
the contact point, and the pointwise trace $`u(0,x)=g(x)`.
:::

Comparison arguments use the predicate split into a subsolution half and a
supersolution half, each with a one-sided initial inequality.

The generic comparison theorem uses space-time coordinates $`(x,t)` on
$`E\times\mathbb R`, where $`E` is a finite-dimensional real inner product
space, and requires tests to be locally $`C^1` at contact.
Ordered initial values remain ordered for $`u_t+H(D_xu)=0`,
when $`H` is continuous and both candidates are bounded and uniformly
continuous on every finite closed time slab. Convexity and a global
Lipschitz bound on $`H` are unnecessary.

The proof doubles space and time. Uniform continuity controls initial
contact, reciprocal time barriers exclude the terminal face, and quadratic
localization gives a maximum on a compact set. Finite dimensionality also
makes the bounded momentum ball compact, so continuity of $`H` controls the
small difference between the two localized test gradients.

For the scalar predicates above, the coordinate map changes $`(t,x)` to
$`(x,t)` and preserves the slab and initial conditions.
Every pulled-back local-$`C^1` test is differentiable at contact, which is
enough for this direction of transport; the converse is not needed.

:::theorem "hyperbolic.hj.viscosity_ivp_sub_super" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.isDifferentiableTestInitialSolution_iff_sub_and_super") (uses := "hyperbolic.hj.viscosity_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "579-606"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The initial-value solution predicate is equivalent to the conjunction of
the initial-value subsolution and supersolution predicates. Their initial
conditions are respectively $`u(0,\cdot)\le g` and
$`g\le u(0,\cdot)`, so the conjunction recovers the exact trace.
:::

:::proof "hyperbolic.hj.viscosity_ivp_sub_super"
Unfold the three predicates. Their slab regularity and interior
touching-test conditions agree componentwise. At time zero, the subsolution
gives $`u(0,x)\leq g(x)` and the supersolution gives the reverse inequality,
so antisymmetry yields the exact trace. Conversely, equality with $`g`
immediately supplies both one-sided trace conditions.
:::

A viscosity solution need not be differentiable, but every differentiable
pointwise solution is one: at a touching point the test function shares the
derivative of $`u`, so the classical equation for $`u` becomes the required
inequality for the test function.

:::theorem "hyperbolic.hj.classical_to_spatial_viscosity" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.isSpatialDifferentiableTestSolution_of_classical") (uses := "hyperbolic.hj.viscosity_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "582-583"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A differentiable pointwise solution of
$`u_t+H(u_x,x)=0` on an open domain satisfies the corresponding
domain-relative viscosity inequalities.
:::

:::proof "hyperbolic.hj.classical_to_spatial_viscosity"
At an interior point where a differentiable test function touches $`u` from
above, the difference $`u-\phi` has a local maximum, so its derivative is
zero and $`D\phi=Du`. Substitution into the classical equation gives the
subsolution inequality, in fact equality. A local minimum gives the same
gradient identity and the supersolution inequality.
:::

In the autonomous case the same argument also delivers the continuity built
into the definition, since differentiability implies continuity.

:::theorem "hyperbolic.hj.classical_to_viscosity" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.isContinuousDifferentiableTestSolution_of_classical") (uses := "hyperbolic.hj.viscosity_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "582-583"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A differentiable pointwise solution of
$`u_t+H(u_x)=0` is a viscosity solution. If a test function $`\phi`,
differentiable at the contact point, touches $`u` from above at $`(t_0,x_0)`, then

$$`
\phi_t(t_0,x_0)+H(\phi_x(t_0,x_0))\leq0;
`

touching from below gives the reverse inequality. At such a touching point,
$`D\phi=Du`, so both follow from the classical equation. On an open domain,
the ambient-local inequalities induce the domain-relative continuous
viscosity solution.
:::

:::proof "hyperbolic.hj.classical_to_viscosity"
At every contact point where the test is differentiable, Fermat's theorem
applied to $`u-\phi` gives $`\phi_t=u_t` and $`\phi_x=u_x`. The classical
equation therefore evaluates
the test residual to zero, which implies the required inequality in either
contact direction. Differentiability supplies continuity, and restricting
the ambient local statement to the open domain gives the domain-relative
viscosity solution.
:::

For general Lipschitz initial data, the Hopf–Lax profile need not be a
classical solution. The one-step dynamic-programming inequality proves the
subsolution inequality, and an attained minimizing footpoint proves the
supersolution inequality. These touching-test arguments first give the
equation for $`H^{**}`; the biconjugate identity then gives the equation
for $`H`.

:::theorem "hyperbolic.hj.hopf_lax_viscosity_solution" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.hopfLaxSpacetime_isContinuousDifferentiableTestSolution_with_initial_trace") (uses := "hyperbolic.hj.viscosity_solution, hyperbolic.hj.hopf_lax_formula")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "114-134"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "579-606"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
For a convex differentiable Hamiltonian with finite Legendre transform, and
for Lipschitz initial data, the Hopf–Lax profile is a continuous viscosity
solution on $`t>0` and converges pointwise to the initial datum as $`t`
decreases to zero.
:::

:::proof "hyperbolic.hj.hopf_lax_viscosity_solution" (uses := "hyperbolic.hj.hopf_lax_semigroup, hyperbolic.hj.hopf_lax_attainment, hyperbolic.hj.legendre_biconjugate, hyperbolic.hj.hopf_lax_lipschitz")
Lipschitz data provide lower bounds and attainment for the variational
problem. Touching-test arguments establish the subsolution and supersolution
inequalities first for the biconjugate Hamiltonian. Convex differentiability
identifies the biconjugate with $`H`; separate spacetime Lipschitz estimates
give continuity and the one-sided initial trace.
:::

The interior result gives no slab regularity, which the initial-value notion
requires. Since the control value coincides with the
Hopf–Lax profile for positive time and with $`g` at time zero, the Lipschitz
estimates upgrade the interior viscosity solution to an initial-value viscosity
solution, provided the datum is bounded as well as Lipschitz.

:::theorem "hyperbolic.hj.control_value_viscosity_ivp" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi1D.controlValueEvolutionSpacetime_isDifferentiableTestInitialSolution") (uses := "hyperbolic.hj.control_hopf_lax, hyperbolic.hj.control_dynamic_programming, hyperbolic.hj.hopf_lax_viscosity_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "579-606"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a convex differentiable autonomous Hamiltonian with finite Legendre
transform and bounded Lipschitz initial data, the closed-time control value
satisfies

$$`
V_t+H(V_x)=0\quad(t>0),\qquad V(0,x)=g(x)
`

in the differentiable-test viscosity sense defined above. The theorem
includes bounded uniform continuity on every closed time slab and gives
the exact time-zero trace.
:::

:::proof "hyperbolic.hj.control_value_viscosity_ivp"
For positive time, the control value equals the Hopf–Lax solution, so it
inherits the interior viscosity inequalities and spacetime regularity.
Define the closed-time value to be $`g` at $`t=0`; the Hopf–Lax initial
trace proves continuity there. Bounded Lipschitz data and the established
time and space estimates give bounded uniform continuity on each slab, so
the subsolution, supersolution, and exact-trace components give the
initial-value predicate above.
:::

For state-dependent dynamics, we first construct the response to a given
control. Let $`E` be a separable real Banach space and $`A` a
pseudometrizable control space, both with their Borel measurable structures.
Assume $`f\colon E\times A\to E` is jointly continuous, uniformly Lipschitz
in the state, and bounded in norm by $`M`. On a finite interval $`[a,b]`,
$`a\le b`, each a.e. strongly measurable control $`\alpha` and initial state
determine an $`M`-Lipschitz trajectory with
$`u'=f(u,\alpha)` almost everywhere. Its integral equation holds at every
time in $`[a,b]`, and it is unique there among absolutely continuous
responses with the same initial state.

The construction uses the nonlinear Carathéodory integral equation.
Successive integrations give a factorial denominator, so some Picard iterate
contracts even on a long finite interval; the affine construction uses the
same Volterra estimate.

We can now attach a cost to each response and minimize over controls. Let
$`h(x,v)` be a bounded running cost, measurable on $`E\times A` for the
product Borel structure, and let the terminal cost $`g` be bounded below.
Measurability is all the integral needs: along a response,
$`t\mapsto h(X(t),\alpha(t))` is then bounded and almost everywhere
measurable on $`[a,b]`. A nonempty control space supplies a competitor; the cost bounds
make the following infimum finite:

$$`
V_{a,b}(x)=\inf_\alpha\left\{\int_a^b
h(X_x^\alpha(t),\alpha(t))\,dt+g(X_x^\alpha(b))\right\}.
`

For every cut $`a\le c\le b`, dynamic programming gives

$$`
V_{a,b}(x)=\inf_{\alpha\text{ on }[a,c]}
\left\{\int_a^c h(X_x^\alpha(t),\alpha(t))\,dt
+V_{c,b}(X_x^\alpha(c))\right\}.
`

Here $`X_x^\alpha` is the response already constructed above. Restricting
a full control gives one inequality. For the other, concatenate a prefix
control with a tail control and use uniqueness to identify the two pieces
of the trajectory. Taking the infima then gives equality, including cuts
at either endpoint. There is no need to select an optimal control.

We can compare two starting points without knowing either optimal control.
Apply the same control to both trajectories. If $`K` is the state Lipschitz
constant of $`f`, Grönwall gives

$$`
\|X_x^\alpha(t)-X_y^\alpha(t)\|\le e^{K(t-a)}\|x-y\|.
`

Suppose the running and terminal costs are Lipschitz in the state, uniformly
in the control, with constants $`L` and $`G`. The separation estimate bounds
the difference of their costs. Its constant does not depend on the control,
so it survives taking the infimum:

$$`
|V_{a,b}(x)-V_{a,b}(y)|\le
\bigl(L(b-a)+G\bigr)e^{K(b-a)}\|x-y\|.
`

Dynamic programming also compares different starting times: a short prefix costs
at most $`C(c-a)` and moves the state by at most $`M(c-a)`, where $`C`
bounds the running cost. The spatial estimate controls the change in the
tail value. Together these give joint Lipschitz regularity on every finite
terminal slab. Directly comparing a trajectory's terminal state with its
starting point also gives

$$`
|V_{a,b}(x)-g(x)|\le (C+GM)(b-a).
`

This last estimate uses only the states reachable from $`x`, so it also
applies when $`g` is unbounded below elsewhere.

To use the forward-time convention, put $`W(x,t)=V_{-t,0}(x)` for $`t\ge0`.
On a real inner product state space the corresponding Hamiltonian is

$$`
H(p,x)=-\inf_v\{\langle p,f(x,v)\rangle+h(x,v)\}.
`

This Hamiltonian has the momentum bound
$`|H(p,x)-H(q,x)|\le M\|p-q\|` and the spatial comparison bound
$`|H(p,x)-H(p,y)|\le(K+L)(1+\|p\|)\|x-y\|`.
The remaining question is local: what can a smooth test tell us when it
just touches this infimum of costs? Let $`\varphi` be $`C^1` near a contact
point $`(x,t)`, with $`t>0`. Along a short controlled response, forward time
for the trajectory means decreasing the horizon in $`W`. The rate of test
value plus running cost is therefore

$$`
R_v=D_x\varphi(x,t)\cdot f(x,v)-\varphi_t(x,t)+h(x,v).
`

At an upper contact, dynamic programming permits us to try any constant
control $`v`. Here the cost needs to be continuous in the state for that fixed
$`v`, which the Lipschitz hypothesis below supplies; no continuity in the
control variable is used. If the rate were negative, a short interval would
lower the cost past the touching value. Hence $`R_v\ge0` for every $`v`. Taking the infimum
gives $`\varphi_t+H(D_x\varphi,x)\le0`.

At a lower contact, suppose instead that $`\inf_v R_v>0`. The common state
Lipschitz bounds and continuity of $`D\varphi` preserve a positive margin
near the contact, uniformly over controls. Bounded speed keeps every short
response there. Integrating the margin would make every prefix cost plus
tail value strictly larger than $`W(x,t)`, contradicting dynamic programming.
Thus $`\inf_v R_v\le0`, which is the supersolution inequality.

This argument holds in a separable real Hilbert space. Apply the chain rule
to the test along the absolutely continuous response; the value itself need
not be differentiable. A terminal cost bounded below suffices for these
interior inequalities.

For bounded Lipschitz $`g`, the earlier estimates also give bounded uniform
continuity on every finite slab and $`W(x,0)=g(x)` exactly.
Thus $`W` is an initial-value viscosity solution of $`W_t+H(DW,x)=0`.
In finite dimension, the Hamiltonian bounds above permit viscosity comparison:
every solution with the same datum in this slab class equals $`W` for all $`t\ge0`.

For a terminal time $`T`, the translation $`t\mapsto t-T` of every control
identifies the terminal value with $`W(x,T-t)`, and time reflection turns the
initial-value inequalities into the terminal ones.

:::theorem "hyperbolic.hj.control_terminal_value" (parent := "hyperbolic.viscosity") (lean := "HamiltonJacobi.controlTerminalValue_solves_terminal_problem")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§10.3.3, Theorem 2, with the Hamiltonian read as an infimum"
    page := "596"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`E` be a finite-dimensional real inner product space and $`A` a
nonempty pseudometrizable control space, each with its Borel structure.
Let $`f\colon E\times A\to E` be continuous, bounded by $`M`, and
$`K`-Lipschitz in $`x` uniformly in $`v`. Let $`h\colon E\times A\to\mathbb R`
be Borel measurable, bounded by $`C`, and $`L`-Lipschitz in $`x` uniformly
in $`v`. Let $`g` be bounded and Lipschitz, and let $`T>0`. For
$`0\le t\le T` put

$$`
u(x,t)=\inf_\alpha\left\{\int_t^T h(X(s),\alpha(s))\,ds+g(X(T))\right\},
`

the infimum over measurable controls on $`[t,T]`, where $`X` is the response
to $`\alpha` starting from $`x` at time $`t`. Then $`u` is bounded and
uniformly continuous on $`E\times[0,T]`, $`u(x,T)=g(x)`, and $`u` is a
viscosity solution of

$$`
u_t+\inf_{v\in A}\{D_xu\cdot f(x,v)+h(x,v)\}=0\qquad(0<t<T)
`

for $`C^1` tests: if $`u-\varphi` has a local maximum at a point of the open
slab, then $`\varphi_t+\inf_v\{D_x\varphi\cdot f(x,v)+h(x,v)\}\ge0` there,
and at a local minimum the reverse inequality holds. Every bounded uniformly
continuous function on $`E\times[0,T]` with terminal value $`g` that satisfies
the same two inequalities for $`C^\infty` tests coincides with $`u` on
$`E\times[0,T]`.
:::

:::proof "hyperbolic.hj.control_terminal_value"
Translating controls identifies $`u(x,t)` with the forward value
$`W(x,T-t)`. The contact arguments and the slab estimates make $`W` a bounded
uniformly continuous viscosity solution of $`W_t+H(D_xW,x)=0` with
$`W(\cdot,0)=g`, where $`H(p,x)=-\inf_v\{p\cdot f(x,v)+h(x,v)\}`. Time
reflection exchanges the two problems and reverses the inequalities.
Uniqueness comes from the finite-dimensional comparison theorem for $`W`,
applied to the reflected competitor.
:::

When $`A` is compact and $`h` is jointly continuous, the infimum in the
Hamiltonian is attained at each $`(p,x)` and is a minimum over the controls.
A bounded Borel cost need not attain it, so the theorem is stated with the
infimum.
