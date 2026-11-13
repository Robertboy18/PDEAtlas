/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod
import PDE.Elliptic.Semilinear.DirichletMonotonicity
import PDE.Elliptic.Semilinear.DirichletNemytskii
import PDE.Elliptic.Semilinear.FixedPoint.MonotoneIteration
import PDE.Elliptic.Semilinear.OddPower.Variational
import PDE.Elliptic.Semilinear.Resolvent.ConvexGradient.Basic
import PDE.Elliptic.Semilinear.Resolvent.MoreauEnvelope.Approximation
import PDE.Elliptic.Semilinear.Resolvent.MoreauEnvelope.Basic
import PDE.Elliptic.Semilinear.Resolvent.MoreauEnvelope.Differentiability
import PDE.Elliptic.Semilinear.Resolvent.ProximalIteration
import PDE.Elliptic.Semilinear.Resolvent.SemilinearEnergy
import PDE.Elliptic.Semilinear.Resolvent.YosidaApproximation
import PDE.Elliptic.Semilinear.VariationalDirichlet

/-!
# Semilinear elliptic methods

Variational existence, monotone iteration, and smooth
convex regularization for semilinear elliptic equations.
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
#doc (Manual) "Semilinear Elliptic Methods" =>

Semilinear elliptic equations take the form $`-\Delta u+g(x,u)=f`. The
lower-order nonlinearity changes the existence argument even though the
principal part remains the Laplacian. For example, $`g(u)=u^3` comes from
a convex quartic potential, while $`g(u)=u^3-u` has a double-well potential
and loses that convexity. The sign and growth of the source determine which
of the methods below apply.

When $`g` is the derivative of a potential $`G`, the weak equation can be read
as the first variation of

$$`
J(u)=\frac12\int_\Omega|\nabla u|^2\,dx
+\int_\Omega G(x,u)\,dx
-\int_\Omega fu\,dx.
`

Convexity of $`G(x,-)` makes the nonlinear part of the energy convex. The
Dirichlet term supplies coercivity, and the direct method produces a minimizer.
Differentiating at that minimizer gives the semilinear weak equation. This
approach admits nonlinearities such as odd powers whose derivatives are not
globally Lipschitz, provided the necessary Sobolev integrability and
differentiability statements are available.

If no useful potential exists, one may instead invert the linear elliptic
operator and search for a fixed point, at the price of a smallness condition
that excludes many large or superlinear nonlinearities.

Monotonicity lies between these viewpoints. A derivative of a convex potential
is monotone, but monotonicity can also be used directly in stability and
uniqueness estimates without referring to a minimizing construction. Ordered
iteration uses sub- and supersolutions to trap extremal solutions. The
resolvents and Moreau envelopes treated here start from a differentiable
convex potential and produce Lipschitz gradient approximations.
Evans (2010, Chapters 8–9) develops the variational
and nonlinear methods; {Informal.citet "brezis-2011"}[] (Chapters 5 and 9) emphasizes monotone
operators and convex analysis.

:::group "methods.semilinear_variational"
Semilinear variational methods
:::

# Convex Energies in Hilbert Space

The abstract energy and resolvent results use a real Hilbert space and
bounded bilinear forms; loads are continuous linear functionals.

:::definition "methods.semilinear.energy" (parent := "methods.semilinear_variational") (lean := "PDE.Elliptic.Semilinear.variationalEnergy")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "454-457"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "465-475"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
For a symmetric elliptic form $`B`, nonlinear potential $`\Phi`, and load
$`\ell`, the energy is

$$`
J(u)=\frac12B(u,u)+\Phi(u)-\ell(u).
`
:::

The quadratic term supplies coercivity of $`J`: it dominates both the linear
load and any potential bounded below by an affine function of the norm.

:::theorem "methods.semilinear.energy_minimizer" (parent := "methods.semilinear_variational") (lean := "PDE.Elliptic.Semilinear.existsUnique_variationalEnergy_minimizer") (uses := "methods.semilinear.energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`B(u,u)\geq c\lVert u\rVert^2` for $`c>0`, $`\Phi` is convex and lower
semicontinuous, and for some $`a\geq0` and $`b\in\mathbb R`

$$`
\Phi(u)\geq-\bigl(a\lVert u\rVert+b\bigr),
`

then $`J` is coercive and strongly convex. Hence

$$`
\exists!\,u\in H,\qquad J(u)=\inf_{v\in H}J(v).
`

The hypotheses are abstract sufficient conditions.
:::

:::proof "methods.semilinear.energy_minimizer" (uses := "methods.direct_method.convex_minimizer")
The proof assembles three ingredients. First, *coercivity*: the quadratic
term satisfies $`\frac12 B(u,u)\geq\frac{c}{2}\|u\|^2`, the potential is
bounded below by $`-(a\|u\|+b)`, and the load contributes at most
$`\|\ell\|\|u\|`. For large norms these linear terms are absorbed, giving
$`J(u)\geq\frac{c}{4}\|u\|^2-C`, confirming that $`J(u)\to+\infty` as
$`\|u\|\to\infty`. Second, *strong convexity*: for $`0<t<1`,

$$`
J((1-t)u+tv)\leq(1-t)J(u)+tJ(v)-\frac{c}{2}t(1-t)\|u-v\|^2,
`

which follows from the quadratic identity for $`B` and convexity of $`\Phi`.
Third, *lower semicontinuity*: the quadratic and load terms are continuous,
while lower semicontinuity of $`\Phi` is assumed. Convexity then upgrades
this strong lower semicontinuity to weak lower semicontinuity through closed
convex sublevel sets. The coercive direct method gives existence; the strict
convexity inequality shows any two minimizers coincide.
:::

Existence of the minimizer used no differentiability of $`\Phi` at all. To
pass from a minimizer to a weak equation one needs the derivative of $`J`,
and this is where differentiability of the potential enters as an additional
hypothesis, at the single point where the derivative is taken.

:::theorem "methods.semilinear.energy_derivative" (parent := "methods.semilinear_variational") (lean := "PDE.Elliptic.Semilinear.hasFDerivAt_variationalEnergy") (uses := "methods.semilinear.energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "454-456"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`\Phi` has Fréchet derivative $`D\Phi(u)` at $`u`, symmetry of $`B`
gives

$$`
DJ(u)[v]=B(u,v)+D\Phi(u)[v]-\ell(v).
`
:::

:::proof "methods.semilinear.energy_derivative"
Differentiate the three summands of $`J` separately. The derivative of the
linear load is $`\ell`. Bilinearity gives the derivative of
$`\frac12B(u,u)` in direction $`v` as
$`\frac12(B(v,u)+B(u,v))`; symmetry reduces this to $`B(u,v)`. Adding the
given derivative of $`\Phi` and subtracting the load proves the formula.
:::

With the derivative formula, the abstract first-variation theorem gives the
weak equation. Differentiability is assumed only at the minimizer itself.

:::theorem "methods.semilinear.euler_equation" (parent := "methods.semilinear_variational") (lean := "PDE.Elliptic.Semilinear.weakEquation_of_variationalEnergy_minimizer") (uses := "methods.semilinear.energy")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "454-456"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "472-474"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
Every differentiable global minimizer satisfies the weak semilinear equation

$$`
B(u,v)+D\Phi(u)[v]=\ell(v)
\qquad\text{for every }v\in H.
`

The Lean theorem assumes the full Fréchet derivative as data.
:::

:::proof "methods.semilinear.euler_equation" (uses := "methods.euler_lagrange.first_variation, methods.semilinear.energy_derivative")
Differentiate the energy at the minimizer, apply the vanishing first-variation
theorem, and evaluate the resulting zero continuous linear functional on an
arbitrary test vector.
:::

For a differentiable convex energy $`J`, every stationary point is a global
minimizer, so strict convexity also gives uniqueness among weak solutions.
Monotonicity proves uniqueness directly and gives a quantitative stability
estimate.

:::theorem "methods.semilinear.monotone_stability" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.Weak.norm_sub_le_load_sub_norm_div")
For a coercive bilinear form and a nonlinear dual-valued map that is monotone
between two candidate states, subtracting their weak equations gives

$$`
\lVert u_1-u_2\rVert
\leq \frac{\lVert \ell_1-\ell_2\rVert}{c}.
`

The estimate takes the two weak equations as hypotheses and uses no
existence theorem or variational construction.
:::

:::proof "methods.semilinear.monotone_stability"
Subtract the two weak equations evaluated at the same test vector $`v`:

$$`
B(u_1-u_2,v)+(N(u_1)-N(u_2))[v]=(\ell_1-\ell_2)[v].
`

Choose $`v=u_1-u_2`. On the left, coercivity gives
$`B(u_1-u_2,u_1-u_2)\geq c\|u_1-u_2\|^2`, and monotonicity of $`N` gives
$`(N(u_1)-N(u_2))[u_1-u_2]\geq 0`. Together:

$$`
c\|u_1-u_2\|^2\leq(\ell_1-\ell_2)[u_1-u_2]
\leq\|\ell_1-\ell_2\|_{H^*}\|u_1-u_2\|.
`

If $`u_1=u_2` the estimate is trivial. Otherwise divide both sides by
$`\|u_1-u_2\|>0` and then by $`c>0` to obtain the stated bound.
:::

For the variational problem $`N=D\Phi`, and monotonicity is not an extra
hypothesis: the derivative of a convex functional is monotone. Specializing
the abstract estimate therefore gives Lipschitz dependence on the load, and
uniqueness with it, at no additional cost.

:::theorem "methods.semilinear.load_stability" (parent := "methods.semilinear_variational") (lean := "PDE.Elliptic.Semilinear.norm_sub_le_load_sub_norm_div_of_convex_potential") (uses := "methods.semilinear.monotone_stability, methods.semilinear.energy_derivative")
For a differentiable convex potential and a bilinear form with coercivity
modulus $`c>0`, weak solutions with loads $`\ell_1` and $`\ell_2` satisfy

$$`
\lVert u_1-u_2\rVert
\leq \frac{\lVert \ell_1-\ell_2\rVert}{c}.
`
:::

:::proof "methods.semilinear.load_stability"
Convexity of $`\Phi` implies monotonicity of its Fréchet derivative. For any
$`u_1,u_2\in H`, convexity gives

$$`
\Phi(u_2)\geq\Phi(u_1)+D\Phi(u_1)[u_2-u_1],
\qquad
\Phi(u_1)\geq\Phi(u_2)+D\Phi(u_2)[u_1-u_2].
`

Adding these two inequalities yields
$`(D\Phi(u_1)-D\Phi(u_2))[u_1-u_2]\geq 0`, which is precisely monotonicity
of the map $`u\mapsto D\Phi(u)`. With this monotonicity established, the
abstract monotone stability theorem applies directly to the two Euler–Lagrange
equations. Setting $`\ell_1=\ell_2` gives $`\|u_1-u_2\|\leq 0`, hence
uniqueness.
:::

Existence by minimization, the Euler equation from differentiability, and
uniqueness from monotonicity are separate theorems with separate
hypotheses. Under global differentiability of the convex potential they
combine: differentiability gives the lower semicontinuity the minimizer
theorem needs, the supporting hyperplane at the origin gives its affine lower
bound, and monotonicity of $`D\Phi` gives uniqueness through the
load-stability estimate.

:::theorem "methods.semilinear.variational_solution" (parent := "methods.semilinear_variational") (lean := "PDE.Elliptic.Semilinear.existsUnique_variational_weak_solution") (uses := "methods.semilinear.energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "470-474"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a bounded symmetric form $`B` with coercivity modulus $`c>0`, and under
the global differentiability and convexity assumptions on the potential,
the variational route produces

$$`
\exists!\,u\in H,\qquad
B(u,v)+D\Phi(u)[v]=\ell(v)\quad(v\in H).
`
:::

:::proof "methods.semilinear.variational_solution" (uses := "methods.semilinear.energy_minimizer, methods.semilinear.euler_equation, methods.semilinear.load_stability")
Choose a direct-method minimizer and apply the first-variation bridge.
Convexity makes the potential derivative monotone, so the load-stability
estimate with equal loads proves uniqueness among all weak solutions.
:::

# Semilinear Dirichlet Problems

:::definition "methods.dirichlet.semilinear_weak_solution" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.IsDirichletSemilinearWeakSolution, SobolevSpace.GraphSpace.dirichletNemytskiiIntegrand") (uses := "elliptic.dirichlet.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "457"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a spatial set $`\Omega\subseteq\mathbb R^n`, a nonlinearity
$`g:\mathbb R^n\times\mathbb R\to\mathbb R`, and forcing $`f\in L^2(\Omega)`,
a field $`u\in H^1_0(\Omega)` is a weak solution of the semilinear Dirichlet
problem $`-\Delta u+g(x,u)=f` in $`\Omega`
when for every test field $`v\in H^1_0(\Omega)` the Nemytskii integrand
$`x\mapsto g(x,u(x))\,v(x)` is integrable and

$$`
\sum_{i=1}^n\int_\Omega\partial_iu\,\partial_iv\,dx
+\int_\Omega g(x,u(x))\,v(x)\,dx
=\int_\Omega f\,v\,dx.
`

The homogeneous Dirichlet condition is encoded by membership in
$`H^1_0(\Omega)`, the closure in the graph-space norm of smooth functions
compactly supported in $`\Omega`. For open $`\Omega`, this is the usual
$`H^1_0` space, and the boundary condition is not a pointwise statement.

Here $`u(x)` and $`v(x)` are the canonical $`L^2` representatives of the
base coordinates, and every integral uses the restricted domain measure of
$`\Omega`. Integrability is part of the definition because the Bochner
integral is totalized: without it the identity could hold vacuously for a
nonintegrable integrand. The nonlinear Poisson equation $`-\Delta u=h(u)`
is the autonomous case $`g(x,u)=-h(u)` with zero forcing.
:::

The abstract Hilbert-space theorems are stated for a dual-valued load
$`N:H\to H^*`, while the Dirichlet weak formulation is written with an integral
of $`g(x,u(x))\,v(x)`. Connecting the two requires an $`L^2` function
representing $`x\mapsto g(x,u(x))` for each $`u`; the integral then becomes an
$`L^2` pairing.

:::theorem "methods.dirichlet.nemytskii_bridge" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.isDirichletSemilinearWeakSolution_iff_nemytskii_load, SobolevSpace.GraphSpace.dirichletNemytskii_pairing_eq_integral") (uses := "methods.dirichlet.semilinear_weak_solution")
Suppose $`N:H^1_0(\Omega)\to L^2(\Omega)` represents the nonlinearity, in the
sense that for every $`u` the function $`N(u)` agrees almost everywhere on
$`\Omega` with $`x\mapsto g(x,u(x))`. Then for all $`u,v\in H^1_0(\Omega)`
the load functional of $`N(u)` is the Nemytskii integral,

$$`
\langle N(u),v\rangle_{L^2}=\int_\Omega g(x,u(x))\,v(x)\,dx,
`

and $`u` is a weak solution of the semilinear Dirichlet problem with forcing
$`f` if and only if

$$`
B(u,v)+\langle N(u),v\rangle_{L^2}=\langle f,v\rangle_{L^2}
\qquad(v\in H^1_0(\Omega)),
`

where $`B` is the Dirichlet form. This is the abstract strong-dual equation
used by the monotonicity, fixed-point, and variational arguments; on this
side the integrability clause of the weak formulation is automatic.
:::

:::proof "methods.dirichlet.nemytskii_bridge"
The load functional of $`N(u)` pairs $`N(u)` with the base coordinate of
$`v` in $`L^2`, and the product of two square-integrable functions is
integrable. Replacing $`N(u)` by its almost-everywhere representative
$`g(x,u(x))` changes neither the integrand almost everywhere nor the
integral, which gives the pairing identity and the integrability of the
Nemytskii integrand for every test field. Substituting the pairing identity
into the weak formulation turns it into the strong-dual equation and back.
:::

The variational route needs more than the load: it needs a potential $`\Phi`
on $`H^1_0(\Omega)` whose Fréchet derivative is the Nemytskii load of $`g`.
The candidate is the integral of a scalar density $`G(x,s)`, with $`g` playing
the role of $`\partial_sG`, evaluated along the canonical representative of
$`u`.

:::definition "methods.dirichlet.integral_potential" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.dirichletIntegralPotential")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "457"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "465-466"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
For a spatial set $`\Omega` and a scalar density $`G(x,s)`, the induced potential
on $`H^1_0(\Omega)` is

$$`
\Phi(u)=\int_\Omega G(x,u(x))\,dx,
`

using the canonical $`L^2`
representative of the base coordinate. The definition allows explicit spatial
dependence.
:::

Convexity of $`\Phi` is the hypothesis of the abstract minimizer theorem that
has to be verified on the PDE side. It is inherited from pointwise convexity
of $`G(x,-)`, as for the general integral functionals, once every admissible
density is integrable so that the totalized integral is the usual one.

:::theorem "methods.dirichlet.integral_convex" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.convexOn_dirichletIntegralPotential") (uses := "methods.dirichlet.integral_potential")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "468-470"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Almost-everywhere pointwise convexity of $`G(x,-)` and integrability of every
admissible density imply convexity of the integral potential on
$`H^1_0(\Omega)`:

$$`
\Phi((1-t)u+tv)\leq(1-t)\Phi(u)+t\Phi(v)
\qquad(0\leq t\leq1).
`

This requires convexity in the zeroth-order variable. The gradient-convexity
criterion for weak lower semicontinuity permits nonconvex dependence on that
variable, under its separate regularity, growth, and convergence hypotheses.
:::

:::proof "methods.dirichlet.integral_convex"
For almost every $`x`, the canonical base representative of
$`(1-t)u+tv` equals $`(1-t)u(x)+tv(x)`. Pointwise convexity of $`G(x,-)`
therefore bounds the integrand by the corresponding affine combination.
Integrability permits monotonicity and linearity of the integral, producing
the convexity inequality for $`\Phi`.
:::

All abstract inputs are now supplied on $`H^1_0(\Omega)`: the Dirichlet form
is symmetric and, on a bounded set in positive dimension, coercive by
Poincaré; the integral potential is convex; and the Nemytskii bridge turns the
abstract weak equation into the Dirichlet weak formulation. The remaining
hypotheses are the Fréchet derivative formula for $`\Phi` and the $`L^2`
representation of the Nemytskii map.

:::theorem "methods.dirichlet.variational_wellposedness" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.existsUnique_dirichlet_semilinear_of_variational") (uses := "methods.dirichlet.integral_potential, methods.dirichlet.semilinear_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "457"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "470-474"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
On a bounded spatial set in positive dimension, an integrable convex
potential whose Fréchet derivative is represented by an $`L^2` Nemytskii map
yields, for every $`f\in L^2(\Omega)`, a unique $`u\in H^1_0(\Omega)` satisfying

$$`
\sum_i\int_\Omega\partial_i u\,\partial_i v\,dx
+\int_\Omega g(x,u)v\,dx
=\int_\Omega fv\,dx
\qquad(v\in H^1_0(\Omega)),
`

the weak form of $`-\Delta u+g(x,u)=f`. No Lipschitz smallness condition is
used. The set $`\Omega` need not be open or measurable: all integrals use its
restricted domain measure.
:::

:::proof "methods.dirichlet.variational_wellposedness" (uses := "methods.dirichlet.integral_convex, methods.semilinear.variational_solution, methods.dirichlet.nemytskii_bridge")
Pointwise convexity and integrability make the integral potential convex.
Poincaré coercivity gives the Dirichlet form a positive ellipticity modulus.
The abstract strongly convex variational theorem then supplies a unique
minimizer, and its first variation is the displayed weak equation.
:::

# Monotonicity and Odd-Power Nonlinearities

:::theorem "methods.dirichlet.monotone_stability" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.norm_sub_le_forcing_sub_norm_div_of_monotone") (uses := "methods.semilinear.monotone_stability, methods.dirichlet.semilinear_weak_solution")
If the represented Nemytskii nonlinearity is pointwise monotone almost
everywhere, two semilinear Dirichlet solutions satisfy

$$`
\lVert u_1-u_2\rVert_{H^1_0}
\leq \frac{\lVert f_1-f_2\rVert_{L^2}}{c},
`

where $`c` is any positive coercivity modulus for the Dirichlet form. This
estimate uses only the two weak equations and monotonicity; the solutions
need not be supplied by the variational construction.
:::

:::proof "methods.dirichlet.monotone_stability"
Subtract the represented Dirichlet weak equations and test with
$`u_1-u_2`. The Dirichlet form contributes at least
$`c\|u_1-u_2\|_{H^1_0}^2`, and pointwise monotonicity makes the Nemytskii
term nonnegative after integration. Cauchy–Schwarz bounds the forcing term
by $`\|f_1-f_2\|_2\|u_1-u_2\|_{H^1_0}`; cancellation gives the result.
:::

The stability estimate needs monotonicity of $`s\mapsto g(x,s)`, and the
variational theorem needs convexity of $`G(x,-)`; for $`g=\partial_sG` these
are the same condition. Odd powers $`s\mapsto as+bs^{2k+1}` with $`a,b\geq0`
satisfy it. When $`b>0` and $`k\geq1`, the scalar source is not globally
Lipschitz.

:::theorem "methods.dirichlet.odd_power_solution" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.existsUnique_dirichlet_odd_power") (uses := "methods.dirichlet.variational_wellposedness, methods.dirichlet.semilinear_weak_solution")
On a bounded spatial set $`\Omega\subseteq\mathbb R^n` with $`n>0`, for
$`k\in\mathbb N`, nonnegative coefficients $`a,b`, and $`f\in L^2(\Omega)`,
the direct method gives a unique weak Dirichlet solution of

$$`
-\Delta u + a u + b u^{2k+1}=f.
`

The theorem states explicitly the integrability and Fréchet-derivative
hypotheses for the odd-power potential and assumes that a supplied
$`L^2`-valued Nemytskii map agrees almost everywhere with
$`a u+b u^{2k+1}`. These are the assumptions that depend on the dimension
and the available Sobolev embedding.
:::

:::proof "methods.dirichlet.odd_power_solution"
Use the potential density
$`G(s)=\frac a2s^2+\frac b{2k+2}s^{2k+2}`. Nonnegativity of $`a` and $`b`
makes $`G` convex, and its derivative is
$`g(s)=as+bs^{2k+1}`. The assumed Sobolev integrability justifies the
integral and Fréchet derivative formula. Applying variational Dirichlet
well-posedness gives existence, while strict coercivity of the gradient term
and monotonicity of $`g` give uniqueness.
:::

The cubic case makes the integrability assumptions concrete. Its potential
$`G(u)=u^4/4` is integrable when $`u\in L^4`, whereas representing
$`g(u)=u^3` in $`L^2` requires $`u\in L^6`, since
$`\int|u^3|^2=\int|u|^6`. Thus finiteness of the energy does not by itself
supply the $`L^2`-valued nonlinear map required here.
The Sobolev embedding and derivative hypotheses must establish that stronger
mapping property in the chosen dimension.

A negative linear coefficient makes $`\frac a2s^2` concave, so the potential
as written is not convex. The linear term can instead be moved into the
bilinear form, a modified Helmholtz form whose coercivity modulus drops by at
most $`a_-`, while the odd-power part stays convex.

:::theorem "methods.dirichlet.odd_power_signed_linear" (parent := "methods.semilinear_variational") (lean := "SobolevSpace.GraphSpace.existsUnique_dirichlet_odd_power_of_negPart_lt_coercivity") (uses := "methods.dirichlet.odd_power_solution, methods.dirichlet.semilinear_weak_solution")
The same conclusion holds for a signed linear coefficient $`a` when its
negative part is strictly smaller than a supplied Dirichlet coercivity
modulus. The higher-power coefficient remains nonnegative. The condition is
measured against the chosen modulus and is only sufficient.
:::

:::proof "methods.dirichlet.odd_power_signed_linear"
Split $`a=a_+-a_-`. The nonnegative terms $`a_+u^2` and
$`bu^{2k+2}` preserve convexity and monotonicity. The negative quadratic part
costs at most $`a_-\|u\|_2^2`; the supplied Dirichlet coercivity estimate
absorbs it because $`a_-<c`. The modified Helmholtz form therefore retains a
positive coercivity modulus. The same direct-method and first-variation
argument then gives the unique weak solution.
:::

# Monotone Iteration Between Barriers

:::theorem "methods.semilinear.monotone_extremal_solutions" (parent := "methods.semilinear_nonvariational") (lean := "SobolevSpace.Weak.isLeast_semilinear_weak_solution_Icc_of_tendsto_iterate, SobolevSpace.Weak.isGreatest_semilinear_weak_solution_Icc_of_tendsto_iterate") (uses := "elliptic.lax_milgram")
Let the ambient ordered Hilbert space have closed order relation, let the
linear form be bounded and coercive, and let $`N:V\to V^*` be continuous.
Assume $`\underline u\leq\overline u` and that the semilinear Picard map
is monotone and preserves $`[\underline u,\overline u]`.
If the iterates from the lower endpoint
converge, their limit is the least weak solution in the interval. If the
iterates from the upper endpoint converge, their limit is the greatest weak
solution there.

Convergence of the iterates is a hypothesis, since order monotonicity gives
no compactness or strong convergence in the ambient Hilbert space.
:::

:::proof "methods.semilinear.monotone_extremal_solutions"
Continuity turns each assumed iterative limit into a fixed point. The
order-interval iteration theorem compares every fixed point with every lower
or upper iterate, and closedness of the order passes those inequalities to
the limit. The fixed-point equation is then rewritten as the semilinear weak
equation.
:::

# Resolvents and Convex Regularization

:::group "methods.semilinear_convex_regularization"
Semilinear convex regularization
:::

:::definition "methods.semilinear.energy_resolvent" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.semilinearEnergyResolvent")
For $`\lambda\geq0`, a symmetric nonnegative form $`B`, and a differentiable
convex potential $`\Phi`, the semilinear-energy resolvent $`J_\lambda x` is the unique field
satisfying

$$`
\langle J_\lambda x,v\rangle+
\lambda\bigl(B(J_\lambda x,v)+D\Phi(J_\lambda x)[v]\bigr)
=\langle x,v\rangle
`

for every test vector $`v`.
:::

The resolvent equation is the weak equation of a variational problem of the
type already solved, with form $`\langle\cdot,\cdot\rangle+\lambda B` and
potential $`\lambda\Phi`; since $`B` is nonnegative, that form has coercivity
modulus at least one, so existence and uniqueness of $`J_\lambda x` follow
from the variational solution theorem. Keeping the contribution of $`B` in
the coercivity estimate also controls how $`J_\lambda` depends on $`x`.

:::theorem "methods.semilinear.resolvent_contraction" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.semilinearEnergyResolvent_norm_sub_le") (uses := "methods.semilinear.energy_resolvent")
If $`B(u,u)\geq c\lVert u\rVert^2` with $`c\geq0` and $`\lambda\geq0`, then

$$`
\lVert J_\lambda x-J_\lambda y\rVert
\leq\frac{\lVert x-y\rVert}{1+\lambda c}.
`

Positive $`c` and $`\lambda` make the resolvent a strict contraction.
:::

:::proof "methods.semilinear.resolvent_contraction"
Subtract the two resolvent equations and test with
$`J_\lambda x-J_\lambda y`. The identity term gives the squared norm,
coercivity of $`B` gives $`\lambda c` times that squared norm, and
monotonicity of $`D\Phi` gives a nonnegative contribution. Cauchy–Schwarz
bounds the right side by
$`\|x-y\|\|J_\lambda x-J_\lambda y\|`; cancellation yields the factor
$`(1+\lambda c)^{-1}`.
:::

With $`c>0` and $`\lambda>0` the factor $`(1+\lambda c)^{-1}` is below one, and
Banach's theorem applies to $`J_\lambda`. Its fixed points are the zeros of
$`u\mapsto Bu+D\Phi(u)`, the semilinear weak equation with zero load, so the
contraction estimate turns into an algorithm for solving that equation.

:::theorem "methods.semilinear.proximal_iteration" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.existsUnique_semilinearEnergyGradient_zero, PDE.Elliptic.Semilinear.exists_zero_and_tendsto_iterate_semilinearEnergyResolvent") (uses := "methods.semilinear.resolvent_contraction")
For a positive coercivity modulus and positive step size, iterating the
semilinear-energy resolvent from any initial field converges to the unique
zero of $`u\mapsto B u+D\Phi(u)`.
:::

:::proof "methods.semilinear.proximal_iteration"
With $`c>0` and $`\lambda>0`, the resolvent estimate has contraction factor
$`q=(1+\lambda c)^{-1}<1`. Banach's theorem gives a unique fixed point and
convergence of every resolvent iterate to it. Substituting $`J_\lambda u=u`
in the resolvent equation cancels the identity terms and shows
$`B(u,v)+D\Phi(u)[v]=0` for every $`v`; conversely every such zero is fixed.
:::

Dropping the form $`B` altogether leaves the resolvent of the gradient of
$`\Phi` alone. Convexity guarantees that this map is nonexpansive; a strict
contraction estimate requires additional information. From this resolvent we
obtain the Yosida approximation, a Lipschitz approximation to $`\nabla\Phi`.

:::definition "methods.semilinear.convex_gradient_resolvent" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.convexGradientResolvent, PDE.Elliptic.Semilinear.convexGradientYosidaApproximation") (uses := "methods.semilinear.variational_solution")
Let $`\Phi` be a convex functional on a real Hilbert space $`H` with Fréchet
derivative $`D\Phi(u)` at every point. For $`\lambda\geq0` and $`x\in H`,
the convex-gradient resolvent $`J_\lambda x` is the unique $`u\in H` with

$$`
\langle u,v\rangle+\lambda\,D\Phi(u)[v]=\langle x,v\rangle
\qquad(v\in H),
`

that is, $`J_\lambda x+\lambda\nabla\Phi(J_\lambda x)=x`. For $`\lambda>0`
the Yosida approximation of the gradient is

$$`
A_\lambda x=\lambda^{-1}\bigl(x-J_\lambda x\bigr).
`

Existence and uniqueness of $`J_\lambda x` come from the variational
theorem applied to the inner-product form and the potential $`\lambda\Phi`.
:::

The Yosida approximation is the gradient of $`\Phi` evaluated at the
resolvent, $`A_\lambda x=\nabla\Phi(J_\lambda x)`, since the resolvent equation
reads $`x-J_\lambda x=\lambda\nabla\Phi(J_\lambda x)`. Unlike $`\nabla\Phi`
itself it is globally Lipschitz, with a constant depending only on
$`\lambda`.

:::theorem "methods.semilinear.yosida_cocoercive" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.convexGradientYosidaApproximation_cocoercive, PDE.Elliptic.Semilinear.convexGradientYosidaApproximation_monotone, PDE.Elliptic.Semilinear.convexGradientYosidaApproximation_lipschitzWith") (uses := "methods.semilinear.convex_gradient_resolvent")
For $`\lambda>0` and a differentiable convex functional, its Yosida approximation
$`A_\lambda=\lambda^{-1}(I-J_\lambda)` is
$`\lambda`-cocoercive. In particular, the approximation is monotone and has
global Lipschitz constant $`1/\lambda`.
:::

:::proof "methods.semilinear.yosida_cocoercive"
Each Yosida value lies in the subdifferential at its resolvent point. Writing
$`A_\lambda=\lambda^{-1}(I-J_\lambda)`, monotonicity of the subdifferential at those two points
rearranges to
$`\langle A_\lambda x-A_\lambda y,x-y\rangle
\geq\lambda\|A_\lambda x-A_\lambda y\|^2`. This is
$`\lambda`-cocoercivity. Monotonicity follows at once, and Cauchy–Schwarz gives the
$`1/\lambda` Lipschitz bound.
:::

Cocoercivity is an operator-level statement about $`A_\lambda`. The resolvent
also has a variational meaning: it is the unique minimizer of $`\Phi`
penalized by the squared distance to the base point, and the minimum value of
that penalized functional defines a smoothed version of $`\Phi`.

:::definition "methods.semilinear.proximal_energy" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.convexGradientMoreauEnvelope, PDE.Elliptic.Semilinear.proximalEnergy") (uses := "methods.semilinear.convex_gradient_resolvent")
For a functional $`\Phi:H\to\mathbb R`, a parameter $`\lambda`, and a base
point $`x`, the proximal energy is

$$`
E_\lambda(x;u)=\Phi(u)+\frac{\lVert x-u\rVert^2}{2\lambda}.
`

When $`\Phi` is convex and differentiable and $`\lambda>0`, the Moreau
envelope of $`\Phi` is the proximal energy evaluated at the resolvent,

$$`
e_\lambda\Phi(x)=E_\lambda(x;J_\lambda x)
=\Phi(J_\lambda x)+\frac{\lVert x-J_\lambda x\rVert^2}{2\lambda}.
`

The Lean definition uses this evaluated form; the proximal minimization
theorem shows that it is the minimum value of
$`E_\lambda(x;\cdot)` over $`H`.
:::

The proximal energy is strongly convex because its quadratic penalty is, so it
has exactly one minimizer, and the resolvent equation is precisely its Euler
equation. The three-point inequality quantifies this: it measures how far any
competitor is from optimality in terms of its distance to $`J_\lambda x`.

:::theorem "methods.semilinear.proximal_minimizer" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.existsUnique_minimizer_proximalEnergy, PDE.Elliptic.Semilinear.convexGradientResolvent_minimizes_proximalEnergy, PDE.Elliptic.Semilinear.convexGradientResolvent_three_point_le") (uses := "methods.semilinear.proximal_energy")
Let $`\Phi` be convex on $`H` with Fréchet derivative $`D\Phi(u)` at every
$`u`, and let $`\lambda>0`. For every $`x\in H` the resolvent satisfies the
strong three-point inequality

$$`
E_\lambda(x;J_\lambda x)+\frac{\lVert u-J_\lambda x\rVert^2}{2\lambda}
\leq E_\lambda(x;u)\qquad(u\in H).
`

Consequently $`J_\lambda x` minimizes $`E_\lambda(x;\cdot)`, and the
proximal energy has exactly one global minimizer:

$$`
\exists!\,u\in H,\qquad E_\lambda(x;u)\leq E_\lambda(x;v)\quad(v\in H).
`
:::

:::proof "methods.semilinear.proximal_minimizer"
Write $`J=J_\lambda x`. Convexity gives the supporting-hyperplane bound
$`D\Phi(J)[u-J]\leq\Phi(u)-\Phi(J)`, while the resolvent equation tested
with $`u-J` identifies $`\langle x-J,u-J\rangle` with
$`\lambda\,D\Phi(J)[u-J]`. Expanding
$`\lVert x-u\rVert^2=\lVert x-J\rVert^2-2\langle x-J,u-J\rangle+\lVert u-J\rVert^2`
and inserting these two facts yields the three-point inequality. Dropping
its nonnegative middle term shows that $`J` is a minimizer. If $`u` is any
minimizer, comparing with $`J` in the three-point inequality forces
$`\lVert u-J\rVert^2/(2\lambda)\leq0`, hence $`u=J`.
:::

Evaluating the proximal energy at its minimizer gives the Moreau envelope. Its
dependence on the base point ties the two halves of this section together:
the gradient of the envelope is the Yosida approximation, so $`e_\lambda\Phi`
is differentiable with a $`\lambda^{-1}`-Lipschitz gradient even when
$`\nabla\Phi` is not Lipschitz, and the price of this regularity, the gap
$`\Phi(x)-e_\lambda\Phi(x)\geq0`, disappears as $`\lambda\downarrow0`.

:::theorem "methods.semilinear.moreau_envelope" (parent := "methods.semilinear_convex_regularization") (lean := "PDE.Elliptic.Semilinear.hasGradientAt_convexGradientMoreauEnvelope, PDE.Elliptic.Semilinear.tendsto_convexGradientMoreauEnvelope") (uses := "methods.semilinear.proximal_energy, methods.semilinear.yosida_cocoercive")
For $`\lambda>0`, the Moreau envelope is differentiable with gradient equal to the Yosida
approximation,

$$`
\nabla e_\lambda\Phi(x)=A_\lambda x
=\lambda^{-1}(x-J_\lambda x),
`

and it converges pointwise to the original functional:

$$`
e_\lambda\Phi(x)\longrightarrow\Phi(x)
\qquad(\lambda\downarrow0).
`
:::

:::proof "methods.semilinear.moreau_envelope"
Compare the envelope at $`x` and $`y` using $`J_\lambda y` and
$`J_\lambda x` as opposite competitors. Expanding the quadratic penalties
and using monotonicity bounds the first-order remainder by
$`\|y-x\|^2/(2\lambda)`. Dividing by $`\|y-x\|` proves differentiability
with gradient $`A_\lambda x`, without differentiating the minimizing map.
For convergence, choosing
$`x` as a competitor gives $`e_\lambda\Phi(x)\leq\Phi(x)`, while convexity
gives the quantitative reverse bound
$`\Phi(x)\leq e_\lambda\Phi(x)+\frac{\lambda}{2}\|\nabla\Phi(x)\|^2`.
The two bounds squeeze the envelope to $`\Phi(x)` as $`\lambda\downarrow0`.
:::

For a scalar example, take $`\Phi(u)=au^2/2` with $`a>0`. The resolvent
equation $`u+\lambda au=x` gives

$$`
J_\lambda x=\frac{x}{1+\lambda a},\qquad
A_\lambda x=\frac{ax}{1+\lambda a},\qquad
e_\lambda\Phi(x)=\frac{a x^2}{2(1+\lambda a)}.
`

The quadratic penalty discourages moving far from $`x`, while the original
energy pulls toward zero. The resolvent is their exact compromise. The
envelope has smaller curvature $`a/(1+\lambda a)`, and that curvature
returns to $`a` as $`\lambda` tends to zero.

These resolvents are built from smooth convex gradients. For a proper
lower-semicontinuous convex energy the subdifferential is multivalued, and its
nonlinear contraction semiflow is constructed in
{bpref "evolution.semigroup.subgradient_closure"}[].
