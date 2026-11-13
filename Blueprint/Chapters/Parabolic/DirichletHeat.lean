/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution
import PDE.Parabolic.Heat.Variational.Dirichlet
import PDE.Parabolic.Evolution.Semigroup.DirichletGenerator
import PDE.Parabolic.Evolution.Semigroup.Dirichlet

/-!
# Dirichlet heat equation

Weak and strong formulations of the Dirichlet heat problem, and the
`L²` Dirichlet heat semigroup.
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
#doc (Manual) "The Dirichlet Heat Equation" =>

Evans's homogeneous-Dirichlet heat problem is the first concrete application
of the abstract evolution theory.

:::definition "parabolic.dirichlet_form" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.Dirichlet.form, HeatEquation.Variational.Dirichlet.form_apply")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "373-375"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For an open set $`\Omega`, we specialize the Gelfand triple to

$$`H_0^1(\Omega)\hookrightarrow L^2(\Omega)\hookrightarrow H^{-1}(\Omega)`

and use the Dirichlet form

$$`B(u,v)=\sum_{i=1}^n\int_\Omega D_i u\,D_i v.`

Thus the abstract evolution equation is exactly the variational form of
$`u_t-\Delta u=\ell` with homogeneous Dirichlet boundary data.
:::

Once the form is fixed, no new solution concept is needed: the integrated
Gelfand-triple identity of the weak-evolution chapter, evaluated with $`B`
on the triple $`H_0^1\hookrightarrow L^2\hookrightarrow H^{-1}`, is the
Dirichlet weak solution. Homogeneous boundary values are carried by the
choice of $`H_0^1(\Omega)` as the energy space, not by a separate boundary
clause.

:::definition "parabolic.dirichlet_weak_solution" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.Dirichlet.IsWeakSolution") (uses := "parabolic.dirichlet_form, parabolic.integrated_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "373-375"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The weak solution is an $`L^2(a,b;H_0^1(\Omega))` Bochner class satisfying
the integrated time-tested identity with forcing in
$`L^2(a,b;H^{-1}(\Omega))` and initial datum in $`L^2(\Omega)`. The definition
is the direct specialization of the strengthened integrated-solution
structure, including a nonempty interval and integrability of every tested
term; no pointwise representative of the forcing is chosen.
:::

The weak-solution predicate asks only for the integrated identity. Time
regularity of $`u`, a continuous representative that can be evaluated at the
initial time, and the energy inequality are additional conclusions, and they
are bundled into a separate predicate so that the existence theorem can
assert them without enlarging the definition of a solution.

:::definition "parabolic.dirichlet_energy_estimate" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.Dirichlet.HasEnergyEstimate") (uses := "parabolic.dirichlet_weak_solution, parabolic.lions_magenes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "376-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The energy predicate records a weak time derivative in
$`L^2(a,b;H^{-1}(\Omega))`, a continuous $`L^2(\Omega)` representative with
the prescribed initial value, the almost-everywhere residual identity
$`u_t=\ell+\Delta u`, and the coercive integral estimate on every prefix.
:::

Boundedness of $`\Omega` enters the existence theorem through the Poincaré
inequality, which makes the Dirichlet form coercive on $`H_0^1(\Omega)` and
supplies the constant $`C` of the energy estimate; the compact embedding
into $`L^2(\Omega)` provides the spectral trial spaces for the Galerkin
construction.

:::theorem "parabolic.dirichlet_existence_energy" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.Dirichlet.existsUnique_weakSolution_with_energy") (uses := "parabolic.dirichlet_weak_solution, parabolic.dirichlet_energy_estimate, parabolic.galerkin.h10_l2_trial_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "375-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`a<b` be finite real endpoints and let $`\Omega\subseteq\mathbb R^n`
be bounded and open, with $`n>0`. Every
$`\ell\in L^2(a,b;H^{-1}(\Omega))` and $`u_0\in L^2(\Omega)` determine a
unique weak solution $`u\in L^2(a,b;H_0^1(\Omega))`.

The conclusion also supplies $`u_t\in L^2(a,b;H^{-1}(\Omega))`, a
representative in $`C([a,b];L^2(\Omega))` with value $`u_0` at the initial
time, the residual identity $`u_t=\ell+\Delta u`, and the coercive energy
estimate on every time prefix.
:::

:::proof "parabolic.dirichlet_existence_energy" (uses := "parabolic.galerkin_existence, parabolic.galerkin.h10_l2_trial_system, parabolic.lions_magenes")
Apply the abstract Galerkin theorem to the Dirichlet form.  Poincaré
coercivity gives the uniform energy bound, while Lions–Magenes supplies the
continuous $`L^2` representative and the initial trace.
:::

The Galerkin weak solution is built for each datum separately. A second
construction produces all solutions at once as a family
of bounded operators $`S(t)` on $`L^2(\Omega)`, with $`S(t)g` the solution at
time $`t` with initial value $`g`. The operator $`S(t)` is the abstract form
of the separated solutions of {bpref "methods.separation.heat.interval"}[]:
on $`(0,\pi)`, $`\sin kx` is an eigenfunction of the Dirichlet Laplacian
with eigenvalue $`-k^2`, and $`S(t)` multiplies it by $`e^{-k^2t}`. The resolvent construction works on a
general open set without requiring an explicit eigenbasis. The framework is §7.4 of
{Informal.citet "evans-2010"}[].

:::definition "parabolic.dirichlet_laplacian_generator" (parent := "parabolic.variational") (lean := "HeatEquation.Semigroup.Dirichlet.generator, HeatEquation.Semigroup.Dirichlet.mem_generator_graph_iff, HeatEquation.Semigroup.Dirichlet.dense_generator_domain, HeatEquation.Semigroup.Dirichlet.hasContractionResolvent_generator, HeatEquation.Semigroup.Dirichlet.resolvent_generator_eq_modifiedHelmholtzSolve") (uses := "parabolic.dirichlet_form, elliptic.modified_helmholtz.solver")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open. The weak Dirichlet Laplacian $`A`
is the partially defined operator on $`L^2(\Omega)` with $`Ax=f` exactly when
$`x` is the class of some $`u\in H_0^1(\Omega)` with $`\Delta u=f` weakly,
that is, $`\sum_i\int_\Omega D_iu\,D_iv=-\int_\Omega fv` for every
$`v\in H_0^1(\Omega)`. Its domain is dense in $`L^2(\Omega)`. For every
$`\lambda>0` the operator $`\lambda-A` is onto, with inverse
$`(\lambda-A)^{-1}f` given by the weak solution of the modified Helmholtz
problem $`\lambda u-\Delta u=f` in $`H_0^1(\Omega)`, and

$$`\|(\lambda-A)^{-1}f\|_{L^2}\leq\frac1\lambda\|f\|_{L^2}.`
:::

The domain of $`A` consists of the functions of $`H_0^1(\Omega)` whose
distributional Laplacian lies in $`L^2(\Omega)`. On a smooth bounded domain
that is $`H^2\cap H_0^1`, by elliptic regularity, but the definition itself
needs neither boundedness nor boundary regularity.

:::definition "parabolic.dirichlet_semigroup" (parent := "parabolic.variational") (lean := "HeatEquation.Semigroup.Dirichlet.semigroup, HeatEquation.Semigroup.Dirichlet.semigroup_isContraction, HeatEquation.Semigroup.Dirichlet.tendsto_semigroup_initial") (uses := "parabolic.dirichlet_laplacian_generator, evolution.semigroup.contraction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Dirichlet heat semigroup on an open set $`\Omega` is the strongly
continuous semigroup $`(S(t))_{t\geq0}` on $`L^2(\Omega)` produced by the
Hille–Yosida theorem from the resolvents of
{bpref "parabolic.dirichlet_laplacian_generator"}[]. Each $`S(t)` is a
contraction, $`\|S(t)g\|_{L^2}\leq\|g\|_{L^2}`, and
$`S(t)h\to g` in $`L^2(\Omega)` as $`(t,h)\to(0,g)`: every $`L^2` datum is
attained, continuously in the datum.
:::

:::theorem "parabolic.dirichlet_semigroup_generator" (parent := "parabolic.variational") (lean := "HeatEquation.Semigroup.Dirichlet.generatorPMap_semigroup, HeatEquation.Semigroup.Dirichlet.mem_semigroup_generator_domain_iff, HeatEquation.Semigroup.Dirichlet.isClosed_generator") (uses := "parabolic.dirichlet_semigroup, evolution.semigroup.generator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The generator of the Dirichlet heat semigroup is exactly the weak Dirichlet
Laplacian $`A`, with equal domains. In particular $`A` is closed, and $`g`
lies in the generator domain if and only if $`g` is the class of some
$`u\in H_0^1(\Omega)` whose distributional Laplacian lies in $`L^2(\Omega)`.
:::

:::proof "parabolic.dirichlet_semigroup_generator" (uses := "parabolic.dirichlet_laplacian_generator, parabolic.dirichlet_semigroup")
The resolvent bound comes from testing the modified Helmholtz equation with
its own solution: $`\lambda\|u\|^2+\|\nabla u\|^2=\int_\Omega fu\leq\|f\|\,\|u\|`,
so $`\lambda\|u\|\leq\|f\|`. A densely defined operator all of whose positive
shifts are onto with inverse norm at most $`1/\lambda` generates a contraction
semigroup, and the generator of the semigroup that the Hille–Yosida
construction returns is the operator it started from, not an extension of it.
The construction is carried out once for any coercive form on a Gelfand
triple, and the Dirichlet case applies it to the form $`B(u,v)` shifted by
the pivot inner product, which is coercive on $`H_0^1(\Omega)` with no
Poincaré inequality. This is why no boundedness of $`\Omega` is needed, in
contrast with {bpref "parabolic.dirichlet_existence_energy"}[].
:::

:::theorem "parabolic.dirichlet_semigroup_trajectory" (parent := "parabolic.variational") (lean := "HeatEquation.Semigroup.Dirichlet.solution_weak_heat_equation, HeatEquation.Semigroup.Dirichlet.solution, HeatEquation.Semigroup.Dirichlet.baseCoordCLM_solution, HeatEquation.Semigroup.Dirichlet.continuous_solution, HeatEquation.Semigroup.Dirichlet.solution_initial, HeatEquation.Semigroup.Dirichlet.hasDerivAt_solution, HeatEquation.Semigroup.Dirichlet.semigroup_mem_domain, HeatEquation.Semigroup.Dirichlet.contDiffOn_semigroup, HeatEquation.Semigroup.Dirichlet.solution_isWeakPoissonSolution") (uses := "parabolic.dirichlet_semigroup_generator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`g` lie in the domain of the weak Dirichlet Laplacian. Then $`S(t)g`
stays in that domain, and the orbit is continuously differentiable in
$`L^2(\Omega)` for $`t>0`. It has a representative $`u:\mathbb R\to H_0^1(\Omega)`
that is continuous in the $`H_0^1` norm, equals the $`H_0^1` function of $`g`
at $`t=0`, and has $`L^2` class $`S(t)g`. For every $`t>0` its strong
$`L^2` derivative is $`S(t)Ag`, and

$$`\int_\Omega u_t\,v\,dx+\sum_{i=1}^n\int_\Omega D_iu\,D_iv\,dx=0
\qquad\text{for all }v\in H_0^1(\Omega).`

In particular $`\Delta u(t)=u_t(t)` holds distributionally.
:::

:::proof "parabolic.dirichlet_semigroup_trajectory" (uses := "parabolic.dirichlet_semigroup_generator")
On the generator domain the orbit is differentiable with derivative
$`AS(t)g=S(t)Ag`, and it stays in the domain. Membership in the domain
provides the $`H_0^1` function $`u(t)` with $`\Delta u(t)=AS(t)g`, which is
the weak equation after substituting the derivative. For continuity in
$`H_0^1`, the Dirichlet energy of a difference is a pivot pairing:
$`\|\nabla(u(t)-u(s))\|^2=-\int_\Omega(Au(t)-Au(s))(u(t)-u(s))`, and both
factors are continuous in $`L^2`.
:::

The semigroup and the Galerkin solution answer different questions. The
Galerkin theorem accepts a forcing in $`L^2(a,b;H^{-1}(\Omega))` on a
bounded domain and returns a Bochner-class solution with an energy estimate.
The semigroup has no forcing term, but it works on any open set and gives the
solution as a continuous function of time and datum together. For data in
the generator domain it gives a strong $`L^2` time derivative rather than a
derivative in $`H^{-1}`.
