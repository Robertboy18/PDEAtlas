/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.DirichletHeat
import PDE.Parabolic.Heat.Variational.DivergenceForm
import PDE.Parabolic.Evolution.Semigroup.DivergenceForm
import PDE.Parabolic.Evolution.Semigroup.ClassicalDomain
import PDE.Parabolic.Semilinear.ReactionDiffusion

/-!
# Time-dependent divergence form

Time-dependent divergence-form operators and their solution theory, the
autonomous divergence-form semigroup, and globally Lipschitz
reaction–diffusion systems.
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
#doc (Manual) "Time-Dependent Divergence Form" =>

Variable-coefficient heat equations are most naturally expressed through
their spatial bilinear forms. At almost every time, the form pairs a trial
state in $`H_0^1(\Omega)` with a test state in the same space and returns the
dual action of the elliptic operator. Time dependence is then handled through
strong measurability and uniform operator bounds rather than pointwise
classical derivatives of the coefficients.

Lower-order terms generally destroy strict coercivity. The correct estimate
is a Gårding inequality: coercivity is recovered after adding a multiple of
the $`L^2` norm. With the shift kept in the statements, the abstract
nonautonomous evolution theory gives the weak equation, a continuous $`L^2`
representative, an energy inequality, and uniqueness.

:::definition "parabolic.divergence_form" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.DivergenceForm.form, HeatEquation.Variational.DivergenceForm.form_apply")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "371-375"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

The nonautonomous form is an operator-valued extension of

$$`u_t-\partial_i(a^{ij}(t)\partial_j u)+b^i(t)\partial_i u+c(t)u=f`

through the principal, first-order, and zeroth-order terms

$$`B(t;u,v)=\sum_{i,j}(A_{ij}(t)D_j u,D_i v)_{L^2}+\sum_i(b_i(t)D_i u,v)_{L^2}+(c(t)u,v)_{L^2}.`

The coefficient data are bounded operators on the spatial $`L^2` space.
Pointwise $`L^\infty` coefficients give multiplication operators, and nonlocal
bounded coefficient operators are allowed as well.
:::

Because the form is an operator-valued function of time with values in
$`\mathcal L(H_0^1(\Omega),H^{-1}(\Omega))`, it can be inserted directly
into the abstract nonautonomous evolution identity. The weak solution for
the full equation is therefore the same integrated Gelfand-triple notion
used for the Dirichlet heat equation, with $`B(t)` in place of the Dirichlet
form.

:::definition "parabolic.divergence_weak_solution" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.DivergenceForm.IsWeakSolution") (uses := "parabolic.integrated_weak_solution, parabolic.divergence_form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "373-375"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

The time-dependent divergence-form weak solution is the same integrated
Gelfand-triple notion, specialized to the form $`B(t)`. For $`a<b`, the
state $`u` is a Bochner $`L^2(a,b;H_0^1(\Omega))` class, the tested form and
forcing terms are integrable, and the initial datum enters through the
boundary term in time integration by parts.

Under the form-measurability and boundedness hypotheses of
{bpref "parabolic.divergence_existence_energy"}[], this class has a continuous
$`L^2` representative $`U`. For
$`t\in[a,b]`, it satisfies

$$`
  (U(t),v)_H-(u_0,v)_H
  +\int_a^t B(s;u(s),v)\,ds
  =\int_a^t\ell(s)(v)\,ds
  \qquad(v\in H_0^1(\Omega)).
`

The integrals use the energy-space Bochner representative $`u`; the endpoint
value $`U(t)` belongs to the continuous pivot representative. The
Dirichlet and divergence-form problems share this one weak-solution
predicate.
:::

Lower-order terms can prevent the energy identity from closing as it did for
the Dirichlet form: the general estimate leaves a term
$`\gamma\int\lVert u\rVert_{L^2}^2` that need not be absorbable by the
unshifted coercive part. The endpoint estimate is therefore a
Gårding-type inequality with two constants, the coercivity fraction
$`\theta` and the mass shift $`\gamma`, instead of the single constant of
the Dirichlet case.

The shift has a concrete meaning in time. In pivot-space notation, set
$`w(t)=e^{-\gamma(t-a)}u(t)` in $`u_t+A(t)u=f`. The product rule gives

$$`
w_t+(A(t)+\gamma I)w=e^{-\gamma(t-a)}f,
\qquad w(a)=u(a).
`

The added mass term is the coercive shift of the spatial form. Solving this
equation and multiplying back by $`e^{\gamma(t-a)}` recovers the original
problem and its initial datum. For $`\gamma\ge0`, undoing the shift costs at
most $`e^{\gamma(b-a)}` on the finite interval; it need not preserve decay.
The {bpref "parabolic.measurable_garding_existence"}[measurable-form theorem]
carries out this change of variables in the integrated weak formulation.

:::definition "parabolic.divergence_garding_energy" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.DivergenceForm.HasGardingEnergyEstimate") (uses := "parabolic.divergence_weak_solution, parabolic.lions_magenes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "376-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The endpoint estimate consists of the weak $`H^{-1}` time derivative, continuous
$`L^2` representative, initial trace, residual equation, and Gårding energy
inequality

$$`\frac12\lVert u(t)\rVert_{L^2}^2+
\frac\theta2\int_a^t\lVert u\rVert_{H_0^1}^2
\le \frac12\lVert u_0\rVert_{L^2}^2+
\frac1{2\theta}\int_a^t\lVert f\rVert_{H^{-1}}^2+
\gamma\int_a^t\lVert u\rVert_{L^2}^2.`

The last term is left for Grönwall, since the unshifted form need not be
coercive.
:::

Uniform ellipticity of the principal part and uniform bounds on the
lower-order coefficients determine both constants explicitly: the theorem
returns $`\theta=\alpha/2` and a shift computed from the ellipticity
constant and the lower-order bounds.

:::theorem "parabolic.divergence_existence_energy" (parent := "parabolic.variational") (lean := "HeatEquation.Variational.DivergenceForm.existsUnique_weakSolution_with_energy") (uses := "parabolic.divergence_weak_solution, parabolic.divergence_garding_energy, parabolic.galerkin.h10_l2_trial_system, parabolic.integrated_garding_uniqueness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "373-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

On a finite interval $`a<b` and a bounded open set $`\Omega`, assume uniform
ellipticity of the principal part and uniform bounds on the lower-order
terms throughout $`[a,b]`. Assume the induced form is a.e. strongly measurable
as a map into $`\mathcal L(H_0^1(\Omega),H^{-1}(\Omega))` with its operator
norm, and uniformly bounded in that norm on $`[a,b]`. Then every
$`L^2(a,b;H^{-1}(\Omega))` forcing and $`L^2(\Omega)` initial datum have a
unique weak solution.

The result includes a continuous $`L^2` representative, weak time derivative,
the variational residual equation, and the Gårding energy inequality with
its lower-order mass term.
:::

:::proof "parabolic.divergence_existence_energy" (uses := "parabolic.galerkin_existence, parabolic.galerkin.h10_l2_trial_system, parabolic.integrated_garding_uniqueness, parabolic.lions_magenes")
Shift the Gårding form by its lower-order mass constant, apply the abstract
nonautonomous Galerkin theorem, undo the exponential shift, and use
Lions–Magenes for the continuous pivot representative and endpoint control.
:::

When the coefficients do not depend on time, the same equation also
generates a semigroup. The Gårding shift $`\gamma` that restores coercivity
reappears as an exponential growth rate: the semigroup of the full operator
is $`e^{\gamma t}` times the contraction semigroup of the shifted one.

:::theorem "parabolic.divergence_semigroup" (parent := "parabolic.variational") (lean := "HeatEquation.Semigroup.Divergence.norm_semigroup_le, HeatEquation.Semigroup.Divergence.semigroup, HeatEquation.Semigroup.Divergence.generatorPMap_semigroup, HeatEquation.Semigroup.Divergence.hasGeneratorAt_semigroup_iff, HeatEquation.Semigroup.Divergence.garding_bound, HeatEquation.Semigroup.Divergence.coerciveShift_nonneg") (uses := "parabolic.dirichlet_semigroup_generator, elliptic.divergence.coercive_shift")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open, let $`a^{ij},b^i,c\in L^\infty(\Omega)`,
and let $`(a^{ij})` be uniformly elliptic with constant $`\alpha>0`. Write
$`Lu=-\sum_{i,j}D_j(a^{ij}D_iu)+\sum_ib^iD_iu+cu` with its Dirichlet form
$`B`. With the explicit Gårding shift $`\gamma\geq0` computed from $`\alpha`,
$`\sum_i\|b^i\|_\infty` and $`\|c\|_\infty`, the form satisfies
$`\frac\alpha2\|u\|_{H_0^1}^2\leq B(u,u)+\gamma\|u\|_{L^2}^2`, and there is a
strongly continuous semigroup $`S(t)` on $`L^2(\Omega)` with

$$`\|S(t)\|\leq e^{\gamma t}\qquad(t\geq0).`

Its generator is $`-L` with the weak Dirichlet domain: $`S` has generator
value $`f` at $`x` exactly when $`x` is the class of some $`u\in H_0^1(\Omega)`
with $`B(u,v)=-\int_\Omega fv` for all $`v\in H_0^1(\Omega)`.
:::

:::proof "parabolic.divergence_semigroup" (uses := "parabolic.dirichlet_semigroup_generator")
The Gårding inequality makes $`B+\gamma(\cdot,\cdot)_{L^2}` coercive on
$`H_0^1(\Omega)`, so the form construction behind
{bpref "parabolic.dirichlet_semigroup_generator"}[] gives a contraction
semigroup $`S_\gamma` generated by $`-(L+\gamma)`. Then
$`S(t)=e^{\gamma t}S_\gamma(t)` has generator $`-L`, with the same domain.
The first-order term makes $`B` nonsymmetric, which the Hille–Yosida
argument does not need: coercivity alone bounds the resolvents.
:::

:::theorem "parabolic.divergence_semigroup_h2_domain" (parent := "parabolic.variational") (lean := "HeatEquation.Semigroup.Divergence.exists_semigroup_h2_generator") (uses := "parabolic.divergence_semigroup")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be bounded and open with a $`C^2` graph boundary, $`n\geq1`.
Let $`a^{ij}` be $`C^1` up to the boundary with
$`\sum a^{ij}(x)\xi_i\xi_j\geq\alpha|\xi|^2` for $`x\in\Omega`, and let
$`b^i`, $`c` be continuous up to the boundary. Then the semigroup of
{bpref "parabolic.divergence_semigroup"}[] for these coefficients satisfies
$`\|S(t)\|\leq e^{\gamma t}`, its generator domain is exactly
$`H^2(\Omega)\cap H_0^1(\Omega)`, and on that domain the generator acts as
$`-L` computed with strong second derivatives.
:::

:::proof "parabolic.divergence_semigroup_h2_domain" (uses := "parabolic.divergence_semigroup")
One inclusion is elliptic boundary regularity: if $`u\in H_0^1` solves
$`Lu=f` weakly with $`f\in L^2`, then $`u\in H^2`. For the other, an
$`H^2\cap H_0^1` function can be integrated by parts against every
$`v\in H_0^1` using the weak Leibniz rule for $`a^{ij}D_iu`, which identifies
its form with the pairing against the strong expression $`Lu`. The
coefficient classes in $`L^\infty` and $`W^{1,\infty}` are computed from the
given functions, so no extension of the coefficients is assumed.
:::

The same Galerkin machinery also handles a nonlinear reaction term, as long
as the reaction is globally Lipschitz. Evans treats this system in §9.2.1 of
{Informal.citet "evans-2010"}[].

:::theorem "parabolic.reaction_diffusion" (parent := "parabolic.variational") (lean := "ReactionDiffusion.existsUnique_weakSolution, ReactionDiffusion.existsUnique_integrated, ReactionDiffusion.exists_evolution, ReactionDiffusion.weakSolution_unique") (uses := "parabolic.galerkin_existence, parabolic.lions_magenes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.2.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be bounded and open, $`a<b`, $`m\geq0`, and
let $`f:\mathbb R^m\to\mathbb R^m` be globally Lipschitz. For every
$`g\in L^2(\Omega;\mathbb R^m)` the system $`u_t-\Delta u=f(u)` with zero
boundary values has a unique weak solution
$`u\in L^2(a,b;H_0^1(\Omega;\mathbb R^m))`: it has a weak time derivative
$`u_t\in L^2(a,b;H^{-1})`, a representative continuous from $`[a,b]` into
$`L^2` with value $`g` at $`t=a`, and for almost every $`t`

$$`\langle u_t,v\rangle+\int_\Omega\nabla u:\nabla v\,dx
=\int_\Omega f(u)\cdot v\,dx\qquad\text{for all }v\in H_0^1(\Omega;\mathbb R^m).`

Two such solutions with the same initial value have the same class, the same
derivative, and equal continuous representatives on $`[a,b]`. For
$`g\in H_0^1(\Omega;\mathbb R^m)` the same conclusions hold with initial value
$`g`.
:::

:::proof "parabolic.reaction_diffusion" (uses := "parabolic.galerkin_existence, parabolic.lions_magenes")
The abstract theorem,
the Lipschitz-reaction existence theorem,
applies to any Gårding form on a Gelfand triple. Given a trajectory
$`w`, solve the linear problem with forcing $`f(w)` by the Galerkin theorem.
This defines a map $`w\mapsto u` whose fixed points are the solutions. Replace
the unknown by $`e^{-\eta(t-a)}u`: the rescaled reaction has the same
Lipschitz constant, because the exponential factors cancel in its difference
estimate, while the linear part gains the coercive term $`\eta\|u\|^2`. For
$`\eta` large the map is a contraction on the whole interval
$`[a,b]`, and the Banach fixed point theorem gives existence and uniqueness
in the integrated formulation. The Gelfand evolution theorem then supplies
the derivative in $`L^2(a,b;H^{-1})` and the continuous representative.

The exponential weight makes the contraction global on $`[a,b]`, with no
restarting. The value $`f(0)` may be nonzero, since a constant offset is square
integrable on a finite interval, and no boundary regularity of $`\Omega` is
used.
:::
