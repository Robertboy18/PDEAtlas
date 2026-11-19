/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.SymmetricSystems
import PDE.Analysis.Evolution.Semigroup.Basic
import PDE.Analysis.Evolution.Semigroup.Generator
import PDE.Analysis.Evolution.Semigroup.LaplaceTransform
import PDE.Analysis.Evolution.Semigroup.Yosida
import PDE.Analysis.Evolution.GradientFlow.Existence.Domain
import PDE.Analysis.Evolution.GradientFlow.Semigroup.Closure

/-!
# Evolution semigroups

Strongly continuous semigroups, their generators, Yosida averages, and the
Laplace-transform resolvent.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso requires every directive header on one physical line, while blank
-- lines delimit Markdown paragraphs and display blocks inside `#doc`.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Strongly Continuous Semigroups" =>

:::group "evolution.semigroups"
Strongly continuous semigroups
:::

For the homogeneous wave equation $`u_{tt}+Au=0`, set
$`U(t)=(u(t),u_t(t))` in the energy space $`H^1_0\times L^2` and formally
write $`U_t=\mathcal GU` with $`\mathcal G(u,v)=(v,-Au)`. When
$`\mathcal G` generates a strongly continuous group, its positive-time
restriction is a semigroup and $`T(t)U(0)` is the wave evolution. The
generator domain records the additional regularity needed to interpret
$`\mathcal GU`.

:::definition "evolution.semigroup.strongly_continuous" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A strongly continuous semigroup consists of bounded linear evolution
operators $`T(t)` for nonnegative time, with $`T(0)=I`,
$`T(s+t)=T(s)T(t)`, and a continuous orbit $`t\mapsto T(t)x` for every
vector $`x`. This definition requires only a real normed space; completeness
enters when the orbits are integrated.
:::

Strong continuity gives a uniform operator-norm bound on each compact time
interval when the space is Banach, by the uniform boundedness principle.
Contractivity is a stronger bound, uniform in time. The Laplace transform uses
it; the generator theory does not.

:::definition "evolution.semigroup.contraction" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsContraction, PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsContraction.lipschitzWith_one, PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsContraction.antitone_norm_orbit, PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsContraction.antitone_dist_orbit") (uses := "evolution.semigroup.strongly_continuous")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A contraction semigroup satisfies $`\lVert T(t)\rVert\leq1` for every
nonnegative time. Consequently each evolution map is nonexpansive, and the
norm of an orbit and the distance between two orbits are nonincreasing in
time.
:::

The generator is defined at those $`x` for which the one-sided derivative of
$`t\mapsto T(t)x` exists at $`0`. The domain can be all of $`X`: the identity
semigroup, for example, has generator zero.

:::definition "evolution.semigroup.generator" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.HasGeneratorAt, PDE.Analysis.Evolution.StronglyContinuousSemigroup.generatorPMap") (uses := "evolution.semigroup.strongly_continuous")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The infinitesimal generator is the strong derivative at zero within
$`[0,\infty)`. Its natural domain and values form Mathlib's partial linear
map $`A\colon X\to_{\mathrm{lin}}X`; uniqueness of one-sided derivatives
makes the value $`Ax` well-defined.
:::

:::theorem "evolution.semigroup.generator_invariance" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.map_mem_generatorPMap_domain") (uses := "evolution.semigroup.generator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435-436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every semigroup operator preserves the generator domain:

$$`
x\in D(A)\Longrightarrow T(t)x\in D(A)
\qquad(t\geq0).
`

This holds for every strongly continuous semigroup, with neither
contractivity nor completeness.
:::

:::proof "evolution.semigroup.generator_invariance"
If $`Ax` is the strong derivative of $`T(h)x` at zero, the semigroup law
rewrites the difference quotient at $`T(t)x` as $`T(t)` applied to the
difference quotient at $`x`. Continuity and linearity of $`T(t)` pass the
limit through, giving generator value $`T(t)Ax` and hence
$`T(t)x\in D(A)`.
:::

Invariance of $`D(A)` means the operators $`T(t)` can be restricted to it.

:::definition "evolution.semigroup.generator_domain_semigroup" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.generatorDomainSemigroup") (uses := "evolution.semigroup.generator_invariance")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435-436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The restrictions $`T(t)|_{D(A)}` themselves form a strongly continuous
semigroup on $`D(A)` with its inherited norm.
:::

The identity $`A(T(t)x)=T(t)(Ax)` says that $`A` intertwines the restricted
semigroup on $`D(A)` with the original one. It is the abstract form of the
statement that, for an autonomous equation, time translation commutes with the
spatial operator.

:::theorem "evolution.semigroup.generator_commutes" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.generatorPMap_generatorDomainMap") (uses := "evolution.semigroup.generator_invariance")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435-436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`x` in the generator domain,

$$`A(T(t)x)=T(t)(Ax).`

As with invariance, neither contractivity nor completeness is needed.
:::

:::proof "evolution.semigroup.generator_commutes" (uses := "evolution.semigroup.generator_invariance")
The difference quotient at $`T(t)x` is, by the semigroup law, $`T(t)`
applied to the difference quotient at $`x`. Passing to the strong limit
through the bounded linear operator $`T(t)` gives
$`A(T(t)x)=T(t)Ax`.
:::

Commutation gives a right derivative at every nonnegative time, and on a
Banach space integration upgrades it to an ordinary derivative at positive
times.

:::theorem "evolution.semigroup.orbit_derivative" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.hasDerivWithinAt_realOrbit_generatorPMap, PDE.Analysis.Evolution.StronglyContinuousSemigroup.hasDerivAt_realOrbit_generatorPMap, PDE.Analysis.Evolution.StronglyContinuousSemigroup.contDiffOn_realOrbit_generatorPMap") (uses := "evolution.semigroup.generator_commutes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "435-436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every orbit starting in the generator domain solves the abstract homogeneous
Cauchy problem. At time zero the derivative is taken within $`[0,\infty)`.
This one-sided statement holds on a normed space. If the ambient space is
Banach, then at every positive real time the orbit has the ordinary two-sided
derivative $`T(t)(Ax)`, and the resulting orbit is $`C^1` on
$`(0,\infty)`.
:::

:::proof "evolution.semigroup.orbit_derivative" (uses := "evolution.semigroup.generator_commutes")
At zero the generator definition gives the right derivative. The semigroup
law transports it to every nonnegative time, and strong continuity makes
$`s\mapsto T(s)Ax` continuous. On a Banach space, the fundamental theorem for
right derivatives gives $`T(s)x=x+\int_0^sT(r)Ax\,dr`. Near a positive time,
the orbit therefore agrees with a differentiable Bochner primitive. Its
ordinary derivative is $`T(t)Ax`, continuous in $`t` by strong continuity.
:::

The $`C^1` claim also requires the derivative $`t\mapsto T(t)Ax` to be
continuous, and this holds without completeness.

:::theorem "evolution.semigroup.generator_orbit_continuous" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.continuous_generatorPMap_orbit") (uses := "evolution.semigroup.generator_commutes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`x\in D(A)`, the map $`t\mapsto A(T(t)x)=T(t)(Ax)` is continuous.
:::

:::proof "evolution.semigroup.generator_orbit_continuous" (uses := "evolution.semigroup.generator_commutes")
Generator commutation rewrites the map as the ordinary semigroup orbit of
$`Ax`. Strong continuity of the semigroup then gives continuity directly.
:::

How large is $`D(A)`? For a general unbounded operator the domain could be
small, but the averages $`\varepsilon^{-1}\int_0^\varepsilon T(s)x\,ds` always
belong to it. Since the averages converge to $`x`, the domain is dense; the
Bochner integral is where completeness of $`X` enters.

:::theorem "evolution.semigroup.dense_generator_domain" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.dense_generatorPMap_domain_of_complete") (uses := "evolution.semigroup.generator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436-437"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every strongly continuous semigroup on a Banach space,

$$`
\overline{D(A)}=X.
`

No contractivity bound is needed.
:::

:::proof "evolution.semigroup.dense_generator_domain"
Average the orbit over $`[0,\varepsilon]` and divide by $`\varepsilon`.
The semigroup law computes the generator of this average from its endpoint
difference, so each average lies in $`D(A)`. Strong continuity at zero makes
the averages converge to the original vector, proving density.
:::

Density is complemented by closedness: even though $`A` need not be bounded,
its graph is closed.

:::theorem "evolution.semigroup.closed_generator" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.isClosed_generatorPMap") (uses := "evolution.semigroup.generator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436-437"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every strongly continuous semigroup on a Banach space, the infinitesimal
generator has a closed graph in $`X\times X`. The local operator bounds needed
to pass to the limit follow from strong continuity and completeness.
:::

:::proof "evolution.semigroup.closed_generator"
Suppose $`x_n\to x` and $`Ax_n\to y`. Integrating the orbit derivative gives
$`T(t)x_n-x_n=\int_0^tT(s)Ax_n\,ds`. Continuity of $`T(s)` and Bochner
integration passes this identity to the limit. Dividing by $`t` and sending
$`t\downarrow0` shows that $`x\in D(A)` and $`Ax=y`.
:::

The resolvent is obtained directly as a Laplace transform of the semigroup,
without spectral theory. Under the
contraction hypothesis,
$`\lVert e^{-\lambda t}T(t)x\rVert\le e^{-\lambda t}\lVert x\rVert` makes the
weighted orbit Bochner integrable on $`(0,\infty)` for every $`\lambda>0`,
so the transform defines an operator.

:::definition "evolution.semigroup.laplace_transform" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.laplaceTransform") (uses := "evolution.semigroup.contraction, evolution.semigroup.generator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436-437"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a contraction semigroup on a Banach space and $`\lambda>0`, the Bochner
integral

$$`R_\lambda x=\int_0^\infty e^{-\lambda t}T(t)x\,dt`

defines a bounded linear operator on $`X`.
:::

:::theorem "evolution.semigroup.laplace_resolvent_bound" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.norm_laplaceTransform_le") (uses := "evolution.semigroup.laplace_transform")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436-437"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Laplace transform satisfies Evans's sharp contraction estimate

$$`\lVert R_\lambda\rVert\leq\lambda^{-1}.`
:::

:::proof "evolution.semigroup.laplace_resolvent_bound"
Contractivity gives
$`\lVert e^{-\lambda t}T(t)x\rVert\leq e^{-\lambda t}\lVert x\rVert`.
The norm estimate for the Bochner integral and
$`\int_0^\infty e^{-\lambda t}\,dt=\lambda^{-1}` yield the operator bound.
:::

A norm bound alone does not explain why $`R_\lambda` deserves the name
resolvent.

:::theorem "evolution.semigroup.laplace_resolvent_identities" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.StronglyContinuousSemigroup.laplaceTransform_generator_identity, PDE.Analysis.Evolution.StronglyContinuousSemigroup.generator_laplaceTransform_identity, PDE.Analysis.Evolution.StronglyContinuousSemigroup.laplaceTransform_mem_generatorPMap_domain, PDE.Analysis.Evolution.StronglyContinuousSemigroup.exists_generator_shift_eq") (uses := "evolution.semigroup.closed_generator, evolution.semigroup.laplace_transform")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "436-437"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Laplace operator maps $`X` into $`D(A)` and is the two-sided inverse of
$`\lambda-A`:

$$`R_\lambda(\lambda-A)x=x\quad(x\in D(A)),`

$$`(\lambda-A)R_\lambda y=y\quad(y\in X).`

In particular, every positive $`\lambda` lies in the resolvent set in the
concrete sense that $`\lambda-A` maps the generator domain bijectively onto
$`X`.
:::

:::proof "evolution.semigroup.laplace_resolvent_identities"
For $`x\in D(A)`, differentiate
$`e^{-\lambda t}T(t)x` and integrate from zero to infinity; exponential
decay removes the boundary term at infinity and gives
$`R_\lambda(\lambda-A)x=x`. Applying the same integrated difference-quotient
calculation to arbitrary $`y` shows $`R_\lambda y\in D(A)` and
$`(\lambda-A)R_\lambda y=y`. The two identities give bijectivity.
:::

These results are the generator and resolvent half of Evans §7.4. The
converse, the Hille–Yosida theorem,
constructs a contraction semigroup from the resolvent estimates; the
Dirichlet heat semigroup and the autonomous wave semigroup are generated
this way.

# Nonlinear evolution from a convex energy

A proper lower semicontinuous convex energy $`I:H\to(-\infty,+\infty]`
on a real Hilbert space can also generate an evolution. Its subdifferential
replaces a linear generator:

$$`u'(t)+\partial I(u(t))\ni0.`

The energy may be infinite outside its effective domain and need not be
differentiable. The construction first solves the weak evolution for
initial values in $`D=\operatorname{dom}\partial I`. Contraction then
extends the solution maps to $`\overline D`, including initial values
where a subgradient is not supplied.

:::theorem "evolution.subgradient.domain_flow" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.exists_unique_subgradientFlow")
Let $`H` be a real Hilbert space, $`I:H\to(-\infty,+\infty]` proper,
lower semicontinuous, and convex, and
$`x_0\in D=\operatorname{dom}\partial I`. There is a continuous trajectory
$`u:[0,\infty)\to H` with $`u(0)=x_0` and a Bochner velocity
$`g\in L^\infty((0,\infty);H)` such that

$$`u'=g\quad\text{in distributions},\qquad
-g(t)\in\partial I(u(t))\quad\text{for almost every }t>0.`

The trajectory is unique in this continuous weak class, and the velocity
is unique almost everywhere. Every $`u(t)` belongs to $`D`. If $`p_0`
is the least-norm element of $`\partial I(x_0)`, then

$$`\|u(t)-u(s)\|\le\|p_0\||t-s|,\qquad
\|g(t)\|\le\|p_0\|\quad\text{for almost every }t>0.`

No density of $`D` or separability of $`H` is required.
:::

:::proof "evolution.subgradient.domain_flow"
The Yosida approximations have a common speed bound supplied by an initial
subgradient and converge uniformly on each bounded time interval.
Their limit has a weak velocity satisfying the subgradient inclusion;
countable exhaustion of the positive half-line gives one global velocity.
Choosing the least-norm initial subgradient sharpens the speed bound.
Monotonicity gives contraction between weak trajectories, hence uniqueness
for equal initial data; uniqueness of the weak derivative identifies their
velocities almost everywhere.
:::

:::theorem "evolution.semigroup.subgradient_closure" (parent := "evolution.semigroups") (lean := "PDE.Analysis.Evolution.exists_unique_subgradientSemiflow")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.6"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`H` be a real Hilbert space and $`I:H\to(-\infty,+\infty]` be proper,
lower semicontinuous, and convex. There is a unique jointly continuous
flow $`S:[0,\infty)\times\overline{\operatorname{dom}\partial I}
\to\overline{\operatorname{dom}\partial I}` which is contractive and
agrees with every weak subgradient trajectory starting in
$`\operatorname{dom}\partial I`. In particular,

$$`S(0)x=x,\qquad S(s+t)x=S(s)(S(t)x),\qquad
\|S(t)x-S(t)y\|\le\|x-y\|.`

For initial values in the closure the orbit is continuous and contractive;
the weak velocity and the subgradient inclusion are part of the
{bpref "evolution.subgradient.domain_flow"}[domain theorem] for initial values
in $`\operatorname{dom}\partial I`.
:::

:::proof "evolution.semigroup.subgradient_closure" (uses := "evolution.subgradient.domain_flow")
The global weak subgradient-flow theorem gives unique trajectories on
$`D`. Monotonicity of the subdifferential makes the distance between two
trajectories nonincreasing. At each fixed time the solution map is
therefore $`1`-Lipschitz, so it extends uniquely from the dense set $`D`
to the complete space $`\overline D`.
The identity and composition laws pass to the closure by continuity.
Contraction controls changes of initial data uniformly in time, while
continuity of each orbit controls changes of time; together they give
joint continuity. Any other flow agreeing on $`D` agrees everywhere
by density.
:::

The {bpref "parabolic.gradient_diffusion"}[nonlinear Dirichlet diffusion]
application identifies a concrete energy's subdifferential with a spatial
differential operator. That identification is what turns this abstract
evolution into a PDE with boundary data.
