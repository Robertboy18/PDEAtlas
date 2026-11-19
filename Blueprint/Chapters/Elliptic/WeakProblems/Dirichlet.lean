/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.EnergyIdentities
import Blueprint.Commands.Figures
import PDE.Elliptic.Variational.DistributionalPoisson
import PDE.Elliptic.Variational.PoissonDirichlet
import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Weak Dirichlet problems

The abstract Lax–Milgram theorem, the homogeneous Dirichlet form and solver,
the equivalence with the distributional Poisson equation, and the stability and
energy-minimization results.
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
#doc (Manual) "Weak Dirichlet Problems" =>

:::group "elliptic.weak_theory"
Weak elliptic problems
:::

# The variational route to Poisson's equation

The weak theory begins with an abstract Hilbert-space equation

$$`B(u,v)=\ell(v)\qquad\text{for every }v.`

Lax–Milgram solves this equation when $`B` is bounded and coercive.  The
Poisson problem is obtained by taking the Hilbert space to be
$`H^1_0(\Omega)`, the bilinear form to be the Dirichlet energy pairing, and
the load to be integration against $`f\in L^2(\Omega)`.  Bounded-domain
Poincaré control is the ingredient that upgrades gradient control to
coercivity for the full Sobolev norm.

There are then two notions of solution.  The variational equation tests
against every element of $`H^1_0`; the distributional equation tests against
compactly supported smooth functions and reads as $`-\Delta u=f`.  Openness
is needed only for the latter PDE-facing formulation.  Density of smooth
tests proves an equivalence, allowing existence and uniqueness to be proved
abstractly and then transported to the distributional statement.

The final results explain the energy interpretation.  Symmetry gives an exact
completion of the square identity, so the weak solution is the minimizer of
the Dirichlet functional.  Coercivity makes that minimizer unique and also
gives continuous dependence on the forcing datum.

:::definition "elliptic.weak_solution" (parent := "elliptic.weak_theory") (lean := "PDE.Analysis.Variational.IsWeakSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314-315"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a bounded bilinear form $`B:H\times H\to\mathbb R` and a continuous dual
load $`\ell\in H^*`, a weak solution is an element $`u\in H` satisfying

$$`B(u,v)=\ell(v)\qquad\text{for every }v\in H.`

This is Evans's variational definition for a bounded bilinear form $`B`, which
need not come from a differential operator.
:::

Boundedness of $`B` alone does not make the equation solvable, and the
definition imposes no sign condition. The extra hypothesis is coercivity, a
lower bound on the quadratic form $`B(v,v)`; symmetry of $`B` is never
required for existence and uniqueness, and it enters only in the energy
interpretation below.

:::theorem "elliptic.lax_milgram" (parent := "elliptic.weak_theory") (lean := "PDE.Analysis.Variational.IsWeakSolution.existsUnique") (uses := "elliptic.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-317"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`H` is a real Hilbert space and, for some $`c>0`,

$$`B(v,v)\ge c\lVert v\rVert_H^2\qquad(v\in H),`

then every $`\ell\in H^*` has a unique weak solution
$`u\in H` satisfying $`B(u,v)=\ell(v)` for all $`v\in H`.
:::

:::proof "elliptic.lax_milgram"
The load is transferred to its Riesz representative.  Mathlib's
Lax–Milgram continuous linear equivalence for the coercive form is then
inverted, and injectivity of that equivalence gives uniqueness.
:::

When $`B` is symmetric, it is itself an inner product, equivalent to the one on
$`H`, and Lax–Milgram becomes the Riesz representation theorem in that inner
product. The solution $`u` is the minimizer of the energy
$`J(v)=\frac12B(v,v)-\ell(v)`, whose level sets are the spheres of $`B` centered
at $`u`. The left panel of the figure draws this in the plane, where $`B` is a
positive definite $`2\times2` matrix and the spheres are ellipses. Restricting the
equation to a closed subspace $`V_1` and solving $`B(u_1,v)=\ell(v)` for
$`v\in V_1` is again a Lax–Milgram problem, because coercivity passes to
subspaces. Its solution $`u_1` is the point where a level ellipse touches the
line, and subtracting the two equations gives $`B(u-u_1,v)=0` for every
$`v\in V_1`. So $`u_1` is the $`B`-orthogonal projection of $`u`, which is
generally not the nearest point in the norm of $`H`. Combining this orthogonality
with boundedness and coercivity gives Céa's lemma,
$`\lVert u-u_1\rVert\le(M/c)\inf_{v\in V_1}\lVert u-v\rVert`. The Galerkin error
is at most a fixed multiple of the best approximation error in the subspace.
The right panels apply this to piecewise linear finite elements on nested
meshes, where the best approximation error, and with it the Galerkin error,
decays like the mesh size. Céa's lemma is the classical statement, checked
numerically in the figure.

{leanpde_figure "lax-milgram-projection"}

To reach Poisson's equation the abstract space is specialized to
$`H^1_0(\Omega)` and the form to the pairing of weak gradients. The form
itself makes sense on any set; geometric restrictions on $`\Omega`
appear only when its lower bound is needed.

:::definition "elliptic.dirichlet.form" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletForm") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "314"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "320"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
On any set $`\Omega`, the Dirichlet form on $`H^1_0(\Omega)` is

$$`B_\Omega(u,v)=\sum_{i=1}^n
  \int_\Omega D_i u(x)\,D_i v(x)\,dx.`

The derivatives are the canonical weak coordinate derivatives in the
graph-space model of $`H^1_0(\Omega)`.
:::

The quadratic form $`B_\Omega(u,u)` is the squared $`L^2` norm of the weak
gradient, so on its own it controls only the derivative coordinates of the
graph-space norm. The base $`L^2` coordinate has to be recovered from the
gradient, which is exactly what the Poincaré inequality does on a bounded
domain.

Write that step in the usual Sobolev norm. If
$`\|u\|_{L^2}\le C_P\|\nabla u\|_{L^2}` for $`u\in H^1_0(\Omega)`, then

$$`
\|u\|_{H^1}^2
=\|u\|_{L^2}^2+\|\nabla u\|_{L^2}^2
\le(1+C_P^2)B_\Omega(u,u).
`

This is coercivity: small energy forces the whole state to be small in the
solution norm. The zero boundary condition matters. Without it, adding an
arbitrary constant leaves the gradient energy unchanged, so that energy
cannot control the size of the function.

:::theorem "elliptic.dirichlet.coercive" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletForm_isCoercive") (uses := "elliptic.dirichlet.form, sobolev.poincare")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "318-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`n\ge1` and $`\Omega` is bounded, then there is
$`c_\Omega>0` such that

$$`B_\Omega(u,u)\ge
  c_\Omega\lVert u\rVert_{H^1_0(\Omega)}^2
  \qquad(u\in H^1_0(\Omega)).`
:::

:::proof "elliptic.dirichlet.coercive"
The Dirichlet form is the squared $`L^2` norm of the weak gradient. On a
bounded domain, Poincaré bounds the base $`L^2` norm of $`u` by that gradient
norm. Combining the two coordinates of the graph-space norm therefore yields
a positive multiple controlled by $`B_\Omega(u,u)`.
:::

With coercivity established, Lax–Milgram applies to $`B_\Omega` and the load
$`v\mapsto\int_\Omega fv` for each $`f\in L^2(\Omega)`. Since that load
depends linearly and continuously on $`f`, the resulting assignment
$`f\mapsto u` is a bounded linear operator.

:::definition "elliptic.dirichlet.solver" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletSolveCLM, SobolevSpace.GraphSpace.dirichletSolve") (uses := "elliptic.lax_milgram, elliptic.dirichlet.coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For positive dimension and a bounded domain, Lax–Milgram gives a
continuous linear solution operator

$$`S:L^2(\Omega)\longrightarrow H^1_0(\Omega).`

The named pointwise solver is evaluation of this operator at the forcing
datum.
:::

The solver is defined through the inverse of the Lax–Milgram equivalence
rather than by the equation, so the statement that $`Sf` satisfies
the weak equation is a theorem. Combined with the uniqueness half of
Lax–Milgram, it identifies $`Sf` as the only element of $`H^1_0(\Omega)` with
this property.

:::theorem "elliptic.dirichlet.solver_weak_equation" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletSolve.isWeakSolution") (uses := "elliptic.dirichlet.solver, elliptic.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`n\ge1` and $`\Omega` is bounded, then for every
$`f\in L^2(\Omega)` the named Dirichlet solver $`S f` satisfies

$$`B_\Omega(Sf,v)=\int_\Omega f(x)v(x)\,dx
  \qquad\text{for every }v\in H^1_0(\Omega).`
:::

:::proof "elliptic.dirichlet.solver_weak_equation"
The solver is defined by applying the inverse Lax–Milgram equivalence to the
$`L^2` load $`v\mapsto\int_\Omega fv`. The defining inverse identity says
precisely that its value satisfies the displayed weak equation for every
test vector.
:::

Up to this point the test functions have ranged over all of $`H^1_0(\Omega)`,
and nothing about $`\Omega` beyond measurability, boundedness, and positive
dimension has been used. Reading the identity as the PDE $`-\Delta u=f` means
testing against $`\varphi\in C_c^\infty(\Omega)` instead, and compactly
supported smooth test functions require $`\Omega` to be open.

:::definition "elliptic.poisson.distributional_solution" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.IsWeakPoissonSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be any set, $`f\in L^2(\Omega)`, and
$`u\in H^1_0(\Omega)`. The distributional Poisson predicate requires
$`\Omega` to be open and

$$`\sum_{i=1}^n\int_\Omega D_i u\,D_i\varphi
  =\int_\Omega f\varphi
  \qquad\text{for every }\varphi\in C_c^\infty(\Omega).`

This is the weak test form of $`-\Delta u=f`.
:::

The two formulations differ only in the class of test functions. Since the
canonical image of $`C_c^\infty(\Omega)` is dense in $`H^1_0(\Omega)` and both
sides of the identity are continuous in the test function, restricting to
smooth tests loses nothing; this equivalence needs openness of $`\Omega` but
neither boundedness nor positive dimension.

:::theorem "elliptic.poisson.distributional_iff_variational" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.isWeakSolution_iff_isWeakPoissonSolution") (uses := "elliptic.poisson.distributional_solution, elliptic.weak_solution, elliptic.dirichlet.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open domain, for $`u\in H^1_0(\Omega)` and
$`f\in L^2(\Omega)`,

$$`
B_\Omega(u,v)=\int_\Omega fv\quad(\forall v\in H^1_0(\Omega))
\quad\Longleftrightarrow\quad
\sum_i\int_\Omega D_i u\,D_i\varphi=\int_\Omega f\varphi
\quad(\forall\varphi\in C_c^\infty(\Omega)).
`
:::

:::proof "elliptic.poisson.distributional_iff_variational"
One implication evaluates the variational equation on the canonical image of
each smooth test function.  Conversely, equality on smooth tests extends to
all of $`H^1_0(\Omega)` because that image has dense range and both sides are
continuous linear functionals.
:::

Existence and uniqueness can therefore be transported from the variational
side, where Lax–Milgram provides them, to the distributional side. The
hypotheses are the union of those used so far: boundedness and positive
dimension for coercivity, openness for the distributional predicate.

:::theorem "elliptic.poisson.distributional_exists_unique" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.IsWeakPoissonSolution.existsUnique") (uses := "elliptic.poisson.distributional_iff_variational, elliptic.dirichlet.solver")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`n\ge1` and $`\Omega` is open and bounded, then every
$`f\in L^2(\Omega)` admits exactly one $`u\in H^1_0(\Omega)` such that

$$`-\Delta u=f\quad\text{in }\mathcal D'(\Omega).`
:::

:::proof "elliptic.poisson.distributional_exists_unique" (uses := "elliptic.poisson.distributional_iff_variational, elliptic.lax_milgram, elliptic.dirichlet.coercive")
Construct the named Lax–Milgram solution for the coercive Dirichlet form and
transport existence and uniqueness across the equivalence between the
variational and smooth-test formulations.
:::

Existence and uniqueness are two of the three components of well-posedness.
The third, continuous dependence on the data, is for a linear problem a norm
bound on the solution operator, and coercivity supplies it, since
$`c_\Omega\lVert Sf\rVert^2\le B_\Omega(Sf,Sf)=\int_\Omega f\,Sf` and the
right-hand side is controlled by
$`\lVert f\rVert_{L^2}\lVert Sf\rVert_{H^1_0}`.

:::theorem "elliptic.dirichlet.apriori_estimate" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletSolve_norm_le") (uses := "elliptic.dirichlet.solver")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "316-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same positive-dimension and bounded-domain assumptions, there is a
constant $`C_\Omega>0`, independent of $`f`, such that

$$`\lVert Sf\rVert_{H^1_0(\Omega)}
  \le C_\Omega\lVert f\rVert_{L^2(\Omega)}.`
:::

:::proof "elliptic.dirichlet.apriori_estimate" (uses := "elliptic.dirichlet.coercive")
Apply the quantitative Lax–Milgram estimate with the coercivity constant,
then bound the concrete $`L^2` load functional by the forcing norm.
:::

Because $`S` is linear, $`Sf-Sg=S(f-g)`, and the a priori estimate applied to
the difference load turns the operator bound into a Lipschitz estimate. The
zero-forcing identity $`S0=0` is the degenerate case of the same linearity.

:::theorem "elliptic.dirichlet.continuous_dependence" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletSolve_zero, SobolevSpace.GraphSpace.dirichletSolve_sub_dirichletSolve_norm_le_load, SobolevSpace.GraphSpace.dirichletSolve_sub_dirichletSolve_norm_le") (uses := "elliptic.dirichlet.solver, elliptic.dirichlet.apriori_estimate")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "316-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a bounded domain of positive dimension, the Dirichlet solution
operator sends zero forcing to zero and is Lipschitz continuous: there is a
positive constant $`C`, depending only on the fixed domain and coercive form,
such that

$$`\lVert S f-S g\rVert_{H^1_0}
  \le C\lVert f-g\rVert_{L^2}`

for all forcing data $`f,g`. A parallel estimate holds in the norm of
the induced dual load.
:::

:::proof "elliptic.dirichlet.continuous_dependence" (uses := "elliptic.dirichlet.apriori_estimate")
Linearity identifies the difference of two solutions with the solution of the
difference load. Apply the Lax–Milgram operator bound and then the norm bound
for the concrete $`L^2` load functional.
:::

The Dirichlet form is also symmetric, and symmetry allows the weak equation
to be recast as the stationarity condition of a quadratic functional.

:::definition "elliptic.dirichlet.energy" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletEnergy") (uses := "elliptic.dirichlet.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "456-457"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For any set $`\Omega` and $`f\in L^2(\Omega)`, the concrete
Dirichlet functional on $`H^1_0(\Omega)` is

$$`J(v)=\frac12 B(v,v)-\ell_f(v).`

This is the quadratic Poisson specialization of Evans's generalized
Dirichlet principle.
:::

Completing the square in $`J(v)-J(u)` requires $`B(u,v)=B(v,u)`, so this is
the first point at which symmetry of the Dirichlet form is used. Once the
square is completed, the weak equation replaces $`B(u,\cdot)` by the load and
every term linear in $`v-u` cancels.

:::theorem "elliptic.dirichlet.energy_identity" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletEnergy_sub_eq") (uses := "elliptic.dirichlet.energy, elliptic.weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "455-457"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`u` satisfies the symmetric Dirichlet weak equation, then for every
$`v\in H^1_0(\Omega)` one has the exact completion of the square identity

$$`J(v)-J(u)=\frac12 B(v-u,v-u).`

It contains the first-variation condition and gives the minimization
argument directly.
:::

:::proof "elliptic.dirichlet.energy_identity"
Expand both quadratic terms, use symmetry of the Dirichlet form, and replace
$`B(u,v)` and $`B(u,u)` by the load functional through the weak equation.
:::

The right-hand side of the identity is nonnegative, since
$`B_\Omega(w,w)=\sum_i\lVert D_iw\rVert_{L^2}^2`. Minimality of the named
solution therefore follows from the identity alone; boundedness of $`\Omega`
enters only through the existence of $`Sf`, not through the inequality.

:::theorem "elliptic.dirichlet.energy_minimizer" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletSolve.minimizesEnergy") (uses := "elliptic.dirichlet.solver, elliptic.dirichlet.energy_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "456-457"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a bounded domain of positive dimension, let $`f\in L^2(\Omega)`
and set

$$`J(v)=\frac12B_\Omega(v,v)-\ell_f(v).`

The named Lax–Milgram solution $`u=Sf` satisfies
$`J(u)\le J(v)` for every $`v\in H^1_0(\Omega)`.
:::

:::proof "elliptic.dirichlet.energy_minimizer" (uses := "elliptic.dirichlet.solver_weak_equation, elliptic.dirichlet.energy_identity")
Apply the energy identity at the named weak solution.  The remaining
Dirichlet quadratic form is a sum of squared $`L^2` derivative norms and is
therefore nonnegative.
:::

Uniqueness of the minimizer is where coercivity, and not merely nonnegativity,
is needed. Equality $`J(v)=J(u)` forces $`B_\Omega(v-u,v-u)=0`, and only the
Poincaré lower bound converts vanishing Dirichlet energy into $`v=u`.
Conversely, every minimizer agrees with the named weak solution and therefore
satisfies its weak equation.

:::theorem "elliptic.dirichlet.unique_energy_minimizer" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.dirichletEnergy.eq_min_iff, SobolevSpace.GraphSpace.dirichletSolve.energy_lt_of_ne, SobolevSpace.GraphSpace.dirichletSolve.unique_energyMinimizer, SobolevSpace.GraphSpace.dirichletEnergy.minimizer_iff_weakSolution") (uses := "elliptic.dirichlet.energy_minimizer, elliptic.dirichlet.coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "456-457"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "471-472"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
On a bounded domain of positive dimension, coercivity gives

$$`J(v)-J(u)=\frac12B(v-u,v-u)\ge0,`

with equality exactly when $`v=u`. Thus the named weak solution is the unique
minimizer of the Dirichlet functional. More generally, minimizing $`J` is
equivalent to the weak Euler–Lagrange equation
$`B(u,w)=\ell(w)` for every test direction $`w`.
:::

:::proof "elliptic.dirichlet.unique_energy_minimizer" (uses := "elliptic.dirichlet.energy_identity, elliptic.dirichlet.solver_weak_equation")
The completion of the square identity reduces equality of energies to
vanishing Dirichlet energy of the difference. Poincaré coercivity forces that
difference to be zero, and the weak equation identifies the minimizer in both
directions.
:::
