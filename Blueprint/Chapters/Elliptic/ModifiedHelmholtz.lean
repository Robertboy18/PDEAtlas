/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.WeakProblems
import PDE.Elliptic.Variational.ModifiedHelmholtz
import PDE.Elliptic.Variational.ModifiedHelmholtzDistributional

/-!
# Modified Helmholtz equation

The weak and distributional modified Helmholtz problem.
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
#doc (Manual) "Modified Helmholtz Equation" =>

:::group "elliptic.modified_helmholtz"
Modified Helmholtz equation
:::

# The role of the positive mass term

The homogeneous-Dirichlet modified Helmholtz problem is

$$`-\Delta u+\lambda u=f,\qquad u\in H^1_0(\Omega).`

Its weak form pairs gradients and adds the mass term
$`\lambda\int_\Omega uv`.  When $`\lambda>0`, the two terms directly control
the full graph-space norm: the gradient controls the derivative coordinates
and the mass term controls the base $`L^2` coordinate.  This is why coercivity
holds without boundedness of the domain or a Poincaré inequality.

There are two levels.  On an arbitrary set, the bilinear form
and its Lax–Milgram solver are functional-analytic objects.  On an open
set, compactly supported smooth functions are available as PDE test
functions, so the same solution can be read distributionally.  Density of
those tests in $`H^1_0` makes the two formulations equivalent.

Besides positive $`\lambda`, we treat a signed regime, in which a negative
mass contribution is allowed whenever its size is smaller than an available
Dirichlet coercivity modulus.

:::definition "elliptic.modified_helmholtz.form" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzForm") (uses := "elliptic.dirichlet.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On $`H^1_0(\Omega)`, the modified Helmholtz form is

$$`B_\lambda(u,v)=
  \int_\Omega\nabla u\cdot\nabla v
  +\lambda\int_\Omega uv.`

It is defined for every set $`\Omega`, measurable or not.
:::

:::theorem "elliptic.modified_helmholtz.coercive" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzForm_isCoercive") (uses := "elliptic.modified_helmholtz.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`\lambda>0`, on every set $`\Omega\subseteq\mathbb R^n` and in every
dimension, the form $`B_\lambda` is coercive on $`H^1_0(\Omega)`: there is a
constant $`c>0` with

$$`B_\lambda(u,u)\ge
  c\,\lVert u\rVert_{H^1_0(\Omega)}^2
  \qquad\text{for all } u\in H^1_0(\Omega).`
:::

:::proof "elliptic.modified_helmholtz.coercive"
Expanding $`B_\lambda(u,u)` gives the squared gradient norm plus
$`\lambda` times the squared base $`L^2` norm. Each coefficient is bounded
below by $`\min(1,\lambda)>0`, so their sum controls that constant times the
full graph-space norm squared; $`c=\min(1,\lambda)` is the constant the
proof supplies.
:::

When $`\lambda` is negative the mass term works against coercivity, and a
lower bound can only come from the gradient term, through a Dirichlet
coercivity modulus. On bounded domains of positive dimension, Poincaré's
inequality supplies one.

:::theorem "elliptic.modified_helmholtz.signed_coercive" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzForm_isCoercive_of_negPart_lt") (uses := "elliptic.modified_helmholtz.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose the Dirichlet form has a coercivity modulus $`c`:

$$`
c\lVert u\rVert_{H^1_0(\Omega)}^2
\leq\int_\Omega |\nabla u|^2
\qquad(u\in H^1_0(\Omega)).
`

If the negative part of the mass coefficient satisfies $`\lambda^-<c`, then

$$`
B_\lambda(u,u)\geq
  (c-\lambda^-)\lVert u\rVert_{H^1_0(\Omega)}^2.
`
:::

:::proof "elliptic.modified_helmholtz.signed_coercive"
Write $`\lambda=\lambda^+-\lambda^-`.  The positive part can be discarded.
The base-coordinate norm is bounded by the full graph-space norm, so the
negative mass contribution is bounded below by
$`-\lambda^-\lVert u\rVert_{H^1_0}^2`.  Subtracting this from the Dirichlet
lower bound leaves the positive coefficient $`c-\lambda^-`.
:::

The signed result gives coercivity, hence unique solvability through
Lax–Milgram. The named solver, and every result built on it, is stated for
$`\lambda>0`. It is the Lax–Milgram solution for the $`L^2` load
$`v\mapsto\int_\Omega fv`.

:::definition "elliptic.modified_helmholtz.solver" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzSolve, SobolevSpace.GraphSpace.modifiedHelmholtzSolve.isWeakSolution, SobolevSpace.GraphSpace.modifiedHelmholtzSolve.isWeakSolution_iff_eq") (uses := "elliptic.modified_helmholtz.form, elliptic.modified_helmholtz.coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`\lambda>0` and $`f\in L^2(\Omega)`, the named solver is the unique
$`u\in H^1_0(\Omega)` satisfying

$$`B_\lambda(u,v)=\int_\Omega fv
  \qquad(v\in H^1_0(\Omega)).`

Satisfying this weak equation is equivalent to equality with the named
solver.
:::

:::theorem "elliptic.modified_helmholtz.stability" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzSolve_zero, SobolevSpace.GraphSpace.modifiedHelmholtzSolve_norm_le, SobolevSpace.GraphSpace.modifiedHelmholtzSolve_sub_modifiedHelmholtzSolve_norm_le") (uses := "elliptic.modified_helmholtz.solver")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On every domain and for $`\lambda>0`, the solver sends zero data
to zero.  Moreover, there is a constant $`C>0`, depending on the fixed form,
such that for all $`f,g\in L^2(\Omega)`,

$$`
\lVert S_\lambda f\rVert_{H^1_0}
\leq C\lVert f\rVert_{L^2},
\qquad
\lVert S_\lambda f-S_\lambda g\rVert_{H^1_0}
\leq C\lVert f-g\rVert_{L^2}.
`
:::

:::proof "elliptic.modified_helmholtz.stability"
The zero-data identity follows from uniqueness.  Boundedness of the
Lax–Milgram solution operator gives the first estimate for some positive
constant depending only on the fixed form.  Apply the same estimate to
$`f-g` and use linearity of the solver to obtain the Lipschitz bound.
:::

The form $`B_\lambda` is symmetric, so the weak equation admits a variational
characterization. The functional is the Dirichlet functional with the mass
term added to its quadratic part.

:::definition "elliptic.modified_helmholtz.energy" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzEnergy") (uses := "elliptic.modified_helmholtz.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For any $`\Omega`, define

$$`
J_{\lambda,f}(v)
=\frac12 B_\lambda(v,v)-\int_\Omega fv.
`
:::

:::theorem "elliptic.modified_helmholtz.energy_principle" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.modifiedHelmholtzEnergy_minimal_of_weakSolution, SobolevSpace.GraphSpace.modifiedHelmholtzSolve.minimizesEnergy, SobolevSpace.GraphSpace.modifiedHelmholtzEnergy.eq_min_iff, SobolevSpace.GraphSpace.modifiedHelmholtzSolve.energy_lt_of_ne, SobolevSpace.GraphSpace.modifiedHelmholtzEnergy.minimizer_iff_weakSolution, SobolevSpace.GraphSpace.modifiedHelmholtzSolve.unique_energyMinimizer") (uses := "elliptic.modified_helmholtz.energy, elliptic.modified_helmholtz.solver")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`\lambda\geq0`, every weak solution minimizes
$`J_{\lambda,f}`.  If $`\lambda>0`, coercivity makes the characterization
exact:

$$`
u\text{ is a global minimizer of }J_{\lambda,f}
\quad\Longleftrightarrow\quad
B_\lambda(u,v)=\int_\Omega fv\quad(\forall v\in H^1_0(\Omega)).
`

The named solution $`S_\lambda f` is the unique minimizer, and every other
field has strictly larger energy.
:::

:::proof "elliptic.modified_helmholtz.energy_principle"
Symmetry and nonnegativity expand the energy difference around a weak
solution into one half of $`B_\lambda(v-u,v-u)`.  For nonnegative
$`\lambda` this proves minimality.  For positive $`\lambda`, coercivity makes
the difference vanish only when $`v=u`, giving the converse, strictness, and
uniqueness.
:::

Everything so far has been Hilbert-space theory on an arbitrary set. To read
$`B_\lambda(u,v)=\int_\Omega fv` as the PDE $`-\Delta u+\lambda u=f`, assume
$`\Omega` is open and test against compactly supported smooth functions. The raw
smooth-test identity makes sense on arbitrary sets; the solution predicate
requires openness.

:::definition "elliptic.modified_helmholtz.distributional_solution" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "313-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open domain, the distributional predicate requires

$$`\int_\Omega\nabla u\cdot\nabla\varphi
  +\lambda\int_\Omega u\varphi
  =\int_\Omega f\varphi
  \qquad(\varphi\in C_c^\infty(\Omega)).`
:::

The variational and distributional formulations differ only in their test
classes, and the canonical image of $`C_c^\infty(\Omega)` is dense in
$`H^1_0(\Omega)`. The equivalence therefore holds for every real $`\lambda`,
coercive or not; the sign of $`\lambda` matters only for solvability.

:::theorem "elliptic.modified_helmholtz.distributional_equivalence" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.isWeakSolution_iff_isWeakModifiedHelmholtzSolution") (uses := "elliptic.weak_solution, elliptic.modified_helmholtz.form, elliptic.modified_helmholtz.distributional_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "313-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open domain,

$$`
B_\lambda(u,v)=\int_\Omega fv\quad(\forall v\in H^1_0(\Omega))
\quad\Longleftrightarrow\quad
(-\Delta+\lambda)u=f\quad\text{in }\mathcal D'(\Omega).
`

The right-hand side is the compactly supported smooth-test formulation.
:::

:::proof "elliptic.modified_helmholtz.distributional_equivalence"
One direction evaluates the Hilbert-space identity on canonical smooth tests.
For the reverse direction, density of smooth compactly supported tests in
$`H^1_0` and continuity of both sides extend equality to every Sobolev test.
:::

Combining the equivalence with the coercive Lax–Milgram theory transports
existence and uniqueness to the distributional side.

:::theorem "elliptic.modified_helmholtz.exists_unique" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.existsUnique") (uses := "elliptic.modified_helmholtz.distributional_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "315-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On every open domain, if $`\lambda>0`, each
$`f\in L^2(\Omega)` admits exactly one $`u\in H^1_0(\Omega)` satisfying

$$`-\Delta u+\lambda u=f\quad\text{in }\mathcal D'(\Omega).`
:::

:::proof "elliptic.modified_helmholtz.exists_unique" (uses := "elliptic.lax_milgram, elliptic.modified_helmholtz.coercive, elliptic.modified_helmholtz.solver, elliptic.modified_helmholtz.distributional_equivalence")
Construct the coercive Lax–Milgram solution, transfer its weak equation to
the distributional predicate, and use the same equivalence plus uniqueness of
the coercive Hilbert-space problem for any competing solution.
:::

Uniqueness can be sharpened to an identification: any distributional solution
must coincide with the named solver. This is the form in which the result is
most useful, since it converts statements about the PDE into statements about
a single operator.

:::theorem "elliptic.modified_helmholtz.distributional_characterization" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.iff_eq_modifiedHelmholtzSolve, SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.zero_iff") (uses := "elliptic.modified_helmholtz.exists_unique, elliptic.modified_helmholtz.solver")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "313-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open domain with $`\lambda>0`, a distributional solution is
the named variational solution:

$$`
(-\Delta+\lambda)u=f
\quad\Longleftrightarrow\quad
u=S_\lambda f.
`

For zero forcing this specializes to $`u=0`.
:::

:::proof "elliptic.modified_helmholtz.distributional_characterization"
The distributional equivalence turns the PDE predicate into the variational
weak equation.  The solver characterization and uniqueness of the coercive
problem then identify $`u` with $`S_\lambda f`.  For zero forcing, combine
this equivalence with the solver's zero-data identity.
:::

Linearity of the distributional predicate in the pair $`(f,u)` holds for every
real $`\lambda`, since it is a property of the integral identity alone.
Through the identification with the named solver it becomes linearity of
$`S_\lambda` for $`\lambda>0`.

:::theorem "elliptic.modified_helmholtz.superposition" (parent := "elliptic.modified_helmholtz") (lean := "SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.add, SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.neg, SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.sub, SobolevSpace.GraphSpace.IsWeakModifiedHelmholtzSolution.smul, SobolevSpace.GraphSpace.modifiedHelmholtzSolve_add, SobolevSpace.GraphSpace.modifiedHelmholtzSolve_smul") (uses := "elliptic.modified_helmholtz.distributional_solution, elliptic.modified_helmholtz.distributional_characterization")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "313-319"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Distributional modified Helmholtz solutions are closed under addition,
negation, subtraction, and real scalar multiplication, with the forcing data
transformed by the same operation.  Consequently, for $`\lambda>0`,

$$`
S_\lambda(f+g)=S_\lambda f+S_\lambda g,
\qquad
S_\lambda(c f)=cS_\lambda f.
`
:::

:::proof "elliptic.modified_helmholtz.superposition"
Linearity of the integral and gradient identities proves closure of the
distributional predicate under the listed operations.  When $`\lambda>0`,
the characterization by the unique named solver turns those closure results
into the two displayed solver identities.
:::
