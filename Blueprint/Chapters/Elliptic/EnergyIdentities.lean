/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.GreenRepresentation
import PDE.Elliptic.Classical.Poisson.Variational.FiniteEnergy
import PDE.EnergyMethods.Dirichlet.Box

/-!
# Green identities and energy uniqueness

Green's first and second identities on coordinate boxes, the energy proof of classical
Dirichlet uniqueness, and Dirichlet's principle for classical competitors.
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
#doc (Manual) "Green Identities and Energy Uniqueness" =>

:::group "elliptic.energy_methods"
Green identities and energy methods
:::

# From boundary flux to uniqueness

Green's identities are the integration-by-parts formulas that connect the
classical Laplacian with the Dirichlet energy.  On a coordinate box they keep
the boundary term completely explicit: each pair of opposite faces contributes
the corresponding outward normal derivative, so no smooth-boundary
integration theory is needed.

The uniqueness argument applies the first identity to the difference
$`w=u-v`.  Equal Laplacians give $`\Delta w=0`, while agreement on every face
removes the boundary flux.  The remaining equality says that the integral of
$`|\nabla w|^2` vanishes.  Continuity turns this integral statement into
pointwise vanishing of the gradient, and convexity of the box then makes
$`w` constant.

These are classical $`C^2` results with pointwise face data. The weak
Dirichlet problem uses the same energy idea in $`H^1_0`, where boundary
values are encoded by the Sobolev space and integration by parts is built into
the variational equation.

:::theorem "elliptic.energy.green_first_box" (parent := "elliptic.energy_methods") (lean := "Energy.greens_first_identity_Icc")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "711-712"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a coordinate box $`Q=[a,b]\subset\mathbb R^{m+1}` with $`a\le b`
coordinatewise, globally $`C^1` $`u`, and globally $`C^2` $`v`,

$$`\int_Q u\,\Delta v
  =-\int_Q\nabla u\cdot\nabla v
   +\int_{\partial Q}u\,\partial_\nu v\,dS.`

The linked theorem expands the boundary term into the signed integrals over
the upper and lower coordinate faces.
:::

:::proof "elliptic.energy.green_first_box"
Apply the divergence theorem on the box to `u grad v`, expand
`div(u grad v)`, and rearrange the two integrals. Both summands are continuous
on the compact box, so their Bochner integrability follows from the stated
regularity.
:::

Interchanging $`u` and $`v` in the first identity and subtracting removes the
gradient term, since $`\nabla u\cdot\nabla v` is symmetric. This requires $`C^2`
regularity of both functions, whereas the first identity needs only $`C^1` for
$`u`.

:::theorem "elliptic.energy.green_second_box" (parent := "elliptic.energy_methods") (lean := "Energy.greens_second_identity_Icc") (uses := "elliptic.energy.green_first_box")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "711-712"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For globally $`C^2` functions on a coordinate box
$`Q=[a,b]\subset\mathbb R^{m+1}` with $`a\le b` coordinatewise,

$$`\int_Q(u\Delta v-v\Delta u)
  =\int_{\partial Q}
    (u\,\partial_\nu v-v\,\partial_\nu u)\,dS.`

As in the first identity, the formal statement represents the boundary flux
as a finite signed sum over coordinate faces.
:::

:::proof "elliptic.energy.green_second_box" (uses := "elliptic.energy.green_first_box")
Apply Green's first identity to `(u,v)` and `(v,u)`, then subtract. Equivalently,
apply the box divergence theorem directly to `u grad v - v grad u`; the mixed
gradient terms cancel pointwise.
:::

Uniqueness uses only the first identity, applied with $`u=v=w` for the
difference $`w` of two solutions. Strictly positive side lengths give the box an
interior on which continuity of $`\nabla w` forces it to vanish pointwise.

:::theorem "elliptic.energy.box_dirichlet_uniqueness" (parent := "elliptic.energy_methods") (lean := "Energy.eqOn_Icc_of_laplacian_eq_of_agreeOnBoxFaces")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "42-43"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`Q=[a,b]` have strictly positive side lengths. If $`u,v\in C^2` satisfy

$$`\Delta u=\Delta v\quad\text{on }Q,\qquad
  u=v\quad\text{on }\partial Q,`

then $`u=v` throughout the closed box.
:::

:::proof "elliptic.energy.box_dirichlet_uniqueness" (uses := "elliptic.energy.green_first_box")
Subtract the functions.  Green's first identity and the zero face data force
the Dirichlet energy to vanish.  Continuity then makes every first derivative
zero in the interior; convexity gives constancy, and the boundary value fixes
that constant to zero.
:::

# Dirichlet's principle

Green's first identity also explains why a solution of Poisson's equation
minimizes an energy. For a bounded open set $`\Omega` and a forcing $`f`, put

$$`I[w]=\int_\Omega\Bigl(\tfrac12|Dw|^2-fw\Bigr)\,dx.`

If $`-\Delta u=f` and $`w=u+v` with $`v=0` on $`\partial\Omega`, then

$$`I[u+v]=I[u]+\int_\Omega(Du\cdot Dv-fv)\,dx+\frac12\int_\Omega|Dv|^2\,dx,`

and integration by parts turns the middle term into
$`\int_\Omega(-\Delta u-f)v\,dx=0`. Conversely, a minimizer makes the first
variation vanish in every compactly supported direction, and a continuous
residual orthogonal to all test functions is zero. On a domain more general
than a box, the integration by parts needs a boundary theory. The formal proof
uses the zero-trace theorem on a domain with $`C^1` graph boundary and needs no
$`C^2` extension of the domain or of the functions.

:::definition "elliptic.energy.classical_dirichlet_class" (parent := "elliptic.energy_methods") (lean := "PoissonEquation.classicalEnergy, PoissonEquation.classicalDirichletClass, PoissonEquation.finiteClassicalDirichletClass") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.5(b), the energy and admissible class of Theorem 17"
    page := "42"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`\Omega\subset\mathbb R^n` and $`f,g\colon\mathbb R^n\to\mathbb R`, the
classical energy of $`w` is the integral $`I[w]` above. The admissible class
$`\mathcal A_g` consists of the functions $`w` that are $`C^2` on $`\Omega`
with derivatives through order two uniformly continuous there, continuous on
$`\overline\Omega`, and equal to $`g` on $`\partial\Omega`. The finite-energy
class $`\mathcal A_g^f\subseteq\mathcal A_g` consists of those $`w` for which
$`\frac12|Dw|^2-fw` is integrable on $`\Omega`.
:::

The energy is a Bochner integral, so $`I[w]` is a real number for every $`w`
and equals zero when the integrand is not integrable. Energies are therefore
compared only between members of $`\mathcal A_g^f`, and the converse half of
the principle quantifies over that class. The second statement of the theorem
shows that for a minimizer this class is all of $`\mathcal A_g`.

:::theorem "elliptic.energy.dirichlet_principle" (parent := "elliptic.energy_methods") (lean := "PoissonEquation.poisson_iff_isMinOn_finiteClassicalEnergy, PoissonEquation.classicalDirichletClass_eq_and_isMinOn_of_finiteClassicalEnergy_min, PoissonEquation.poisson_iff_isMinOn_classicalEnergy_of_continuousOn_closure") (uses := "elliptic.energy.classical_dirichlet_class, foundations.boundary_calculus.c1_graph_boundary, foundations.operators.laplacian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.5(b), Theorem 17, with the energy read as a real number"
    page := "42-43"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge1`, let $`\Omega\subset\mathbb R^n` be a bounded open set with
$`C^1` graph boundary, let $`f` be continuous on $`\Omega`, and let
$`u\in\mathcal A_g`. Then

$$`-\Delta u=f\ \text{in }\Omega
\iff u\in\mathcal A_g^f\ \text{and}\ I[u]\le I[w]\ \text{for every }
w\in\mathcal A_g^f.`

If $`u\in\mathcal A_g^f` minimizes $`I` over $`\mathcal A_g^f`, then
$`\mathcal A_g^f=\mathcal A_g` and $`u` minimizes $`I` over all of
$`\mathcal A_g`. When $`f` is continuous on $`\overline\Omega`, every member of
$`\mathcal A_g` has finite energy, and $`u` solves $`-\Delta u=f` exactly when
$`I[u]\le I[w]` for every $`w\in\mathcal A_g`.
:::

:::proof "elliptic.energy.dirichlet_principle" (uses := "sobolev.trace_kernel_characterization")
Suppose $`-\Delta u=f`. The second derivatives of $`u` are bounded on the
bounded set $`\Omega`, so $`f` is square integrable there and every member of
$`\mathcal A_g` has finite energy. A competitor differs from $`u` by a
function $`v` vanishing on $`\partial\Omega`. On the $`C^1` graph domain such a
$`v` has zero trace and so lies in $`H^1_0(\Omega)`, which justifies the
integration by parts in the expansion above; hence the competitor's energy is
at least $`I[u]`.

Conversely, let $`u` minimize over $`\mathcal A_g^f` and let $`\varphi` be smooth
with compact support in $`\Omega`. Interior continuity of $`f` makes
$`f\varphi` integrable, so $`u+t\varphi` stays in $`\mathcal A_g^f` for every
real $`t`. The function $`t\mapsto I[u+t\varphi]` is a quadratic polynomial
with a minimum at $`t=0`, and its derivative there is
$`\int_\Omega(-\Delta u-f)\varphi\,dx`. This vanishes for every $`\varphi`,
and the residual $`-\Delta u-f` is continuous, so it is zero in $`\Omega`.
:::

For a finite-energy minimizer, $`f=-\Delta u` in $`\Omega`. The second
derivatives of $`u` are uniformly continuous there, so $`f` agrees in
$`\Omega` with a continuous function on $`\mathbb R^n`.
