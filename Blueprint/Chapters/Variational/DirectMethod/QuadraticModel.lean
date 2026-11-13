/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod.AbstractMinimization

/-!
# A quadratic integral model

The direct method for the squared $`L^2` distance: its exact norm identity,
strong convexity, weak lower semicontinuity, coercivity, convergence criterion,
and unique minimizer.
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
#doc (Manual) "A Quadratic Integral Model" =>

# A quadratic `L²` integral model

:::definition "methods.l2.quadratic_energy" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.quadraticIntegralEnergy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For prescribed Hilbert-valued data $`f\in L^2(\mu;H)`, the quadratic fidelity
functional is the integral

$$`
J_f(u)=\int \lVert u(x)-f(x)\rVert_H^2\,d\mu(x).
`

It is a concrete model of the coercive convex energies used by the direct
method.
:::

The integral equals the squared $`L^2` distance to $`f`. This identity
gives convexity, continuity, coercivity, and the minimizer.

:::theorem "methods.l2.quadratic_identity" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.quadraticIntegralEnergy_eq_norm_sq") (uses := "methods.l2.quadratic_energy")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The integral is exactly the square of the $`L^2` distance:

$$`
J_f(u)=\lVert u-f\rVert_{L^2(\mu;H)}^2.
`
:::

:::proof "methods.l2.quadratic_identity"
Mathlib's `L²` inner-product formula identifies the integral of the pointwise
squared norm with the Hilbert norm squared.
:::

Once $`J_f` is the squared distance to $`f`, convexity is inherited from the
squared norm of an inner-product space, which satisfies the exact identity

$$`
\lVert(1-t)u+tv\rVert^2
=(1-t)\lVert u\rVert^2+t\lVert v\rVert^2-t(1-t)\lVert u-v\rVert^2
\qquad(0\leq t\leq1);
`

translation by $`f` leaves the correction term unchanged.

:::theorem "methods.l2.quadratic_strong_convexity" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.strongConvexOn_quadraticIntegralEnergy") (uses := "methods.l2.quadratic_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "471-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The map $`u\mapsto J_f(u)` is $`2`-strongly convex in Mathlib's
normalization:

$$`
J_f((1-t)u+tv)
\leq (1-t)J_f(u)+tJ_f(v)-t(1-t)\lVert u-v\rVert_{L^2}^2
`

for $`0\leq t\leq1`. It is therefore strictly convex; the numerical modulus is
specific to the squared-distance model.
:::

:::proof "methods.l2.quadratic_strong_convexity"
Subtracting the strong-convexity correction `‖u‖²` from `‖u-f‖²` leaves an
affine functional of `u`, which is convex.
:::

The direct method needs lower semicontinuity in the weak $`L^2` topology, and
convexity upgrades norm continuity to it.

:::theorem "methods.l2.quadratic_weak_lsc" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.lowerSemicontinuous_weakSpace_quadraticIntegralEnergy") (uses := "methods.l2.quadratic_strong_convexity, methods.direct_method.convex_weak_lsc")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "467-470"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The quadratic integral is lower semicontinuous for the weak $`L^2` topology:

$$`
u_\alpha\rightharpoonup u
\quad\Longrightarrow\quad
J_f(u)\leq\liminf_\alpha J_f(u_\alpha).
`
:::

:::proof "methods.l2.quadratic_weak_lsc"
The squared-distance formula gives strong continuity, while strong convexity
gives convexity. The theorem on closed convex sublevel sets then gives weak lower
semicontinuity.
:::

Weak lower semicontinuity is one of the two direct-method inputs; coercivity
is the other. For a squared distance it is immediate, since $`J_f(u)` is at
least $`(\lVert u\rVert-\lVert f\rVert)^2` and so grows like
$`\lVert u\rVert^2` once $`\lVert u\rVert` is large.

:::theorem "methods.l2.quadratic_coercive" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.quadraticIntegralEnergy_coercive") (uses := "methods.l2.quadratic_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-467"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The energy is coercive:

$$`
\lVert u\rVert_{L^2}\longrightarrow\infty
\quad\Longrightarrow\quad
J_f(u)\longrightarrow\infty.
`
:::

:::proof "methods.l2.quadratic_coercive"
Translation by `f` preserves the cobounded filter, and squaring a nonnegative
quantity tending to infinity again tends to infinity.
:::

The exact identity yields more than the qualitative hypotheses of the direct
method. Because $`J_f` is literally a squared distance, small energy means
proximity to $`f` in norm, so minimizing sequences for this model converge
strongly.

:::theorem "methods.l2.quadratic_energy_convergence" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.tendsto_quadraticIntegralEnergy_nhds_zero_iff") (uses := "methods.l2.quadratic_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For any filter-indexed family $`(u_i)`,

$$`
J_f(u_i)\longrightarrow0
\quad\Longleftrightarrow\quad
u_i\longrightarrow f\ \text{strongly in }L^2.
`
:::

:::proof "methods.l2.quadratic_energy_convergence"
Take square roots in the identity $`J_f(u_i)=\lVert u_i-f\rVert^2`; conversely, continuity
of the energy sends strong convergence to convergence of energy values.
:::

Completeness of the coefficient space $`H` enters only in the existence
step, through the weak compactness of $`L^2(\mu;H)`.

:::theorem "methods.l2.quadratic_unique" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.existsUnique_global_minimizer_quadraticIntegralEnergy, PDE.CalculusOfVariations.quadraticIntegralEnergy_eq_zero_iff") (uses := "methods.l2.quadratic_weak_lsc, methods.l2.quadratic_coercive, methods.l2.quadratic_strong_convexity, methods.direct_method.unique_minimizer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "470-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
When the coefficient Hilbert space is complete, the direct method gives a
unique global minimizer, characterized by

$$`
\operatorname*{arg\,min}_{u\in L^2(\mu;H)}J_f(u)=\{f\}.
`

This is the quadratic case of Evans's existence and uniqueness pattern.
:::

:::proof "methods.l2.quadratic_unique"
Weak lower semicontinuity and coercivity give existence, and strict convexity
gives uniqueness. Since $`J_f(f)=0` and the energy is nonnegative, the unique
minimizer is `f`.
:::
