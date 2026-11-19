/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Elliptic.MaximumPrinciples
import Blueprint.Commands.Figures
import PDE.Elliptic.Semilinear.MovingPlanes.Ball

/-!
# Moving planes

Radial symmetry of positive solutions of `-Δu = f(u)` on the unit ball with zero
boundary values, proved by reflecting across moving hyperplanes.
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
#doc (Manual) "Radial Symmetry by Moving Planes" =>

# Reflecting a cap

The maximum principle also proves symmetry. Let $`u>0` solve

$$`-\Delta u=f(u)\quad\text{in }B(0,1),\qquad u=0\quad\text{on }\partial B(0,1),`

with $`f` Lipschitz. The equation is invariant under rotations, but nothing in
the hypotheses says that $`u` is. {Informal.citet "gidas-ni-nirenberg-1979"}[] showed that it must
be radial and strictly decreasing in $`|x|`. The version proved here is
Theorem 2 of {Informal.citet "evans-2010"}[] §9.5.2.

Fix a unit vector $`e` and a number $`\lambda\in[0,1)`. The hyperplane
$`x\cdot e=\lambda` cuts off the cap
$`\Sigma_\lambda=\{x\in B(0,1):x\cdot e>\lambda\}`, and reflection across the
plane sends $`x` to $`x^\lambda`. Because $`\lambda\ge0`, the mirror image of
the cap lies in the ball again. The difference
$`w_\lambda(x)=u(x^\lambda)-u(x)` is defined on the cap, vanishes on the flat
face, and is nonnegative on the spherical face, where $`u=0`.

{leanpde_figure "moving-planes"}

The figure shows the plane moving from $`\lambda=\tfrac12` toward the centre
for the first Dirichlet eigenfunction of the disc. Along the whole motion the
reflected profile stays above the original one, and at $`\lambda=0` the two
agree. The theorem says the same happens for every positive solution and every
direction $`e`.

The first step is a sign. Subtracting the equations at $`x` and $`x^\lambda`
and using the Lipschitz bound turns the nonlinear equation into a linear
inequality for $`w_\lambda`, with the Lipschitz constant as potential. The
strong maximum principle then makes a nonnegative $`w_\lambda` strictly
positive.

:::theorem "elliptic.moving_planes.strict_comparison" (parent := "elliptic.representation") (lean := "Elliptic.Semilinear.MovingPlanes.lt_reflection_of_le_reflection, Elliptic.Semilinear.MovingPlanes.neg_laplacian_reflection_sub_add_mul_nonneg") (uses := "elliptic.maximum.matrix_strong")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.5.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u` be $`C^2` on $`\mathbb R^n`, positive in $`B(0,1)`, zero on the
sphere, and a solution of $`-\Delta u=f(u)` in the ball, with $`f` Lipschitz
with constant $`L`. Let $`e` be a
unit vector and $`\lambda>0`. Wherever $`w_\lambda\ge0` in the cap,

$$`-\Delta w_\lambda+L\,w_\lambda\ge0.`

If $`w_\lambda\ge0` on all of $`\Sigma_\lambda`, then $`w_\lambda(x)>0` at
every $`x` of the closed ball with $`x\cdot e>\lambda`.
:::

:::proof "elliptic.moving_planes.strict_comparison" (uses := "elliptic.maximum.matrix_strong")
The Laplacian commutes with reflection, so
$`-\Delta w_\lambda=f(u(x^\lambda))-f(u(x))\ge-L\,w_\lambda` when
$`w_\lambda\ge0`. The cap is convex and so connected. On its spherical face
$`u=0` while $`u(x^\lambda)>0`, because $`\lambda>0` puts $`x^\lambda` inside
the ball. So $`w_\lambda` is positive somewhere, and the strong principle for
$`-\Delta+L` rules out an interior zero.
:::

The plane then moves, from $`\lambda=1`, where the cap is empty, down to
$`\lambda=0`. The set of parameters at which $`w_\lambda\ge0` is closed by
continuity, and strict comparison together with the Hopf lemma on the flat face
makes it open, so it is all of $`(0,1]`.

:::theorem "elliptic.moving_planes.continuation" (parent := "elliptic.representation") (lean := "Elliptic.Semilinear.MovingPlanes.le_reflection") (uses := "elliptic.moving_planes.strict_comparison, elliptic.maximum.hopf")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.5.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u` be $`C^2` on $`\mathbb R^n`, positive in $`B(0,1)`, zero on the
sphere, and a solution of $`-\Delta u=f(u)` in the ball with $`f` Lipschitz.
For every unit vector $`e`, every $`\lambda\ge0`, and every $`x\in B(0,1)`
with $`x\cdot e>\lambda`,

$$`u(x)\le u(x^\lambda).`
:::

:::proof "elliptic.moving_planes.continuation" (uses := "elliptic.moving_planes.strict_comparison")
For $`\lambda\ge1` the cap is empty. Closedness of the good set of parameters
follows from continuity of $`u`. For openness at a good $`\lambda>0`, strict
comparison gives $`w_\lambda>0` in the cap and the Hopf lemma gives
$`\partial_eu<0` on the flat face. Near the sphere, a separate argument shows
that $`u` decreases along every outward-pointing direction. By the Hopf lemma
$`\partial_\nu u` can vanish on the sphere only when $`f(0)<0`, and there the
Hessian supplies the sign. Compactness makes these
neighbourhoods uniform, so every nearby plane is good. The interval is
connected, and the case $`\lambda=0` is a limit.
:::

At $`\lambda=0` comparison holds in the directions $`e` and $`-e`, so $`u`
is even under reflection in every hyperplane through the origin, and any two
points of the same norm are exchanged by one such reflection.

:::theorem "elliptic.moving_planes.radial_symmetry" (parent := "elliptic.representation") (lean := "Elliptic.Semilinear.exists_strictAntiOn_radial_profile_of_lipschitz, Elliptic.Semilinear.MovingPlanes.eq_of_norm_eq, Elliptic.Semilinear.MovingPlanes.exists_strictAntiOn_radial_profile") (uses := "elliptic.moving_planes.continuation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.5.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f:\mathbb R\to\mathbb R` be Lipschitz, and let $`u` be $`C^2` up to the
boundary of $`B(0,1)`, with

$$`-\Delta u=f(u)\ \text{ and }\ u>0\ \text{ in }B(0,1),\qquad u=0\ \text{ on }\partial B(0,1).`

Then there is a continuous $`v:[0,1]\to[0,\infty)` that is strictly
decreasing on $`[0,1]`, with $`v(1)=0` and

$$`u(x)=v(|x|)\qquad(x\in\overline B(0,1)).`
:::

:::proof "elliptic.moving_planes.radial_symmetry" (uses := "elliptic.moving_planes.continuation")
Extend $`u` from the closed ball to a $`C^2` function on $`\mathbb R^n`; the
equation only involves the open ball, so it is unchanged. Continuation at
$`\lambda=0` in the directions $`\pm e` gives $`u(x)=u(x^0)`. For
$`|x|=|y|` and $`x\ne y`, take $`e=(x-y)/|x-y|`; the reflection with
$`\lambda=0` sends $`x` to $`y`, so $`u(x)=u(y)`. Define
$`v(r)=u(re_1)`. For $`0\le r<s\le1`, strict comparison at
$`\lambda=(r+s)/2` in the direction $`e_1` compares $`se_1` with its mirror
image $`re_1` and gives $`v(s)<v(r)`. Dimension zero is handled separately.
:::

The theorem is stated for globally Lipschitz $`f`. Since $`u` is bounded,
only the values of $`f` on the range of $`u` matter, so a locally Lipschitz
$`f` can be modified outside that range. The conclusion is strict monotonicity
on the closed interval:
$`v(s)<v(r)` whenever $`0\le r<s\le1`.
