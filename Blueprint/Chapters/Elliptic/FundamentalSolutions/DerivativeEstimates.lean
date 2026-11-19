/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.FundamentalSolutions.MeanValues
import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates
import PDE.Elliptic.Classical.Harmonic.IteratedDerivativeEstimates

/-!
# Interior derivative estimates for harmonic functions

Boundary-supremum, integral, and iterated interior derivative estimates for
harmonic functions, and the bounded Liouville theorem that follows from them.
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
#doc (Manual) "Interior Derivative Estimates" =>

# Derivative estimates and Liouville's theorem

Interior derivative estimates express the rigidity of harmonic functions
quantitatively: the derivatives of $`u` at a point are controlled by the size of
$`u` on any surrounding sphere or ball. The proof identifies $`u` with the
Poisson extension of its boundary trace and differentiates the Poisson kernel
at the center, which yields the constant $`n/r` without assuming in advance
that the derivatives are harmonic.

:::theorem "elliptic.harmonic.boundary_sup_derivative_estimate" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.norm_fderiv_le") (uses := "elliptic.poisson.ball.uniqueness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "27-30"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, suppose $`r>0`, $`M\ge0`, $`u` is harmonic on a set
containing the closed ball of radius $`r` about $`x`, and
$`|u| \le M` on the boundary sphere. Then
$`\lVert Du(x)\rVert \le nM/r`.
:::

:::proof "elliptic.harmonic.boundary_sup_derivative_estimate" (uses := "elliptic.poisson.ball.uniqueness")
Translate the ball to the origin, extend the boundary trace, and identify the
translated function locally with its Poisson extension.  Differentiating the
Poisson kernel at the center and estimating the resulting spherical integral
by Cauchy–Schwarz gives the explicit constant $`nM/r`.
:::

Replacing the boundary supremum by an integral of $`|u|` costs the volume of a
half-radius ball: the boundary estimate is applied on $`B(x,r/2)`, and $`|u|` at
each point of its sphere is bounded by the ball average of $`|u|` over a ball of
radius $`r/2` that still lies inside $`B(x,r)`. The constant
$`2^{n+1}n/\alpha(n)` produced this way is Evans's.

:::theorem "elliptic.harmonic.first_derivative_estimate" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.norm_fderiv_le_integral_abs") (uses := "elliptic.harmonic.boundary_sup_derivative_estimate, elliptic.mean_value.sphere_and_ball")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "29-30"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`r>0` and $`u` is harmonic on a set containing
$`\overline{B(x,r)}`, then

$$`\lVert Du(x)\rVert \le
\frac{C_1}{r^{n+1}}\int_{B(x,r)} |u(y)|\,dy,\qquad
C_1=\frac{2^{n+1}n}{\alpha(n)},`

where $`\alpha(n)` is the volume of the unit ball. The bound is for the
operator norm of the Fréchet derivative, so it bounds each coordinate
derivative.
:::

:::proof "elliptic.harmonic.first_derivative_estimate" (uses := "elliptic.harmonic.boundary_sup_derivative_estimate, elliptic.mean_value.sphere_and_ball")
Apply the boundary-supremum estimate on the half-radius ball.  At each point
of its boundary sphere, apply the ball mean-value formula on the ball of
radius $`r/2` centered there. These smaller open balls lie in $`B(x,r)`;
the triangle inequality, monotonicity of the integral of $`|u|`, and
$`|B(0,r/2)|=\alpha(n)(r/2)^n` give Evans's constant.
:::

Iterating the first-order estimate bounds derivatives of every order, and each
iteration spends part of the available radius: to control $`D^ku` at $`x`, one
estimates $`D^{k-1}u` on a sphere of radius $`r_0` about $`x`, each point of
which must still have a ball of radius $`r_1+\dots+r_{k-1}` inside the domain.
The sum of radii records this nested geometry.

:::theorem "elliptic.harmonic.iterated_derivative_estimate" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.norm_iteratedFDeriv_radii_le, LaplacianEquation.IsHarmonicPDE.norm_iteratedFDeriv_le, LaplacianEquation.IsHarmonicPDE.norm_iteratedFDeriv_succ_le") (uses := "elliptic.harmonic.boundary_sup_derivative_estimate")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "29-30"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, let $`u` be harmonic on an open set $`U`, let $`k`
be any natural number, and assign a positive radius budget $`r_i` to each
derivative step. If

$$`
\overline{B\left(x,\sum_{i=0}^{k-1}r_i\right)}\subseteq U,
\qquad
|u|\le M
\quad\text{on this ball},
`

then

$$`
\lVert D^k u(x)\rVert\le
\frac{n^kM}{\prod_{i=0}^{k-1}r_i}.
`

Taking every $`r_i=r` gives the uniform estimate on
$`\overline{B(x,kr)}` with denominator $`r^k`. In particular, $`k=2` and
$`k=3` recover the usual second- and third-derivative nested-ball estimates.
The order-zero case is included.
:::

:::proof "elliptic.harmonic.iterated_derivative_estimate" (uses := "elliptic.harmonic.boundary_sup_derivative_estimate")
First derive harmonicity of the evaluated derivatives from harmonicity of
$`u` on the open domain. Then induct on $`k`, spending the head radius in
the final first-derivative estimate. On its boundary sphere, the induction
hypothesis controls the preceding iterated derivative using the tail radii.
Apply the first-order estimate to each multilinear evaluation and use the
operator norm to reassemble the directional bounds. Constant radius budgets
give the uniform theorem; replacing $`k` by $`k+1` gives the successor form.
:::

Liouville's theorem is the limiting case of the boundary-supremum estimate on
all of $`\mathbb R^n`: if $`|u|\le M` everywhere, then
$`\lVert Du(x)\rVert\le nM/r` for every $`r>0`, so $`Du` vanishes identically
and $`u` is constant.

:::theorem "elliptic.harmonic.liouville_bounded" (parent := "elliptic.representation") (lean := "LaplacianEquation.IsHarmonicPDE.eq_const_of_bounded") (uses := "elliptic.harmonic.boundary_sup_derivative_estimate")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "30"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In positive dimension, if $`u:\mathbb R^n\to\mathbb R` is harmonic and
globally bounded, then

$$`\exists c\in\mathbb R,\qquad u(x)=c\quad\text{for every }x\in\mathbb R^n.`
:::

:::proof "elliptic.harmonic.liouville_bounded" (uses := "elliptic.harmonic.boundary_sup_derivative_estimate")
Apply the boundary-supremum derivative estimate on
arbitrarily large balls.  If the derivative norm were positive, choosing a
radius larger than its bound would give a strict contradiction.  Mathlib's
zero-derivative constancy theorem then identifies every value with the value
at the origin.
:::
