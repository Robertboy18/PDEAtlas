/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.FundamentalSolutions.DerivativeEstimates
import PDE.Elliptic.Classical.OneDimensional.LaplaceEquation
import PDE.Elliptic.PotentialTheory.OneDimensional.FundamentalSolution

/-!
# One-dimensional Laplace theory

This module collects the scalar fundamental solution and its distributional
normalization with the affine and mean-value characterizations of
one-dimensional harmonic functions.
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
#doc (Manual) "One-Dimensional Laplace Theory" =>

# The one-dimensional fundamental solution

Dimension one deserves its own formula.  The higher-dimensional Newtonian
kernel is replaced by

$$`\Phi(x)=-\frac12|x|.`

Away from the origin this function is affine and hence harmonic.  Its corner
at the origin carries the entire source: differentiating twice in the
distributional sense produces $`-\delta_0`.  The factor $`1/2` is fixed by the
two half-lines, each of which contributes half of the jump in the first
derivative.

:::definition "elliptic.fundamental_solution.one_dimensional" (parent := "elliptic.representation") (lean := "PotentialTheory.OneDimensional.fundamentalSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On the scalar real line, the normalized fundamental solution is
$`\Phi(x)=-|x|/2`. This scalar presentation is convenient for the
one-dimensional integration-by-parts proof.
:::

The canonical kernel $`\Phi_n` with $`n=1` lives on $`\mathbb R^1`, a
one-dimensional Euclidean space, rather than on the scalar type $`\mathbb R`.
The identification below is what allows the scalar integration-by-parts identity
to be transported to the canonical kernel, so that the dimension-one branch of
$`\Phi_n` is covered by the distributional theorem without a second proof.

:::theorem "elliptic.fundamental_solution.one_dimensional_bridge" (parent := "elliptic.representation") (lean := "PotentialTheory.OneDimensional.canonical_fundamentalSolution_apply") (uses := "elliptic.fundamental_solution, elliptic.fundamental_solution.one_dimensional")
Under the standard scalar embedding $`x \mapsto (x) \in \mathbb R^1`, the
canonical dimension-one Euclidean kernel is exactly the scalar function
$`-|x|/2`.
:::

:::proof "elliptic.fundamental_solution.one_dimensional_bridge"
In one Euclidean dimension, the norm of the embedded scalar coordinate is
$`|x|`. Substituting $`n=1` into the canonical kernel selects its
one-dimensional branch, so evaluation reduces to $`-|x|/2`.
:::

The point-source identity is first proved as an integral formula against
compactly supported $`C^2` test functions, with the classical second
derivative $`\varphi''`.

:::theorem "elliptic.fundamental_solution.distributional_one_dimensional" (parent := "elliptic.representation") (lean := "PotentialTheory.OneDimensional.fundamentalSolution_distributional, PotentialTheory.OneDimensional.canonical_fundamentalSolution_distributional") (uses := "elliptic.fundamental_solution.one_dimensional_bridge")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "21-24"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every compactly supported $`C^2` test function $`\varphi` on the real
line, the scalar kernel $`\Phi(x)=-|x|/2` satisfies

$$`\int_{\mathbb R}\Phi(x)\varphi''(x)\,dx=-\varphi(0).`

It is the one-dimensional case of the normalization $`-\Delta\Phi=\delta_0`.
The test function is Mathlib's bundled finite-order test
function. The result holds both for the scalar presentation and for the
canonical $`\mathbb R^1` kernel pulled back along the standard embedding.
:::

:::proof "elliptic.fundamental_solution.distributional_one_dimensional"
Split the integral into the two half-lines. On each half-line the absolute
value becomes affine, and two compact-support integration-by-parts identities
reduce the integral to the value of the test function at the origin. The two
half-line contributions each supply one half of the required negative sign.
:::

To state the identity as an equation between distributions, the kernel must
first be realized as a regular distribution. Local integrability of $`\Phi`,
which in dimension one is immediate from continuity, is what makes the pairing
below well defined.

:::definition "elliptic.fundamental_solution.one_dimensional_distribution" (parent := "elliptic.representation") (lean := "PotentialTheory.OneDimensional.fundamentalSolutionDistribution") (uses := "foundations.distributions.regular, elliptic.fundamental_solution.one_dimensional")
The locally integrable kernel $`\Phi(x)=-|x|/2` defines the ordinary
distribution

$$`
  T_\Phi(\varphi)
  =\int_{\mathbb R}\varphi(x)\Phi(x)\,dx.
`

This is the canonical regular-distribution realization of the scalar kernel.
:::

The operator side needs the same bundling: $`-D^2` is taken as a continuous
linear map on distributions, so that the fundamental-solution predicate can be
stated as an equality $`-D^2T_\Phi=\delta_0` in the distribution space rather
than as a family of integral identities.

:::definition "elliptic.fundamental_solution.one_dimensional_operator" (parent := "elliptic.representation") (lean := "PotentialTheory.OneDimensional.negativeSecondDerivativeCLM, PotentialTheory.OneDimensional.negativeSecondDerivativeCLM_apply") (uses := "foundations.distributions.constant_coefficient_operator")
The operator $`-D^2` is bundled as a continuous linear endomorphism of
ordinary distributions:

$$`
  T\longmapsto-D(DT).
`
:::

Pairing $`-D^2T_\Phi` with a smooth test function $`\varphi` moves both
derivatives onto $`\varphi`; the two sign changes of the distributional
derivative cancel, leaving the pairing $`-\int\Phi\varphi''`. The integration
identity evaluates this as $`\varphi(0)`, which is the action of $`\delta_0`, so
the theorem is that identity restated in the distribution space.

:::theorem "elliptic.fundamental_solution.one_dimensional_equation" (parent := "elliptic.representation") (lean := "PotentialTheory.OneDimensional.fundamentalSolutionDistribution_isFundamentalSolution") (uses := "elliptic.fundamental_solution.distributional_one_dimensional, elliptic.fundamental_solution.one_dimensional_distribution, elliptic.fundamental_solution.one_dimensional_operator, foundations.distributions.fundamental_solution_action")
The regular distribution associated with $`\Phi(x)=-|x|/2` is a
fundamental solution for the one-dimensional negative second derivative:

$$`
  -D^2T_\Phi=\delta_0.
`

Equivalently, for every smooth compactly supported test function $`\varphi`,

$$`
  \langle-D^2T_\Phi,\varphi\rangle=\varphi(0).
`
:::

:::proof "elliptic.fundamental_solution.one_dimensional_equation"
Lower a smooth test function to Mathlib's bundled compactly supported
$`C^2` function. Its two directional derivatives in direction one agree
pointwise with the ordinary second derivative. The finite-order integration
identity therefore evaluates $`-D^2T_\Phi` as $`\varphi(0)`. Extensionality
against all test functions identifies the resulting distribution with
$`\delta_0`, which is exactly the generic fundamental-solution predicate.
:::

# The one-dimensional mean-value model

For ordinary functions, the equation $`u''=0` has no hidden geometry: every
solution is affine on each interval contained in its domain.  The interval
mean-value property then follows by integrating that affine formula around the
center.  This elementary model mirrors the higher-dimensional route from
harmonicity to mean values while making every analytic step visible.

:::theorem "elliptic.mean_value.one_dimensional_affine" (parent := "elliptic.representation") (lean := "Laplace1D.IsHarmonicPDE.exists_eq_affineOn_closedBall")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`u\in C^2(U)`, $`u''=0` on $`U`, and $`[a,b]\subseteq U` with $`a<b`,
then there are constants $`A,B\in\mathbb R` such that

$$`u(x)=Ax+B\qquad(a\le x\le b).`

This is the complete local classification of one-dimensional harmonic
functions.
:::

:::proof "elliptic.mean_value.one_dimensional_affine"
The first derivative has zero derivative on the interior interval and is
therefore constant.  Subtracting the corresponding affine function leaves a
function with zero first derivative.  Continuity extends the resulting
identity from the open interval to both endpoints.
:::

:::theorem "elliptic.mean_value.one_dimensional_ball" (parent := "elliptic.representation") (lean := "Laplace1D.IsHarmonicPDE.hasBallMeanValueProperty") (uses := "elliptic.mean_value.one_dimensional_affine")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "25-26"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`u\in C^2(U)`, $`u''=0` on $`U`, and $`[x-r,x+r]\subseteq U`
with $`r>0`, then

$$`u(x)=\frac{1}{2r}\int_{x-r}^{x+r}u(y)\,dy.`

This is the one-dimensional ball mean-value identity.
:::

:::proof "elliptic.mean_value.one_dimensional_ball" (uses := "elliptic.mean_value.one_dimensional_affine")
Insert the affine representation into the interval integral.  The odd part
around the center cancels, while the constant part contributes exactly the
interval length times the value at the center.
:::
