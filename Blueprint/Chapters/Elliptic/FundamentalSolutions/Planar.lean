/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.FundamentalSolutions.OneDimensional
import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarDistribution

/-!
# The planar logarithmic pole

The distributional normalization of the two-dimensional
Laplace fundamental solution.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "The Planar Logarithmic Pole" =>

The planar kernel is logarithmic, so its point source cannot be detected by
the pointwise identity $`\Delta\Phi_2=0` away from the origin. The
proof regularizes the pole, computes the exact negative Laplacian of the
regularization, proves that this nonnegative kernel has mass one, and passes
to the limit against compactly supported test functions.

:::definition "elliptic.fundamental_solution.planar_regularization" (parent := "elliptic.representation") (lean := "PotentialTheory.Planar.regularizedFundamentalSolution, PotentialTheory.Planar.poleApproximation") (uses := "elliptic.fundamental_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`\varepsilon>0`, set

$$`
\Phi_\varepsilon(x)
  =-\frac{1}{4\pi}\log\bigl(|x|^2+\varepsilon^2\bigr),
\qquad
K_\varepsilon(x)
  =\frac{\varepsilon^2}
    {\pi\bigl(|x|^2+\varepsilon^2\bigr)^2}.
`

The exact classical identity is $`-\Delta\Phi_\varepsilon=K_\varepsilon`.
Each $`K_\varepsilon` is nonnegative, integrable, and has total mass one.
:::

:::theorem "elliptic.fundamental_solution.distributional_planar" (parent := "elliptic.representation") (lean := "PotentialTheory.Planar.laplacian_regularizedFundamentalSolution, PotentialTheory.Planar.integral_poleApproximation, PotentialTheory.Planar.integral_fundamentalSolution_mul_laplacian") (uses := "elliptic.fundamental_solution.planar_regularization, elliptic.fundamental_solution.local_integrability")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "23-25"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every compactly supported $`C^2` test function $`\varphi` on
$`\mathbb R^2`, the logarithmic kernel satisfies

$$`
\int_{\mathbb R^2}\Phi_2(x)\,\Delta\varphi(x)\,dx
  =-\varphi(0).
`

Equivalently, $`-\Delta\Phi_2=\delta_0` in the distributional sense.
:::

:::proof "elliptic.fundamental_solution.distributional_planar" (uses := "foundations.distributions.regular_action")
Differentiate $`\Phi_\varepsilon` explicitly to obtain
$`-\Delta\Phi_\varepsilon=K_\varepsilon`. Polar integration gives
$`\int K_\varepsilon=1`, and scaling shows that $`K_\varepsilon` is an
approximate identity. Integration by parts moves the Laplacian from the test
function onto the smooth regularization.

For $`0<\varepsilon\leq1` and $`x\ne0`, monotonicity of the logarithm
places $`\Phi_\varepsilon(x)` between $`\Phi_{\varepsilon=1}(x)` and
$`\Phi_2(x)`. Thus the absolute value of the left integrand is bounded by
$`(|\Phi_{\varepsilon=1}|+|\Phi_2|)|\Delta\varphi|`. This bound is integrable:
the first kernel is smooth, the second is locally integrable, and
$`\Delta\varphi` is continuous with compact support. The excluded origin
has measure zero. Dominated convergence therefore handles the logarithmic
kernel, while approximate-identity convergence sends the right side to
$`-\varphi(0)`.
:::

So far the identity is an integral formula for $`C^2` test functions. Turning it
into an equation in the distribution space requires both sides as distributions:
the regular distribution $`T_{\Phi_2}`, which exists by local integrability, and
the negative distributional Laplacian as a bundled operator.

:::definition "elliptic.fundamental_solution.planar_distribution_operator" (parent := "elliptic.representation") (lean := "PotentialTheory.fundamentalSolutionDistribution, Distribution.negativeLaplacianCLM, Distribution.negativeLaplacianCLM_apply") (uses := "foundations.distributions.regular, foundations.distributions.constant_coefficient_operator, elliptic.fundamental_solution.local_integrability")
The canonical locally integrable kernel defines a regular distribution
$`T_{\Phi_n}` in every positive dimension. The dimension-independent operator
$`-\Delta` is bundled as the negative sum of the second coordinate
distributional derivatives; here both constructions are specialized to
$`n=2`.
:::

The pairing $`\langle-\Delta T_{\Phi_2},\varphi\rangle` unfolds to
$`-\int\Phi_2\,\Delta\varphi`, which the integration identity evaluates as
$`\varphi(0)`. Written as an equality with $`\delta_0`, this evaluation is the
fundamental-solution predicate that the one-dimensional kernel also satisfies.

:::theorem "elliptic.fundamental_solution.planar_equation" (parent := "elliptic.representation") (lean := "PotentialTheory.Planar.fundamentalSolutionDistribution_isFundamentalSolution") (uses := "elliptic.fundamental_solution.distributional_planar, elliptic.fundamental_solution.planar_distribution_operator, foundations.distributions.fundamental_solution_action")
The regular distribution induced by the logarithmic kernel is a
fundamental solution for the planar negative Laplacian:

$$`
-\Delta T_{\Phi_2}=\delta_0.
`

The equality is extensional against every smooth compactly supported test
function and therefore holds in Mathlib's distribution space.
:::

:::proof "elliptic.fundamental_solution.planar_equation"
The generic action formula for the negative distributional Laplacian reduces
the claim to the test-function identity $`\int\Phi_2\Delta\varphi=-\varphi(0)`.
The fundamental-solution
predicate then combines the interior pole and the resulting equality with
$`\delta_0`; its general action theorem recovers evaluation on every test
function.
:::
