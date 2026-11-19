/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.FundamentalSolutions.Planar
import PDE.Elliptic.PotentialTheory.FundamentalSolution.NewtonianDistribution

/-!
# The Newtonian pole

The test-function identity and distributional normalization of the Newtonian kernel.
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
#doc (Manual) "The Newtonian Pole" =>

For $`n\ge3`, the power-law kernel has the same point-source normalization as
the logarithmic kernel. We recover the point source by spherical integration:
the normalized radial flux gives the value of a test function at the origin.

:::theorem "elliptic.fundamental_solution.distributional_newtonian" (parent := "elliptic.representation") (lean := "PotentialTheory.Newtonian.integral_fundamentalSolution_mul_laplacian, PotentialTheory.Newtonian.fundamentalSolutionDistribution_isFundamentalSolution, PotentialTheory.Newtonian.negativeLaplacian_fundamentalSolutionDistribution") (uses := "elliptic.fundamental_solution, elliptic.fundamental_solution.local_integrability, elliptic.fundamental_solution.planar_distribution_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§2.2.1, the Newtonian fundamental-solution normalization"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge3`. For every compactly supported $`C^2` test function
$`\varphi\colon\mathbb R^n\to\mathbb R`,

$$`\int_{\mathbb R^n}\Phi_n(x)\Delta\varphi(x)\,dx=-\varphi(0).`

Consequently the regular distribution induced by the Newtonian kernel is a
fundamental solution of the negative Laplacian:

$$`-\Delta T_{\Phi_n}=\delta_0.`
:::

:::proof "elliptic.fundamental_solution.distributional_newtonian" (uses := "elliptic.fundamental_solution.flux_normalization, elliptic.geometry.coarea_balls, foundations.distributions.fundamental_solution_action")
Write $`M(r)` for the spherical mean of $`\varphi` and $`B(r)` for the
integral of $`\Delta\varphi` over $`B(0,r)`. The ball divergence theorem
expresses $`B(r)` through $`M'(r)`. The normalized kernel flux then makes the
spherical integral of $`\Phi_n\Delta\varphi` the derivative of
$`rM'(r)/(n-2)+M(r)`. This primitive tends to $`\varphi(0)` as $`r\to0` and
vanishes beyond the support of $`\varphi`. Coarea and the fundamental theorem
of calculus give the displayed identity. Applying it to smooth test functions
identifies the negative distributional Laplacian with $`\delta_0`.
:::
