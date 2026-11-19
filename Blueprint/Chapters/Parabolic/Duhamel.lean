/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.InitialData
import PDE.Parabolic.Heat.Duhamel.Equation
import PDE.Parabolic.Heat.DuhamelClassical.SourceEvolution.Bounds
import PDE.Parabolic.Heat.ConvolutionSpace.SpatialDifferentiation
import PDE.Parabolic.Heat.DuhamelClassical.SourceEvolution.TimeDifferentiation
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.JointDifferentiability
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.ResidualAndInitialTrace
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.ClassicalProblem

/-!
# Duhamel's principle

Source-term representations for the inhomogeneous heat equation.
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
#doc (Manual) "Duhamel's Principle" =>

Duhamel's principle treats a forcing term as a continuous superposition of
new initial data inserted at every source time. A source slice created at time
$`s` evolves for heat age $`t-s`, and integrating those evolutions from
$`s=0` to $`s=t` produces the forced solution.

The formal difficulty is the moving upper endpoint. Differentiating in the
observation time in source-time coordinates produces both an interior
derivative and the endpoint value $`f(x,t)`. In heat-age coordinates the
moving endpoint instead contributes the heat evolution at age $`t` of the
time-zero source slice. This representation avoids differentiating the
singular zero-age Gaussian directly.

:::definition "parabolic.duhamel_solution" (parent := "parabolic.classical") (lean := "HeatEquation.nonhomogeneousSolution") (uses := "parabolic.initial_convolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a spacetime source $`f` and $`t>0`, define

$$`u(x,t)=\int_0^t\int_{\mathbb R^n}\Gamma_n(x-y,t-s)f(y,s)\,dy\,ds.`

The Lean function is zero for $`t\leq0`. For $`0<s<t`, the inner integral
is the heat evolution of the source slice $`f(\cdot,s)` at age $`t-s`.
Replacing it by the totalized initial-value solution changes only an endpoint
of the time integral. Recovery of the zero initial trace as a limit uses the
compact-support estimates of {bpref "parabolic.duhamel_residual_trace"}[].
:::

Substituting the heat age $`r=t-s` rewrites the integrand as the heat
evolution, at age $`r`, of the source slice at time $`t-r`. Observation time
then enters only through the source slice, so differentiating in $`t`
differentiates $`f` rather than the kernel; the lemmas that make this
rigorous need one common compact support for all slices.

:::theorem "parabolic.duhamel_source_evolution" (parent := "parabolic.classical") (lean := "HeatEquation.nonhomogeneousSolution_eq_age_integral, HeatEquation.hasDerivAt_initialValueSolution_sourceTime, HeatEquation.secondPartial_initialValueSolution_eq_convolution_source, HeatEquation.exists_uniform_sourceSecond_bound") (uses := "parabolic.duhamel_solution, parabolic.initial_convolution_residual")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
After the substitution from source time to heat age, observation-time
differentiation can be transferred to the source rather than applied to the
kernel at age zero. For a globally $`C^2`, compactly supported source, the
source-time derivative and both spatial derivatives commute with fixed-age
heat evolution, and compact support supplies a uniform bound on the pure
second spatial derivatives. These lemmas provide the domination and endpoint
control used in the classical Duhamel calculation.
:::

:::proof "parabolic.duhamel_source_evolution"
Substitute the heat age $`r=t-s`, so the integrand is the heat evolution at
age $`r` of the source slice at time $`t-r`. For fixed positive age, the
initial-value convolution theorem permits source-time and spatial
differentiation under the spatial integral. Compact spacetime support bounds
all source derivatives on one compact set; convolution with the positive
unit-mass kernel transfers those bounds uniformly. These estimates provide
the domination needed near both the moving endpoint and positive heat ages.
:::

The residual calculation requires Leibniz differentiation and interchange
of the time and spatial derivatives with the integrals.

:::theorem "parabolic.duhamel_analytic_core" (parent := "parabolic.classical") (lean := "HeatEquation.nonhomogeneousSolution_positive_time_residual") (uses := "parabolic.duhamel_solution, parabolic.initial_convolution_residual")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At a fixed positive-time point, the following hypotheses justify the
differentiation of Duhamel's integral:
assume continuity and boundedness of each interior source slice, the
moving-boundary Leibniz formula with endpoint term $`f(x,t)`, and passage of
both pure spatial derivatives through the source-time integral, together
with interval integrability of the resulting second derivatives. Then

$$`\partial_tu-\Delta_xu=f.`

The dominated-differentiation theorem assumes that, on a spatial
neighbourhood, the slice evolutions are measurable and integrable in source
time, and they and their first coordinate derivatives are spatially
differentiable for almost every source time. Measurable derivative covectors
with locally uniform, integrable norm bounds then justify spatial interchange
and give integrability of the resulting second derivatives. For globally
$`C^2`, compactly supported sources, {bpref "parabolic.duhamel_residual_trace"}[]
verifies these hypotheses and the moving-endpoint calculation.
:::

:::proof "parabolic.duhamel_analytic_core" (uses := "parabolic.initial_convolution_residual")
Apply the homogeneous heat equation to every interior source slice, integrate
that identity over source time, and use the supplied Leibniz and
derivative-interchange identities. The two integrated Laplacians cancel,
leaving exactly the moving-endpoint contribution $`f(x,t)`.
:::

The residual theorem uses the ordinary time derivative and the spatial
Laplacian of the Duhamel integral separately. Joint Fréchet
differentiability in $`(t,x)` is a stronger statement: it identifies the
spacetime time-coordinate derivative in the heat operator with the
one-variable derivative of the residual.

:::theorem "parabolic.duhamel_joint_differentiability" (parent := "parabolic.classical") (lean := "HeatEquation.differentiableAt_nonhomogeneousSolution_timeSpace_classical") (uses := "parabolic.duhamel_solution, parabolic.duhamel_source_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a globally $`C^2`, compactly supported spacetime source, the Duhamel
integral is jointly Fréchet differentiable in observation time and space at
every positive-time point.
:::

:::proof "parabolic.duhamel_joint_differentiability"
Write $`S(r)` for heat evolution. For each $`r>0`, the parameterized
convolution theorem gives the joint Fréchet derivative of
$`(t,x)\mapsto [S(r)f(t-r)](x)`. Compact support bounds its operator norm
uniformly in heat age, so dominated differentiation applies first on a fixed
age interval. Continuity at the moving upper endpoint then permits the
moving-interval rule, which adds the covector
$`(h_t,h_x)\mapsto [S(t)f(0)](x)h_t`. This proves joint differentiability
for $`t>0` without differentiating the zero-age kernel.
:::

For a globally $`C^2`, compactly supported source, the Leibniz and
interchange hypotheses of the analytic core all follow from the
source-evolution lemmas.

:::theorem "parabolic.duhamel_residual_trace" (parent := "parabolic.classical") (lean := "HeatEquation.nonhomogeneousSolution_forced_heat_residual_and_initial_trace") (uses := "parabolic.duhamel_analytic_core, parabolic.duhamel_source_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`f` is globally $`C^2` and compactly supported in spacetime, Duhamel's
formula satisfies

$$`\partial_tu-\Delta_xu=f`

at every positive time, has exact value $`u(x,0)=0`, and converges uniformly
in space to zero as $`t\downarrow0`.
:::

:::proof "parabolic.duhamel_residual_trace" (uses := "parabolic.duhamel_analytic_core, parabolic.duhamel_source_evolution")
Use the source-time representation $`u(t)=\int_0^t S(t-s)f(s)\,ds`, where
$`S(r)` is heat evolution and $`S(0)` is the identity. The source-time
Leibniz theorem gives endpoint term $`f(t)`; the homogeneous heat equation
identifies the interior derivative with the integrated spatial Laplacian.
Spatial interchange then gives $`u_t-\Delta u=f`. Compact support supplies
the required bounds. In particular, $`\|u(t)\|_\infty\le t\|f\|_\infty`
gives the uniform initial trace, and the formula has exact value zero at
$`t=0`.
:::

Joint differentiability identifies the time and space derivatives in the
spacetime heat equation.

:::theorem "parabolic.duhamel_classical_package" (parent := "parabolic.classical") (lean := "HeatEquation.nonhomogeneousSolution_satisfiesPDEProblem_of_contDiff_two_compactSupport") (uses := "parabolic.duhamel_residual_trace, parabolic.duhamel_joint_differentiability, parabolic.heat_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "49-50"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same global $`C^2` and compact-support assumptions, the Duhamel
formula gives a `SatisfiesPDEProblem` witness for the forced heat residual and
assigned zero initial value. The uniform trace as $`t\downarrow0` is part of
{bpref "parabolic.duhamel_residual_trace"}[].
:::

:::proof "parabolic.duhamel_classical_package" (uses := "parabolic.duhamel_residual_trace, parabolic.duhamel_joint_differentiability")
Combine the residual and trace theorem with the separately established joint
spacetime differentiability of the compactly supported Duhamel integral.
:::
