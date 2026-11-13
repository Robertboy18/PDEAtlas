/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.GaussianKernel
import PDE.Parabolic.Heat.ApproximateIdentity
import PDE.Parabolic.Heat.ConvolutionSpace.Equation
import PDE.Parabolic.Heat.ConvolutionSpace.JointDifferentiability
import PDE.Parabolic.Heat.ConvolutionTime
import PDE.Parabolic.Heat.InfinitePropagation
import PDE.Parabolic.Heat.InitialValue
import PDE.Parabolic.Heat.PointwiseIVP

/-!
# Initial data and convolution

Convolution solutions and recovery of heat-equation initial data.
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
#doc (Manual) "Initial Data and Convolution" =>

The Gaussian kernel turns an initial profile into a positive-time heat flow by
spatial convolution. Three facts drive the construction: the kernel is
nonnegative, it has mass one, and its mass concentrates at the origin as time
approaches zero. Positivity and unit mass give the $`L^\infty` estimate;
concentration recovers the initial trace.

For positive time the same formula is smoother than the original datum.
Differentiating the Gaussian under the integral proves the heat equation even
when the initial profile is assumed only bounded and continuous. The argument
has four parts: the convolution formula, the domination needed for
differentiation, the PDE residual, and the approximate-identity limit at time
zero.

:::definition "parabolic.initial_convolution" (parent := "parabolic.classical") (lean := "HeatEquation.initialValueSolution") (uses := "parabolic.heat_kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For initial data $`g:\mathbb R^n\to\mathbb R` and $`t>0`, define

$$`u(x,t)=\int_{\mathbb R^n}\Gamma_n(x-y,t)g(y)\,dy.`

The total Lean function returns $`g(x)` for $`t\leq0`.
:::

Since $`\Gamma_n(\cdot,t)\,dy` is a probability measure for each $`t>0`,
the convolution is an average of values of $`g`, and an average cannot
exceed a uniform bound on the datum.

:::theorem "parabolic.initial_convolution_linfty" (parent := "parabolic.classical") (lean := "HeatEquation.initialValueSolution_const, HeatEquation.abs_initialValueSolution_le") (uses := "parabolic.initial_convolution, parabolic.heat_kernel_mass")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-49"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The whole-space heat evolution preserves constant data. More generally, if
$`g` is continuous and $`|g(y)|\le M` for every $`y`, then

$$`
\left|\int_{\mathbb R^n}\Gamma_n(x-y,t)g(y)\,dy\right|\le M
\qquad (t>0).
`

The totalized Lean formula satisfies the same estimate for $`t\le0` by its
definition. This is the $`L^\infty`-contraction estimate for the explicit
heat-kernel evolution, stated pointwise.
:::

:::proof "parabolic.initial_convolution_linfty"
For constant data, pull the constant through the convolution and use unit
mass. For bounded data, dominate the absolute value of the integrand by
$`M\Gamma_n`, integrate, and again use unit mass.
:::

Boundedness of $`g` and unit mass control the size of the evolution but say
nothing about its derivatives. Those come from the kernel alone: for
$`t>0` the time derivative of the Gaussian is dominated near $`t` by an
integrable majorant, so differentiation passes through the integral even
though the datum is merely bounded and continuous.

:::theorem "parabolic.heat_kernel_convolution_time_derivative" (parent := "parabolic.classical") (lean := "HeatEquation.hasDerivAt_heatKernel_convolution_time") (uses := "parabolic.heat_kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`g:\mathbb R^n\to\mathbb R` be continuous with $`|g(y)|\le M` for
every $`y`, fix $`x\in\mathbb R^n`, and let $`t>0`. Then the heat-kernel
convolution

$$`
s\longmapsto\int_{\mathbb R^n}\Gamma_n(x-y,s)\,g(y)\,dy
`

is differentiable at $`s=t`, with derivative

$$`
\int_{\mathbb R^n}
\left(\frac{\lVert x-y\rVert^2}{4t^2}-\frac{n}{2t}\right)
\Gamma_n(x-y,t)\,g(y)\,dy.
`

The integrand is the pointwise time derivative of the Gaussian multiplied by
the datum, so this is the first "differentiate under the integral sign" step
of Evans's heat initial-value theorem. The statement concerns the convolution
integral itself; the totalized initial-value formula agrees with it near every
positive time, which is how
{bpref "parabolic.initial_convolution_differentiation"}[] inherits this
derivative.
:::

:::proof "parabolic.heat_kernel_convolution_time_derivative"
Work on the time ball $`|s-t|<t/2`. There the coefficient
$`\lVert z\rVert^2/(4s^2)-n/(2s)` is bounded by
$`\lVert z\rVert^2/t^2+n/t`, and the Gaussian $`\Gamma_n(z,s)` is bounded by
a constant depending on $`t` times $`\exp(-\lVert z\rVert^2/(6t))`. Their
product is therefore dominated by a polynomial in $`\lVert z\rVert` times the
slower Gaussian $`\exp(-\lVert z\rVert^2/(12t))`, which is integrable, and
multiplying by the global bound $`M` for $`g` keeps it integrable. The
dominated differentiation theorem for parameter-dependent integrals then
moves the time derivative of the Gaussian inside the integral.
:::

The time derivative is one slot of the first- and second-order calculus
needed to evaluate $`Hu`. The same Gaussian majorants control the spatial
gradient and Hessian, and since the totalized formula agrees with the
convolution on a neighbourhood of every positive time, the derivative just
computed transfers to the initial-data convolution unchanged.

:::theorem "parabolic.initial_convolution_differentiation" (parent := "parabolic.classical") (lean := "HeatEquation.hasDerivAt_initialValueSolution_time, HeatEquation.hasFDerivAt_initialValueSolution_space, HeatEquation.differentiableAt_initialValueSolution_timeSpace, HeatEquation.differentiableAt_partialDeriv_initialValueSolution_space, HeatEquation.laplacian_heatKernel_convolution") (uses := "parabolic.initial_convolution, parabolic.heat_kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`g` be continuous and globally bounded. At every positive-time point,
the heat-kernel convolution is differentiable in time and Fréchet
differentiable in space, with both derivatives obtained by differentiating
the Gaussian beneath the integral. It is jointly differentiable in
$`(t,x)`, every first spatial coordinate derivative is itself spatially
differentiable, and the spatial Laplacian may be moved through the
convolution integral.

These are dominated-differentiation theorems with explicit integrable
Gaussian majorants. They give the first- and second-order regularity that
the classical heat residual needs. Joint $`C^\infty` smoothness on the
positive-time half-space is the joint smoothness theorem.
:::

:::proof "parabolic.initial_convolution_differentiation" (uses := "parabolic.heat_kernel_convolution_time_derivative")
Work in a positive-time neighbourhood bounded away from zero. Derivatives of
the Gaussian are bounded there by a polynomial times a slower Gaussian,
which is integrable and remains an admissible majorant after multiplication
by the global bound for $`g`. Apply the parameter-dependent integral
theorems for the time derivative, spatial derivative, and Hessian slots, and
sum the diagonal Hessian slots to obtain the Laplacian formula.
:::

With both derivatives expressed as integrals against the datum, the residual
reduces to an identity between integrands. The time derivative of
$`\Gamma_n(x-y,t)` and its Laplacian in $`x` agree pointwise by the kernel
equation, so their difference integrates to zero against any bounded $`g`.

:::theorem "parabolic.initial_convolution_residual" (parent := "parabolic.classical") (lean := "HeatEquation.initialValueSolution_positive_time_residual_zero") (uses := "parabolic.initial_convolution_differentiation, parabolic.heat_kernel_equation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`g` is continuous and bounded, then its heat-kernel evolution satisfies

$$`\partial_tu(x,t)-\Delta_xu(x,t)=0`

for every $`x` and every $`t>0`. The assumptions justify differentiating
under the spatial integral.
:::

:::proof "parabolic.initial_convolution_residual" (uses := "parabolic.initial_convolution_differentiation, parabolic.heat_kernel_equation")
Differentiate beneath the integral using Gaussian derivative majorants, then
integrate the pointwise heat-kernel identity against the bounded datum.
:::

The positive-time residual says nothing about $`t=0`. The totalized formula
takes the value $`g(x)` there by definition, but that assignment is not a
limit statement; recovering the datum from positive times is a separate
approximate-identity argument, driven by concentration of kernel mass near
the origin rather than by any derivative bound.

:::theorem "parabolic.initial_convolution_trace" (parent := "parabolic.classical") (lean := "HeatEquation.initialValueSolution_locally_uniform_initial_trace") (uses := "parabolic.initial_convolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For bounded continuous $`g`, fix $`x_0` and $`\varepsilon>0`. Then there is
$`\delta>0` such that, for every $`x` and $`t`,

$$`\lVert x-x_0\rVert<\delta,\quad 0<t<\delta\quad\Longrightarrow\quad |u(x,t)-g(x_0)|<\varepsilon.`
:::

:::proof "parabolic.initial_convolution_trace" (uses := "parabolic.heat_kernel_mass")
Use unit mass to subtract `g(x_0)` inside the convolution.  Split into a near
region controlled by continuity and a far Gaussian tail controlled by
boundedness.
:::



:::definition "parabolic.pointwise_initial_value_solution" (parent := "parabolic.classical") (lean := "HeatEquation.IsPointwiseInitialValueSolution") (uses := "parabolic.heat_ivp")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A pointwise solution of the forced heat Cauchy problem has the time and
spatial differentiability needed to interpret every derivative in the
equation, satisfies the forced residual at positive time, takes the assigned
value at time zero, and converges locally uniformly to that datum as time
decreases to zero.
:::



:::theorem "parabolic.initial_convolution_solution" (parent := "parabolic.classical") (lean := "HeatEquation.initialValueSolution_isPointwiseHomogeneousInitialValueSolution") (uses := "parabolic.initial_convolution, parabolic.pointwise_initial_value_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "47-48"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For bounded continuous initial data, the convolution formula simultaneously
satisfies

$$`
  u(x,t)=(\Gamma_n(\cdot,t)*g)(x),\qquad
  \partial_tu-\Delta u=0\quad(t>0),\qquad
  u(\,\cdot\,,t)\longrightarrow g
`

locally uniformly as $`t\downarrow0`. The conclusion is bundled as a
pointwise-solution structure containing the required derivative hypotheses,
the residual equation, the assigned value at zero, and the locally uniform
trace.
:::

:::proof "parabolic.initial_convolution_solution" (uses := "parabolic.initial_convolution_residual, parabolic.initial_convolution_trace")
Combine the positive-time differentiability and residual theorems with the
locally uniform initial-trace theorem.
:::

Positivity of the kernel has a qualitative consequence beyond the
$`L^\infty` bound. Because $`\Gamma_n(\cdot,t)>0` everywhere for $`t>0`, a
nonnegative datum that is positive at one point contributes a strictly
positive amount to the convolution at every spatial point, however far that
point lies from where the datum is positive.

:::theorem "parabolic.infinite_propagation" (parent := "parabolic.classical") (lean := "HeatEquation.initialValueSolution_pos_of_nonneg_of_exists_pos") (uses := "parabolic.initial_convolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "48-49"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If the initial datum is continuous and bounded, is nonnegative everywhere,
and is strictly positive at some point, then

$$`
  g\geq0,\quad g(x_0)>0
  \quad\Longrightarrow\quad
  (\Gamma_n(\cdot,t)*g)(x)>0
  \quad\text{for every }x\in\mathbb R^n,\ t>0.
`

Thus the heat-kernel evolution is immediately positive at every spatial
point, even when the initial positivity is localized.
:::

:::proof "parabolic.infinite_propagation" (uses := "parabolic.heat_kernel")
Continuity gives a ball on which the datum has a uniform positive lower bound.
At a fixed positive time the Gaussian has a positive lower bound on that
ball, so the convolution has a strictly positive contribution there; the
remaining integrand is nonnegative.
:::
