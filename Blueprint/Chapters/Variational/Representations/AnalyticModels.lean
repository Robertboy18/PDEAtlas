/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.Fourier
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Noncharacteristic
import PDE.Hyperbolic.Models.Transport.AnalyticTranslation
import PDE.Analytic.CauchyKovalevskaya.Solution.TimeDependent
import PDE.Cauchy.Hypersurface.Existence
import PDE.Cauchy.Hypersurface.Uniqueness

/-!
# Analytic model methods

The implicit-function theorem constructs noncharacteristic initial surfaces.
Convergent power series construct coupled analytic evolution and scalar solutions
with prescribed normal data on analytic hypersurfaces; translation gives explicit
solutions for constant-coefficient transport.
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
#doc (Manual) "Analytic Model Methods" =>

# Power-series and analytic model methods

Power-series methods build a solution from its Taylor coefficients, and the
first requirement is that the equation determine the normal derivative of
the unknown on the initial surface. For a first-order scalar equation
$`F(t,x,z,p)=0`, with $`z` standing for the value of $`u` and $`p` for its
derivative normal to the flat surface $`\{t=0\}`, that determination is an
implicit-function problem in the single variable $`p`. Once a system is in
normal form, the coupled analytic evolution theorem solves it.

:::definition "methods.power_series.noncharacteristic" (parent := "methods.representations") (lean := "NonlinearFirstOrder.IsNoncharacteristicInP")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "232-237"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
An equation $`F(t,x,z,p)=0` is noncharacteristic in $`p` at
$`(t_0,x_0,z_0,p_0)` when

$$`
p\longmapsto F(t_0,x_0,z_0,p)\ \text{is differentiable at }p_0,
\qquad
\partial_pF(t_0,x_0,z_0,p_0)\neq0.
`

This is the scalar implicit-function condition for the flat surface
$`\{t=0\}`.
:::

Nonvanishing of $`\partial_pF` at a point is precisely the invertibility
hypothesis of the implicit-function theorem for the map
$`(x,p)\mapsto F(0,x,g(x),p)`, once the initial datum $`g` is substituted
for $`z`. The step determines only the first normal derivative. Cauchy–Kovalevskaya goes further,
solving a recurrence for all higher normal derivatives and summing the
resulting power series.

:::theorem "methods.power_series.implicit_surface" (parent := "methods.representations") (lean := "NonlinearFirstOrder.IsNoncharacteristicInP.exists_local_implicitFunction") (uses := "methods.power_series.noncharacteristic")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "232-237"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`F(0,x_0,g(x_0),p_0)=0`, the derivative in $`p` is nonzero
there, and the composite $`(x,p)\mapsto F(0,x,g(x),p)` has positive
regularity order $`k` at $`(x_0,p_0)`. Then an open neighborhood of
$`x_0` carries a graph $`p=p(x)` with

$$`
F(0,x,g(x),p(x))=0
`

throughout that neighborhood, $`p(x_0)=p_0`, and the same regularity order
at $`x_0`. The theorem covers finite, smooth, and analytic orders. Choosing
Mathlib's analytic order $`\omega` gives the analytic initial graph.
:::

:::proof "methods.power_series.implicit_surface"
The scalar nonzero derivative gives the invertible partial derivative
required by Mathlib's implicit-function theorem. Apply it to the composite
at order $`k`. Its graph preserves the level $`F(0,x_0,g(x_0),p_0)`,
which is zero by the base equation, and passes through the prescribed point.
:::

## Coupled analytic evolution

Once the equation is solved for its time derivative, the remaining problem
is convergence: the PDE recursively determines Taylor coefficients, but a
formal series need not define a function. The analytic evolution construction
bounds those coefficients by a convergent majorant, sums them, and identifies
the derivatives of the sum with the original equation. Evans develops this
analytic Cauchy theory in §4.6.3.

:::theorem "methods.power_series.analytic_evolution" (parent := "methods.representations") (lean := "PDE.Analytic.CauchyKovalevskaya.exists_analytic_solution, PDE.Analytic.CauchyKovalevskaya.exists_analytic_solution_time_dependent")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "240"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    }
  ]
}
%%%
Let $`d,m\in\mathbb N`. Suppose $`g:\mathbb R^d\to\mathbb R^m` is
analytic near $`0`, and every coefficient $`B_{jik}(t,z,x)` and $`c_i(t,z,x)`
is analytic near $`(0,g(0),0)`. There are $`r>0` and an analytic field $`u`
on the coordinate ball $`\|(t,x)\|_\infty<r` such that

$$`
\partial_tu_i(t,x)=\sum_{j=1}^d\sum_{k=1}^m
 B_{jik}(t,u(t,x),x)\,\partial_{x_j}u_k(t,x)+c_i(t,u(t,x),x),
\qquad u(0,x)=g(x).
`

The initial equality holds for every $`\|x\|_\infty<r`. The dimensions may
be zero. The time-independent coefficient version is stated separately at the
center $`(g(0),0)`.
:::

:::proof "methods.power_series.analytic_evolution"
Subtract $`g(x)` from the unknown. Analyticity of $`g` and its spatial
derivatives makes the transformed coefficients analytic and reduces the
initial trace to zero. A majorant bounds the recursively constructed formal
solution and gives a positive convergence radius. Compatibility of power
series with products, substitution, and differentiation proves the PDE for
the sum. Restoring $`g` gives the original equation and trace. To include
explicit time dependence, adjoin a clock component with derivative one and
zero initial value; analytic uniqueness identifies it with $`t`.
:::

:::theorem "methods.power_series.analytic_uniqueness" (parent := "methods.representations") (lean := "PDE.Analytic.CauchyKovalevskaya.eventuallyEq_of_analytic_solutions, PDE.Analytic.CauchyKovalevskaya.eventuallyEq_of_analytic_solutions_time_dependent") (uses := "methods.power_series.analytic_evolution")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "240"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    }
  ]
}
%%%
Under the same analytic coefficient and data hypotheses, two fields analytic
near $`(0,0)` that satisfy the equation there and have initial trace $`g`
near $`0` agree on a neighborhood of $`(0,0)`. This is uniqueness of analytic
germs at $`(0,0)`, and the neighborhood depends on the two solutions.
:::

:::proof "methods.power_series.analytic_uniqueness"
After subtracting the initial function, the recurrence determines every
Taylor coefficient of either solution. Analytic functions with the same
Taylor series agree near their center. Adjoining the clock reduces the
explicitly time-dependent case to the same argument.
:::

## Prescribed normal data on an analytic hypersurface

For a scalar equation of order $`m`, the Cauchy data prescribe $`m` normal
derivatives. The normal is held fixed at each evaluation point:

$$`
D_\nu^j u(x)=D^j u(x)[\nu(x),\ldots,\nu(x)]
=\left.\frac{d^j}{dt^j}u(x+t\nu(x))\right|_{t=0}.
`

Thus derivatives of the normal field itself do not enter the datum.
Expanding this tensor in coordinates includes the usual mixed-partial
multiplicities, while the coefficients of the differential equation retain
their original normalization.

:::theorem "methods.power_series.analytic_hypersurface" (parent := "methods.representations") (lean := "PDE.Cauchy.Quasilinear.Analytic.exists_analytic_solution_of_normal_data, PDE.Cauchy.Quasilinear.Analytic.eventuallyEq_of_analytic_solution_of_normal_data") (uses := "methods.power_series.analytic_evolution, methods.power_series.analytic_uniqueness")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "233"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    },
    {
      page := "240"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 23, endLine := 28 }
    }
  ]
}
%%%
Let $`n,m\ge1`, let $`p\in\Omega` with $`\Omega` open, and suppose
$`\varphi` is analytic near $`p`, $`\varphi(p)=0`, and
$`\nabla\varphi(p)\ne0`. Let $`g_0,\ldots,g_{m-1}` be analytic near
$`p`; their restrictions to $`\Gamma=\{\varphi=0\}` are the prescribed
data. Use the unit normal $`\nu=\nabla\varphi/|\nabla\varphi|`.
Consider the scalar equation

$$`
\sum_{|\alpha|=m}a_\alpha(x,J_{<m}u(x))\,\partial^\alpha u(x)
=b(x,J_{<m}u(x)).
`

Here $`J_{<m}u` records all derivatives below order $`m`. Let $`q_0` be
the lower jet at $`p` determined by the prescribed data. Assume the coefficient
germs are analytic at $`(p,q_0)` and
$`\sum_{|\alpha|=m}a_\alpha(p,q_0)\nu(p)^\alpha\ne0`.
Then some ball $`B(p,r)\subseteq\Omega`, $`r>0`, carries an analytic
solution of the equation with $`D_\nu^j u=g_j` on $`\Gamma\cap B(p,r)`
for every $`j<m`. Two analytic solution germs with the same normal data
agree near $`p`.
:::

:::proof "methods.power_series.analytic_hypersurface"
Construct an analytic level chart and interpolate the individual normal data
to an analytic function. These constructions determine the lower jet, so
a compatible extension of the data need not be given. The nonzero principal
symbol lets the transformed equation solve for its highest transverse
derivative. Reduction to analytic evolution gives a local solution, which
is pulled back through the chart. Tangential differentiation of equal normal
data recovers the full lower jet, and analytic uniqueness gives germ equality.
:::

## An explicit transport model

For constant-coefficient transport, translation provides a closed formula.
Its analyticity, slice derivatives, initial trace, and residual can all be
checked directly, illustrating the evolution theorem without a power-series
construction.

:::definition "methods.power_series.transport_problem" (parent := "methods.representations") (lean := "TransportEquation.translatedTransportProfile, TransportEquation.transportResidual1D, TransportEquation.SolvesTransportIVP1D")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "239-244"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the one-dimensional Cauchy problem $`u_t-cu_x=0`, $`u(0,x)=g(x)`, the
translated profile is $`u(t,x)=g(x+ct)`. The solution predicate records
differentiability of each time and space slice, the pointwise identity
$`u(0,x)=g(x)`, and vanishing of the residual for all $`t,x\in\mathbb R`.
The slice hypotheses make the residual a sum of true partial derivatives.
:::

For $`u_t-v\cdot\nabla u=0` the characteristics are the lines along which
$`x+tv` is constant, so $`g(x+tv)` gives an explicit solution with datum $`g`.
The differential identity needs only differentiability of $`g`; analyticity
is used for the joint analyticity of the solution.

:::theorem "methods.power_series.transport_multidimensional" (parent := "methods.representations") (lean := "TransportEquation.analyticAt_translation, TransportEquation.translation_transport_residual_eq_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "239-244"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For any $`n\in\mathbb N`, a constant velocity $`v\in\mathbb R^n`, and initial
datum $`g:\mathbb R^n\to\mathbb R` real-analytic at every point, the translated profile

$$`u(t,x)=g(x+t v)`

is jointly analytic, has initial trace $`g`, and satisfies
$`u_t-v\mathbin{\cdot}\nabla u=0` on all of spacetime.
:::

:::proof "methods.power_series.transport_multidimensional" (uses := "hyperbolic.transport.characteristic_solution")
Analyticity is preserved by composition with the affine characteristic map.
The ordinary transport formula supplies the coordinate residual, with the
velocity sign chosen to match $`u_t-v\cdot\nabla u=0`.
:::

In one dimension this is $`u(t,x)=g(x+ct)`.

:::theorem "methods.power_series.transport_model" (parent := "methods.representations") (lean := "TransportEquation.analytic_translatedTransportProfile_solves_transportIVP") (uses := "methods.power_series.transport_problem, methods.power_series.transport_multidimensional")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "239-244"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For analytic one-dimensional initial data, the translated profile

$$`
u(t,x)=g(x+ct)
`

is jointly analytic and satisfies

$$`
u_t-cu_x=0,\qquad u(0,x)=g(x).
`
:::

:::proof "methods.power_series.transport_model"
The affine map $`(t,x)\mapsto x+ct` is analytic, so composition with analytic
$`g` is jointly analytic. The chain rule gives
$`u_t=c\,g'(x+ct)` and $`u_x=g'(x+ct)`, hence
$`u_t-cu_x=0`. At $`t=0`, the translated argument is $`x`, so the initial
trace is exactly $`g`.
:::
