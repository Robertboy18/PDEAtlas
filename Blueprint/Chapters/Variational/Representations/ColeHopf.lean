/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.Similarity
import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf
import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Cauchy
import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Exponential
import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Stationary
import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.TwoExponential

/-!
# Cole–Hopf transformation

The heat-to-Burgers transformation, its construction for bounded continuous
initial data, and exact exponential and stationary examples.
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
#doc (Manual) "Cole–Hopf Transformation" =>

# Cole–Hopf: a nonlinear-to-linear transformation

## Why the Cole–Hopf transform works

The Cole–Hopf transform (Cole, 1951; Hopf, 1950; Evans, 2010, pp. 206–207)
sends a nonvanishing heat solution $`v` to the solution $`u=-2\nu v_x/v` of
viscous Burgers.

For the converse calculation, suppose $`\nu\ne0` and $`u` is a sufficiently
smooth Burgers solution on $`I\times\mathbb R`. The logarithmic derivative
determines $`v` only up to a time-dependent factor:

$$`
v(t,x)=a(t)\exp\!\Bigl(-\frac{1}{2\nu}\int_0^x u(t,s)\,ds\Bigr),
\qquad
\frac{a'(t)}{a(t)}=\frac{u(t,0)^2}{4\nu}-\frac{u_x(t,0)}2.
`

Choosing a nonzero $`a` satisfying this scalar equation makes $`v` solve
the heat equation. Fixing $`a=1` does not work in general: for $`\nu=1`
and $`u=-2` it gives $`e^x`, whereas $`e^{t+x}` is a heat solution with
the same Cole–Hopf quotient. We formalize the forward heat-to-Burgers
implication.

For that implication, suppose $`v\neq0` is $`C^3` and solves $`v_t=\nu v_{xx}`.
Define $`u=-2\nu v_x/v`. Then:

1. *First derivative.* Differentiating the quotient:
   $`u_x=-2\nu(v_{xx}/v-v_x^2/v^2)`.

2. *Second derivative.* Differentiating again in space:
   $`u_{xx}=-2\nu(v_{xxx}/v-3v_{xx}v_x/v^2+2v_x^3/v^3)`.

3. *Time derivative.* From $`v_t=\nu v_{xx}` and $`v_{xt}=\nu v_{xxx}`:
   $`u_t=-2\nu(v_{xt}/v-v_xv_t/v^2)=-2\nu(\nu v_{xxx}/v-\nu v_xv_{xx}/v^2)`.

4. *Assembly.* The nonlinear term $`uu_x` combines with $`u_t` and $`-\nu u_{xx}`:
   the common-denominator numerator cancels term by term, leaving
   $`u_t+uu_x-\nu u_{xx}=0`.

The formal proof has two layers: a jet-level polynomial cancellation that
holds algebraically, and an analytic domain theorem that supplies the
regularity (quotient rules, mixed-derivative commutation, nonvanishing of
$`v`) needed to justify each step.

:::definition "methods.cole_hopf.transform" (parent := "methods.representations") (lean := "BurgersEquation.ColeHopf.coleHopfTransform")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "206-208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a heat profile $`v`, the Cole–Hopf transform is

$$`
u=-2\nu\,\frac{v_x}{v}.
`

Division in Lean is total, so the theorems about the transform assume
separately that $`v` is nonzero on the domain under consideration.
:::

The cancellation that makes the transform work is purely algebraic and can be
isolated first: treat
$`v,v_x,v_{xx},v_{xxx},v_t,v_{xt}` at one point as six real numbers
$`a\neq0,b,c,d,e,f`, impose $`e=\nu c` and $`f=\nu d`, and check that the
quotient-rule expressions for $`u_t`, $`u_x`, and $`u_{xx}` satisfy the
Burgers identity.

:::theorem "methods.cole_hopf.jet" (parent := "methods.representations") (lean := "BurgersEquation.ColeHopf.coleHopf_jet_residual_eq_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "206-208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The algebraic jet identity isolates the exact cancellation: the heat equation
and its spatial derivative imply that the quotient-rule jets of the
Cole–Hopf transform satisfy

$$`
u_t+u\,u_x-\nu u_{xx}=0.
`
:::

:::proof "methods.cole_hopf.jet"
Differentiate $`u=-2\nu v_x/v` formally in $`t` and twice in $`x`, put all
terms over a common power of $`v`, and substitute $`v_t=\nu v_{xx}` together
with $`v_{xt}=\nu v_{xxx}`. The numerator then cancels term by term,
leaving zero. No analytic hypothesis enters at this level.
:::

Turning the jet identity into a theorem about functions requires that the
six jet values are the value and derivatives of $`v`, and that the quotient-rule
expressions give the derivatives of $`u=-2\nu v_x/v`. That is where
$`C^3` regularity, nonvanishing of $`v`, and openness of the domain enter,
since the quotient rule and the commutation $`v_{xt}=v_{tx}` are local
statements.

:::theorem "methods.cole_hopf.domain" (parent := "methods.representations") (lean := "BurgersEquation.ColeHopf.coleHopfTransform_solvesViscousBurgersOn") (uses := "methods.cole_hopf.transform")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "206-208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an arbitrary open spacetime domain, if $`v\in C^3`, $`v\neq0`, and

$$`
v_t=\nu v_{xx},
`

then $`u=-2\nu v_x/v` satisfies

$$`
u_t+u\,u_x=\nu u_{xx}.
`
:::

:::proof "methods.cole_hopf.domain" (uses := "methods.cole_hopf.jet")
The analytic hypotheses justify the quotient rules and commutation of mixed
partials. Differentiating the heat equation supplies the spatial derivative
identity, after which the jet-level polynomial and rational cancellation
closes the viscous Burgers residual.
:::

## Constructing the heat profile from the velocity

The domain theorem starts with a heat solution. For the Cauchy problem, the
input is instead a bounded continuous velocity $`u_0:\mathbb R\to\mathbb R`
and a positive viscosity $`\nu`. Integrating the logarithmic derivative
determines a positive initial potential:

$$`
P(y)=\exp\!\left(-\frac{1}{2\nu}\int_0^y u_0(s)\,ds\right).
`

Bounded velocity does not mean bounded potential: constant nonzero velocity
already gives an exponential. The construction must therefore justify the
Gaussian integral for this growing datum as well as its initial derivative.

:::theorem "methods.cole_hopf.cauchy" (parent := "methods.representations") (lean := "BurgersEquation.ColeHopf.exists_viscousBurgersCauchySolution, BurgersEquation.ColeHopf.cauchySolution_initial_trace, BurgersEquation.ColeHopf.cauchyPotential_eq_integral, BurgersEquation.ColeHopf.integrable_cauchyPotential_kernel") (uses := "methods.cole_hopf.domain")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 4 (Cole–Hopf transformation)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`\nu>0` and bounded continuous $`u_0`, the potential is

$$`
v(t,x)=\int_{\mathbb R}
\frac{e^{-(x-y)^2/(4\nu t)}}{\sqrt{4\pi\nu t}}\,P(y)\,dy,
\qquad t>0.
`

The integrand is integrable, and $`v` is positive and smooth at positive
time. Its Cole–Hopf transform $`u=-2\nu v_x/v` is a classical, jointly
$`C^2` solution of $`u_t+u u_x=\nu u_{xx}` there. At every $`x_0\in\mathbb R`,

$$`
\lim_{\substack{(t,x)\to(0,x_0)\\t>0}}u(t,x)=u_0(x_0).
`

The integral is formalized on the standard one-dimensional Euclidean space.
:::

:::proof "methods.cole_hopf.cauchy"
Set $`L=\|u_0\|_\infty/(2\nu)`. The primitive bound gives
$`0<P(y)\le e^{L|y|}`. Normalize it by $`e^{Ly}+e^{-Ly}` to obtain a
positive bounded continuous amplitude. Evolve this amplitude by the heat
kernel and apply the two opposite exponential tilts. Their sum is a positive
smooth heat solution; the Gaussian tilt identities prove both the displayed
integral formula and integrability. The domain theorem now gives the Burgers PDE.

Continuity of $`u_0` gives $`P'=-u_0P/(2\nu)`. The normalized amplitude
also has a bounded continuous derivative, so its heat evolution and spatial
derivative extend continuously to time zero. Undoing the tilts yields the
joint traces $`v\to P(x_0)` and $`v_x\to P'(x_0)`. Since $`P(x_0)>0`,
the quotient tends to $`-2\nu P'(x_0)/P(x_0)=u_0(x_0)`.
:::

## Exact profiles

The simplest heat profile to which the transform applies is $`v=e^{t+x}`,
for which $`v_t=v_x=v_{xx}=v` and the quotient collapses to the constant
$`-2` at unit viscosity. The quotient of $`e^x` is the same constant,
although $`e^x` does not solve the heat equation; in the forward direction
there is no such ambiguity, since the transform is a function of $`v`.

:::theorem "methods.cole_hopf.exponential_example" (parent := "methods.representations") (lean := "BurgersEquation.ColeHopf.coleHopfExpTransform_solves_unit_burgers") (uses := "methods.cole_hopf.transform")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "206-208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the heat solution $`v(t,x)=e^{t+x}` and unit viscosity, the Cole–Hopf
transform is the constant velocity $`u=-2`, which solves viscous Burgers on
all spacetime. Positivity of the exponential discharges the denominator
condition, while symbolic differentiation verifies the closed-form
transform identity.
:::

:::proof "methods.cole_hopf.exponential_example"
For $`v=e^{t+x}`, both $`v_t` and $`v_{xx}` equal $`v`, so $`v` solves the
unit heat equation and is everywhere positive. Also $`v_x=v`, hence the
Cole–Hopf quotient is $`-2v/v=-2`. All derivatives of this constant vanish,
so its Burgers residual is zero.
:::

A constant velocity does not exercise the nonlinear term. Adding the
reflected exponential $`e^{t-x}` keeps $`v` a positive heat solution, since
each summand solves the heat equation separately, but makes $`v_x/v`
$`x`-dependent: the velocity is $`-2\tanh x`, and it is stationary because
the common factor $`e^t` cancels in the quotient.

:::theorem "methods.cole_hopf.nonconstant_examples" (parent := "methods.representations") (lean := "BurgersEquation.ColeHopf.coleHopfTwoExpProfile_closed_residual_eq_zero, BurgersEquation.ColeHopf.coleHopfTwoExpHeat_analytic_residual_eq_zero, BurgersEquation.ColeHopf.coleHopfTwoExpTransform_eq_velocity, BurgersEquation.ColeHopf.coleHopfStationaryBurgers_closed_residual_eq_zero, BurgersEquation.ColeHopf.coleHopfStationaryBurgers_analytic_residual_eq_zero") (uses := "methods.cole_hopf.transform, methods.cole_hopf.domain")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "206-208"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The positive heat profile

$$`v(t,x)=e^{t+x}+e^{t-x}`

has zero heat residual, and its ordinary Cole–Hopf transform agrees
pointwise with

$$`
-2\,\frac{e^{t+x}-e^{t-x}}{e^{t+x}+e^{t-x}}.
`

The algebraically equivalent stationary velocity
$`-2+4/(1+e^{2x})` has zero unit-viscosity Burgers residual everywhere.
Positivity of the exponential denominators discharges the quotient side
conditions. In this stationary example, nonlinear advection and viscosity
balance each other while the time derivative vanishes.
:::

:::proof "methods.cole_hopf.nonconstant_examples"
Differentiate the two exponential summands separately; each solves the unit
heat equation, so their sum does as well and is strictly positive. Substituting
$`v_x=e^{t+x}-e^{t-x}` into $`-2v_x/v` gives the displayed velocity. Multiply
numerator and denominator by $`e^{x-t}` to obtain
$`-2+4/(1+e^{2x})`. Direct differentiation of this stationary expression,
followed by clearing its positive denominator, reduces the Burgers residual
to a polynomial identity that normalizes to zero.
:::
