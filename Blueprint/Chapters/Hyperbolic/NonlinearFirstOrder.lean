/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws
import PDE.Analysis.ODE.FirstVariation
import PDE.Analysis.ODE.SmoothDependence
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticCharacteristicFlow
import PDE.Analysis.ODE.SmoothDependence.InitialData
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.CharacteristicFamily
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.SmoothConstruction
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticInverseCoordinates
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Transport
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.ImplicitFunction
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.ClassicalSolution

import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.CompleteIntegral.Clairaut

/-!
# Nonlinear first-order equations

Characteristics and first-variation tools for nonlinear equations.
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
#doc (Manual) "Characteristics and Local Existence" =>

Evans §3.2 (pp. 96–108) derives the characteristic system, compatibility
and noncharacteristic conditions, local characteristic coordinates, and the
local-existence argument for
$`F(Du,u,x)=0`. Here we track how the characteristic flow changes with its
initial data. Its first variation satisfies a linear ODE, and estimates for
that ODE identify the derivative of the flow. This is the differentiability
needed to invert characteristic coordinates and recover a classical solution.

:::group "hyperbolic.first_order"
Nonlinear first-order equations
:::

# Characteristic Equations and Compatible Data

The characteristic system evolves the spatial point, the candidate gradient,
and the value of the solution in one phase space. A classical solution induces
this system, while the converse construction needs compatible boundary data
and a noncharacteristic initial surface.

:::definition "hyperbolic.first_order.characteristic_system" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.characteristicVectorField")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "97-98"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a phase-space state $`q=(p,z,x)`, the characteristic vector field is

$$`
\mathcal V_F(q)=
\left(-D_xF(q)-F_z(q)p,\;D_pF(q)\mathbin{\cdot}p,\;D_pF(q)\right).
`

Thus an integral curve $`q(s)` solves Evans's three equations (11) as one
autonomous ODE. The field is defined on all of phase space; the PDE
constraint and compatibility of the initial data are imposed separately.
:::

The field is chosen so that the graph of a classical solution is invariant
under its flow: along a curve in the base moving with velocity $`D_pF`, the
values and gradients of a
$`C^2` solution obey exactly these equations.

:::theorem "hyperbolic.first_order.characteristics_local" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.characteristic_equations_at") (uses := "hyperbolic.first_order.characteristic_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "97-99"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a $`C^1` phase-space Hamiltonian, if a $`C^2` solution satisfies the
equation on an open set, then at every parameter value where a characteristic
lies in that set its position,
gradient, and value satisfy Evans's characteristic ODE identities.
:::

:::proof "hyperbolic.first_order.characteristics_local"
Differentiate $`x(s)`, $`z(s)=u(x(s))`, and
$`p(s)=Du(x(s))` along a curve with velocity $`D_pF`. The chain rule gives
the equations for $`x` and $`z`; differentiating
$`F(Du,u,x)=0` in the spatial directions and substituting the Hessian term
gives the equation for $`p`.
:::

Conversely, a characteristic triple need not come from a solution. What
survives is the constraint: $`F` is a first integral of the characteristic
field, so the hypersurface $`F=0` is invariant under its flow.

:::theorem "hyperbolic.first_order.constraint_preserved" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.deriv_residual_along_characteristic_eq_zero") (uses := "hyperbolic.first_order.characteristic_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "98"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

At a point where the phase-space Hamiltonian is differentiable, every
differentiable characteristic triple $`q(s)=(p(s),z(s),x(s))` satisfies

$$`
\frac d{ds}F(p(s),z(s),x(s))=0.
`

The theorem is pointwise. If these hypotheses hold on an open interval containing zero, then
$`F(q(s))=F(q(0))` there by the mean value theorem, so compatible initial data with
$`F(q(0))=0` stay on the constraint hypersurface. For a continuously differentiable
Hamiltonian, the interval form holds for every characteristic curve; see the automatic flow below.
:::

:::proof "hyperbolic.first_order.constraint_preserved"
Apply the chain rule to $`F(p(s),z(s),x(s))` and substitute the three
characteristic equations. The $`D_xF`, $`F_zp`, and $`D_pF` contributions
cancel pairwise, so the derivative is zero and the residual is constant.
:::

Starting characteristics from boundary data requires an initial gradient,
which the data alone do not determine: the trace prescribes only the
tangential components of $`Du`, and the equation itself supplies one more
scalar relation. Compatibility records both requirements.

:::definition "hyperbolic.first_order.compatible_gradient" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.IsCompatibleInitialGradientAt") (uses := "hyperbolic.first_order.characteristic_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "103-104"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a parametrized initial surface $`x_0(y)` and prescribed trace $`g(y)`, a
candidate initial gradient $`p_0` is compatible at $`y_0` when

$$`
F(p_0,g(y_0),x_0(y_0))=0,
\qquad
Dg(y_0)[\eta]=p_0\mathbin{\cdot}Dx_0(y_0)[\eta]
`

for every tangent parameter $`\eta`. This is the coordinate-free form of
Evans's compatibility conditions (29)–(30).
:::

A classical solution automatically satisfies them, which shows that
compatibility is a necessary condition rather than an artificial one.

:::theorem "hyperbolic.first_order.compatibility" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.isCompatibleInitialGradientAt_of_classical_trace") (uses := "hyperbolic.first_order.compatible_gradient")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "103-104"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Suppose $`x_0` is differentiable at $`y_0`, $`u` is differentiable at
$`x_0(y_0)`, the trace identity $`u(x_0(y))=g(y)` holds near $`y_0`, and
the classical PDE holds at $`x_0(y_0)`. With $`p_0=Du(x_0(y_0))`, the chain
rule and the PDE give

$$`
F(p_0,g(y_0),x_0(y_0))=0,\qquad
Dg(y_0)[\eta]=p_0\cdot Dx_0(y_0)[\eta].
`

The converse direction, solving for a
compatible gradient field from boundary data, uses the implicit function
theorem in {bpref "hyperbolic.first_order.local_existence_from_c2_family"}[].
:::

:::proof "hyperbolic.first_order.compatibility"
Evaluate the PDE at $`x_0(y_0)` to obtain the residual equation. Then
differentiate the trace identity $`u\circ x_0=g` at $`y_0`; the chain rule
identifies its derivative with
$`Du(x_0(y_0))\circ Dx_0(y_0)`, which is the tangential compatibility
condition.
:::

Compatibility fixes the initial phase state, but for the characteristics
leaving the surface to fill a neighborhood, the characteristic direction must
be transversal to it. That transversality is the noncharacteristic condition,
formulated as invertibility of the linear map that later turns out to be the
initial Jacobian of the spatial characteristic map.

:::definition "hyperbolic.first_order.noncharacteristic" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.characteristicInitialDerivative, NonlinearFirstOrder.IsNoncharacteristicAt") (uses := "hyperbolic.first_order.characteristic_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "104-105"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

At a parametrized initial surface, the boundary-tangent directions together
with the characteristic direction $`D_pF` define an invertible linear map
onto the ambient space. In coordinates this is Evans's determinant
condition (36).
:::

# Constructing Characteristic Families

Picard–Lindelöf constructs the phase-space trajectories and continuous
dependence supplies a common family over nearby boundary parameters.
Constraint preservation then keeps compatible initial states on the
hypersurface $`F=0`.

:::theorem "hyperbolic.first_order.automatic_flow" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_characteristic_flow") (uses := "hyperbolic.first_order.characteristic_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "104-106"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

If the uncurried Hamiltonian is $`C^2`, Picard–Lindelöf constructs, through
every phase-space state $`q_0`, a local curve satisfying

$$`
q(0)=q_0,\qquad q'(s)=\mathcal V_F(q(s)).
`
:::

:::proof "hyperbolic.first_order.automatic_flow"
The $`C^2` Hamiltonian makes the characteristic vector field continuously
differentiable and therefore locally Lipschitz. Picard–Lindelöf supplies a
unique local integral curve through $`q_0`, with the initial condition and
ODE identities built into the resulting flow.
:::

A single trajectory is not enough; the construction needs the trajectories
through all boundary states near $`y_0` on a common time interval, jointly
continuous in the parameter. Continuous dependence on initial conditions
supplies precisely this.

:::theorem "hyperbolic.first_order.automatic_family" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_characteristic_family, NonlinearFirstOrder.characteristic_equations_of_hasDerivAt, NonlinearFirstOrder.exists_local_evans_characteristics") (uses := "hyperbolic.first_order.automatic_flow")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "104-106"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Near any base parameter, a $`C^2` phase-space Hamiltonian and a $`C^1` boundary-state family
$`q_0(y)` give a family $`q(s,y)`, jointly continuous for short times, with

$$`
q(0,y)=q_0(y),\qquad
\partial_sq(s,y)=\mathcal V_F(q(s,y)).
`

Projecting to components gives Evans's three equations for $`p`, $`z`, and
$`x`. The initial states need not be compatible.
:::

:::proof "hyperbolic.first_order.automatic_family"
Apply local existence with continuous dependence to the initial states
$`q_0(y)` near the base parameter, shrinking to one common time interval.
The resulting flow composed with $`q_0` is jointly continuous, and its time
derivative is the characteristic vector field; projecting to the three
components gives Evans's equations.
:::

Adding compatibility of the initial gradients on a neighborhood, the first
integral $`F` vanishes at the start of every characteristic in the family, and
its invariance keeps the whole family on the constraint hypersurface.

:::theorem "hyperbolic.first_order.automatic_constraint_family" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_characteristics_preserving_residual") (uses := "hyperbolic.first_order.automatic_family, hyperbolic.first_order.compatible_gradient, hyperbolic.first_order.constraint_preserved")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "104-106"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Retain the $`C^2` Hamiltonian and $`C^1` boundary-state hypotheses, and
suppose the initial gradient is compatible with the boundary data throughout
a neighborhood of the base parameter. Then there is a continuous family of
characteristics that starts from the prescribed phase states, solves the full
characteristic vector-field ODE, and satisfies

$$`F(p(s),z(s),x(s))=0`

at every point of the local flow.
:::

:::proof "hyperbolic.first_order.automatic_constraint_family" (uses := "hyperbolic.first_order.constraint_preserved")
Construct the common local characteristic family, shrink its parameter set so
the compatibility condition holds everywhere, and apply uniqueness for the
scalar ODE satisfied by the residual along each characteristic.
:::

# First Variation and Smooth Dependence

Local inverse coordinates require derivatives with respect to the initial
state. The first-variation equation computes the candidate derivative, while
a quantitative smooth-dependence theorem identifies that candidate with the
Fréchet derivative of the selected flow.

:::theorem "hyperbolic.first_order.general_first_variation" (parent := "hyperbolic.first_order") (lean := "PDE.Analysis.ODE.exists_local_firstVariation_family")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a $`C^2` autonomous vector field on a complete normed space, there is a
common local time interval on which nearby initial states generate continuous
trajectories together with continuous variational operators. The trajectories
solve

$$`q'=v(q),`

and the operators start at the identity and solve

$$`J'=Dv(q)\circ J.`
:::

:::proof "hyperbolic.first_order.general_first_variation"
Solve one autonomous ODE on the product of the state space and the space of
continuous linear operators, with vector field
$`(q,J)\mapsto(v(q),Dv(q)\circ J)`. Local ODE theory gives a common family
starting from $`(q_0,I)`, and projection yields the trajectory and
variational equations.
:::

For boundary data $`i(y)`, the characteristic family is
$`\gamma(y,t)=\Phi(i(y),t)`. Its boundary derivative is
$`D_y\gamma=D_q\Phi\circ Di(y)`. The initial derivative $`Di(y)` stays fixed
when time varies, so the variational equation for $`D_q\Phi` also gives the
time derivative of $`D_y\gamma`. Only one derivative of $`i` is needed.

:::theorem "hyperbolic.first_order.automatic_first_variation" (parent := "hyperbolic.first_order") (lean := "PDE.Analysis.ODE.exists_local_contDiff_one_family_with_initialData") (uses := "hyperbolic.first_order.general_first_variation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`v` be a globally $`C^1` vector field on a finite-dimensional real
normed space, and let $`i` be a locally $`C^1` initial map from a real normed
parameter space. Near any parameter in its open domain, there is a jointly
$`C^1` family $`\gamma(y,t)` solving the ODE with $`\gamma(y,0)=i(y)`.
Its boundary derivative $`B(y,t)=D_y\gamma(y,t)` satisfies

$$`
\partial_t B(y,t)=Dv(\gamma(y,t))\circ B(y,t),\qquad B(y,0)=Di(y).
`

For characteristics, a globally $`C^2` Hamiltonian supplies the required
$`C^1` vector field. Compatibility is not needed here; it enters when the
PDE residual and the contact identity are propagated.
:::

:::proof "hyperbolic.first_order.automatic_first_variation" (uses := "hyperbolic.first_order.general_first_variation")
Construct the local $`C^1` flow together with its state derivative.
Compose the flow with $`i`. The chain rule identifies the boundary derivative
with the state derivative applied to $`Di(y)`; differentiating this expression
in time gives the variational equation.
:::

The identification of the variational operator with the Fréchet derivative
rests on estimates for the flow remainder.

:::theorem "hyperbolic.first_order.flow_smooth_dependence" (parent := "hyperbolic.first_order") (lean := "PDE.Analysis.ODE.hasFDerivAt_flow_of_firstVariation") (uses := "hyperbolic.first_order.general_first_variation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`\Phi(t,q_0)` be a local autonomous flow and let $`J` solve

$$`
\partial_tJ(t,q_0)=Dv(\Phi(t,q_0))\circ J(t,q_0),
\qquad J(0,q_0)=I.
`

Under explicit local Lipschitz control of $`\Phi`, a bound on $`Dv`, and a
quadratic Taylor-remainder estimate, the theorem identifies

$$`
D_{q_0}\Phi(t,q_0)=J(t,q_0).
`

The proof treats positive and negative time by Grönwall estimates. Applying it
to the automatic characteristic flow requires these quantitative hypotheses
on one common neighborhood.
:::

:::proof "hyperbolic.first_order.flow_smooth_dependence"
Compare the increment
$`\Phi(t,q_0+h)-\Phi(t,q_0)` with $`J(t,q_0)h`. Taylor's formula turns the
difference into an integral equation with a quadratic remainder. The local
Lipschitz and derivative bounds control that remainder, and Grönwall's
inequality makes it $`o(\lVert h\rVert)`, proving that $`J` is the Fréchet
derivative.
:::

# Inverse Characteristic Coordinates

At initial time, the derivative of the spatial characteristic map is exactly
the noncharacteristic linear map. The inverse function theorem therefore
turns boundary parameters and characteristic time into local spatial
coordinates once the family has the required differentiability.

For example, take $`u_x=0` in the plane. Data on
$`x=0` determine the local solution $`u(x,y)=g(y)`: the characteristic
direction $`(1,0)` and the initial-line tangent $`(0,1)` span the plane.
Data on $`y=0` behave differently. That line is itself characteristic;
compatibility forces the datum to be constant along it, and even a
compatible constant leaves the values on neighboring horizontal lines
undetermined. The noncharacteristic condition prevents exactly this
failure to fill a neighborhood with independent coordinates.

:::theorem "hyperbolic.first_order.local_characteristic_coordinates" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_inverse_coords_of_noncharacteristic") (uses := "hyperbolic.first_order.noncharacteristic")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-106"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`X(s,y)` be the spatial characteristic map, $`C^1` near $`(0,y_0)`. If
$`D_{(s,y)}X(0,y_0)` is the noncharacteristic initial isomorphism, the inverse
function theorem produces neighborhoods and a local inverse
$`\Psi=(S,Y)` satisfying

$$`
\Psi(X(s,y))=(s,y),\qquad
X(S(x),Y(x))=x.
`

Thus boundary parameters and characteristic time give local spatial coordinates. The formal
statement records only the second identity, near the image of the basepoint.
:::

:::proof "hyperbolic.first_order.local_characteristic_coordinates"
The assumed initial derivative is a continuous linear equivalence, and the
$`C^1` hypothesis supplies the neighborhood regularity. The Banach-space
inverse function theorem therefore restricts $`X` to mutually
inverse maps between neighborhoods of $`(0,y_0)` and $`X(0,y_0)`, giving the
coordinate functions $`S` and $`Y`.
:::

The inversion theorem assumes that the derivative at $`(0,y_0)` is the
noncharacteristic map. For a family that starts on the surface and follows the
characteristic ODE this is a computation rather than an assumption: the time
column is $`D_pF` and the parameter columns are $`Dx_0`.

:::theorem "hyperbolic.first_order.automatic_initial_jacobian" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.hasFDerivAt_characteristicPosition_initial") (uses := "hyperbolic.first_order.characteristic_system, hyperbolic.first_order.automatic_family")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-106"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a differentiable phase-space Hamiltonian and a $`C^1` characteristic
family with the prescribed initial phase trace, in particular
$`X(0,y)=x_0(y)`, the initial Jacobian is

$$`
D_{(s,y)}X(0,y_0)[\tau,\eta]
=\tau\,D_pF(p_0,g(y_0),x_0(y_0))
+Dx_0(y_0)[\eta].
`

The right side is Evans's noncharacteristic linear map. The identity holds
without the noncharacteristic condition, which is needed only for
invertibility.
:::

:::proof "hyperbolic.first_order.automatic_initial_jacobian"
Differentiate $`X` separately in characteristic time and in the boundary
parameter. The characteristic ODE gives the time column $`D_pF`, while the
initial identity $`X(0,y)=x_0(y)` gives the tangential columns $`Dx_0`.
Linearity of the total derivative combines them into the displayed map.
:::

Substituting the computed Jacobian into the inversion theorem removes its
separately supplied derivative hypothesis.

:::theorem "hyperbolic.first_order.automatic_local_coordinates" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_inverse_coords_of_characteristic_family") (uses := "hyperbolic.first_order.noncharacteristic, hyperbolic.first_order.local_characteristic_coordinates, hyperbolic.first_order.automatic_initial_jacobian")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-106"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a differentiable phase-space Hamiltonian, a $`C^1` characteristic family
with the prescribed initial trace and ODE has local inverse coordinates at a
noncharacteristic basepoint, which the position map sends back to each nearby point:

$$`
\det D_{(s,y)}X(0,y_0)\ne0
\Longrightarrow
(s,y)\longleftrightarrow x=X(s,y)
\quad\text{locally}.
`

Applying this theorem to the continuous Picard–Lindelöf family requires the
smooth-dependence input that supplies its $`C^1` family hypothesis.
:::

:::proof "hyperbolic.first_order.automatic_local_coordinates"
The initial-Jacobian identity identifies $`DX(0,y_0)` with the
noncharacteristic map. Since that map is invertible, the local inverse
function theorem applies to the characteristic position map and produces the
claimed coordinate neighborhoods and inverse.
:::

# Contact Preservation and the Local Solution

The contact identity says that the differential of the transported value is
represented by the transported momentum. Once it is preserved along the
flow, inverse characteristic coordinates define the spatial function
$`u=z\circ x^{-1}` and identify its gradient with $`p`.

:::definition "hyperbolic.first_order.local_flow_box" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.LocalCharacteristicFlow") (uses := "hyperbolic.first_order.characteristic_system")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A regular local flow box consists of $`C^1` maps $`(p,z,x)(s,y)` satisfying

$$`
\dot x=D_pF,\qquad
\dot z=D_pF\cdot p,\qquad
\dot p=-D_xF-F_zp,
`

their prescribed initial traces, and the homogeneous first-variation equation
for the contact defect
$`C=\partial_yz-p\cdot\partial_yx`. A uniform local bound on $`F_z` records
the coefficient control used by ODE uniqueness. The structure collects
hypotheses; a constructor builds one from a $`C^1` characteristic family.
:::

The contact equation follows by differentiating the defect in time. The
boundary derivative supplied by the ODE construction satisfies the
variational equation, so this step needs only a $`C^1` family. Differentiating
the preserved residual $`F=0` in a boundary direction cancels the remaining
terms and gives $`C'=-F_z C`.

:::definition "hyperbolic.first_order.local_flow_box_from_c2_family" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.LocalCharacteristicFlow.ofContDiffOneCharacteristicFamily") (uses := "hyperbolic.first_order.local_flow_box, hyperbolic.first_order.compatible_gradient, hyperbolic.first_order.constraint_preserved")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a globally $`C^2` Hamiltonian, a $`C^1` characteristic family with the
prescribed initial trace, compatible initial gradients, and a local bound on
$`F_z` determines a regular flow box, provided its boundary derivative
satisfies the variational equation. The constructor derives the component
equations and the contact evolution from these hypotheses.
:::

The contact defect measures the failure of $`p` to represent the differential
of $`z` in the boundary directions. Compatibility makes it vanish at $`s=0`,
and its homogeneous linear evolution forces it to vanish for all
characteristic times; this is the step that turns the transported momentum
into a gradient.

:::theorem "hyperbolic.first_order.contact_preservation" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.LocalCharacteristicFlow.contactDefect_eq_zero") (uses := "hyperbolic.first_order.compatible_gradient, hyperbolic.first_order.local_flow_box")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "106-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a regular characteristic flow satisfying the first-variation equation,
the contact defect

$$`\partial_y z-p\cdot\partial_y x`

vanishes initially by compatibility and remains zero by uniqueness for its
homogeneous linear ODE. Combining the tangential and characteristic-time
directions proves that the differential of $`z` is the pullback of the
covector represented by $`p`.
:::

:::proof "hyperbolic.first_order.contact_preservation"
Compatibility makes the contact defect zero at initial time. Its
first-variation equation is a homogeneous scalar linear ODE with locally
bounded coefficient, so uniqueness forces it to remain zero. Together with
the characteristic-time identity, this identifies every derivative of $`z`
with pairing against $`p` through the derivative of $`x`.
:::

Evans's construction combines three ingredients: inverse
characteristic coordinates from the noncharacteristic condition, $`Du=p` from
contact preservation, and $`F(Du,u,x)=0` from constraint preservation.

:::theorem "hyperbolic.first_order.local_existence" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_classicalSolution_of_characteristicFlow") (uses := "hyperbolic.first_order.constraint_preserved, hyperbolic.first_order.noncharacteristic, hyperbolic.first_order.automatic_local_coordinates, hyperbolic.first_order.contact_preservation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "105-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For a $`C^1` phase-space Hamiltonian, given compatible boundary gradients,
a noncharacteristic basepoint, and a regular characteristic flow, there are
open neighborhoods of the boundary parameter and boundary point and a $`C^2`
function $`u` that satisfies

$$`F(Du,u,x)=0`

on the spatial neighborhood and has the prescribed boundary trace. Local
invertibility, $`Du=p`, and the PDE residual are all derived from
noncharacteristicity and the characteristic and first-variation equations.
:::

:::proof "hyperbolic.first_order.local_existence"
Invert the spatial characteristic map near the noncharacteristic basepoint
and define $`u(x)=z(S(x),Y(x))`. Contact preservation and the inverse-map
identity give $`Du=p`; residual preservation then yields
$`F(Du,u,x)=0`. Restricting to the initial surface recovers the prescribed
trace. The momentum in inverse coordinates is $`C^1`, so $`Du` is $`C^1`
and $`u` is $`C^2`.
:::

The local existence theorem takes a flow box as input. To construct it from
boundary data, first solve the compatibility equations for the momentum by the
implicit function theorem; $`C^2` boundary and value data give a $`C^1`
momentum field. The $`C^1` flow and its variational equation then provide the
contact transport needed for the local $`C^2` solution.

:::theorem "hyperbolic.first_order.local_existence_from_c2_family" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_classicalSolution_of_contDiff_two_boundary_data") (uses := "hyperbolic.first_order.noncharacteristic, hyperbolic.first_order.local_flow_box_from_c2_family, hyperbolic.first_order.local_existence")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "104-108"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Assume $`F` is $`C^2` near the initial phase $`(p_0,g(y_0),b(y_0))`, the
boundary parametrization $`b` and values $`g` are $`C^2` on an open parameter
neighborhood of $`y_0`, and the base momentum $`p_0` satisfies

$$`
F(p_0,g(y_0),b(y_0))=0,\qquad
\langle p_0,Db(y_0)h\rangle=Dg(y_0)h.
`

Suppose the initial tangent/characteristic map at this state is invertible,
and $`b(y_0)` lies in the open ambient domain. Then some open spatial
neighborhood within that domain carries a $`C^2` classical solution of
$`F(Du,u,x)=0` with trace $`u(b(y))=g(y)` near $`y_0` and $`Du(b(y_0))=p_0`.
:::

:::proof "hyperbolic.first_order.local_existence_from_c2_family"
Choose a globally $`C^2` Hamiltonian $`G` agreeing with $`F` near the initial
phase. Its value and derivatives there preserve compatibility and
noncharacteristicity. For $`G`, the implicit function theorem constructs a
compatible $`C^1` momentum field through $`p_0`. Construct the $`C^1`
characteristic family and its first variation. Shrink the flow box
so its positions lie in the ambient domain and $`G_z` is bounded. Residual
preservation and the variational equation give contact transport; the
noncharacteristic map is the initial position derivative. The preceding
theorem supplies inverse coordinates and the local $`C^2` solution, with
base gradient $`p_0`. Continuity of $`(Du,u,x)` permits a smaller spatial
neighborhood on which $`G(Du,u,x)=F(Du,u,x)`. Restrict the boundary
neighborhood as well to retain the trace.
:::


# Complete integrals and stationary envelopes

A family of classical solutions can produce a new solution by selecting a
parameter at each spatial point. The chain rule explains the restriction on
that selection: for $`v(x)=u(x,\phi(x))`, the extra term is
$`D_a u(x,\phi(x))D\phi(x)`. Stationarity in the parameter makes it vanish.

:::definition "hyperbolic.first_order.complete_integral" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.IsCompleteIntegral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 3, complete integrals and envelopes"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
In positive spatial dimension $`n`, a complete integral is a jointly $`C^2`
family $`u(x,a)` on open spatial and parameter sets, with $`n` parameters,
whose members solve $`F(D_xu,u,x)=0` and whose parameter-to-jet derivative

$$`D_a(u,D_xu):\mathbb R^n\longrightarrow\mathbb R^{n+1}`

is injective at every point. This is rank $`n` of the first jet;
invertibility of $`D_a^2u` is a separate condition, used by the envelope
theorem.
:::

:::theorem "hyperbolic.first_order.stationary_envelope" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.exists_local_stationary_envelope, NonlinearFirstOrder.IsCompleteIntegral.exists_local_envelope") (uses := "hyperbolic.first_order.complete_integral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 3, complete integrals and envelopes"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
Let $`u(x,a)` be a jointly $`C^2` family of classical solutions on open
sets. At an interior base point $`(x_0,a_0)`, assume
$`D_a u(x_0,a_0)=0` and that $`D_a^2u(x_0,a_0)` is invertible. Then a
neighborhood $`V` of $`x_0` carries a $`C^1` selector $`\phi`, with
$`\phi(x_0)=a_0`, taking values in the parameter domain and satisfying

$$`
D_a u(x,\phi(x))=0,\qquad
v(x)=u(x,\phi(x)),\qquad Dv(x)=D_xu(x,\phi(x)).
`

The envelope $`v` is $`C^2` and solves $`F(Dv,v,x)=0` on $`V`. The
stationary parameter is locally unique near the base point. The general
result permits any finite number of parameters; complete integrals give a
special case.
:::

:::proof "hyperbolic.first_order.stationary_envelope"
Apply the implicit function theorem to $`D_a u=0`, using the actual
parameter Hessian as its invertible derivative. This constructs the local
$`C^1` selector and its local uniqueness. In the chain rule for $`v`,
stationarity cancels the parameter term. The remaining derivative
$`D_xu(x,\phi(x))` is $`C^1`, so $`v` is $`C^2`; substituting it into the
family's PDE proves the envelope equation.
:::

:::theorem "hyperbolic.first_order.clairaut_envelope" (parent := "hyperbolic.first_order") (lean := "NonlinearFirstOrder.clairautSolution_isCompleteIntegral, NonlinearFirstOrder.exists_clairaut_envelope") (uses := "hyperbolic.first_order.stationary_envelope")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 3, Clairaut equations"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
For $`f\in C^2(A)` on an open parameter set, the family
$`u(x,a)=a\cdot x+f(a)` is a complete integral of

$$`x\cdot Dv+f(Dv)=v.`

At $`a_0\in A` where $`D^2f(a_0)` is invertible, it has a local stationary
envelope near $`x_0=-\nabla f(a_0)`, with
$`x+\nabla f(\phi(x))=0` and $`Dv(x)=\phi(x)`.
:::

:::proof "hyperbolic.first_order.clairaut_envelope"
Each affine member has gradient $`a`, so it solves the equation and the
gradient component of the parameter-to-jet derivative is the identity.
This proves complete-integral rank even when the Hessian of $`f` is singular.
At a point with invertible Hessian, the stationary-envelope theorem applies
to $`x+\nabla f(a)=0` and constructs the claimed branch.
:::
