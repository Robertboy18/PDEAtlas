/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.Compactness
import PDE.Fluid.Incompressible.Solenoidal

/-!
# Solenoidal spaces and weak pressure

The solenoidal kernel of an abstract divergence, its weak and Bochner closure,
the cubic cancellation of a skew convection form, and pressure recovery from a
closed-range divergence.
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
#doc (Manual) "Solenoidal Spaces and Weak Pressure" =>

:::group "fluid.solenoidal"
Solenoidal spaces and weak pressure
:::

# The divergence-free energy space

Let $`V` be a normed space of velocity fields, let $`Q` be a normed scalar
space, and let

$$`
D:V\longrightarrow Q
`

be a continuous linear divergence operator. The domain, boundary condition,
and Sobolev realization are left open.

:::definition "fluid.solenoidal_space" (parent := "fluid.solenoidal") (lean := "IncompressibleFlow.SolenoidalSpace, IncompressibleFlow.solenoidalInclusion, IncompressibleFlow.mem_solenoidalSpace_iff") (uses := "analysis.weak_compactness.linear_constraints")
%%%
source := {
  document := "temam-navier-stokes"
  spans := #[{
    page := "1-27"
    text := some { path := "Blueprint/Sources/TemamNavierStokes.md", startLine := 1, endLine := 12 }
  }]
}
%%%
The solenoidal energy space is the closed linear subspace

$$`
V_\sigma=\ker D=\{v\in V:Dv=0\}.
`

It comes with its canonical continuous inclusion $`V_\sigma\hookrightarrow
V`. Representing incompressibility as a kernel makes the constraint available
to the general theory of submodules, weak limits, and restricted forms.
:::

A continuous linear kernel is weakly closed, so weak limits preserve the
divergence-free constraint. This is the closure property needed when passing
from approximate solutions to a weak solution.

:::theorem "fluid.solenoidal_weak_closure" (parent := "fluid.solenoidal") (lean := "IncompressibleFlow.isClosed_solenoidalWeakSet, IncompressibleFlow.mem_solenoidalSpace_of_tendsto_weak, IncompressibleFlow.solenoidalWeakSet, IncompressibleFlow.toWeakSpace_mem_solenoidalWeakSet") (uses := "fluid.solenoidal_space, parabolic.bochner_linear_constraints")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "726"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 30, endLine := 33 }
  }]
}
%%%
The set $`V_\sigma` is closed in the weak topology of $`V`. Consequently, if

$$`
u_j\rightharpoonup u\quad\text{in }V
`

and $`Du_j=0` eventually, then $`Du=0`.
:::

:::proof "fluid.solenoidal_weak_closure" (uses := "parabolic.bochner_linear_constraints")
Regard $`D` as the one-member family of constraints in the abstract weak
constraint theorem. Its lifted weak-space kernel is closed, and every limit
of an eventually kernel-valued net lies in that kernel.
:::

Approximate solutions of an evolution problem are trajectories
$`u\in L^2(\mu;V)` rather than single vectors, and incompressibility is then
imposed only for almost every time. Composing with $`D` lifts the constraint to
a continuous linear map on Bochner $`L^2`, so the previous argument applies
verbatim once the almost-everywhere condition is identified with the kernel of
that lift.

:::theorem "fluid.solenoidal_bochner_limits" (parent := "fluid.solenoidal") (lean := "IncompressibleFlow.isCompact_inter_solenoidalTrajectoryWeakSet, IncompressibleFlow.isSolenoidalTrajectory_of_tendsto_weak, IncompressibleFlow.isClosed_solenoidalTrajectoryWeakSet, IncompressibleFlow.solenoidalTrajectoryWeakSet, IncompressibleFlow.toWeakSpace_mem_solenoidalTrajectoryWeakSet, IncompressibleFlow.IsSolenoidalTrajectory, IncompressibleFlow.isSolenoidalTrajectory_iff_ae, IncompressibleFlow.isSolenoidalTrajectory_iff_compLpL_eq_zero") (uses := "fluid.solenoidal_space, parabolic.bochner_linear_constraints")
%%%
source := {
  document := "temam-navier-stokes"
  spans := #[{
    page := "182-215"
    text := some { path := "Blueprint/Sources/TemamNavierStokes.md", startLine := 1, endLine := 12 }
  }]
}
%%%
For $`u\in L^2(\mu;V)`, almost-everywhere incompressibility,

$$`
Du(t)=0\quad\text{for almost every }t,
`

is equivalent to vanishing of the lifted continuous map
$`D_{L^2}:L^2(\mu;V)\to L^2(\mu;Q)`. Hence the solenoidal trajectory space is
weakly closed, and weak $`L^2` limits of eventually solenoidal trajectories
remain solenoidal. If additionally $`V` is a real Hilbert space, intersecting
this constraint set with any weakly closed, norm-bounded family is weakly
compact.
:::

:::proof "fluid.solenoidal_bochner_limits" (uses := "parabolic.bochner_linear_constraints")
The Bochner lift agrees almost everywhere with pointwise composition by
$`D`. Equality of Bochner classes identifies its kernel with
almost-everywhere vanishing, after which weak closedness of a continuous
linear kernel gives the limit theorem. The weak compactness theorem for
closed norm-bounded Hilbert-space families remains valid after intersecting
with this closed constraint set.
:::

# Convection on the constrained space

For smooth fields on a domain where the boundary flux vanishes, the model
convection form is

$$`
b(u,v,w)=\int_\Omega ((u\cdot\nabla)v)\cdot w.
`

The product rule gives
$`b(u,v,w)+b(u,w,v)=\int_\Omega u\cdot\nabla(v\cdot w)`.
Integration by parts turns this into
$`-\int_\Omega(\nabla\cdot u)(v\cdot w)=0`. For example, compact support
removes the boundary term. Setting $`v=w` explains the energy cancellation:
incompressible transport redistributes energy without creating it. The
abstract theorem takes this skew identity as a hypothesis; in a concrete
Sobolev space it comes from justifying the integrals and the boundary step.

Let $`b:V\times V\times V\to\mathbb R` be a continuous trilinear convection
form. Assume the integration-by-parts skew identity for solenoidal transport
fields: for $`u\in V_\sigma` and $`v,w\in V`,

$$`
b(u,v,w)=-b(u,w,v).
`

:::theorem "fluid.solenoidal_convection" (parent := "fluid.solenoidal") (lean := "IncompressibleFlow.solenoidalConvectionForm_energy_eq_zero, IncompressibleFlow.solenoidalConvectionForm_isSkewInLastTwo, IncompressibleFlow.solenoidalConvectionForm_isBoundedBy, IncompressibleFlow.solenoidalConvectionForm, PDE.Analysis.ContinuousTrilinearForm.IsSkewInLastTwoOn.restrictToSubmodules, PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy.restrictToSubmodules, PDE.Analysis.ContinuousTrilinearForm.restrictToSubmodules") (uses := "fluid.solenoidal_space, parabolic.trilinear_energy_cancellation")
%%%
source := {
  document := "temam-navier-stokes"
  spans := #[{
    page := "105-120"
    text := some { path := "Blueprint/Sources/TemamNavierStokes.md", startLine := 1, endLine := 12 }
  }]
}
%%%
Restriction of $`b` to $`V_\sigma^3` is again a continuous trilinear form.
Every ambient product bound

$$`
|b(u,v,w)|\leq C\|u\|_V\|v\|_V\|w\|_V
`

passes to the restricted form with the same constant. Skew-symmetry for
solenoidal transport fields becomes global skew-symmetry on $`V_\sigma^3`,
and therefore

$$`
b_\sigma(u,u,u)=0.
`

The nonlinear energy cancellation holds without choosing a particular domain
or a Navier–Stokes solution predicate.
:::

:::proof "fluid.solenoidal_convection" (uses := "parabolic.trilinear_energy_cancellation")
Compose each slot of the ambient form with the continuous inclusion
$`V_\sigma\hookrightarrow V`. Subtype norms equal ambient norms, so the
product estimate is unchanged. The first restricted argument is solenoidal,
so the assumed integration-by-parts skew identity applies; diagonal
skew-symmetry then gives the cubic cancellation.
:::

# Recovering pressure

Pressure restores the part of the momentum equation that divergence-free
tests cannot see. In a finite-dimensional example, take
$`D(v_1,v_2)=v_1+v_2`. The admissible directions are multiples of
$`(1,-1)`. A linear residual that vanishes on all these directions must have
the form $`\ell(v)=a(v_1+v_2)=aDv`. The scalar $`a` is the multiplier. The
same factorization holds for a continuous divergence operator, with closed
range supplying the needed continuity of the recovered multiplier.

:::theorem "fluid.abstract_pressure_recovery" (parent := "fluid.solenoidal") (lean := "IncompressibleFlow.annihilates_solenoidal_iff_ker_le, IncompressibleFlow.recoveredPressureInRange, IncompressibleFlow.recoveredPressure, IncompressibleFlow.coe_recoveredPressureInRange, IncompressibleFlow.recoveredPressure_mem_range, IncompressibleFlow.inner_recoveredPressure_divergence, IncompressibleFlow.recoveredPressure_unique_of_mem_range, IncompressibleFlow.existsUnique_pressure_mem_range, IncompressibleFlow.adjoint_recoveredPressure_eq") (uses := "fluid.solenoidal_space, parabolic.closed_range_multiplier")
%%%
source := {
  document := "temam-navier-stokes"
  spans := #[{
    page := "15-27"
    text := some { path := "Blueprint/Sources/TemamNavierStokes.md", startLine := 1, endLine := 12 }
  }]
}
%%%
Assume now that $`V` and $`Q` are real Hilbert spaces and that $`D` has
closed range. If $`\ell\in V^*` annihilates every solenoidal vector, then
there is a unique $`p\in\operatorname{range}D` such that

$$`
\ell(v)=\langle p,Dv\rangle_Q\qquad(v\in V).
`

The chosen pressure satisfies the equivalent adjoint equation

$$`
D^*p=R_V^{-1}\ell.
`

The range condition fixes the otherwise possible pressure gauge. A concrete
Sobolev divergence operator still requires its own closed-range or inf-sup
theorem; given that input, this result reconstructs the pressure.
:::

:::proof "fluid.abstract_pressure_recovery" (uses := "parabolic.closed_range_multiplier")
Annihilation of $`V_\sigma=\ker D` is precisely the kernel inclusion
$`\ker D\subseteq\ker\ell`. Factor $`\ell` through the closed range of $`D`
and apply Fréchet–Riesz representation there. The representative belongs to
$`\operatorname{range}D`, satisfies the displayed pairing identity, and is
unique because the difference of two such representatives is both in the
range and orthogonal to it. The adjoint identity is the same equality tested
against every $`v\in V`.
:::
