/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.CanonicalForm
import PDE.Hyperbolic.ConservationLaw.System.Basic
import PDE.Hyperbolic.ConservationLaw.System.IntegralCurveFamily
import PDE.Hyperbolic.ConservationLaw.System.PSystem
import PDE.Hyperbolic.ConservationLaw.System.PSystem.Diagonal
import PDE.Hyperbolic.ConservationLaw.System.PSystem.Rarefaction.Fan
import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannInvariant
import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannSolution
import PDE.Hyperbolic.ConservationLaw.System.PSystem.Shock
import PDE.Hyperbolic.ConservationLaw.System.Riemann
import PDE.Hyperbolic.ConservationLaw.System.Riemann.InitialValue
import PDE.Hyperbolic.ConservationLaw.System.SimpleWave
import PDE.Hyperbolic.ConservationLaw.System.WaveCurve

/-!
# Systems of conservation laws

Conservative and quasilinear formulations for one-dimensional systems, their
characteristic fields and elementary waves, and the p-system Riemann-invariant
and diagonalization results.
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
#doc (Manual) "Systems of Conservation Laws" =>

:::group "hyperbolic.conservation"
Scalar and system conservation laws
:::

:::definition "hyperbolic.conservation.system_flux_forms" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.fluxResidual, PDE.Hyperbolic.ConservationLaw.System.quasilinearResidual, PDE.Hyperbolic.ConservationLaw.System.fluxResidual_eq_quasilinearResidual")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "612-615"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a vector state $`u(t,x)` and flux $`f`, the conservative residual is
$`u_t+(f(u))_x`, while the quasilinear residual is
$`u_t+Df(u)u_x`. The Fréchet chain rule identifies the two forms at every
point where both maps are differentiable.
:::

The quasilinear form exposes the Jacobian $`Df(u)`, and the classification of
the system is the spectral classification of this matrix at each state.

:::definition "hyperbolic.conservation.system_hyperbolicity" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.IsHyperbolicAt, PDE.Hyperbolic.ConservationLaw.System.IsStrictlyHyperbolicAt, PDE.Hyperbolic.ConservationLaw.System.IsSymmetricAt")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "615-620"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A system is hyperbolic at $`u` when $`f` is differentiable there and

$$`
Df(u)r_k=\lambda_k r_k,\qquad
\lambda_k\in\mathbb R,\qquad
\operatorname{span}\{r_1,\ldots,r_m\}=\mathbb R^m.
`

Strict hyperbolicity additionally requires the speeds $`\lambda_k` to be
pairwise distinct. Symmetry means that the Fréchet Jacobian satisfies
$`Df(u)^*=Df(u)` for the Euclidean inner product.
:::

Hyperbolicity asserts that an eigenbasis exists at each state separately.
Following one eigenvalue and one eigenvector across state space, as functions
of $`u`, is a further choice, and it is this selected pair that defines a
characteristic family and its integral curves.

:::definition "hyperbolic.conservation.characteristic_field" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.CharacteristicField, PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.vectorField") (uses := "hyperbolic.conservation.system_hyperbolicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "615-624"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A characteristic field selects functions $`\lambda_k(u)\in\mathbb R` and
$`r_k(u)\ne0` satisfying

$$`
Df(u)r_k(u)=\lambda_k(u)r_k(u).
`

Its autonomous ODE field is $`u'=r_k(u)`. Unlike strict hyperbolicity, this is
data for one consistently selected family. Smooth dependence of the selected
speed or vector field is a separate hypothesis.
:::

Two important cases depend on how the speed changes along its own
characteristic field. Genuine nonlinearity supports local shock and
rarefaction curves; linear degeneracy gives contact discontinuities. These
conditions do not exhaust all characteristic fields: the directional
derivative can vanish at some states without vanishing everywhere.

:::definition "hyperbolic.conservation.characteristic_classes" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.IsGenuinelyNonlinearAt, PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.IsGenuinelyNonlinear, PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.IsLinearlyDegenerate") (uses := "hyperbolic.conservation.characteristic_field")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "623-624"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Genuine nonlinearity means
$`D\lambda_k(u)\,r_k(u)\ne0` at every state. Linear degeneracy means the
same directional derivative vanishes everywhere. Lean expresses the latter
by saying that the speed is a Riemann invariant of its own characteristic
field, so differentiability of the speed is part of the proposition.
:::

Along an integral curve $`\gamma` of $`r_k`, linear degeneracy says that
$`\lambda_k\circ\gamma` has zero derivative.

:::theorem "hyperbolic.conservation.linearly_degenerate_speed" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.IsLinearlyDegenerate.speed_eq_on_integralCurve") (uses := "hyperbolic.conservation.characteristic_classes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "629-630"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`D\lambda_k(u)r_k(u)=0` and
$`\gamma'(s)=r_k(\gamma(s))`, then

$$`
\lambda_k(\gamma(s))=\lambda_k(\gamma(t))
\qquad\text{for all }s,t.
`

Thus the characteristic speed of a linearly degenerate field is constant
along each global integral curve of its right eigenvector field.
:::

:::proof "hyperbolic.conservation.linearly_degenerate_speed"
Apply the chain rule to $`\lambda_k\circ\gamma`. Its derivative is
$`D\lambda_k(\gamma(s))\,\gamma'(s)`, which becomes
$`D\lambda_k(\gamma(s))\,r_k(\gamma(s))=0` by the integral-curve equation
and linear degeneracy. A differentiable real-valued function with zero
derivative on the interval is constant.
:::

Producing the eigenbasis demanded by hyperbolicity is easiest when the
Jacobian is self-adjoint, since the real spectral theorem then supplies real
speeds and an orthonormal eigenbasis at once.

:::theorem "hyperbolic.conservation.symmetric_hyperbolic" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.IsSymmetricAt.isHyperbolicAt") (uses := "hyperbolic.conservation.system_hyperbolicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "615-620"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every symmetric flux Jacobian is hyperbolic:

$$`
Df(u)^*=Df(u)
\Longrightarrow
\mathbb R^m=\bigoplus_{\lambda\in\sigma(Df(u))}
\ker(Df(u)-\lambda I).
`
:::

:::proof "hyperbolic.conservation.symmetric_hyperbolic"
The Jacobian is a self-adjoint endomorphism of a finite-dimensional real
inner-product space. The real spectral theorem supplies an orthonormal basis
of eigenvectors and real eigenvalues. Reindexing this basis gives the
characteristic speeds and spanning family required by hyperbolicity.
:::

The spectral data describe smooth solutions. Discontinuous solutions are
governed instead by an algebraic relation between the two states and the speed
of a jump, which for systems is a vector identity and therefore overdetermines
the speed.

:::definition "hyperbolic.conservation.system_jump" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.RankineHugoniot, PDE.Hyperbolic.ConservationLaw.System.RankineHugoniot.unique_speed")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "612-615"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The vector Rankine–Hugoniot relation is
$`f(u_R)-f(u_L)=s(u_R-u_L)`. A nonzero jump determines at most one shock
speed.
:::

Rankine–Hugoniot alone admits jumps in both directions, so admissibility has
to be added, and it is added family by family: each of the three elementary
waves is a way of connecting two states through the $`k`th characteristic
family.

:::definition "hyperbolic.conservation.system_elementary_waves" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.LaxShock, PDE.Hyperbolic.ConservationLaw.System.ContactDiscontinuity, PDE.Hyperbolic.ConservationLaw.System.IsRarefactionConnection") (uses := "hyperbolic.conservation.system_jump, hyperbolic.conservation.characteristic_classes")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "625-632"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A $`k`-Lax shock satisfies Rankine–Hugoniot, $`\lambda_k(u_R)<s<\lambda_k(u_L)`,
and the neighboring-family conditions $`\lambda_j(u_L)<s` for $`j<k` and
$`s<\lambda_j(u_R)` for $`j>k`. A $`k`-contact discontinuity satisfies
Rankine–Hugoniot and $`s=\lambda_k(u_L)=\lambda_k(u_R)`. A rarefaction
connection follows the $`k`th characteristic integral curve while its speed
increases strictly along the entire oriented segment from $`u_L` to $`u_R`. The
predicates contain only the displayed connection conditions.
:::

For a linearly degenerate family the constancy of $`\lambda_k` along integral
curves produces contact discontinuities directly: any two
states on the same integral curve satisfy Rankine–Hugoniot with that common
speed.

:::theorem "hyperbolic.conservation.linearly_degenerate_contact" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.ContactDiscontinuity.of_linearlyDegenerate_integralCurve") (uses := "hyperbolic.conservation.system_elementary_waves, hyperbolic.conservation.linearly_degenerate_speed")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "625-632"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If the flux is globally $`C^1`, any two states on a $`C^1` integral curve of
a differentiable, linearly degenerate characteristic speed form a contact
discontinuity. Integral curves use Mathlib's `IsIntegralCurve`, whose
`HasDerivAt` formulation includes differentiability.
:::

:::proof "hyperbolic.conservation.linearly_degenerate_contact"
The speed is constant along the characteristic integral curve by linear
degeneracy; call the common value $`s`. Along that curve the chain rule and
the eigenvector equation give
$`\frac d{d\tau}f(\gamma(\tau))=s\,\gamma'(\tau)`. Integrating between the
two parameter values yields
$`f(u_R)-f(u_L)=s(u_R-u_L)`, while constancy gives
$`s=\lambda_k(u_L)=\lambda_k(u_R)`. These are precisely the contact
conditions.
:::

Solving the Riemann problem for a system means joining $`u_L` to $`u_R` by one
wave from each family, applied in a fixed order.

:::definition "hyperbolic.conservation.ordered_wave_map" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily, PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.IsElementary, PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.composedWaveMap") (uses := "hyperbolic.conservation.system_elementary_waves, hyperbolic.conservation.characteristic_field")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "632-634"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A local wave family on a state domain supplies transformations $`T_k(t_k,u)` with a
strict Fréchet derivative at zero strength at each domain state: the strength column is $`r_k(u)`
and the state block is the identity. No $`C^1` regularity near zero strength
is required. Their ordered composition starts at the left state and applies
one transformation for each characteristic family. An elementary family
uses admissible shocks, rarefactions, or contacts for these transformations.
:::

The zero-strength derivative condition is exactly what the flow of the
characteristic vector field $`r_k` satisfies, so the rarefaction curves
through each state furnish the analytic part of such a family.

:::theorem "hyperbolic.conservation.characteristic_flow_family" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.hasDerivAt_curve_zero, PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.ofCharacteristicFlows, PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.curveTangent_zero") (uses := "hyperbolic.conservation.ordered_wave_map")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "622-625"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A global Mathlib flow whose trajectories solve a characteristic ODE and
whose joint time-state map is locally $`C^1` yields a `LocalWaveFamily`.
The flow laws provide the identity state block at zero time, and the ODE
provides the right-eigenvector strength column. This is the analytic
rarefaction-curve germ used by Evans. An elementary $`T_k` family also
splices in the admissible shock
branch, or the contact branch in the linearly degenerate case.
:::

:::proof "hyperbolic.conservation.characteristic_flow_family"
At time zero the flow law makes every trajectory start at its input state,
so the derivative in the state variable is the identity. Differentiating the
trajectory in time at zero and using the characteristic ODE gives
$`r_k(u)`. Local $`C^1` regularity makes these two blocks a strict
derivative at zero, as a local wave family requires.
:::

Composing the $`m` transformations gives a map from strength vectors to
states, and the derivative conditions imposed on each factor determine its
derivative at zero strength column by column.

:::theorem "hyperbolic.conservation.wave_map_columns" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.composedWaveDerivative_single") (uses := "hyperbolic.conservation.ordered_wave_map")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "633-634"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At zero strengths, the $`k`th column of the derivative of the ordered wave
map is the $`k`th right characteristic vector.
:::

:::proof "hyperbolic.conservation.wave_map_columns"
Differentiate the ordered composition with respect to the $`k`th strength.
Every other wave has zero strength, so its state derivative is the identity.
The sole nonidentity factor is the strength derivative of $`T_k` at zero,
which is $`r_k(u_L)`. The chain rule therefore returns that vector as the
$`k`th derivative column.
:::

Pairwise distinct speeds at $`u_L` make the columns
$`r_1(u_L),\ldots,r_m(u_L)` a basis, so the derivative is invertible and the
inverse function theorem applies. The strengths it returns have physical
meaning when the family is elementary.

:::theorem "hyperbolic.conservation.local_riemann_solver" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.LocalWaveFamily.existsUnique_localRiemann_strength") (uses := "hyperbolic.conservation.wave_map_columns, hyperbolic.conservation.system_hyperbolicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "633-634"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let

$$`
\Phi(t_1,\ldots,t_m;u_L)
=T_m(t_m,\cdot)\circ\cdots\circ T_1(t_1,\cdot)(u_L).
`

For a left state in the family's state domain, if $`r_1(u_L),\ldots,r_m(u_L)` form a basis, then
the inverse function theorem gives open neighborhoods $`U` of $`0` and $`V` of $`u_L` such that
every $`u_R\in V` has a unique $`t\in U` with $`\Phi(t;u_L)=u_R`. This is the
analytic parametrization step of Evans's argument; the elementary curves and
the self-similar weak solution come from the wave family.
:::

:::proof "hyperbolic.conservation.local_riemann_solver"
The derivative of $`\Phi` at zero has the characteristic vectors
$`r_1(u_L),\ldots,r_m(u_L)` as its columns. Because these vectors form a
basis, that strict derivative is invertible. The inverse function theorem
for strict derivatives makes $`\Phi` a local homeomorphism, giving existence
and uniqueness of the nearby wave-strength vector.
:::

Building the wave family from local shock curves and characteristic integral
curves turns this parametrization into a solution of the Riemann problem.

:::theorem "hyperbolic.conservation.local_riemann_initial_value" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.exists_local_riemann_initialValue_solution") (uses := "hyperbolic.conservation.local_riemann_solver, hyperbolic.conservation.system_elementary_waves")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "633-634"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f\in C^2(\mathbb R^m;\mathbb R^m)` be strictly hyperbolic at every state,
and let each characteristic family be genuinely nonlinear or linearly
degenerate. For every $`u_L` there are $`\delta>0` and bounds $`K,M\ge0` such
that each $`u_R` with $`\|u_R-u_L\|<\delta` has intermediate states
$`u_L=u_0,u_1,\ldots,u_m=u_R`. Each successive pair admits an elementary
connection: a $`k`-rarefaction, a $`k`-Lax shock, a $`k`-contact, or equal
states. There are also bounded, measurable, self-similar weak waves $`w_k`
with these outer states in separated, ordered speed windows in $`[-M,M]`.
Their finite gluing $`u=u_L+\sum_k(w_k-u_{k-1})` is a bounded, measurable,
self-similar weak solution of $`u_t+f(u)_x=0` in $`t>0` that attains the
Riemann datum in the weak initial-value sense and strongly in
$`L^1_{\mathrm{loc}}` as $`t\downarrow0`. It equals $`u_L` for $`x<-Mt`
and $`u_R` for $`x\ge Mt`.

`IsElementaryConnection` is a predicate on the endpoint states alone, so the
elementary connections and the weak waves $`w_k` are separate conclusions
that share their outer states.
:::

:::proof "hyperbolic.conservation.local_riemann_initial_value"
Local shock curves and characteristic integral curves supply an elementary
wave family. The wave-strength theorem gives the strengths for nearby $`u_R`
and keeps the intermediate states inside the construction neighborhoods.
The construction also supplies bounded, measurable, self-similar weak waves
with those outer states in separated speed windows. Their finite gluing
preserves the weak equation. Uniform boundedness and finite propagation give
the strong local $`L^1` initial trace, which supplies the initial face in the
weak initial-value identity.
:::

Admissibility for systems is formulated, as in the scalar case, through
additional conserved quantities. An entropy pair is a scalar function of the
state together with a flux for it, compatible with $`f` through
$`Dq=D\eta\circ Df`.

:::definition "hyperbolic.conservation.system_entropy_pair" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.EntropyPair, PDE.Hyperbolic.ConservationLaw.System.ConvexEntropyPair")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "646-649"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Lean definitions factor the conditions of an entropy pair: `EntropyPair`
records scalar $`C^1` functions satisfying
$`Dq=D\eta\circ Df`, while `ConvexEntropyPair` adds convexity of $`\eta` on
the whole state space. Convex entropy inequalities need the second
structure.
:::

Compatibility is precisely the condition under which the chain rule turns the
conservation law for $`u` into a conservation law for $`\eta(u)`.

:::theorem "hyperbolic.conservation.system_entropy_identity" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.EntropyPair.entropyResidual_eq_zero_of_flux") (uses := "hyperbolic.conservation.system_flux_forms, hyperbolic.conservation.system_entropy_pair")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "646-649"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every differentiable classical solution satisfies
$`\partial_t\eta(u)+\partial_xq(u)=0` for each compatible system entropy
pair.
:::

:::proof "hyperbolic.conservation.system_entropy_identity"
The chain rule gives
$`\partial_t\eta(u)=D\eta(u)u_t` and
$`\partial_xq(u)=Dq(u)u_x`. Compatibility replaces $`Dq` by
$`D\eta\circ Df`, so their sum is
$`D\eta(u)\bigl(u_t+Df(u)u_x\bigr)`. The classical conservation law makes
the vector in parentheses zero.
:::

The one-dimensional p-system of nonlinear elasticity is the running example
for all of this structure: two equations, two characteristic families, and a
physically meaningful entropy pair given by mechanical energy.

:::definition "hyperbolic.conservation.p_system" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.flux, PDE.Hyperbolic.ConservationLaw.System.PSystem.mechanicalEntropy, PDE.Hyperbolic.ConservationLaw.System.PSystem.mechanicalEntropyFlux")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "610-612"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "649"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
The one-dimensional elasticity p-system has strain–velocity state $`(v,w)`
and flux $`F(v,w)=(-w,-p(v))`, where $`p` is the stress law. Its mechanical
energy and energy flux are
$`\eta(v,w)=w^2/2+P(v)` and $`q(v,w)=-p(v)w`.
:::

The Jacobian of $`F` has characteristic polynomial $`\lambda^2-p'(v)`, so
positivity of $`p'(v)` gives two distinct real speeds.

:::theorem "hyperbolic.conservation.p_system_hyperbolic" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.isStrictlyHyperbolicAt") (uses := "hyperbolic.conservation.p_system, hyperbolic.conservation.system_hyperbolicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "620"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Where $`p'(v)>0`, the p-system flux Jacobian has the distinct
characteristic speeds $`-\sqrt{p'(v)}` and $`\sqrt{p'(v)}`, with an explicit
right eigenbasis.
:::

:::proof "hyperbolic.conservation.p_system_hyperbolic"
The characteristic polynomial of the flux Jacobian is
$`\lambda^2-p'(v)`. Positivity of $`p'(v)` gives the two distinct real roots
$`\lambda=\pm\sqrt{p'(v)}`. Solving the two corresponding linear systems
produces nonzero eigenvectors with different eigenvalues, hence a basis of
the two-dimensional state space.
:::

Mechanical energy is the natural entropy for the p-system. Its compatibility
with the flux is a direct computation using $`P'=p`, while convexity in the
state variables requires $`p'>0`, the same condition as strict hyperbolicity.

:::definition "hyperbolic.conservation.p_system_entropy" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.mechanicalConvexEntropyPairOfDerivPositive") (uses := "hyperbolic.conservation.p_system, hyperbolic.conservation.system_entropy_pair")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "649"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`p` and $`P` are globally $`C^1`, $`P'=p`, and $`p'>0`, the mechanical
energy and energy flux form a compatible convex entropy pair for the
p-system.
:::

Returning to general systems, rarefaction waves are built from states that
move along a single characteristic curve in state space. If $`u` takes values
on such a curve, the vector system collapses to a scalar transport equation
for the curve parameter.

:::theorem "hyperbolic.conservation.simple_wave" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.quasilinearResidual_simpleWave") (uses := "hyperbolic.conservation.system_flux_forms, hyperbolic.conservation.system_hyperbolicity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "621-623"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At a spacetime point $`z`, suppose $`\phi` is differentiable at $`z` and
$`w` is differentiable at $`\phi(z)`. If its tangent satisfies the eigenvector
equation $`Df(w(\phi))w'(\phi)=\lambda(\phi)w'(\phi)`, the quasilinear
residual of $`u=w(\phi)` is $`(\phi_t+\lambda(\phi)\phi_x)w'(\phi)`, with
all quantities evaluated at $`z`. It also equals the conservative residual
when $`f` is differentiable at $`w(\phi(z))`. The identity is pointwise;
the phase and the characteristic curve are given.
:::

:::proof "hyperbolic.conservation.simple_wave"
Differentiate $`u=w\circ\phi` in time and space. The chain rule factors both
derivatives through $`w'(\phi)`, and the eigenvector relation replaces
$`Df(w(\phi))w'(\phi)` by
$`\lambda(\phi)w'(\phi)`. Factoring the common tangent vector leaves exactly
$`\bigl(\phi_t+\lambda(\phi)\phi_x\bigr)w'(\phi)`.
:::

Choosing the phase to be the similarity variable $`\xi=x/t` gives the centered
wave. Its transport factor vanishes precisely when the characteristic speed at
$`w(\xi)` equals $`\xi`, so the eigenvector condition with eigenvalue $`\xi`
is the pointwise form of the rarefaction profile equation.

:::theorem "hyperbolic.conservation.self_similar_wave" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.fluxResidual_selfSimilarWave_eq_zero") (uses := "hyperbolic.conservation.simple_wave")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "624-625"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At a point with $`t\ne0`, suppose the profile is differentiable at
$`\xi=x/t`, the flux is differentiable at $`w(\xi)`, and
$`Df(w(\xi))w'(\xi)=\xi w'(\xi)`. Then $`u(t,x)=w(x/t)` solves the
conservative system at that point. The centered-rarefaction construction
builds the profile by inverting a characteristic speed and joins the fan
to constant end states; for the p-system these steps are carried out in the
{bpref "hyperbolic.conservation.p_system_rarefaction_fan"}[rarefaction fan].
:::

:::proof "hyperbolic.conservation.self_similar_wave"
For $`\xi=x/t`, direct differentiation gives
$`\xi_t=-\xi/t` and $`\xi_x=1/t`. The chain rule therefore rewrites the
quasilinear residual as
$`t^{-1}\bigl(Df(w(\xi))-\xi I\bigr)w'(\xi)`, which vanishes by the profile
eigenvector equation. The conservative residual agrees with the
quasilinear one at the differentiability point.
:::

Scalar quantities constant along the integral curves of $`r_k` are the natural
coordinates for describing $`k`-rarefactions, since such a wave changes the
state only along one such curve.

:::definition "hyperbolic.conservation.riemann_invariant" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.IsRiemannInvariant")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "635-636"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A Riemann invariant $`R` for the $`k`th field is differentiable and satisfies

$$`
DR(u)\,r_k(u)=0
`

at every state.
:::

The annihilation condition is infinitesimal; integrating it along an integral
curve is what makes the invariant literally constant there.

:::theorem "hyperbolic.conservation.riemann_invariant_constant" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.CharacteristicField.IsRiemannInvariant.eq_on_integralCurve") (uses := "hyperbolic.conservation.riemann_invariant")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "635-636"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`\gamma'(s)=r_k(\gamma(s))` and $`DR\,r_k=0`, then the chain rule gives

$$`
\frac d{ds}R(\gamma(s))=0,
\qquad
R(\gamma(s))=R(\gamma(t)).
`

Hence a Riemann invariant is constant along every Mathlib integral curve of
its characteristic vector field.
:::

:::proof "hyperbolic.conservation.riemann_invariant_constant"
Apply the chain rule to $`R\circ\gamma`. The integral-curve equation changes
its derivative to $`DR(\gamma(s))\,r_k(\gamma(s))`, and the Riemann-invariant
condition makes this zero. The zero-derivative theorem then shows that the
composition has the same value at every pair of parameters.
:::

For the p-system both invariants can be written down. The right eigenvectors
are $`(1,\pm c)` with $`c=\sqrt{p'}`, and the functions $`w\mp A(v)` with
$`A'=c` are annihilated by them.

:::theorem "hyperbolic.conservation.p_system_riemann_invariants" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.isRiemannInvariant_riemannInvariant, PDE.Hyperbolic.ConservationLaw.System.PSystem.riemannInvariant_eq_on_integralCurve") (uses := "hyperbolic.conservation.p_system, hyperbolic.conservation.p_system_hyperbolic, hyperbolic.conservation.riemann_invariant_constant")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "610-611"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "635-639"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
For a globally $`C^1` stress law with $`p'(v)>0`, set
$`c(v)=\sqrt{p'(v)}` and $`A(v)=\int_{\mathrm{base}}^v c(x)\,dx`. With the
p-system flux $`F(v,w)=(-w,-p(v))`, the family with speed $`-c` and right
eigenvector $`(1,c)` has invariant $`w-A(v)`, while the family with speed
$`c` and right eigenvector $`(1,-c)` has invariant $`w+A(v)`. Each is
constant along every global Mathlib integral curve of its field.

This is the p-system case of Evans's general two-equation Riemann-invariant
calculation, distinct from the barotropic-gas invariants that follow it there.
The hypotheses are global because `CharacteristicField` is defined on the
whole state space.
:::

:::proof "hyperbolic.conservation.p_system_riemann_invariants"
The fundamental theorem of calculus gives $`A'(v)=c(v)`. Consequently the
gradients of $`w-A(v)` and $`w+A(v)` are $`(-c(v),1)` and $`(c(v),1)`.
Their products with the corresponding right eigenvectors $`(1,c(v))` and
$`(1,-c(v))` vanish. Thus each function is a Riemann invariant, and the
general constancy theorem applies along the associated integral curves.
:::

Riemann invariants do more than label rarefaction curves. In the variables
$`R_0=w-A(v)` and $`R_1=w+A(v)` the p-system has diagonal transport
equations, one per characteristic speed. They remain coupled through the
sound speed $`c(v)`: recovering $`v` uses both invariants. Where $`p'>0`,
the passage between this diagonal form and the original system is reversible.

:::theorem "hyperbolic.conservation.p_system_diagonal" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.quasilinearResidual_eq_zero_iff_riemannInvariant_transport") (uses := "hyperbolic.conservation.system_flux_forms, hyperbolic.conservation.p_system_riemann_invariants")
Let the stress $`p` be globally $`C^1`. At a point where $`p'(v)>0`, a
field differentiable there solves the p-system if and only if both acoustic
Riemann invariants satisfy their diagonal transport equations

$$`
\partial_t R_k-\lambda_k\partial_x R_k=0.
`

The sign is determined by the flux convention $`F(v,w)=(-w,-p(v))`.
For a classical solution, an invariant is constant along any characteristic
with tangent $`(1,-\lambda_k)` on an open connected time interval, provided
the curve stays in the solution's domain and $`p'(v)\ge0` along it.
:::

:::proof "hyperbolic.conservation.p_system_diagonal" (uses := "hyperbolic.conservation.p_system_hyperbolic")
The forward implication is the chain rule applied to the two signed acoustic
invariants. Conversely, adding the two diagonal equations recovers
$`w_t-p'(v)v_x=0`. Subtracting them and dividing by twice the positive sound
speed recovers $`v_t-w_x=0`.
:::

With the state-space geometry in place, the elementary waves of the p-system
can be written explicitly, beginning with the shock branch. Prescribing the
right strain and solving Rankine–Hugoniot for the right velocity and the speed
gives the Hugoniot curve of each family, on which Lax admissibility holds for
one sign of the strain jump.

:::definition "hyperbolic.conservation.p_system_hugoniot_branch" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.shockSpeed, PDE.Hyperbolic.ConservationLaw.System.PSystem.shockState, PDE.Hyperbolic.ConservationLaw.System.PSystem.rankineHugoniot_shockState, PDE.Hyperbolic.ConservationLaw.System.PSystem.laxShock_shockState_zero_of_left_lt_right, PDE.Hyperbolic.ConservationLaw.System.PSystem.laxShock_shockState_one_of_right_lt_left") (uses := "hyperbolic.conservation.p_system, hyperbolic.conservation.p_system_hyperbolic, hyperbolic.conservation.system_jump, hyperbolic.conservation.system_elementary_waves")
For the p-system with stress law $`p`, a left state $`u_L=(v_L,w_L)` and a
prescribed right strain $`v_R`, let

$$`
q(v_L,v_R)=\begin{cases}
\dfrac{p(v_R)-p(v_L)}{v_R-v_L},& v_R\ne v_L,\\
p'(v_L),& v_R=v_L
\end{cases}
`

be the differentiable difference quotient of the stress. The signed shock
speeds of the two families are

$$`
s_0(v_L,v_R)=-\sqrt{q(v_L,v_R)},\qquad s_1(v_L,v_R)=\sqrt{q(v_L,v_R)},
`

so that zero jump returns the characteristic speeds $`\mp\sqrt{p'(v_L)}`
rather than the artificial value $`0`. The Hugoniot endpoint of family $`k`
is

$$`
H_k(v_R;u_L)=\bigl(v_R,\;w_L-s_k(v_L,v_R)\,(v_R-v_L)\bigr).
`

Whenever $`q(v_L,v_R)\ge0`, which is automatic when $`p'>0`, the states
$`u_L` and $`H_k(v_R;u_L)` satisfy the vector Rankine–Hugoniot relation with
speed $`s_k(v_L,v_R)`. If moreover $`p` is $`C^2` with $`p'>0` and $`p''>0`,
the jump is a Lax $`k`-shock, $`\lambda_k(u_R)<s_k<\lambda_k(u_L)`, on the
physical half of each branch: $`v_L<v_R` for family $`0` and $`v_R<v_L` for
family $`1`.
:::

For the opposite sign of the strain jump the admissible connection is a
rarefaction along the characteristic curve, realized in spacetime as a
self-similar fan.

:::definition "hyperbolic.conservation.p_system_rarefaction_fan" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.rarefactionFan") (uses := "hyperbolic.conservation.p_system, hyperbolic.conservation.p_system_hyperbolic, hyperbolic.conservation.p_system_riemann_invariants, hyperbolic.conservation.self_similar_wave")
Let $`c=\sqrt{p'}` be the sound speed, $`A(v)=\int_0^v c(x)\,dx`, and let
$`\lambda_0=-c` and $`\lambda_1=c` be the characteristic speeds as functions
of the strain. The $`k`th characteristic curve through $`u_L=(v_L,w_L)` at
strength $`\sigma` is

$$`
\gamma_k(\sigma;u_L)=\bigl(v_L+\sigma,\;w_L\pm(A(v_L+\sigma)-A(v_L))\bigr),
`

with the sign $`+` for $`k=0` and $`-` for $`k=1`, so that the Riemann
invariant $`w-A(v)` of family $`0`, respectively $`w+A(v)` of family $`1`, is
constant along it. For $`t>0` and ordered edge speeds
$`\lambda_k(v_L)\le\lambda_k(v_L+\sigma)`, the rarefaction fan of family
$`k` with left state $`u_L` and strength $`\sigma` has the spacetime profile

$$`
u(t,x)=\begin{cases}
u_L,& x<\lambda_k(v_L)\,t,\\
R_k(x/t),& \lambda_k(v_L)\,t\le x<\lambda_k(v_L+\sigma)\,t,\\
\gamma_k(\sigma;u_L),& x\ge\lambda_k(v_L+\sigma)\,t.
\end{cases}
`

For a $`C^2` stress with $`p'>0` and $`p''>0` and ordered edge speeds
$`\lambda_k(v_L)\le\lambda_k(v_L+\sigma)`, the middle state $`R_k(\xi)` is the
point of the characteristic curve whose strain $`v` solves
$`\lambda_k(v)=\xi`, so the fan is the self-similar rarefaction wave joining
$`u_L` to $`\gamma_k(\sigma;u_L)`. Lean extends $`R_k` outside the fan
interval by its endpoint tangent lines to obtain a global $`C^1` middle map;
on the wedge this extension agrees with $`R_k`, so it affects no value of an
ordered fan. The definition is total in $`\sigma`; for $`p''>0` the ordering
holds when $`\sigma\le0` in family $`0` and when $`\sigma\ge0` in family
$`1`.
:::

The two branches meet at zero strength, where the Hugoniot endpoint and the
characteristic curve both reduce to $`u_L` and the shock speed reduces to the
characteristic speed. Splicing them by the sign of $`\sigma` yields one total
wave per family, and it is this spliced family that the local Riemann theorem
for the p-system concatenates.

:::definition "hyperbolic.conservation.p_system_elementary_wave" (parent := "hyperbolic.conservation") (lean := "PDE.Hyperbolic.ConservationLaw.System.PSystem.elementaryWaveSolution") (uses := "hyperbolic.conservation.p_system_hugoniot_branch, hyperbolic.conservation.p_system_rarefaction_fan")
Write $`\mathrm{fan}_k(\sigma;u_L)` for the rarefaction fan and
$`\mathrm{shock}(u_L,u_R;s)` for the planar profile equal to $`u_L` on
$`x<st` and to $`u_R` on $`x\ge st`. The physical elementary wave of family
$`k` with left state $`u_L=(v_L,w_L)` and strength $`\sigma` is

$$`
W_k(\sigma;u_L)=\begin{cases}
\mathrm{fan}_0(\sigma;u_L),& k=0,\ \sigma\le0,\\
\mathrm{shock}\bigl(u_L,H_0(v_L+\sigma;u_L);s_0(v_L,v_L+\sigma)\bigr),& k=0,\ \sigma>0,\\
\mathrm{shock}\bigl(u_L,H_1(v_L+\sigma;u_L);s_1(v_L,v_L+\sigma)\bigr),& k=1,\ \sigma<0,\\
\mathrm{fan}_1(\sigma;u_L),& k=1,\ \sigma\ge0.
\end{cases}
`

In every case the strain increment across the wave is $`\sigma`; the right
state is $`\gamma_k(\sigma;u_L)` on the rarefaction branches and
$`H_k(v_L+\sigma;u_L)` on the shock branches. The definition places no
hypothesis on $`p`. For a $`C^2` stress with $`p'>0` and $`p''>0`, the
rarefaction branch is used where the edge speeds of the fan are ordered and
the shock branch where the Hugoniot jump is a Lax $`k`-shock; family-zero
waves then propagate with negative speeds and family-one waves with positive
speeds.
:::
