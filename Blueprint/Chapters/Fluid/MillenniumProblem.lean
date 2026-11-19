/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Fluid.NavierStokes
import PDE.Fluid.NavierStokes.MillenniumProblem
import PDE.Solution.Singularity.FiniteTime.Norm.Continuation

/-!
# The Navier–Stokes Millennium Problem

The real-domain alternatives of Fefferman's official Clay problem
description, stated over the classical Navier–Stokes solution class, with the
abstract continuation alternative and the zero datum as a checked instance.
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
#doc (Manual) "The Navier–Stokes Millennium Problem" =>

:::group "fluid.millennium"
Navier–Stokes global regularity
:::

{Informal.citet "leray-1934"}[] constructed global finite-energy weak
solutions in three dimensions. Smooth solutions are known locally for smooth
data, but no theorem rules out a singularity at a later time for every
admissible datum. The open question is whether a smooth three-dimensional flow
can concentrate strongly enough to lose regularity.

What is formalized here is the statement of the problem and two proved facts.
The statement is Fefferman's pair of real-domain alternatives (A) and (C), two
Lean propositions over the classical solution class; the open problem asks for
a proof of one of them. The proved facts are an abstract
continuation alternative for norm trajectories, which takes the model-specific
continuation criterion as a hypothesis, and the zero datum, which satisfies the
existence predicate of alternative (A) at every positive viscosity. The scaling
calculation and the regularity theory recalled first are background.

# Scaling and critical spaces

For $`\lambda>0`, the scaling

$$`
u_\lambda(x,t)=\lambda u(\lambda x,\lambda^2t),
\qquad
p_\lambda(x,t)=\lambda^2p(\lambda x,\lambda^2t)
`

preserves the unforced three-dimensional equation. A change of variables
gives, for $`1\leq p<\infty`,

$$`
\|u_\lambda(t)\|_{L^p(\mathbb R^3)}
=\lambda^{1-3/p}
  \|u(\lambda^2t)\|_{L^p(\mathbb R^3)}.
`

The spatial $`L^3` norm is invariant, whereas

$$`
\|u_\lambda(t)\|_{L^2}^2
=\lambda^{-1}\|u(\lambda^2t)\|_{L^2}^2.
`

Concentration can therefore make the kinetic energy smaller. For example,
at corresponding times, $`\lambda=10` multiplies the velocity by ten and
compresses its spatial volume by a factor of a thousand. The squared
$`L^2` norm falls by a factor of ten, while spatial derivatives become a
hundred times as large at corresponding points. This is why an energy bound
alone cannot exclude concentration on smaller and smaller scales. The vorticity
scales even more strongly,

$$`
\omega_\lambda(x,t)=\lambda^2\omega(\lambda x,\lambda^2t),
`

and in three dimensions its equation contains the stretching term
$`(\omega\cdot\nabla)u`. The corresponding two-dimensional vorticity is a
scalar and has no stretching term.

# What is known

The obstruction is peculiar to three dimensions. In two dimensions,
energy and enstrophy estimates yield global regularity for smooth
incompressible data. In three dimensions the known theory separates into
several levels.

* {Informal.citet "leray-1934"}[] constructed global finite-energy weak
  solutions. They satisfy an energy inequality, but their global smoothness
  and uniqueness are not known. The Leray–Hopf and classical solution classes
  of the Navier–Stokes section make the same distinction.

* {Informal.citet "caffarelli-kohn-nirenberg-1982"}[] proved partial
  regularity for suitable weak solutions: the possible singular set has
  one-dimensional parabolic Hausdorff measure zero. Partial regularity does
  not show that this set is empty.

* The Prodi–Serrin family of criteria, represented here by
  {Informal.citet "serrin-1962"}[], shows that a weak solution is regular when
  its velocity belongs locally to $`L^q_tL^p_x` with

  $$`
  \frac{2}{q}+\frac{3}{p}\leq1,\qquad p>3.
  `

  {Informal.citet "escauriaza-seregin-sverak-2003"}[] established the
  scale-critical endpoint $`L^\infty_tL^3_x`. These results reduce regularity
  to control of a critical norm; the energy inequality alone controls a
  weaker scale.

# Continuation and loss of regularity

Local existence alone does not decide global regularity. One also needs a
continuation theorem identifying a norm whose boundedness prevents the
solution from stopping at a finite time.

:::theorem "fluid.millennium.continuation_alternative" (parent := "fluid.millennium") (lean := "PDE.Solution.Singularity.FiniteTime.normUnboundedAt_or_extendable, PDE.Solution.Singularity.FiniteTime.normUnboundedAt_of_not_extendable") (uses := "parabolic.blowup.norm_trajectory")
Let $`u:\mathbb R\to E` be a trajectory in a normed space and let $`T` be a
candidate terminal time. Suppose a model-specific theorem says that an
eventual bound

$$`
\|u(t)\|\leq C\qquad(t<T,\ t\ \text{near }T)
`

implies that the solution extends through $`T`. Then either $`u` is
norm-unbounded as $`t\uparrow T`, or the solution extends. In particular,
failure of extension forces norm-unboundedness.

The conclusion is weaker than
$`\|u(t)\|\to\infty`: an unbounded trajectory may repeatedly return to a
bounded region. Upgrading unboundedness to norm blow-up requires an additional
persistence property.
:::

:::proof "fluid.millennium.continuation_alternative"
Split on whether an eventual finite norm bound exists. In the bounded case,
the assumed continuation criterion gives extension. In the unbounded case,
the negation of every eventual bound is exactly norm unboundedness near the finite horizon. If
extension is known to fail, norm-unboundedness remains.
:::

# Fefferman's real-domain alternatives

:::definition "fluid.millennium.fefferman" (parent := "fluid.millennium") (lean := "MillenniumNSRDomain.FeffermanA, MillenniumNSRDomain.FeffermanC") (uses := "fluid.navier_stokes.classical")
%%%
source := {
  document := "fefferman-navier-stokes"
  spans := #[{
    page := "1-2"
    text := some { path := "Blueprint/Sources/FeffermanNavierStokes.md", startLine := 1, endLine := 9 }
  }]
}
%%%
An admissible initial velocity on $`\mathbb R^3` is smooth, divergence free,
and rapidly decreasing together with all its derivatives. An admissible force
is smooth and rapidly decreasing in space and time together with all its
spacetime derivatives. A datum has a global smooth finite-energy solution when
its Navier–Stokes problem has a global classical solution whose kinetic energy
is bounded uniformly in $`t\geq0`.

Alternative (A) is the statement that for every positive viscosity and every
admissible initial velocity, the unforced problem has a global smooth
finite-energy solution. Alternative (C) is the statement that for every
positive viscosity there are an admissible initial velocity and an admissible
force with no global smooth finite-energy solution. The Clay problem on
$`\mathbb R^3` asks for a proof of (A) or a proof of (C). Their disjunction
alone follows classically: if (A) fails at some viscosity $`\nu`, the scaling
$`v(x,t)=a\,u(x,at)` with $`a>0` maps solutions at viscosity $`\nu` to
solutions at viscosity $`a\nu` and keeps zero force zero, so (C) holds at
every viscosity. We therefore state the two alternatives separately.

The force is a smooth function on all of spacetime, and only its restriction
to $`t\geq0` enters the problem. A global classical solution
satisfies the momentum equation and incompressibility for $`t>0`, with
relative smoothness of velocity and pressure and the initial trace on
$`t\geq0`, so no totalized ambient derivative at the initial-time boundary is
read as a one-sided physical derivative.
:::

# Verified computation and the open problem

For the exact rotation and forced shear flows, the symbolic proofs establish
incompressibility and vanishing of each momentum residual component in Lean.
Neither velocity has finite energy,
so neither is admissible data for the Clay alternatives. On rational spacetime
boxes, CEGA can certify scalar bounds for supported residual expressions after
their derivative formulas have been justified. A bound in a chosen vector or
function norm needs an explicit reduction to these certificates; with that
reduction, estimates take the form

$$`
\|\nabla\cdot\widetilde u\|\leq\varepsilon_{\mathrm{div}},
\qquad
\|R_{NS}(\widetilde u,\widetilde p)\|
  \leq\varepsilon_{\mathrm{mom}}.
`

A computer-assisted proof for a nontrivial Navier–Stokes regime would combine
such bounds with an analytic validation theorem converting residual bounds into
a nearby true solution, quantitative control of a continuation norm, and an
argument covering the entire time interval. The exact CAS checks, the interval
certificates, and the abstract continuation alternative are formalized; such a
validation theorem is not.

The simplest solved datum checks that the formal Clay statement connects
correctly to the core equation.

:::theorem "fluid.millennium.zero_datum" (parent := "fluid.millennium") (lean := "MillenniumNSRDomain.zeroInitialData_hasGlobalSmoothFiniteEnergySolution") (uses := "fluid.millennium.fefferman, fluid.navier_stokes.zero_classical")
For every positive viscosity, the zero initial velocity with zero forcing has
a global smooth finite-energy solution:

$$`
u_0=0,\qquad f=0,\qquad u(t,x)=0,\qquad p(t,x)=0.
`

Its kinetic energy vanishes for every nonnegative time, so the existence
predicate of alternative (A) holds for this datum.
:::

:::proof "fluid.millennium.zero_datum"
The global zero classical solution supplies smooth velocity and pressure on
the physical half-space. The initial velocity is divergence free, and it and
the force are smooth and rapidly decreasing because they vanish identically.
Every term in the momentum equation is zero, and the kinetic energy is zero at
every time.
Any positive constant therefore gives the strict uniform energy bound required
by alternative (A) for this datum.
:::

Alternative (A) asks for the same conclusion for every admissible initial
velocity; alternative (C) asks, at each viscosity, for one admissible datum and
force where it fails.
