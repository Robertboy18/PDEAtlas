/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.Semigroups

/-!
# Hyperbolic theory scope

Characteristic, energy, weak, and nonlinear methods for hyperbolic equations.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Characteristics, Waves, and Nonlinear Models" =>

:::group "hyperbolic.chapter_guide"
Hyperbolic theory
:::

# Propagation along characteristics

We begin with transport and the one-dimensional wave equation. D'Alembert's
formula satisfies the wave equation and both initial identities under
explicit smoothness assumptions. Energy identities then give the domain of
dependence and finite propagation. In higher dimensions the Kirchhoff,
Poisson, and general odd- and even-dimensional formulas solve the Cauchy
problem with both joint initial traces. Duhamel's principle adds a forcing
term with zero Cauchy data in every positive spatial dimension, including
the one-dimensional retarded d'Alembert formula.

For semilinear waves, the local energy balance yields two complementary
conclusions. Shrinking-ball transport gives finite propagation when the
potential is nonnegative and vanishes at zero. On all of space, a normalized
$`C^2` potential and a $`C^2` wave with separately compact displacement
slices give conservation of total energy in every positive dimension.
The proof derives common support on finite slabs, including control of the
actual initial right velocity. For a normalized $`C^1` potential,
conservation is proved in one and two dimensions with $`C^3` and $`C^4`
waves respectively, and in every positive dimension with a $`C^3` wave
and a quadratic lower bound on the potential near zero. A nonnegative
potential makes the conserved energy control the kinetic, spatial-gradient,
and potential terms separately.

A separate construction starts from data in $`H^1_0(\Omega)\times L^2(\Omega)`
on a nonempty bounded open domain in positive dimension. With an autonomous
bounded measurable symmetric uniformly elliptic principal matrix and a
locally Lipschitz map from this energy space to $`L^2(\Omega)`,
the semigroup construction gives a
maximal continuous energy-space trajectory and its weak wave
equation on every compact initial interval before the lifetime. Both initial
values are attained. Uniqueness holds among weak solutions represented by
continuous energy-space curves. Finite-lifetime norm blowup additionally
requires a Lipschitz bound on every bounded energy ball. Nonlinear energy
conservation and the estimates for specific power nonlinearities require
further hypotheses and arguments.

On $`\mathbb R^n`, a globally Lipschitz scalar $`f` with $`f(0)=0` gives
a global forward solution of $`u_{tt}-\Delta u+f(u)=0` for arbitrary
$`H^1\times L^2` data. Both strong initial traces and the integrated
weak PDE are proved, with uniqueness among energy-continuous PDE solutions;
see {bpref "hyperbolic.semiwave.whole_space_cauchy"}[].
This is an energy-space theorem. For smooth compact data in three dimensions,
the construction below gives classical solutions and a lifespan alternative.

For $`C_c^\infty` Cauchy data on $`\mathbb R^3` and any smooth scalar
reaction fixing zero, a separate construction gives a maximal smooth wave;
see {bpref "hyperbolic.semiwave.maximal_smooth_wave"}[].
If its lifespan is finite, displacement is unbounded on every terminal
time strip.

For nonlinear first-order equations, let the boundary parametrization $`b`
and values $`g` be $`C^2` on an open neighborhood of $`y_0`, and let $`F` be
$`C^2` near the initial phase $`(p_0,g(y_0),b(y_0))`. Assume $`p_0` satisfies
the PDE and tangential compatibility conditions and that the initial
tangent/characteristic map is invertible. If $`b(y_0)` lies in the prescribed
open ambient domain, we construct a $`C^2` solution on a smaller open spatial
neighborhood within that domain, with $`F(Du,u,x)=0`, trace $`u(b(y))=g(y)`
near $`y_0`, and base gradient $`Du(b(y_0))=p_0`.

The implicit function theorem constructs a compatible $`C^1` momentum field.
The $`C^1` characteristic flow and its first variation propagate the
contact identity. Inverse characteristic coordinates then
identify $`Du` with a $`C^1` momentum field, giving $`u\in C^2`. A global
$`C^2` representative of the equation near the initial phase supplies the
construction; restricting the solution back to the agreement neighborhood
recovers the original $`F`. Two $`C^2` solutions with the same boundary
values and the same base momentum agree near the basepoint.

# Conservation laws and Hamilton–Jacobi equations

For scalar one-dimensional conservation laws, weak solutions and entropy
solutions are kept distinct. The Burgers shock and rarefaction profiles
satisfy the positive-time weak and entropy identities and reach their
Riemann data through a strong local initial trace. For a $`C^1` flux,
uniformly bounded entropy solutions with strong local $`L^1` initial traces
obey Kružkov's local $`L^1` contraction, so two of them with the same trace
agree almost everywhere. For a $`C^2` flux with $`f''` bounded below by a
positive constant, the Lax–Oleinik formula gives a weak solution for every
$`L^\infty` datum and the sharp one-sided bound
$`u(t,x+z)-u(t,x)\le z/(\theta t)` for $`z\ge0` when $`f''\ge\theta>0`.
This bound applies to the selected solution even when minimizers are not unique.

For smooth scalar data, the characteristic construction covers the entire
spatial line before the first degeneracy time. The maximality theorem excludes
a longer classical strip without requiring a characteristic to attain that
time; gradient blow-up along a particular characteristic additionally assumes
attainment. For a curved shock, two classical side fields satisfying
Rankine–Hugoniot and downward trace ordering give a whole-spacetime entropy
solution when the flux is convex between the traces.

For finite-dimensional systems we prove that the conservative and quasilinear
residuals agree, develop hyperbolicity and characteristic fields, record the
elementary wave predicates, construct analytic local wave families from supplied
characteristic flows, and prove the inverse-function stage of the local Riemann
solver. There is also a Bochner-valued interior weak formulation and a concrete
p-system entropy and Riemann-invariant chain. For the p-system specifically, the
shock and rarefaction branches assemble into a local mechanically
entropy-admissible Riemann solution with a strong local $`L^1` initial trace.
An almost-everywhere limit of uniformly bounded classical viscous solutions
is an entropy solution with the limiting initial datum.
For a general $`C^2` strictly hyperbolic system whose families are each
genuinely nonlinear or linearly degenerate, the local Riemann problem with
nearby states has a self-similar weak solution with a strong local $`L^1`
initial trace, glued from elementary connections between successive states
(Evans, §11.2.4); entropy admissibility is proved for the p-system.

For a convex superlinear Hamiltonian on a finite-dimensional real inner
product space and Lipschitz initial data, the Hopf–Lax value equals the
minimum over absolutely continuous paths with finite action. A straight path
from a minimizing footpoint attains it; see
{bpref "hyperbolic.hj.hopf_lax_path_formula"}[].

For one-dimensional Hamiltonians with finite Legendre transform and
Lipschitz initial data, the Hopf–Lax formula agrees with the absolutely
continuous path formula. Its operators form a semigroup on nonnegative
times, preserve order, and preserve uniform distance bounds. For convex
differentiable $`H`, the formula also gives a continuous viscosity solution
on positive time with the initial trace; bounded Lipschitz data give a
closed-time initial-value solution. Tests need only be differentiable at
contact. Spatial dependence is allowed in the scalar viscosity definitions,
while these constructed solutions use autonomous $`H`.

On a finite-dimensional real inner product space, a real-valued convex
superlinear Lagrangian and bounded uniformly continuous initial data also
construct a Hopf–Lax viscosity initial-value solution for the dual Hamiltonian.
The data need not be Lipschitz, and neither the Lagrangian nor its dual is
assumed differentiable. This theorem uses locally $`C^1` tests. Its solution is
unique for nonnegative times among solutions bounded and uniformly continuous
on each finite closed time slab.

Comparison also holds for continuous autonomous Hamiltonians on any
finite-dimensional real inner product space, using tests that are locally
$`C^1`. If the sub- and supersolution are bounded and uniformly continuous
on every finite closed time slab, initial ordering propagates to all
nonnegative times, giving uniqueness in this class. Scalar solutions defined
with differentiable-contact tests also satisfy these local-$`C^1` tests after
changing from $`(t,x)` to $`(x,t)` coordinates; the same holds separately for
sub- and supersolutions. For a position-dependent
$`H(p,x)`, uniformly Lipschitz in $`p` and with
$`|H(p,x)-H(p,y)|\le C\|x-y\|(1+\|p\|)`, comparison and uniqueness hold in
the same slab class. Perron's method gives a continuous viscosity solution
of the autonomous equation on the interior of a compact spacetime set,
between continuous sub- and supersolution barriers that agree on its
frontier.

# Weak waves and higher regularity

The variational wave theory runs on measurable operator fields, Galerkin
approximation, weak compactness, and an energy argument for uniqueness. A
differentiated Galerkin chain together with elliptic spatial lifts gives
higher regularity on the decreasing Sobolev scales in Evans's estimate. The
order-two nonsymmetric divergence-form lift is concrete. At higher orders,
the symmetric existence theorem takes a stable Galerkin scheme, Ritz
orthogonality, and elliptic lifts as hypotheses. The nonsymmetric estimate
assembly takes the two top energy bounds and the spatial recurrence as inputs.
