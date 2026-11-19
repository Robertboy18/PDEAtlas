/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Hyperbolic.Scope
import Blueprint.CodeExamples
import PDE.Hyperbolic.ConservationLaw.Burgers.AffineSolution
import CAS

/-!
# Hyperbolic equations chapter

Hyperbolic equations: classical waves, first-order equations, conservation
laws, and variational waves. The global dependency graph is emitted after
every chapter has been loaded.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- The re-elaborated proofs below keep the layout of their source files; the
-- sixty-column limit is Verso's default for short calculator snippets.
set_option verso.code.warnLineLength 100

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Hyperbolic Equations" =>
%%%
htmlSplit := .never
%%%

Hyperbolic equations carry information at finite speed. Where the heat equation
spreads a bump of data over the whole domain at once, a plucked string splits into
a left-moving half and a right-moving half, and the value at a point depends only
on the data in a cone beneath it. In nonlinear transport
and conservation laws the characteristic speed depends on the solution itself, so
for suitable decreasing initial data the characteristics of Burgers's equation
$`u_t+uu_x=0` run into one another, the gradient steepens without bound in finite
time, and the classical solution simply stops existing. The theory then has to
decide what the word "solution" means on the other side of that breakdown.

Different equations need different solution concepts. Distributional
conservation laws admit more than one weak solution, so entropy inequalities are
brought in to select among them. Hamilton–Jacobi solutions crease rather than
jump, so viscosity inequalities replace derivatives that are not there. Weak waves
want energy spaces and second-order evolution, and symmetric systems keep their
matrix structure in first-order form. Each concept comes with the
calculations that support it: explicit formulas checked against
their residuals and initial traces, energy identities yielding uniqueness and
finite propagation, the Rankine–Hugoniot and entropy conditions sorting admissible
discontinuities from inadmissible ones, and variational formulas related to
viscosity solutions under stated hypotheses.

# Propagation, shocks, and weak selection

The transport solution $`u(x,t)=g(x-tb)` is data
sliding along straight characteristics. For the one-dimensional wave equation
with unit wave speed, d'Alembert's formula

$$`u(x,t)=\tfrac12\bigl(g(x+t)+g(x-t)\bigr)+\tfrac12\int_{x-t}^{x+t}h(y)\,dy`

splits a plucked string into left- and right-moving halves. The
{ref "symbolic-sine-example"}[checked traveling-sine example]
reuses the sine profile from the heat chapter: translation preserves its
amplitude, while the heat mode decays. Its derivative identities verify both
the wave residual and the unit-speed transport equation; the transport example
also checks the initial datum. The
{ref "certified-plots"}[certified plots] of the computation chapter draw the
traveling wave $`\sin(x-t)` and the Burgers rarefaction profile as bands whose
panels are kernel-checked enclosure theorems. Burgers's equation $`u_t+uu_x=0` has
characteristics that carry their own speed and, for suitable decreasing initial
data, run into each other in finite time. Conservation laws have weak solutions
that may contain shocks, governed by the Rankine–Hugoniot condition.
Hamilton–Jacobi equations have continuous solutions that develop creases rather
than jumps.

Entropy inequalities do more than narrow the field: in scalar classes with a
comparison theorem they pick out exactly one admissible solution, which is the
best outcome available once uniqueness of weak solutions has been lost.

For the classical geometric perspective, see {Informal.citet "courant-hilbert-1962"}[].
{Informal.citet "evans-2010"}[] provides a route through the analytic tools: the early chapters for
classical wave formulas and nonlinear first-order equations, §7.2 for
variational waves, and the later chapters for Hamilton–Jacobi equations,
conservation laws, and nonlinear waves. {Informal.citet "crandall-lions-1983"}[]
develops the viscosity-solution approach to Hamilton–Jacobi equations.
For weak evolution in function spaces, see
{Informal.citet "lions-magenes-1972"}[].

## Propagation and characteristics

### Characteristic geometry

A first-order PDE $`a(x,u)\cdot\nabla u=b(x,u)` collapses to an ODE along curves
called *characteristics*, determined by the coefficient field $`a`. You solve
those ODEs and invert the characteristic map back to physical coordinates, and
you have a local solution wherever the construction is regular and the map
remains invertible. Loss of invertibility is one way this local construction
can break down.

For a one-dimensional quasilinear system the characteristic speeds are the
eigenvalues of the coefficient or flux-Jacobian matrix. Hyperbolicity means
those speeds are real and the eigenbasis is complete; strict hyperbolicity
means they are also distinct. Each eigenpair gives a characteristic field.
Whether a matching Riemann invariant exists is a further question, requiring
integrability conditions, and the p-system section later constructs them for
that particular model.

The geometry takes a different form for each equation.

- *Transport equation* ($`u_t+b\cdot\nabla u=0`): the solution is
  constant along characteristics, so $`u(x,t)=u_0(x-bt)` (Evans, 2010,
  pp. 18–19).

- *Wave equation* ($`u_{tt}-c^2u_{xx}=0`): the two families of
  characteristics $`x\pm ct=\text{const}` give d'Alembert's formula
  (Evans, 2010, pp. 65–69).

- *Conservation laws* ($`u_t+f(u)_x=0`): characteristics travel at speed
  $`f'(u)`, which depends on the solution itself. Compressive initial data can
  drive them together and cause gradient blow-up in finite time. Classical
  regularity then fails; an entropy continuation may contain shocks. This
  geometric breakdown motivates the move from classical to weak to entropy
  solutions.

- *Hamilton–Jacobi* ($`u_t+H(\nabla u)=0`): the characteristics of the
  associated scalar conservation law determine the gradient in one space
  dimension while the solution is smooth; recovering the solution by spatial
  integration also requires fixing its time-dependent additive constant
  (Evans, 2010, p. 144; Crandall and Lions,
  1983).

For comparison, the heat equation
$`u_t=u_{xx}` has a parabolic principal symbol, not a real characteristic cone,
so nothing limits how fast it propagates. Its Gaussian kernel is positive
everywhere at every positive time, so nonnegative, nonzero continuous
compactly supported data give a positive solution everywhere immediately.
Sign-changing data can cancel at individual points. Hyperbolic equations have
finite domains of dependence, set by their characteristic velocities.

## Hypotheses carried by each solution concept

Classical transport and wave statements carry differentiability, support,
and initial-data hypotheses. Local energy is integrated over moving spatial
regions, so finite propagation depends on the geometry of those regions as
much as on the PDE identity.

Nonlinear first-order equations use characteristic ODEs for the position, the
unknown, and the gradient, and a noncharacteristic condition is what makes the
characteristic coordinates locally invertible. Conservation laws work
differently, with distributional identities, entropy pairs, Rankine–Hugoniot
relations, and strong local initial traces.

Weak wave equations live in a Gelfand triple with second-order time
dynamics. Symmetric first-order systems carry matrix symmetry, coercivity,
and coefficient regularity. Hamilton–Jacobi statements keep the classical,
variational, and viscosity notions apart rather than treating them as
synonyms.

## From classical propagation to weak selection

The first route moves from transport to waves:

$$`\text{characteristics}\longrightarrow\text{explicit wave formulas}
\longrightarrow\text{energy identity}
\longrightarrow\text{finite propagation and uniqueness}.`

The nonlinear first-order route moves from smooth characteristics to
nonsmooth solution concepts:

$$`\text{characteristic family}\longrightarrow\text{local classical solution}
\longrightarrow\text{weak conservation law}
\longrightarrow\text{entropy or viscosity selection}.`

The variational route builds weak waves by Galerkin approximation, proves
energy uniqueness, and then puts differentiated time estimates together with
elliptic spatial lifts to get higher regularity. The semigroup section
supplies the abstract language for linear evolution generated by an
operator.

## The affine Burgers solution, step by step

Burgers's equation with affine data $`u(0,x)=ax+c` is solved by
$`u(t,x)=(ax+c)/(1+at)` for as long as the denominator does not vanish. The
denominator is also the derivative of the characteristic position with respect
to its initial footpoint. Its nonvanishing is therefore the geometric
condition that lets us recover a unique footpoint from the current position.
The division in the formula and the invertibility of characteristics carry
the same restriction.

The {bpref "hyperbolic.burgers.affine_solution"}[affine-solution theorem]
follows by differentiating on $`1+at\ne0` and checking that
$`u_t+u\,u_x=0`:

```Blueprint.leanExample
open BurgersEquation PDE.Common in
open PDE (SpaceTime partialDeriv) in
example (a c : ℝ) (x : SpaceTime 1) (hden : burgersDenom a x ≠ 0) :
    partialDeriv (0 : Fin 2) (burgersAffineSolution a c) x =
      -a * burgersNumer a c x * (burgersDenom a x)⁻¹ * (burgersDenom a x)⁻¹ := by
  unfold burgersAffineSolution burgersNumer burgersInvDenom burgersDenom
  unfold burgersDenom at hden
  cas
```

```Blueprint.leanExample
open BurgersEquation PDE.Common in
open PDE (SpaceTime partialDeriv) in
example (a c : ℝ) (x : SpaceTime 1) (hden : burgersDenom a x ≠ 0) :
    partialDeriv (1 : Fin 2) (burgersAffineSolution a c) x =
      a * (burgersDenom a x)⁻¹ := by
  unfold burgersAffineSolution burgersNumer burgersInvDenom burgersDenom
  unfold burgersDenom at hden
  cas
```

```Blueprint.leanExample
open BurgersEquation PDE.Common in
open PDE (SpaceTime partialDeriv) in
example (a c : ℝ) (x : SpaceTime 1) (hden : burgersDenom a x ≠ 0) :
    partialDeriv (0 : Fin 2) (burgersAffineSolution a c) x +
        burgersAffineSolution a c x *
          partialDeriv (1 : Fin 2) (burgersAffineSolution a c) x = 0 := by
  unfold burgersAffineSolution burgersNumer burgersInvDenom burgersDenom
  unfold burgersDenom at hden
  cas
```

## Viscosity solutions

Crandall and Lions introduced viscosity solutions in 1983 ("Viscosity
solutions of Hamilton–Jacobi equations", *Trans. AMS* 277) for first-order
Hamilton–Jacobi equations. The trick is to stop differentiating the
solution. Instead you test the PDE against smooth functions that touch the
solution locally, requiring the subsolution inequality at every upper
contact and the supersolution inequality at every lower one.

Concretely, $`u` is a viscosity subsolution of $`u_t+H(\nabla u)=0` when the
following holds: whenever a smooth $`\phi` touches $`u` from above at
$`(x_0,t_0)`, meaning $`\phi\geq u` nearby with equality at the point, we have
$`\phi_t(x_0,t_0)+H(\nabla\phi(x_0,t_0))\leq 0`. Every derivative in that
definition belongs to $`\phi`. None belongs to $`u`.

Given hypotheses that supply barriers and a comparison theorem, Perron's
method gives existence, comparison gives uniqueness, and the corresponding
limit theorems give stability. These are three separate results;
none of them falls out of the definition by itself. Chapter 10 of Evans is
the textbook treatment, and {Informal.citet "crandall-ishii-lions-1992"}[] is
the standard reference for the general theory.

`WeakSolution` records the distributional equation, and an entropy solution
adds the inequality that picks out the physical branch. A theorem about an
explicit Burgers shock or rarefaction concerns that profile only. Viscosity
definitions quantify over touching test functions rather than evaluating a
derivative that does not exist. Characteristic constructions are local, with
the time interval, invertibility neighborhood, and noncharacteristic assumption
together fixing where the resulting classical solution is valid.

## Coverage and the transition to fluids

Characteristics construct classical solutions, energy estimates control them,
and entropy and viscosity conditions give meaning to equations after classical
differentiability is lost. The theorem chains cover classical transport and waves,
weak-wave evolution, selected semilinear energies, scalar Riemann problems,
local system constructions, and one-dimensional Hopf–Lax evolution.

For Hamilton–Jacobi equations, the one-dimensional Hopf–Lax and
autonomous-control constructions sit beside a finite-dimensional comparison
theorem. For continuous autonomous $`H`, viscosity sub- and supersolutions
tested with local $`C^1` functions preserve their initial ordering when both
are bounded and uniformly continuous on every finite closed time slab. The
same holds for position-dependent $`H(p,x)` that is uniformly Lipschitz in
$`p` with spatial variation bounded by $`C\|x-y\|(1+\|p\|)`. A scalar
coordinate change brings the one-dimensional differentiable-contact
predicates into this comparison class. Perron's method gives continuous
solutions of the autonomous equation on compact spacetime sets between
boundary barriers that agree on the frontier. For state-dependent optimal
control on a finite-dimensional state space, with bounded Lipschitz dynamics
and a bounded Borel running cost that is Lipschitz in the state, the
{bpref "hyperbolic.hj.control_terminal_value"}[value function] is the unique
bounded uniformly continuous viscosity solution of the terminal
Hamilton–Jacobi–Bellman problem.

For conservation laws we have scalar Burgers solutions, local characteristic
and wave-map geometry for systems, and a concrete p-system development.
Scalar entropy solutions with strong initial traces satisfy Kružkov's local
$`L^1` contraction and are unique, the Lax–Oleinik formula gives weak
solutions for uniformly convex fluxes, and almost-everywhere limits of bounded
viscous solutions are entropy solutions. For a general $`C^2` strictly
hyperbolic system whose families are each genuinely nonlinear or linearly
degenerate, the Riemann problem with nearby states has a local self-similar
weak solution with a strong initial trace, glued from elementary connections.

On nonlinear waves, the energy identities and finite-propagation estimates
apply to given regular solutions. There is also a construction on a
nonempty bounded open domain: symmetric, bounded, uniformly elliptic
coefficients give a linear Dirichlet wave evolution, and a locally Lipschitz
map from $`H^1_0\times L^2` to $`L^2` gives a maximal nonlinear trajectory.
Each compact time interval before its lifetime satisfies the weak wave
equation and both initial traces. Pointwise power nonlinearities need their
own mapping estimates, and the global subcritical and critical theories need
more than this construction.

On all of space, a globally Lipschitz reaction with $`f(0)=0` instead gives
a global forward solution for every $`H^1\times L^2` datum. The
{bpref "hyperbolic.semiwave.whole_space_cauchy"}[whole-space Cauchy theorem]
identifies both strong initial traces and the weak PDE, and proves uniqueness
within the energy-continuous PDE class. Smooth compact Cauchy data on
$`\mathbb R^3` give a
{bpref "hyperbolic.semiwave.maximal_smooth_wave"}[maximal smooth wave]
for every smooth scalar reaction fixing zero, and the nonlinear-wave section
proves energy conservation for waves whose displacement slices are separately
compactly supported.

For symmetric first-order systems on all of space, the construction reaches
the original equation with $`H^1` initial data and $`L^2_tH^1_x` forcing.
The coefficient entries lie in spatial $`W^{1,\infty}`, are continuous in
time in the $`L^\infty` norm on the chosen interval, and have uniformly
bounded spatial derivative norms. The solution has an $`L^\infty_tH^1_x`
bound and a continuous $`L^2` initial trace. Under the same coefficient
conditions, approximation also constructs a solution for rough $`L^2`
initial data and $`L^2_tL^2_x` forcing, with a continuous $`L^2` representative.
Uniqueness holds among Bochner $`L^2` classes satisfying the weak equation
with its initial boundary term. The construction satisfies both separated
tests and smooth compactly supported spacetime tests.

# Transport and Classical Waves

{include 2 Blueprint.Chapters.Hyperbolic.Transport}
{include 2 Blueprint.Chapters.Hyperbolic.CanonicalForm}
{include 2 Blueprint.Chapters.Hyperbolic.ClassicalWave}
{include 2 Blueprint.Chapters.Hyperbolic.NonlinearWaves}

# Weak Waves and Evolution

{include 2 Blueprint.Chapters.Hyperbolic.WeakWaves}
{include 2 Blueprint.Chapters.Hyperbolic.EnergyUniqueness}
{include 2 Blueprint.Chapters.Hyperbolic.HigherRegularity}
{include 2 Blueprint.Chapters.Hyperbolic.Semigroups}

# Nonlinear First-Order Equations

{include 2 Blueprint.Chapters.Hyperbolic.NonlinearFirstOrder}
{include 2 Blueprint.Chapters.Hyperbolic.HamiltonJacobi}

# Symmetric Systems and Conservation Laws

{include 2 Blueprint.Chapters.Hyperbolic.SymmetricSystems}
{include 2 Blueprint.Chapters.Hyperbolic.ConservationLaws}

# Coverage and Open Problems

For classical propagation we have d'Alembert's formula with both initial identities, energy
identities with domain of dependence and finite propagation, the Kirchhoff,
Poisson, and general odd- and even-dimensional formulas as classical
solutions, Duhamel's principle, and the semilinear energy estimates as a
priori bounds on a given solution. The Dirichlet construction gives a maximal
energy-space wave and identifies its weak equation. On all of space, globally
Lipschitz reactions vanishing at zero give global energy existence and
uniqueness for arbitrary $`H^1\times L^2` data. Smooth compact data in
three dimensions give a maximal smooth wave for every smooth reaction
fixing zero. For a merely continuous reaction, conservation from separately
compact slices is proved in dimensions one and two and under a quadratic lower
bound on the potential near zero. At a finite lifespan the displacement is
unbounded on every terminal time strip.

For nonlinear first-order
equations we have the characteristic constructions,
including the Picard family that preserves the contact relation and the
smooth-dependence theorem for first variations. Local $`C^2` regularity of
the equation and boundary data, together with compatibility and
noncharacteristicity at the basepoint, supplies the characteristic family
and a local $`C^2` solution, unique near the basepoint among $`C^2` solutions
with the same boundary values and base momentum.

For conservation laws the explicit Burgers profiles sit beside Oleinik and
Kružkov uniqueness, the Lax–Oleinik solution for uniformly convex fluxes,
its Riemann solutions and N-wave asymptotics. For systems we have the local
Riemann solver, gradient blowup in Riemann coordinates, small viscous
profiles, and the passage to the limit in a convergent family of viscous
solutions; the Riemann solver has no global counterpart. For Hamilton–Jacobi equations the
one-dimensional
Hopf–Lax construction sits beside finite-dimensional comparison for sub- and
supersolutions in the slab class. For weak waves the elliptic lifts on which
the higher-regularity chain relies are named. Open items include existence
for scalar conservation laws with nonconvex flux, compactness of viscous
approximations, and the quasilinear and global power-wave theories.

{include 2 Blueprint.Chapters.Hyperbolic.Scope}
