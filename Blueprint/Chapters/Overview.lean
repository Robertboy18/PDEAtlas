/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George, Peicong Song, Anima Anandkumar
-/

import Blueprint.Bibliography
import Blueprint.CodeExamples
import Blueprint.Commands.Figures
import Blueprint.Commands.Notebook
import CAS
import Verso
import VersoBlueprint

/-!
# Introduction

A heat mode on a rod, followed from its derivative calculation to the
analysis a PDE problem needs: solution concepts, the mathematical choices
behind the library, and how checked computation enters analytic proofs.
The source documents cited by the theorem cards of the whole book are
registered here. The page renders as one route (`htmlSplit := .never`).
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false in
#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
tag := "pde-introduction"
%%%

:::source_document "evans-pde"
%%%
title := "Partial Differential Equations, Second Edition"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "simon-compactness"
%%%
title := "Compact Sets in the Space Lp(0,T;B)"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "marcus-mizel-1972"
%%%
title := "Absolute Continuity on Tracks and Mappings of Sobolev Spaces"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "fefferman-navier-stokes"
%%%
title := "Existence and Smoothness of the Navier–Stokes Equation"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "majda-bertozzi"
%%%
title := "Vorticity and Incompressible Flow"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "temam-navier-stokes"
%%%
title := "Navier–Stokes Equations: Theory and Numerical Analysis"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "wiedemann-euler-weak"
%%%
title := "Existence of Weak Solutions for the Incompressible Euler Equations"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "leray-1934"
%%%
title := "Sur le mouvement d'un liquide visqueux emplissant l'espace"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "chen-hou-boussinesq"
%%%
title := "Stable Nearly Self-Similar Blowup of the 2D Boussinesq and 3D Euler Equations \
  with Smooth Data I: Analysis"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

:::source_document "hou-wang-yang-2025"
%%%
title := "Nonuniqueness of Leray–Hopf Solutions to the Unforced Incompressible \
  3D Navier–Stokes Equation"
kind := .text
pageRoot := "Blueprint/Sources"
%%%
:::

Imagine a rod with a warm middle and both ends held at zero temperature.
Heat flows toward the cold ends, and the temperature falls. The heat equation
describes that evolution. An explicit formula gives one solution; an energy
estimate proves uniqueness and controls changes in the initial temperature.

On a rod with its ends held at zero temperature, a sine-shaped profile decays
without changing shape:
$$`
u(t,x)=e^{-t}\sin x,\qquad 0\le x\le\pi.
`
Here time and length have been scaled so that the heat equation is
$`u_t=u_{xx}`. Differentiating once in time and twice in space gives
$$`
\begin{aligned}
u_t&=-e^{-t}\sin x,\\
u_x&=e^{-t}\cos x,\\
u_{xx}&=-e^{-t}\sin x.
\end{aligned}
`
So $`u_t=u_{xx}`: the profile satisfies the heat equation. It also vanishes at
both ends of the rod, and at time zero it is $`\sin x`. These are separate
facts that together identify the solution and its data.

The first calculation checks $`u_t-u_{xx}=0`.

{leanpde_notebook}

There is a reason this calculation closes so neatly. The second derivative
of $`\sin x` is $`-\sin x`, so substituting $`u(t,x)=a(t)\sin x` reduces the
PDE to $`a'(t)=-a(t)`. A spatial eigenfunction has turned the evolution into
an ordinary differential equation. For the higher mode $`\sin(kx)`, with
positive integer $`k`, the same calculation gives
$`u_k(t,x)=e^{-k^2t}\sin(kx)`. Finer oscillations decay faster.

The same initial shape behaves differently on a vibrating string. With zero
initial velocity, the wave equation gives $`u_k(t,x)=\cos(kt)\sin(kx)`.
Both ends stay fixed in each problem. Compare their evolution below.

{leanpde_mode_explorer}

For the heat mode, try $`k=3`. Its amplitude at time $`t` equals the amplitude
of the first mode at time $`9t`. At the same amplitude, the extra oscillations
make the spatial gradient larger and increase the rate of heat dissipation. For the wave
mode, displacement and velocity exchange energy as the string vibrates.

The calculation also exposes what has not yet been answered. It gives one
solution; uniqueness needs an argument that applies to every solution in a
specified class. Replacing the initial sine by a rough temperature profile
requires a construction that survives limits. Replacing the rod by all of
space leads to the Gaussian kernel, whose initial point mass is understood
through convergence against test functions rather than pointwise substitution.

# What a partial differential equation asks

A differential equation relates an unknown function to its derivatives, and a
partial differential equation has several independent variables. Schematically
a PDE is a relation
$$`
F\bigl(x,u(x),Du(x),D^2u(x),\ldots,D^ku(x)\bigr)=0
`
on a domain $`\Omega`. It may be linear or nonlinear in $`u` and its
derivatives, stationary or evolutionary. The notation compares values at a
point. Yet the questions we care about concern a whole domain or an entire
evolution. For the rod, holding the ends at zero lets heat escape; insulating
them imposes a zero normal derivative and conserves total heat. The interior
equation is the same.

The heat equation $`u_t-\Delta u=0`, the wave equation
$`u_{tt}-c^2\Delta u=0`, and the incompressible Navier–Stokes equations
$$`
\partial_t u +(u\cdot\nabla)u-\nu\Delta u+\nabla p=f,\qquad
\operatorname{div}u=0
`
all need this surrounding information. A domain, function spaces, boundary
and initial data, and a meaning for the derivatives turn a differential
identity into a PDE problem.

For Poisson's equation, the choice of boundary data appears directly in the
problem statement:
$$`
-\Delta u=f\quad\text{in }\Omega,\qquad u=g\quad\text{on }\partial\Omega.
`
The statement still leaves us work to do. Does $`g` mean an ordinary
restriction of a continuous function, or a Sobolev trace? Is $`f` continuous,
square-integrable, or a distribution? The answers determine whether we seek
pointwise second derivatives or an integral identity. They also determine
which estimates are available. An interior equation alone leaves the boundary
value free, just as the heat residual alone did not choose the rod's ends.

Hadamard's *well-posedness* asks for existence, uniqueness, and continuous
dependence on the data. Existence says there is a solution in our chosen class.
Uniqueness says the same data cannot produce two solutions in that class.
Continuous dependence says that a small change in the data produces a small
change in the solution, measured in specified norms. This last requirement
is what makes an approximation to the data useful.

We can see it in the rod without leaving the sine functions. Add a small,
finer oscillation to the initial temperature:
$$`
g_\delta(x)=\sin x+\delta\sin(4x).
`
Linearity gives the corresponding solution
$$`
u_\delta(t,x)=e^{-t}\sin x+\delta e^{-16t}\sin(4x).
`
Subtracting the original solution $`u_0(t,x)=e^{-t}\sin x` leaves just the
perturbation. Its size in the $`L^2(0,\pi)` norm is
$$`
\|u_\delta(t)-u_0(t)\|_{L^2}
=|\delta|\sqrt{\frac{\pi}{2}}e^{-16t}
\le \|g_\delta-g_0\|_{L^2},\qquad t\ge0.
`
Here the $`L^2` norm measures the square root of the integrated squared
temperature error. Heat flow damps that error; the fine oscillation disappears
even faster than the original profile. The formula constructs solutions for
these particular data. The energy argument below will explain why the
same stability estimate applies much more generally, and why it also gives
uniqueness when the initial difference is zero.

{leanpde_figure "heat-stability"}

Trying to recover the past temperature reverses this advantage. Fix $`T>0`.
The final profiles $`e^{-n^2T}\sin(nx)` tend to zero in $`L^2` as
$`n\to\infty`, but their initial profiles $`\sin(nx)` all have norm
$`\sqrt{\pi/2}`. Arbitrarily small errors at the final time can therefore
hide a substantial initial oscillation. Even on these smooth, exactly
solvable data, the inverse heat map is not continuous in $`L^2`.
Well-posedness belongs to an equation *together with* its data, direction
of evolution, solution class, and topology.

For linear second-order equations, the principal part explains much of this
behavior. Elliptic equations describe equilibrium. Harmonic functions obey
mean-value identities and maximum principles, so boundary values constrain
the interior. Divergence-form operators
$$`
-\operatorname{div}(A(x)\nabla u)+b(x)\cdot\nabla u+c(x)u=f
`
are particularly suited to integration by parts: their weak formulations
expose bilinear forms whose coercivity can give existence and uniqueness.
Parabolic equations describe diffusion. The decay of the higher sine modes is
one manifestation of smoothing; spreading a localized pulse with a Gaussian
is another. Hyperbolic equations describe propagation along characteristics,
with finite speed in the wave equation.

{leanpde_figure "pde-zoo"}

The three panels show a steady harmonic saddle, a spreading heat pulse, and a
traveling wave. The distinction matters when choosing a proof: a maximum
principle controls an equilibrium through its boundary, a diffusion estimate
controls smoothing, and characteristics follow information as it moves.
Nonlinearity can change the solution class itself. A smooth initial profile
for a conservation law may develop a shock. The distributional equation
continues to make sense, but entropy inequalities are needed to select an
admissible solution. Hamilton–Jacobi equations instead use viscosity
solutions, defined through comparison with touching test functions.

Fluid mechanics brings these methods together. Euler describes inviscid
transport constrained by incompressibility; Navier–Stokes adds viscous
diffusion. Pressure is recovered through an elliptic equation even though
velocity evolves in time. Leray's global weak solutions to three-dimensional
Navier–Stokes supply energy control in a weak solution class. Classical
regularity and uniqueness require further arguments in a specified class.

# How the subject acquired its language

The higher heat modes suggest a way to handle more general initial data:
expand the temperature in a sine series and evolve each coefficient. For a
finite sum, differentiation and addition commute and the calculation is
immediate. For an infinite series, convergence, differentiation, and recovery
of the initial function become part of the problem. This is an old source of
new analysis.

D'Alembert's wave equation already raised the question: its solutions involve
arbitrary traveling profiles, while the eighteenth-century understanding of a
function was tied to analytic expressions, and Euler, d'Alembert, and the
Bernoullis disagreed over which shapes could count as initial data. Fourier's
trigonometric series represented rough initial temperatures and evolved them
by damping high frequencies long before convergence and termwise
differentiation were understood. These two equations pushed analysis toward
the arbitrary function, rigorous integration, and Fourier analysis.

Potential theory exposed a different difficulty. Dirichlet's principle
related a harmonic function with prescribed boundary values to a minimizer of
an energy. Riemann used the principle successfully, but Weierstrass objected
to the existence argument: an energy can have an infimum without attaining
it. Choosing functions whose energies approach the best possible value does
not yet produce a best function. Completeness, compactness, and lower
semicontinuity explain when that limiting step works. We will meet the same
issue when constructing weak solutions from approximations.

Hilbert-space methods gave linear PDE an abstract setting, but limits still
need not preserve classical derivatives. Sobolev's weak derivatives made it
possible to complete smooth functions in norms controlling both values and
derivatives. Schwartz's distributions gave differentiation a setting in which
it is always defined and continuous. Leray's Navier–Stokes construction
combined a weak formulation with energy control to obtain global solutions,
without thereby obtaining global smoothness or uniqueness. This remains a
productive way to approach an equation: choose a solution concept stable
under the estimates, construct a solution there, and then investigate its
regularity. Entropy and viscosity solutions make different choices because
shocks and nondifferentiable value functions present different obstacles.

Computer-assisted analysis creates another need for a usable mathematical
object. We may be able to inspect the idea of an estimate without reading
every one of its arithmetic steps. A certificate records data from which a
checker can prove the claimed identity or bound. The search for it can use
heuristics; the accepted result has a precise mathematical meaning. PDEAtlas
uses such certificates alongside weak derivatives and energy estimates, so
that a long calculation can enter an argument through an ordinary theorem.

# Solution concepts

Suppose the initial temperature on the rod has a jump. Finite sine sums still
give smooth approximate evolutions, but their limit at time zero need not be
differentiable. Requiring the same pointwise calculus at every stage would
exclude the datum we wanted to study. We need a meaning of differentiation
that makes sense before smoothing has occurred.

Our sine mode is a classical solution: all derivatives in the equation exist
in the ordinary sense. Classical regularity is often the conclusion we hope
to recover from an existence proof. It can be too much to demand of an
approximation limit, and some nonlinear equations destroy it during the
evolution.

A distributional solution tests the equation against smooth compactly
supported functions and moves derivatives by integration by parts. If $`u` and
$`f` are locally integrable, $`-\Delta u=f` in distributions means
$$`
\int_\Omega u\,(-\Delta\varphi)
=\int_\Omega f\,\varphi
\qquad
\text{for every }\varphi\in C_c^\infty(\Omega).
`
The unknown no longer needs two pointwise derivatives. The test function
supplies them, and its compact support removes the boundary terms. The
Heaviside step makes the change tangible: if $`H(x)` is zero to the left of
the origin and one to the right, then
$$`
\langle H',\varphi\rangle
=-\int_0^\infty\varphi'(x)\,dx
=\varphi(0).
`
It has no classical derivative at the origin, but its
{bpref "foundations.distributions.heaviside_derivative"}[distributional derivative]
is the Dirac mass.

Sobolev {bpref "sobolev.weak_derivative"}[weak derivatives] impose an
additional requirement: the distributional derivative must be represented by
an $`L^p` function. Thus $`W^{1,p}(\Omega)` controls the integrability of both
the function and its first weak derivatives. The step function illustrates
the distinction: its Dirac derivative is a distribution, but is not an
$`L^p` function across the jump. Distributional and Sobolev derivatives solve
related problems with different amounts of regularity.

For the elliptic equation $`-\operatorname{div}(A\nabla u)=f`, moving one
derivative onto a test function gives
$$`
\int_\Omega A\nabla u\cdot\nabla v
=\int_\Omega f\,v
\qquad\text{for every admissible test function }v.
`
The left side is a bilinear form in $`u` and $`v`. This lets
{bpref "elliptic.lax_milgram"}[Lax–Milgram] apply once the form is bounded
and coercive and the right side is a continuous functional. Monotone
operators, compactness, and Fredholm theory extend this approach to other
equations. The zero-boundary space $`H_0^1(\Omega)` encodes a homogeneous
Dirichlet condition by closure of compactly supported smooth functions. A
trace theorem, when available on the domain, relates that condition to the
boundary values of the function.

Variational formulations express the equation as an identity against test
functions. When an energy is available, its first variation can yield this
identity. For example, Dirichlet's principle seeks a minimizer of
$$`
E(u)=\frac12\int_\Omega |\nabla u|^2-\int_\Omega fu.
`
For an admissible variation $`v`, expand $`E(u+\varepsilon v)` and
differentiate at $`\varepsilon=0`. At a minimizer the result is
$$`
0=\left.\frac{d}{d\varepsilon}E(u+\varepsilon v)\right|_{\varepsilon=0}
=\int_\Omega\nabla u\cdot\nabla v-\int_\Omega fv.
`
This is the weak Poisson equation. The calculation explains what a minimizer
would satisfy. To show that a
{bpref "methods.direct_method.convex_minimizer"}[minimizer exists], we need
coercivity to bound a minimizing sequence, weak compactness to extract a
limit, weak closedness to keep the limit admissible, and weak lower
semicontinuity to keep its energy minimal. The first variation and the
existence argument answer different parts of Dirichlet's principle.

Time adds a further issue. For weak heat flow, the spatial energy naturally
controls $`u` in $`L^2(0,T;V)`, while the equation controls $`u_t` in
$`L^2(0,T;V^*)`. A typical choice is $`V=H_0^1(\Omega)` and
$`H=L^2(\Omega)`, with the dense continuous inclusions
$`V\hookrightarrow H\hookrightarrow V^*` forming a
{bpref "parabolic.gelfand_triple"}[Gelfand triple]. The time derivative is
a functional on spatial test functions; it need not itself lie in $`H`.

An $`L^2` class in time has no preferred value at time zero. Lions–Magenes
theory recovers an $`H`-continuous representative and an
{bpref "parabolic.lions_magenes_energy_identity"}[energy identity] from the
two time-space bounds. This is how initial data can become meaningful again
after an existence argument has passed through almost-everywhere classes.

Fluid mechanics adds named classes because their extra conditions do
mathematical work. A
{bpref "fluid.navier_stokes.leray_hopf"}[Leray–Hopf solution] satisfies the
weak Navier–Stokes equations together with integrability, weak continuity, and
an energy inequality; a suitable weak solution carries the local energy
inequality needed for partial regularity; a
{bpref "fluid.navier_stokes.classical"}[classical solution] has enough
regularity for pointwise calculus. A theorem about one class says nothing
about another until a regularity or comparison argument connects them.

For
{bpref "hyperbolic.conservation.entropy_solution"}[entropy solutions],
an inequality selects among distributional solutions of a nonlinear
conservation law. For
{bpref "hyperbolic.hj.viscosity_solution"}[viscosity solutions],
how smooth test functions touch a possibly nondifferentiable function from
above or below is what matters.

# Formalization in Lean

{leanpde_figure "formalization-routes"}

For the sine mode, "the boundary term vanishes" can be checked by evaluating
the sine at zero and $`\pi`. For a weak solution in a zero-boundary Sobolev
space, the same words refer to approximation or traces. The diagram shows
why moving between solution concepts needs a mathematical argument: an
integration-by-parts step moves in one direction, a regularity theorem may
permit the reverse direction, and minimizing an energy introduces its own
conditions.

In several variables the Fréchet derivative is a continuous linear map; applying it to a coordinate
direction gives a partial derivative. In one dimension we use the ordinary
scalar derivative. Building these operations from Mathlib's definitions lets
a coordinate calculation feed into theorems about linear maps and norms.
The mathlib4 discussion
[Partial derivatives](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Partial.20derivatives.html)
explains why coordinates, differentiation along a line, and Fréchet
differentiation need to be distinguished. Regularity hypotheses tell us
when we may move between them.

There is a less familiar consequence of using these definitions. Lean
functions are total: division, logarithms, square roots, and differentiation
return values even outside the domain where a textbook uses their usual
rules. We can write $`\Delta u` without first proving that $`u` is twice
differentiable. To interpret it as a classical Laplacian, we must supply the
regularity that justifies the two differentiations. Similarly, the rational
identity in the opening notebook keeps its nonzero-denominator assumption.
The ability to write an expression does not grant the calculus rule we want
to apply to it.

Equality needs comparable care. A function can change on a set of measure
zero without changing its $`L^p` class or the distribution it represents.
Such a change can still alter a pointwise boundary value. To recover a
pointwise statement from an almost-everywhere one, we need further structure,
such as continuous representatives. The time-continuity theorem for weak
heat flow is one example of this work, not a matter of changing notation.

Boundary regularity presents another choice. "Let $`\Omega` be smooth" can
mean many things depending on the theorem: extension, trace, surface measure,
Green's identity, elliptic estimates, and boundary flattening need different
geometric assumptions. Where a proof uses a chart, a cutoff, a flattening
map, a Jacobian estimate, or an orientation, PDEAtlas can take that object
and its properties as explicit input. This makes a local analytic argument
usable before every geometric construction is available. It also leaves an
obligation visible: a theorem assuming those data is not yet a construction
of them from a Lipschitz or smooth boundary.

## Lean, Mathlib, and the trusted core

Lean is both a programming language and an interactive theorem prover. Its
logic identifies propositions with types and proofs with terms: a statement
such as
$$`
\forall x\in\Omega,\; \Delta u(x)=f(x)
`
is a type, and a proof is a term of that type. A tactic helps construct the
term; the kernel checks it against the statement. This separation lets us
use elaborate search procedures without making their every decision part
of the mathematical justification. A mistaken candidate still needs to pass
the checker.

Mathlib supplies the shared objects: real and complex numbers, measures and
Bochner integrals, normed spaces and continuous linear maps, derivatives and
distributions. Its Fourier analysis, weak topologies, spectral results, and
compact operators support the later arguments. Reusing these definitions
matters when two proofs meet. The derivative returned by the CAS and the
derivative used by an energy theorem should describe the same operation;
otherwise every application would need another equivalence proof. The
expression language used for computation therefore comes with theorems
connecting its interpretation to ordinary Mathlib functions.

CAS, bare `cega`, ordinary proofs, and the numerical checks are checked in the
kernel. Users can explicitly opt into `cega [fast]` for closed finite certificates
and polynomial interval evaluation; under the fast build profile these checks
additionally trust Lean's compiler and native evaluation, and the results that use
them inherit the generated native axioms. The default build profile checks them in
the kernel. If these routes cannot
certify the goal, the tactic falls back to kernel CEGA; the exponential,
logarithmic, and other proof-bearing planner routes remain unchanged.

The kernel checks the implication we stated, relative to the foundations and
assumptions it uses. Choosing that statement is still our responsibility.
A proof of a residual identity cannot detect that the author meant to ask
for the initial-boundary value problem. Nor can it decide whether an equation
models a particular fluid or whether the prose describes a cited paper
correctly.

We follow {Informal.citet "evans-2010"}[] from classical formulas through
Sobolev spaces to weak equations, variational methods, conservation laws,
and Hamilton–Jacobi theory.
{bpref "foundations.pde_problems.problem"}[PDE problem records] distinguish
the residual, initial data, boundary data, and regularity of a solution.

## From a paper theorem to a Lean theorem

Take the weak Poisson problem on a bounded open domain
$`\Omega\subset\mathbb R^n`, $`n\ge1`, with zero boundary data.
For $`f\in L^2(\Omega)`, choose $`V=H_0^1(\Omega)` and set
$$`
a(u,v)=\int_\Omega\nabla u\cdot\nabla v,\qquad
F(v)=\int_\Omega fv.
`
Cauchy–Schwarz bounds both expressions. Poincaré's inequality makes the
gradient control the full $`H^1` norm on $`V`, giving coercivity of $`a`
and continuity of $`F`. Lax–Milgram then supplies a unique $`u\in V` with
$`a(u,v)=F(v)` for every $`v\in V`. Unfolding the two definitions gives
exactly the weak equation.

Lax–Milgram applies to a bounded coercive form on any real Hilbert space.
The Poisson argument verifies those hypotheses for the gradient form. A coefficient matrix
$`A` changes the boundedness and coercivity estimates, but leaves the
abstract theorem available. A claim of classical regularity adds another
argument beyond the weak existence result.

A paper can distribute these assumptions over a chapter. The Lean statement
has to gather the ambient spaces, measures, exponents, coefficient and domain
conditions, and solution class.
An interior regularity theorem, for example, has no boundary conclusion,
although both results go by the name elliptic regularity.

## Five recurring proof patterns

An explicit solution gives us something to calculate. To prove uniqueness,
handle rough data, or solve an equation without a formula, we need arguments
that use less information about the unknown. The following patterns explain
how the analysis grows beyond the opening example.

_Explicit formulas and residuals._ On all of $`\mathbb R^n`, the heat kernel is
$$`
\Gamma(x,t)
=\frac{1}{(4\pi t)^{n/2}}
\exp\left(-\frac{|x|^2}{4t}\right),
\qquad t>0,
`
and differentiation gives the
{bpref "parabolic.heat_kernel_equation"}[heat equation] at positive time.
The spatial and time derivatives produce the same factor:
$$`
\Delta\Gamma(x,t)
=\left(\frac{|x|^2}{4t^2}-\frac{n}{2t}\right)\Gamma(x,t)
=\partial_t\Gamma(x,t).
`
Near the peak this factor is negative, so the temperature falls there as the
pulse spreads. The condition $`t>0` is essential to the calculation because
the formula divides by $`t`.

The new issue is the initial datum. The kernel has mass one at every positive
time, but its mass concentrates at the origin as $`t\downarrow0`. Its
initial value is a Dirac mass in the distributional sense. For bounded,
continuous $`g`, convolution $`\Gamma(\cdot,t)*g` tends to $`g` locally
uniformly. To prove this, normalization accounts for the constant part of
$`g`; continuity controls its variation near a point; and the Gaussian tail
controls the integral far away. This approximation-of-the-identity argument
connects the classical formula at positive time with its initial data.
Differentiating the formula does not perform that limiting argument.

Harmonic kernels, traveling waves, similarity profiles, shear flows, and
rotating solutions share this pattern: establish regularity, calculate the
residual, and identify the data or normalization. A singular formula can
make the last step the most revealing. The
{bpref "elliptic.fundamental_solution"}[fundamental solution] of the
Laplacian is
{bpref "elliptic.fundamental_solution.harmonic_off_pole"}[harmonic away from its pole],
yet it has a distributional point source there. A zero classical residual on
the punctured domain misses that source. Flux and integration by parts
recover it. This is another place where the classical and distributional
views supply different parts of the answer.

_Energy estimates and uniqueness._ Multiply the heat equation by $`u`,
integrate, and use the zero boundary value to obtain
$$`
\frac12\frac{d}{dt}\|u(t)\|_{L^2}^2
+\|\nabla u(t)\|_{L^2}^2=0,
`
under regularity assumptions that justify the differentiation and integration
by parts. For the sine mode on $`(0,\pi)`, the energy is
$`\tfrac12\|u(t)\|_{L^2}^2=\tfrac\pi4e^{-2t}` and the dissipation is
$`\|u_x(t)\|_{L^2}^2=\tfrac\pi2e^{-2t}`. The energy derivative is
the negative of the dissipation, as the identity predicts. The useful feature
of the energy identity is that its proof does not require knowing the
formula for $`u`.

Apply it to the difference of two heat solutions with the same data. The
difference begins with zero energy; dissipation prevents the energy from
increasing; nonnegativity forces it to stay zero. This proves uniqueness in
a class where the argument is justified. For weak solutions, the Gelfand
triple and Lions–Magenes identity supply the time pairing, while the
zero-boundary space supplies the integration-by-parts step.

For the wave equation the energy includes velocity and spatial gradient.
For Navier–Stokes the transport term formally cancels, leaving viscous
dissipation; making that cancellation valid requires the appropriate
integrability and boundary behavior. A weak solution may give only an
energy inequality, which supports different conclusions from an equality.
Energy also helps construct solutions. In Galerkin approximation we solve
finite-dimensional equations first, then use bounds independent of the
dimension to obtain a limit. Grönwall, Poincaré, and Sobolev inequalities
turn these bounds into stability, uniqueness, or compactness estimates.

_Compactness and passage to a limit._ A finite sine sum can be differentiated
term by term. Passing to an infinite expansion requires control independent
of the number of terms. The same need appears with smoother, truncated, or
regularized approximations $`u_m`. Bounds in a reflexive Banach space give
weakly convergent subsequences, and continuous linear functionals pass to
the limit. This is why weak formulations are well suited to construction.

Nonlinear terms expose what weak convergence loses. On $`(0,2\pi)`, the
sequence $`\sin(mx)` converges weakly to zero in $`L^2`, while
$$`
\sin^2(mx)=\frac{1-\cos(2mx)}{2}
\rightharpoonup\frac12.
`
Squaring and taking a weak limit do not commute. Strong compactness,
monotonicity, compensated structure, or a separate identification argument
is needed to handle such terms. In an evolution problem, spatial compactness
alone also leaves room for rapid oscillation in time. Aubin–Lions–Simon
estimates combine a compact spatial embedding with a bound on time variation
to give strong convergence in an intermediate space. PDEAtlas proves the
{bpref "parabolic.aubin_lions_hilbert"}[version for a Hilbert triple], with
square-integrable bounds in time.

The initial condition is still a separate step. Convergence on an open time
interval does not determine a value at its endpoint. Lions–Magenes continuity
or appropriately chosen time test functions recover that value, which is why
a complete {bpref "parabolic.galerkin_existence"}[Galerkin theorem] includes
more than an interior weak equation.

_Coercivity, minimization, and operator methods._ The weak Poisson argument
has reduced the PDE to $`a(u,v)=F(v)` for all $`v\in V`. Boundedness and
coercivity of the bilinear form on a real Hilbert space, together with
continuity of $`F`, give the unique solution through Lax–Milgram. The direct
method gives another route when an energy is available: bound a minimizing
sequence, keep its weak limit in the admissible set, and use weak lower
semicontinuity to obtain a minimum. Strict convexity gives uniqueness, and
an admissible first variation gives the Euler–Lagrange equation.

Other operator methods preserve this separation between an abstract theorem
and the PDE estimates that make it applicable. Minty–Browder arguments use
monotonicity to identify weak limits of nonlinear operators. Writing an
equation as $`u=T(u)` can permit a Banach contraction argument for a short
time or small data, or a Schauder argument using continuity and compactness.
Fredholm theory describes solvability through the kernel of an operator and
its adjoint when unconditional invertibility is unavailable. Each method
asks for properties of the spaces and operators that the PDE proof must
establish.

_Comparison, characteristics, and admissibility._ Order provides a different
kind of control. {bpref "elliptic.maximum.weak_ball"}[Maximum principles]
and comparison principles turn boundary or data inequalities into bounds
on the solution. They can give positivity, barriers, and uniqueness, with
coefficient signs and boundary assumptions determining the precise result.
For constant-velocity transport, the solution is
{bpref "hyperbolic.transport.characteristic_solution"}[carried along]
$`x(t)=x_0+tb`, giving $`u(x,t)=u_0(x-tb)`. The traveling-wave panel showed
this preservation of shape. In a quasilinear equation, the speed can depend
on the solution, so characteristics may intersect and the classical
construction can break down.

The weak conservation law allows discontinuities but constrains their motion
through the
{bpref "hyperbolic.conservation.planar_shock_weak"}[Rankine–Hugoniot relation].
Entropy inequalities impose the dissipation direction that selects admissible
shocks. Viscosity sub- and supersolutions instead express comparison through
touching test functions. In each case the extra condition supplies information
that the distributional equation alone would leave undecided.

# Verified symbolic and numerical computation

The heat-mode calculation asks a computer to do something quite specific:
differentiate a product of elementary functions, then recognize that the two
resulting expressions agree. The weak existence argument asks for something
else: quantify over a space of functions and pass to limits. We want the
first calculation to produce a theorem that the second kind of argument can
use. That requirement explains both the expression language of the CAS and
its connection to Mathlib.

The same division between a candidate calculation and a checked conclusion
appears in Lewis and Wu's Lean–Mathematica interface
{Informal.citet "lewis-wu-2021"}[]. Hex supplies verified computational algebra,
with Mathlib correspondence layers where available
{Informal.citet "hex-2026"}[]. Our task here is to connect calculations to the
analytic functions used by a PDE proof: a normalized derivative must agree with
Mathlib's derivative, and an interval must contain the actual real expression.

An arbitrary function $`\mathbb R\to\mathbb R` need not come with a formula
that a program can inspect. PDEAtlas therefore represents a limited language
of formulas as data: variables, constants, arithmetic, powers, trigonometric
functions, exponentials, logarithms, and square roots. A program can walk the
resulting expression tree, apply the product or chain rule at each node, and
normalize the result. A soundness theorem proves that the transformed tree
has the claimed meaning as a real function. This is a deep embedding: syntax
is an object we can compute with, and its interpretation is tied to the
ordinary mathematics by a proof. Users write ordinary Lean notation; the
conversion to a tree happens internally.

For the heat mode, the final task is to connect the computed derivatives to
the analytic heat residual. The
{bpref "symbolic.residual_bridge"}[residual bridge theorems] supply this
connection. Gradient and Laplacian calculations must preserve the coordinate
order: differentiating in time and differentiating in space are different
operations even when both coordinates are real numbers. The same distinction
appears in a smaller example. Treat $`y` as an independent parameter and
differentiate $`\sin(xy)` with respect to $`x`:

```Blueprint.leanExample (name := overviewDerivative)
-- Differentiate in x.
-- Treat y as an independent parameter.
#cas [derive x] (sin (x * y))
```

The factor $`y` is the derivative of the inner expression $`xy`. The command
reports:

```InlineLean.leanOutput overviewDerivative +summarize
#cas [derive x]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (scalar ℝ): cos(x*y)*y

[CAS.Command.details] More details
```

A tactic instead closes a stated derivative equality. The next example uses
Mathlib's one-dimensional `deriv` for the function $`\sin x`, rather than the
two-variable inspection calculation above:

```Blueprint.leanExample
-- Discharge an ordinary Mathlib derivative
-- statement with the tactic.
example (x : ℝ) : deriv Real.sin x = Real.cos x := by
  cas
```

The inspection command displays a result; the tactic must close the goal
with a proof. Exact simplification similarly produces an equality theorem.
Integration searches for a supported antiderivative, then differentiates the
candidate and checks that its difference from the integrand normalizes to
zero. Thus finding an antiderivative and accepting it can use different
procedures. A complicated search still ends with a derivative calculation
whose meaning is proved.

Domain conditions travel with these calculations. The notebook's rational
identity cancels $`x^2-1`, so it assumes $`x^2-1\ne0`. Cancelling $`x/x`
needs $`x\ne0`; replacing $`\exp(\log x)` by $`x` needs $`x>0`. The last
condition is stronger than differentiability of Mathlib's real logarithm,
which holds at every nonzero real input. A classical square-root derivative
requires a positive argument. Total functions make these distinctions easy
to miss on the page: an expression still has a value where a proposed rule
is invalid. The CAS must prove the condition for the particular rule it uses.
In the Gaussian calculation, this is why positive time accompanies the
formula throughout the proof.

The exact layer includes normalization, differentiation, selected
antiderivative search, polynomial reasoning, and real-root certificates.
Its expressions form a fixed grammar of real elementary functions, and its
integrator searches a finite family of antiderivative forms. A goal outside
the grammar, or one that the search cannot settle, is left unchanged and the
tactic reports an error.

For explicit expressions, the checked tactics let the proof concentrate on
how a calculation is used. Abstract functions, symbolic dimension, norms and
inner products, sums, piecewise formulas, and vector-valued derivatives can
still require direct Mathlib arguments. This division is useful in the
Gaussian example: a concrete coordinate residual is a good CAS calculation,
while normalization and convergence to the initial datum require analysis.
Like Mathlib's reflected algebra and arithmetic tactics, the CAS proves
statements about Mathlib's own objects. Its additional expression and
certificate machinery handles the continuous operations needed here.

## Certified numerical work

The notebook's third cell bounds $`x/(1+x)` for every $`x\in[0,1]`.
Ordinary interval arithmetic already gives a valid enclosure: the numerator
lies in $`[0,1]` and the denominator in $`[1,2]`, so their quotient lies in
$`[0,1]`. But treating those ranges independently loses information. A
numerator near one has a denominator near two. Differentiation recovers the
relationship:
$$`
\frac{d}{dx}\frac{x}{1+x}=\frac{1}{(1+x)^2}>0
\qquad (0\le x\le1).
`
Monotonicity reduces the sharp bound to the two endpoints, giving
$`0\le x/(1+x)\le1/2`. The notebook proves that bound over the entire
interval. This explains why a numerical checker benefits from symbolic
calculus: algebra and derivative information can sharpen a bound that raw
interval operations make too wide.

CEGA (Certified Enclosures, Guarantees, and Approximations) states such
bounds as theorems about ordinary real expressions. An interval enclosure
covers every input in a rational box. A bound certificate proves an upper or
absolute bound. An approximation certificate pairs an approximating function
with a uniform error theorem. Taylor and quadrature certificates include the
hypotheses and remainder estimates needed for their inequalities. Each
conclusion holds on the whole domain, which no finite sample of points could
establish.

The basic interval backend uses exact rational endpoints and proved inclusion
rules for arithmetic and supported transcendental functions. A search may
use monotonicity, derivative bounds, sparse polynomial structure, or
subdivision to obtain a sufficiently narrow interval. Scalar Taylor
certificates retain a polynomial and a certified uniform
{bpref "symbolic.taylor_remainder_bound"}[remainder] on each interval.
Quadrature proofs use exactness on polynomial pieces and derivative bounds
to control the integral error.
Root isolation, {bpref "symbolic.interval_newton_certificate"}[interval Newton],
{bpref "symbolic.krawczyk_unique_zero"}[Krawczyk-style] arguments, and
validated linear algebra use the same separation between proposing data and
checking its consequence. A search proposes a bracket, an approximate
inverse, or a subdivision. A Lean checker proves what follows from those
data. Search choices affect sharpness and runtime; they cannot change the
statement to be established. If the expression, domain conditions, or
required certificate cannot be handled within the search budget, the
proof-producing interface fails. Displaying an intermediate result does
not discharge the goal.

To see what a residual certificate could contribute to a PDE argument,
return to the rod and suppose we approximate $`e^{-t}` by a continuously
differentiable function $`q(t)` with $`q(0)=1`. The candidate
$`\widetilde u(t,x)=q(t)\sin x` has the exact boundary and initial data,
but its heat residual is
$$`
r(t,x)=\widetilde u_t-\widetilde u_{xx}
=\bigl(q'(t)+q(t)\bigr)\sin x.
`
For $`T>0` and $`\varepsilon\ge0`, suppose a certificate proves
$`|q'(t)+q(t)|\le\varepsilon` on $`[0,T]`. This is a bound on a particular
real expression, with its time interval specified. It gives
$`\|r(t)\|_{L^2(0,\pi)}^2\le(\pi/2)\varepsilon^2`, using the integral
of $`\sin^2 x` on the rod.

Now compare the candidate with the exact heat solution and write
$`e=\widetilde u-u`. The error has zero initial and boundary data and
satisfies $`e_t-e_{xx}=r`. The energy calculation gives
$$`
\frac12\frac{d}{dt}\|e(t)\|_{L^2}^2+\|e_x(t)\|_{L^2}^2
=\int_0^\pi e(t,x)r(t,x)\,dx
\le\frac12\|e(t)\|_{L^2}^2+\frac12\|r(t)\|_{L^2}^2.
`
Dropping the nonnegative dissipation and applying Grönwall yields
$$`
\|e(t)\|_{L^2(0,\pi)}^2
\le\frac\pi2\varepsilon^2(e^t-1),\qquad 0\le t\le T.
`
The residual bound has become a solution-error bound because the heat
equation supplies the stability argument. For a nonlinear equation, the
corresponding estimate may require smallness, weights, or operator bounds,
and proving those conditions can be most of the work. A certificate is
useful precisely when its conclusion matches an input of that analytic
argument.

# Sources

{Informal.citet "evans-2010"}[] is the principal reference because it connects
the core equation families to the functional analysis needed to study them.
We contacted Evans about following his book, and he was excited about the project.
Results that track it carry source locators, which refer to the AMS second
edition (2010). The source notes record the contents of that edition and
the pages of selected passages. The explanations here
are written for this project, not copied from the book.

The time-space arguments above draw on {Informal.citet "simon-1987"}[]
for compactness and {Informal.citet "lions-magenes-1972"}[] for recovery of
time continuity. {Informal.citet "marcus-mizel-1972"}[] supplies the context
for absolute continuity on lines and Sobolev composition. The abstract
existence methods lead to {Informal.citet "banach-1922"}[],
{Informal.citet "schauder-1930"}[], {Informal.citet "minty-1962"}[], and
{Informal.citet "browder-1963"}[] for fixed points, monotonicity, and nonlinear
variational arguments. {Informal.citet "crandall-lions-1983"}[] is the
reference for viscosity solutions.

For fluids, the choice of solution class is particularly important.
{Informal.citet "leray-1934"}[] is the historical
source for global weak Navier–Stokes solutions;
{Informal.citet "caffarelli-kohn-nirenberg-1982"}[] studies partial regularity
of suitable weak solutions. {Informal.citet "serrin-1962"}[] and
{Informal.citet "escauriaza-seregin-sverak-2003"}[] give interior and endpoint
regularity criteria. {Informal.citet "majda-bertozzi-2002"}[] and
{Informal.citet "temam-2001"}[] develop the vorticity and functional
frameworks, {Informal.citet "ukhovskii-yudovich-1968"}[] the axisymmetric
setting, and {Informal.citet "chen-hou-2022"}[] the nearly self-similar
Boussinesq and Euler analysis. Fefferman's official description fixes the
Clay problem under discussion, and Wiedemann is the source for weak
incompressible Euler solutions.

The computation chapter gives the references behind its algorithms: Moore
and Neumaier on interval analysis, Berz and Makino on Taylor models, Risch
and Bronstein on symbolic integration, and Sturm's theorem for real-root
certificates.

Blowup for the De Gregorio model follows a different kind of singularity:
vorticity grows while its physical support expands along the real line. Its
formalization, the real-line $`a=1` conclusion of Chen–Hou–Huang's Theorem 1,
builds on this library's De Gregorio equation in the companion repository
[BlowupZoo](https://github.com/Robertboy18/BlowupZoo).
