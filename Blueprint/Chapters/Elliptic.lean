/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Elliptic.Scope
import Blueprint.CodeExamples
import CAS
import PDE.Symbolic.Command.CAS.Laplacian

/-!
# Elliptic equations chapter

The elliptic chapter: classical harmonic theory, weak solutions, Fredholm
theory and the weak spectrum, and Sobolev regularity. Each section lives in its
own module under `Blueprint.Chapters.Elliptic`.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Elliptic Equations" =>
%%%
htmlSplit := .never
%%%

Elliptic equations describe things that have settled down: the steady temperature
in a room, the electrostatic potential around a conductor, the shape of a soap
film spanning a wire frame. We prescribe the equation inside a domain and data
on its boundary, then ask whether those data determine a solution and how
regular that solution is.

There are two approaches. The classical approach studies the
fundamental solution of Laplace's equation, the mean-value
property, the maximum principle, interior estimates, and representations by
Green's functions and Poisson kernels on the ball, the half-space, and bounded
domains with $`C^1` boundary. The variational approach rewrites a
divergence-form equation as a bounded coercive bilinear form on
$`H^1_0(\Omega)` and solves it with the
{bpref "elliptic.lax_milgram"}[Lax–Milgram theorem]. Where lower-order
terms destroy coercivity, the
{bpref "elliptic.fredholm.alternative"}[Fredholm alternative] and the weak
spectrum of the operator describe solvability instead.

Regularity theory connects the two approaches. A weak solution gains Sobolev
derivatives when the coefficients, forcing, and boundary are regular enough,
and with smooth data at every order it has a representative smooth on
$`\overline\Omega`.

# Equilibrium, representation, and coercivity

The prototype is Laplace's equation $`\Delta u = 0`, whose solutions are called
harmonic, and harmonic functions are remarkably constrained. They satisfy the
mean-value property and are real-analytic in the interior. On a bounded domain,
one that is continuous up to the closure attains its maximum and minimum on the
boundary, so two of them agreeing on the boundary agree everywhere inside. In
two dimensions they are locally real parts of holomorphic functions, and
globally so on simply connected domains, which is a convenient source of
examples. The real part of $`z^3 = (x+iy)^3`, for instance, gives the harmonic
cubic

```Blueprint.leanExample (name := ellipticHarmonicCubic)
-- Verify that the real part of z^3 has zero Laplacian.
#cas [laplacian x, y] (x ^ 3 - 3 * x * y ^ 2)
```

whose Laplacian the verified computer algebra system certifies to vanish:

```InlineLean.leanOutput ellipticHarmonicCubic +summarize
#cas [laplacian x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x ^ 3 - 3 * x * y ^ 2)
Output (scalar ℝ): 0

[CAS.Command.details] More details
```

This repeats the harmonic-polynomial check from Foundations at one higher
degree. The checked residual makes the cubic a candidate for a Dirichlet
problem with its own boundary values. Uniqueness, proved by the maximum
principle below, is what identifies that candidate with any other solution
having those values. We use both arguments because differentiation verifies
the formula, while uniqueness explains why the boundary data determine it.

For a forced example, take the interval $`(-1,1)` and solve
$`-u''=1` with $`u(-1)=u(1)=0`. Integrating twice gives

$$`
u(x)=\frac{1-x^2}{2},\qquad u'(x)=-x,\qquad -u''(x)=1.
`

The solution is positive inside the interval. This checks the sign convention:
positive forcing for $`-\Delta` produces a concave solution in one dimension.
For $`\varphi\in C_c^\infty(-1,1)`, integration by parts gives
$`\int_{-1}^1u'\varphi'=\int_{-1}^1\varphi`, the smooth-test identity in
{bpref "elliptic.poisson.distributional_iff_variational"}[the weak formulation].
The zero endpoint values specify the homogeneous Dirichlet boundary class.

The two approaches to the general problem use different information about
the equation.

The *classical route* writes down explicit integral formulas, the fundamental
solution, Green's functions, Poisson kernels, and studies their pointwise
behavior. On the ball, the Poisson integral of a continuous boundary datum
$`g` is the harmonic function extending continuously to those boundary values.
This gives concrete representations on model domains, and it leads to
mean-value formulas, maximum principles, and interior derivative estimates.

The *variational route* starts with the weak equation. Rewrite
$`-\operatorname{div}(A\nabla u) = f` as a bilinear form
$`B[u,v]=\int_\Omega A\nabla u\cdot\nabla v` on $`H^1_0(\Omega)` and ask only
that the form be bounded and coercive. Lax–Milgram then hands back a unique
weak solution for every bounded linear load, and on a bounded domain an $`L^2`
forcing is such a load. Bounded measurable principal coefficients suffice
under uniform ellipticity. Lower-order terms can destroy coercivity, so that
Lax–Milgram does not apply directly. The Fredholm alternative then describes
solvability: a load must be orthogonal to the adjoint kernel, and when the
homogeneous and adjoint kernels are both trivial one recovers unique solvability
for every load, just as in finite-dimensional linear algebra.

Green and Poisson kernels expose pointwise structure on model domains. The
variational theory instead gives a Sobolev element satisfying an integral
identity. Regularity theory is the
bridge: a weak solution picks up extra Sobolev derivatives whenever the
coefficients, forcing, and boundary allow it, and with enough derivatives a
Sobolev embedding hands back a classical representative. We formalize the
$`L^2` elliptic bootstrap at every finite Sobolev order under the chart,
coefficient, and forcing hypotheses for that order. Smooth charts and coherent
data at all orders allow Sobolev–Morrey reconstruction to produce one
representative smooth on $`\overline\Omega` for the principal equation.

The classical formulas follow Chapter 2 of {Informal.citet "evans-2010"}[],
and the weak theory follows Chapter 6. For further classical estimates see
{Informal.citet "gilbarg-trudinger-2001"}[]; for Lax–Milgram, Fredholm theory,
and spectral analysis see {Informal.citet "brezis-2011"}[].

To recover the mean value, solve the ball Poisson problem with the boundary
values of the given harmonic function. Uniqueness identifies the constructed
solution with that function throughout the ball. At the center, the Poisson
kernel is constant on the sphere, so its weighted boundary integral becomes
the spherical average. Green's representation then writes a solution
in terms of boundary data by correcting $`\Phi` with a domain-dependent
harmonic function. This follows Evans's §2.2.

# Harmonic Functions and Model Kernels

The Laplace kernel, its dimension-dependent normalization, and its
distributional point-source identity come first.

{include 2 Blueprint.Chapters.Elliptic.FundamentalSolutions.Kernel}
{include 2 Blueprint.Chapters.Elliptic.FundamentalSolutions.OneDimensional}
{include 2 Blueprint.Chapters.Elliptic.FundamentalSolutions.Planar}
{include 2 Blueprint.Chapters.Elliptic.FundamentalSolutions.Newtonian}

# Model Dirichlet Problems and Harmonic Rigidity

The ball and half-space constructions provide the weak maximum principle and
Poisson uniqueness used by the checked mean-value argument. Mean values then
lead to derivative estimates, stronger maximum principles, Harnack
comparison, and Liouville rigidity.

{include 2 Blueprint.Chapters.Elliptic.GreenRepresentation}
{include 2 Blueprint.Chapters.Elliptic.FundamentalSolutions.MeanValues}
{include 2 Blueprint.Chapters.Elliptic.FundamentalSolutions.DerivativeEstimates}
{include 2 Blueprint.Chapters.Elliptic.MaximumPrinciples}
{include 2 Blueprint.Chapters.Elliptic.MovingPlanes}

# Energy and Weak Boundary-Value Problems

Energy arguments produce solutions without explicit formulas. Green's first identity
on a coordinate box already shows the mechanism: for the difference $`w` of two
$`C^2` solutions with the same boundary values, the identity collapses to
$`\int|\nabla w|^2=0`, and uniqueness follows without any representation
formula. The weak theory keeps that argument and drops the classical
regularity. On $`H^1_0(\Omega)` the Dirichlet form
$`\int_\Omega\nabla u\cdot\nabla v` is bounded, the Poincaré inequality of the
Sobolev chapter makes it coercive on bounded domains, and Lax–Milgram returns a
unique weak solution of $`-\Delta u=f` for every $`f\in L^2(\Omega)`, together
with an a priori estimate, continuous dependence on the load, and a
characterization as the minimizer of the Dirichlet energy. For classical
competitors on a bounded domain with $`C^1` graph boundary, the
{bpref "elliptic.energy.dirichlet_principle"}[classical Dirichlet principle]
gives the same characterization.

The same pattern extends to variable principal coefficients, where
almost-everywhere ellipticity yields the integrated coercivity, and to
lower-order terms, where coercivity can fail and a Gårding inequality with a
spectral shift takes its place. The modified Helmholtz problem
$`-\Delta u+\lambda u=f` with $`\lambda>0` works on any measurable domain:
the gradient and mass terms together control the full $`H^1` norm without a
Poincaré inequality. The shifted
lower-order solver is the input of the Fredholm section, and the weak solutions
built here are what the regularity section improves.

{include 2 Blueprint.Chapters.Elliptic.EnergyIdentities}
{include 2 Blueprint.Chapters.Elliptic.WeakProblems}
{include 2 Blueprint.Chapters.Elliptic.ModifiedHelmholtz}

# Fredholm Solvability and Weak Spectrum

Lower-order terms leave a gap in the previous section: adding a large multiple
of the $`L^2` inner product makes the form coercive and the shifted problem
uniquely solvable, but the original equation, at the parameter of interest, may
not be. Compactness closes the gap. Inverting the shifted
form and composing with the Rellich embedding of the Sobolev chapter,
represented here as a compact mass operator on $`H^1_0(\Omega)`, turns the
original equation into $`(I-K)u=g` with $`K` compact. Abstract Hilbert-space
theory then gives the Fredholm alternative: either the homogeneous problem has
a nonzero solution, or every load is uniquely solvable, and for a fixed load
solvability is equivalent to orthogonality against the adjoint kernel. None of
this needs symmetry of the form.

Varying the mass parameter produces the weak spectrum. A reciprocal change of
variables identifies the exceptional parameters with the nonzero eigenvalues of
one compact solution operator, so eigenspaces are finite-dimensional, the
spectrum is countable with no finite accumulation point, and off the spectrum
every load is solvable. On a nonempty bounded open set in positive dimension,
symmetric uniformly elliptic $`L^\infty` coefficients also give an $`L^2`
orthonormal eigenbasis and a nondecreasing sequence of positive eigenvalues
tending to infinity, counted with multiplicity, with its min–max
characterization. No boundary smoothness or connectedness is assumed.

{include 2 Blueprint.Chapters.Elliptic.FredholmSpectrum}

# Elliptic Regularity and Solution Operators

A weak solution from the previous two sections is, so far, only an element of
$`H^1_0(\Omega)`. It is more regular when coefficients, forcing, and boundary
allow, and the improved solution map is a bounded linear operator. The engine
is Nirenberg's difference-quotient method:
testing the weak equation with a second difference quotient of the solution,
ellipticity bounds the difference quotients of the gradient in $`L^2`, and the
difference-quotient criterion of the Sobolev chapter turns those bounds into a
second weak derivative. Cutoffs localize the argument to the interior, the
flattening charts of an operational $`C^2` boundary atlas carry it to the
boundary, and a finite partition of unity assembles the global $`H^2` estimate
for the homogeneous Dirichlet problem.

Linearity of the equation and uniqueness of the weak solution make the
regular solution map linear; the closed graph theorem makes it continuous.
The resulting $`H^2` and higher-order solution operators have trajectory and
Bochner lifts for applying the spatial estimates to time-dependent data.

{include 2 Blueprint.Chapters.Elliptic.Regularity}
{include 2 Blueprint.Chapters.Elliptic.SolutionOperators}

# Coverage and Open Problems

The classical, variational, and regularity routes use different hypotheses,
collected here.

{include 2 Blueprint.Chapters.Elliptic.Scope}
