/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Foundations.CauchyProblems
import Blueprint.Chapters.Foundations.Scope
import Blueprint.CodeExamples
import Blueprint.Commands.Figures
import CAS
import PDE.Symbolic.Command.CAS.Laplacian

/-!
# Foundations chapter

Assembles the Foundations subdocuments. The mathematical nodes live in the
submodules for each subject; the global dependency graph is emitted after every
chapter has been loaded.
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
#doc (Manual) "Foundations" =>
%%%
htmlSplit := .never
%%%

To state $`\Delta u = 0`, we choose a domain, a function space, and a notion
of derivative. A classical equation holds pointwise; a distributional equation
holds against test functions. Boundary conditions impose further requirements.
The operators and solution predicates below record these choices explicitly.

The classical operators are built from the Fréchet derivative on Mathlib's
Euclidean $`\mathbb R^n`. Above them sit typed problem records that keep an
equation, its data, and its solution concept apart, so that a pointwise residual
identity, a weak formulation, and Hadamard well-posedness are three propositions
rather than three readings of one sentence.
{bpref "foundations.pde_problems.solution"}[Solving a problem] is itself a
definition: it requires the field to satisfy every identity stored in the
problem record.

# Operators, solution concepts, and weak formulations

The formula $`\Delta u = \sum_{i=1}^n u_{x_ix_i}` in
{Informal.citet "evans-2010"}[] combines a choice of coordinate derivatives
with assumptions under which they exist. We fix those operators and state the
regularity needed to interpret them classically.

The starting point is the Fréchet derivative, the linear first-order
approximation that carries the chain rule, the inverse function theorem, and
variational calculus in normed spaces. Out of that single notion we build the
gradient, divergence, and Laplacian as finite coordinate operations, so that
"$`u(x,y)=x^2-y^2` is harmonic" unfolds all the way down to iterated Fréchet
derivatives along basis directions. The
verified computer algebra system of the computation chapter uses the same
conventions. Asking it for the Laplacian of the model harmonic polynomial

```Blueprint.leanExample (name := foundationsHarmonic)
-- Check the planar Laplacian using the
-- coordinate conventions fixed below.
#cas [laplacian x, y] (x ^ 2 - y ^ 2)
```

produces a checked zero residual, rendered from the compiler's own output:

```InlineLean.leanOutput foundationsHarmonic +summarize
#cas [laplacian x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x ^ 2 - y ^ 2)
Output (scalar ℝ): 0

[CAS.Command.details] More details
```

The calculation certifies $`\Delta(x^2-y^2)=2-2=0` for the same coordinate
Laplacian used in the later analytic statements.

On the unit disk, this polynomial is harmonic but does not solve the
zero-boundary Dirichlet problem: its boundary values at $`(1,0)` and
$`(0,1)` are $`1` and $`-1`. On the circle
$`(x,y)=(\cos\theta,\sin\theta)`, its boundary datum is
$`\cos(2\theta)`. The residual calculation verifies the interior equation;
the boundary calculation determines which Dirichlet problem it solves.

In a {bpref "symbolic.polynomial_heat_example"}[polynomial heat solution],
the spatial Laplacian instead balances a time derivative.

A residual can vanish at every point while the boundary condition is
still unproved. A derivative term exists in Lean whether or not the function is
differentiable, because `fderiv` is a total function. A distributional identity
can hold without a locally integrable representative. The solution predicates
state separately which identities and regularity conditions are required.

## Classical, weak, and well-posed problems

{leanpde_figure "formalization-routes"}

The routes in the figure share these operators, but require different evidence
about a proposed solution. A classical calculation supplies pointwise
identities; a weak formulation pairs the function with test functions; an
existence proof constructs an object satisfying the chosen formulation.
Integration by parts relates classical and weak formulations; regularity
can recover classical derivatives from a weak solution.

Well-posedness asks a further question about a whole family of problems.
For each allowed datum, does a solution exist, is it unique in the chosen
class, and do small changes in the data produce small changes in the solution?
The word “small” needs a topology on both spaces. The
{bpref "foundations.well_posedness.global"}[well-posedness definition] is
introduced through a Dirichlet problem on an interval, where all three
requirements are visible in one calculation. Regularity asks how many
derivatives that solution has; it is a separate conclusion.

For differentiable initial data $`g` and constant velocity $`b`, transport
has the classical solution $`u(x,t)=g(x-tb)`. The chain rule gives
$`u_t=-b\cdot\nabla g(x-tb)` and $`\nabla_xu=\nabla g(x-tb)`, so
$`u_t+b\cdot\nabla_xu=0`; substituting $`t=0` gives the initial datum.

## Main objects

Finite-dimensional space is Mathlib's Euclidean type $`\mathbb R^n`.
Spacetime points carry a distinguished time coordinate and a spatial
projection. Coordinate derivatives are derived from Mathlib's Fréchet
derivative, and the familiar operators are finite coordinate constructions
built on top of it:

$$`\nabla u = (\partial_1 u,\dots,\partial_n u),\qquad
\operatorname{div} F = \sum_{i=1}^n \partial_i F_i,\qquad
\Delta u = \sum_{i=1}^n \partial_i\partial_i u.`

The coordinate identity $`\Delta u = \operatorname{div}(\nabla u)` holds
unconditionally for these total Lean expressions. Interpreting them as
classical derivatives requires regularity. In particular, local $`C^2`
regularity identifies this iterated-coordinate Laplacian with Mathlib's
Laplacian defined through the second Fréchet derivative.

A locally integrable function $`f`
acts on compactly supported smooth test functions $`\varphi` by integration,
$`\varphi \mapsto \int f\varphi`, and distributional differentiation pushes the
derivative onto the test function with the usual sign:

$$`\langle \partial_i T, \varphi\rangle = -\langle T, \partial_i\varphi\rangle.`

Distributional differentiation also gives meaning to derivatives of
discontinuous functions. The standard illustration is the Heaviside step
function on $`\mathbb R`. It has no derivative at the origin in any pointwise
sense, and yet its distributional derivative is the Dirac mass $`\delta_0`,
because $`-\int_0^\infty \varphi'(x)\,dx = \varphi(0)` for every test function
$`\varphi`. PDE theory needs this much generality. Solutions of hyperbolic
conservation laws grow jumps like that in finite time, and elliptic theory has
to cope with forcing terms that are rough to begin with.

The {bpref "foundations.boundary_calculus.green_second_ball"}[second Green identity on a ball]
relates the interior equations of two $`C^2` functions to their values and
normal derivatives on the sphere. Gauss–Green extends this calculation to
bounded $`C^1` graph domains, using intrinsic surface measure and outward normals.

# PDE Problems and Differential Operators

{include 2 Blueprint.Chapters.Foundations.ProblemFamilies}
{include 2 Blueprint.Chapters.Foundations.DifferentialOperators}
{include 2 Blueprint.Chapters.Foundations.PDEProblems}
{include 2 Blueprint.Chapters.Foundations.CauchyProblems}

# Coordinates and Boundary Calculus

{include 2 Blueprint.Chapters.Foundations.Coordinates}
{include 2 Blueprint.Chapters.Foundations.BoundaryCalculus}

# Distributions and Fourier Analysis

{include 2 Blueprint.Chapters.Foundations.Distributions}
{include 2 Blueprint.Chapters.Foundations.TemperedDistributions}

# Coverage and Open Problems

{include 2 Blueprint.Chapters.Foundations.Scope}
