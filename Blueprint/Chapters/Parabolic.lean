/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Parabolic.Scope
import Blueprint.CodeExamples
-- Verso elaborates the Lean blocks of a chapter without the module's prefix for auxiliary names,
-- so the `#cas` examples here and in the overview would both create `_proof_1`, `_simp_1`, ...
-- and the Blueprint could not import both chapters. Importing the overview makes the names here
-- continue after its names.
import Blueprint.Chapters.Overview
import PDE.Parabolic.Heat.Kernel.TimeDerivative
import PDE.Parabolic.Heat.MeanValue.Geometry
import PDE.Parabolic.ReactionDiffusion.Turing.Instability
import PDE.Parabolic.Quasilinear.GradientFlow.Existence
import CAS

/-!
# Parabolic equations chapter

The parabolic chapter: classical heat flow, weak evolution on Gelfand
triples, bounded-domain regularity, and finite-time behavior. Each topic's
Blueprint nodes live in its own subdocument; the global dependency graph is
emitted after every chapter has been loaded.
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

-- The re-elaborated proofs below keep the layout of their source files; the
-- sixty-column limit is Verso's default for short calculator snippets.
set_option verso.code.warnLineLength 100

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Parabolic Equations" =>
%%%
htmlSplit := .never
%%%

:::group "parabolic.classical"
Classical heat equation
:::

:::group "parabolic.variational"
Weak parabolic evolution
:::

:::group "parabolic.regularity"
Parabolic regularity
:::

:::group "parabolic.maximum_principles"
Parabolic maximum principles
:::

:::group "parabolic.scope"
Parabolic scope and open problems
:::

Give the Laplacian a time direction to act in and you get the heat equation
$`u_t = \Delta u`. Temperature in a conducting body, the concentration of a
diffusing chemical, and the probability density of a Brownian particle all evolve
by it, and what they have in common is that detail gets destroyed: corners in
the initial profile are gone at every positive time. Run the clock backwards and
the same mechanism amplifies high frequencies without bound, which is why the
backward problem is ill posed on the standard data spaces and why the theory is
not symmetric in time.

The Gaussian convolution solves the equation by differentiation under the
integral and attains its initial datum by an approximate-identity limit.
The classical route starts with the Gaussian kernel:
{bpref "parabolic.heat_kernel_equation"}[it solves the heat equation] at
every positive time, its convolution with the data attains the datum as
$`t\downarrow0`, Duhamel's formula absorbs a forcing term, and the heat-ball
mean-value formula and the maximum and comparison principles follow.

For weak solutions, Galerkin approximation on a Gelfand triple replaces the
explicit formula, and the Lions–Magenes theorem gives the weak solution a
continuous representative in the pivot space. Choosing the triple gives
{bpref "parabolic.dirichlet_existence_energy"}[existence and uniqueness] for the
Dirichlet heat equation and for divergence-form operators with lower-order
terms, and a graded family of regularity theorems states which Bochner-space
conclusion each level of data buys. Convex gradient diffusion and Turing's
diffusion-driven instability give a nonlinear and a coupled example. A final
part asks when diffusion loses and a nonlinear solution ceases to exist in
finite time.

# Diffusion and weak evolution

The simplest example shows the smoothing mechanism. Take the separated
candidate $`u(x,t)=e^{-t}\sin x` and differentiate in time:

```Blueprint.leanExample (name := parabolicSeparated)
-- Compute the time derivative of the separated heat mode.
#cas [derive t] (exp (-t) * sin x)
```

```InlineLean.leanOutput parabolicSeparated +summarize
#cas [derive t]
Domain: (t, x) ∈ ℝ^2
Input (scalar ℝ): (exp (-t) * sin x)
Output (scalar ℝ): -(exp(-t)*sin(x))

[CAS.Command.details] More details
```

The result is exactly $`u_{xx}`, because $`\partial_x^2\sin x=-\sin x`. The
mode $`\sin x` decays at the rate its own curvature dictates. Higher-frequency
modes $`\sin(kx)` decay like $`e^{-k^2t}`, quadratically faster in the
frequency, and that is the spectral mechanism behind smoothing. Extend this to
an infinite mode expansion and you still owe summability estimates before
convergence and term-by-term differentiation are legitimate.

For example, the initial profile $`g(x)=\sin x+\sin(2x)` evolves as

$$`
u(x,t)=e^{-t}\sin x+e^{-4t}\sin(2x).
`

Both terms have equal amplitude at $`t=0`. At $`t=\log 2`, their amplitudes
are $`1/2` and $`1/16`: the shorter wavelength has become eight times smaller
than the longer one. Differentiating each term gives $`u_t=u_{xx}`, and
substitution at zero gives the initial profile. This smooth periodic example
illustrates relative decay of frequencies; it has infinite $`L^2` norm on
the whole line.

We can see the derivative budget in the same teaching calculation. For a
nonnegative integer $`m`, frequency $`k\ge0`, and $`t>0`,

$$`
k^m e^{-k^2t}
=t^{-m/2}(k\sqrt t)^m e^{-(k\sqrt t)^2}
\le C_m t^{-m/2},
\qquad C_m=\sup_{z\ge0}z^m e^{-z^2}<\infty.
`

Each spatial derivative costs a factor $`k`; positive-time decay pays for
every fixed number of them. The price $`t^{-m/2}` grows near the initial
slice, where the datum may be rough. Reversing the mode evolution replaces
$`e^{-k^2t}` by $`e^{k^2t}`, so arbitrarily small errors at high frequencies
can become large. This calculation explains smoothing and backward
instability for a single mode.

The polynomial examples from Foundations give another way to see the balance.
For the {bpref "symbolic.polynomial_heat_example"}[planar polynomial heat solution],
the two spatial squares contribute a constant Laplacian, which is matched by
a linear time term. The verified calculation uses the same derivatives as the
harmonic-polynomial check, but now the spatial terms add instead of canceling.
This growing polynomial also explains why decay and finite-energy conclusions
need assumptions on the data and domain beyond a vanishing heat residual.

Parabolic equations generalize the picture to an elliptic spatial operator
coupled to forward evolution. For weak solutions, the time derivative may
belong to a dual space; the initial value is then supplied by a continuous
pivot-space representative.

For the variational evolution framework we follow Chapter 7 of
{Informal.citet "evans-2010"}[], and for the Gelfand-triple formulation and the
continuous-representative theorem, {Informal.citet "lions-magenes-1972"}[]; the
compactness step behind the nonlinear limits follows
{Informal.citet "simon-1987"}[]. The classical kernel material follows Evans's
§2.3. The finite-time singularity mechanisms come from a literature specific to
each model equation: Kaplan's eigenfunction method and concavity arguments for
nonlinear heat, moment arguments for Keller–Segel.

## Positive time and the initial instant

Smoothing holds at positive time, while convergence to the initial datum
may take place in a weaker norm. With rough coefficients, the time
derivative may exist only in a dual space.

Initial data cannot be swapped for an arbitrary time trace, and estimates that
hold almost everywhere in time need not hold at the initial instant. Each
passage to $`t=0` needs a continuity or limiting theorem of its own.

## Why the heat kernel is fundamental

The Gaussian kernel

$$`\Gamma_n(x,t) = \frac{1}{(4\pi t)^{n/2}}\,e^{-|x|^2/(4t)},\qquad t>0,`

is the heat equation's response to a unit point source. You can derive it:
parabolic scaling and radial symmetry cut a mass-preserving candidate down to an
ODE in $`|x|^2/t`, and solving that ODE and normalizing the mass gives the
Gaussian. Four properties are proved separately. It solves the heat equation
for $`t>0`. It carries unit mass $`\int\Gamma_n(x,t)\,dx=1` at every positive
time. It is strictly positive at every positive time. And as $`t\downarrow 0`
it concentrates into an approximate identity. Convolving against it,
$`u(t)=\Gamma_n(\cdot,t)*g`, therefore solves the equation for positive time,
because differentiation passes under the integral onto the kernel, and recovers
$`g` as $`t\downarrow0`, by the approximate-identity limit. The
{ref "certified-plots"}[certified plots] of the computation chapter draw
$`\Gamma_1(\cdot,t)` at three times as bands whose panels are kernel-checked
enclosure theorems.

## The kernel's derivative, step by step

The kernel time derivative below uses positivity of $`4\pi t` when
differentiating its real power. The calculation applies to the Gaussian
branch at positive time.

```Blueprint.leanExample
open PDE.Common HeatEquation in
example {n : ℕ} (x : ℝ^n) (t : ℝ) (ht : t > 0) :
    deriv (fun s ↦ fundamentalSolutionHeat (n := n) x s) t =
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
        fundamentalSolutionHeat (n := n) x t := by
  have hgt_pos : 0 < 4 * Real.pi * t := by positivity
  -- Work with the `t > 0` branch of the definition via
  -- an eventual equality near `t`.
  have hbranch :
      (fun s ↦ fundamentalSolutionHeat (n := n) x s) =ᶠ[nhds t]
        (fun s ↦
          (4 * Real.pi * s) ^ (-(n : ℝ) / 2) *
            Real.exp (-(‖x‖ ^ 2 / (4 * s)))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [fundamentalSolutionHeat, not_le_of_gt hs, mul_comm]
  rw [hbranch.deriv_eq, fundamentalSolutionHeat, ite_eq_right (not_le_of_gt ht)]
  cas using hgt_pos
```

The squared heat-ball slice radius is
$`2n\tau\log(r^2/(4\pi\tau))`. Its derivative calculation uses
$`r\ne0` and $`\tau\ne0` to differentiate the logarithm.

```Blueprint.leanExample
open HeatEquation in
example (n : ℕ) {r τ : ℝ} (hr : r ≠ 0) (hτ : τ ≠ 0) :
    HasDerivAt (heatBallSliceRadiusSq n r)
      (2 * (n : ℝ) * (Real.log (r ^ 2 / (4 * Real.pi * τ)) - 1)) τ := by
  unfold heatBallSliceRadiusSq
  cas
```

# Classical Heat Flow

The heat operator, Gaussian kernel, initial convolution, Duhamel formula, and
comparison principles form one continuous construction. On bounded domains,
energy identities give backward uniqueness, and a localization argument shows
that every classical solution is smooth in the interior.

{include 2 Blueprint.Chapters.Parabolic.Equation}
{include 2 Blueprint.Chapters.Parabolic.GaussianKernel}
{include 2 Blueprint.Chapters.Parabolic.InitialData}
{include 2 Blueprint.Chapters.Parabolic.Duhamel}
{include 2 Blueprint.Chapters.Parabolic.MaximumPrinciples}
{include 2 Blueprint.Chapters.Parabolic.Smoothing}

# Weak Evolution

The explicit Gaussian formula uses constant coefficients and whole-space
geometry. To study $`u_t+Lu=f` with a measurable, time-dependent operator field
$`L`, we use the variational framework and its boundedness and coercivity
hypotheses on a Gelfand triple, typically
$`H^1_0(\Omega)\hookrightarrow L^2(\Omega)\hookrightarrow H^{-1}(\Omega)`.

{include 2 Blueprint.Chapters.Parabolic.WeakEvolution}

# Bounded Domains and Improved Regularity

With the abstract evolution theory in place, the two concrete heat problems of
Evans's Chapter 7 follow by choosing the triple and the form: the Dirichlet form
on $`H^1_0(\Omega)` for the heat equation, and a Gårding-shifted divergence form
when lower-order terms destroy strict coercivity. The regularity theorems follow
Evans's Section 7.1.3. Testing the Galerkin system with its own velocity puts
$`u_t` in $`L^2(0,T;L^2(\Omega))`, the equation at almost every time becomes an
elliptic problem for $`u(t)` with an $`L^2` right-hand side, and an induction on
the order reaches Evans's Theorems 6 and 7 for smooth coefficients.

{include 2 Blueprint.Chapters.Parabolic.DirichletHeat}
{include 2 Blueprint.Chapters.Parabolic.DivergenceForm}
{include 2 Blueprint.Chapters.Parabolic.Regularity}

# Nonlinear gradient diffusion

The evolution of a convex energy supplies a nonlinear application with a
different set of coefficient hypotheses. On $`L^2(\Omega)`, extend
$`I(w)=\int_\Omega L(Dw)\,dx` by $`+\infty` outside $`H^1_0(\Omega)`.
Identifying the subdifferential $`\partial I` turns its gradient flow into the
equation $`u_t=\operatorname{div}DL(Du)`; the spatial first variation and
elliptic regularity make that identification.

:::theorem "parabolic.gradient_diffusion" (parent := "parabolic.variational") (lean := "PDE.Parabolic.Quasilinear.GradientFlow.exists_weakSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.6.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n`, $`n>0`, be bounded and open with $`C^2`
graph boundary. Suppose $`L:\mathbb R^n\to\mathbb R` is $`C^2` and
there are constants $`\theta>0` and $`C\ge0` such that

$$`\theta|v|^2\le D^2L(p)[v,v],\qquad \|D^2L(p)\|\le C
\qquad(p,v\in\mathbb R^n).`

For every $`u_0\in H^2(\Omega)\cap H^1_0(\Omega)` there is a global
continuous $`L^2` trajectory $`u` with $`u(0)=u_0`, a distributional time
derivative $`g\in L^\infty((0,\infty);L^2(\Omega))`, and
$`u(t)\in H^2(\Omega)\cap H^1_0(\Omega)` at every $`t\ge0`.
At almost every positive time, for every $`v\in H^1_0(\Omega)`,

$$`\langle g(t),v\rangle_{L^2}
+\int_\Omega DL(Du(t))\cdot Dv\,dx=0.`

This is the weak Dirichlet equation $`u_t=\operatorname{div}DL(Du)`
with a continuous initial trace.
:::

:::proof "parabolic.gradient_diffusion" (uses := "evolution.subgradient.domain_flow")
The Hessian bounds make the extended gradient energy proper, convex,
and lower semicontinuous on $`L^2`. Its subdifferential domain is exactly
$`H^2\cap H^1_0` under the boundary hypotheses, so $`u_0` is admissible
for the global weak subgradient-flow construction. That construction
provides the continuous trajectory, bounded weak time derivative, and
domain membership at every nonnegative time. The first-variation identity
identifies $`-g(t)` as the subgradient precisely when the displayed spatial
test equation holds, which supplies the PDE and the boundary condition.
:::

# Diffusion-driven linear instability

Diffusion damps each scalar Fourier mode of the heat equation. In a coupled
system, unequal diffusion rates can instead destabilize a reaction matrix
whose spatially homogeneous evolution is stable. For

$$`\partial_t\begin{pmatrix}u\\v\end{pmatrix}
=D\partial_{xx}\begin{pmatrix}u\\v\end{pmatrix}
+A\begin{pmatrix}u\\v\end{pmatrix},
\qquad A=\begin{pmatrix}a&b\\c&d\end{pmatrix},
\quad D=\operatorname{diag}(d_1,d_2),`

a cosine of frequency $`k` evolves by the matrix $`A-k^2D`.
The theorem finds a growing mode from the raw coefficient inequalities.

:::theorem "parabolic.turing_instability" (parent := "parabolic.classical") (lean := "ReactionDiffusion.Turing.turing_instability, ReactionDiffusion.Turing.exists_unstable_neumann_interval") (uses := "foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.1 (Turing instability)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose $`d_1,d_2>0` and, writing $`w=ad_2+dd_1`,

$$`a+d<0,\qquad ad-bc>0,\qquad
w>0,\qquad w^2>4d_1d_2(ad-bc).`

Then the homogeneous ODE is asymptotically stable, but the linear PDE on
the line admits arbitrarily small uniformly bounded initial perturbations
whose first component at the origin grows without bound in magnitude. The
constructed solutions are cosine modes $`e^{\lambda t}\cos(kx)q` with
$`k,\lambda>0`. There is also an explicitly chosen interval
$`[0,\pi/k]` on which these solutions have zero Neumann derivatives at both
endpoints and spatially nonconstant initial data.

The interval length is determined by the unstable frequency, and the
instability is that of the linear system.
:::

:::proof "parabolic.turing_instability"
The trace and determinant of $`A` give homogeneous asymptotic stability.
For a spatial mode with $`\mu=k^2`, the determinant becomes
$`d_1d_2\mu^2-w\mu+(ad-bc)`. The strict inequalities make this quadratic
negative for some $`\mu>0`, so the mode matrix has a positive real
eigenvalue $`\lambda` and a nonzero eigenvector with nonzero first
component. Multiplying that eigenvector by a sufficiently small scalar
gives any requested initial uniform bound, while $`e^{\lambda t}`
forces growth at the origin. Setting the interval length to $`\pi/k`
makes the sine factors in both boundary derivatives vanish.
:::

# Finite-Time Behavior

The linear existence theorems work on prescribed finite time intervals. For
nonlinear parabolic equations, the length of that interval can itself become a
question: a reaction term can outrun diffusion and force a norm to infinity in
finite time, and Keller–Segel aggregation can concentrate mass. The finite-time
results include the large-data obstruction for
{bpref "parabolic.nonlinear_heat_large_data"}[nonlinear heat] and moment-based
obstructions for Keller–Segel.

{include 2 Blueprint.Chapters.Parabolic.FiniteTime}

# Coverage and Open Problems

{include 2 Blueprint.Chapters.Parabolic.Scope}
