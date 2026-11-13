/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.ConservationLaws.SystemLimits
import Blueprint.Commands.Figures

/-!
# Conservation laws

Conservation laws: scalar characteristics, weak and entropy solutions,
Burgers's equation, and finite-dimensional systems.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Conservation Laws" =>

# The Mathematical Transition at Shock Formation

Characteristics solve a conservation law right up until the characteristic map
stops being invertible. Once characteristics intersect, classical derivatives are
gone and the equation has to be read through an integral identity instead.
For Burgers, that identity admits both compression and expansion shocks. An entropy
condition distinguishes them and supplies the additional selection needed
for scalar uniqueness.

For scalar equations we follow that transition; for finite-dimensional systems
we build the parallel local geometry. Burgers's equation and the p-system are
the concrete models, since shocks, rarefactions, entropy, and initial traces
can all be checked explicitly in them.

## Why Entropy Conditions Are Needed

Consider Burgers's equation $`u_t+(u^2/2)_x=0` with Riemann data
$`u_0(x)=1` for $`x<0` and $`u_0(x)=0` for $`x>0`. Its entropy solution is
a shock moving at speed $`s=1/2`:

$$`u(x,t)=\begin{cases}1&x<t/2,\\0&x>t/2.\end{cases}`

But the same equation with the *reversed* Riemann data $`u_0(x)=0` for
$`x<0` and $`u_0(x)=1` for $`x>0` shows why the weak identity is
insufficient. The entropy solution is the expansion fan
$`u(x,t)=x/t` for $`0<x<t`, but the nonphysical expansion shock jumping
from 0 to 1 at speed $`s=1/2` is also a distributional weak solution. The
speed is fixed, not arbitrary: Rankine–Hugoniot gives
$`s=[f(u)]/[u]=(1/2-0)/(1-0)=1/2`.

{leanpde_figure "shock-formation"}

The figure places two mechanisms side by side in one initial profile: a
descending ramp compresses, while a separate upward jump opens into a fan.
Before the ramp breaks, its characteristic denominator is the same one
checked in the {bpref "hyperbolic.burgers.affine_solution"}[affine Burgers
example]. At the breaking time that denominator vanishes. Continuing the
picture past that time requires the weak and entropy formulations, with the
two-state Riemann profiles as explicit models.

The entropy condition resolves this ambiguity by imposing a directionality on
shocks. The Lax condition $`f'(u_L)>s>f'(u_R)` requires that characteristics
enter the shock from both sides, modeling compression. For the displayed
convex Burgers jump, this selects the same branch as the Kružkov inequalities
$`\partial_t|u-k|+\partial_x(\operatorname{sgn}(u-k)(f(u)-f(k)))\leq 0` for
every constant $`k`. With this mathematical-entropy convention, the spatial
integral of the entropy is nonincreasing when boundary fluxes vanish. Physical
entropy is often written with the opposite sign.

The physical origin of this condition is the vanishing-viscosity limit. The
equation $`u_t^\epsilon+(f(u^\epsilon))_x=\epsilon u_{xx}^\epsilon` is
parabolic for $`\epsilon>0`. Under the standard scalar-flux and data
hypotheses, its solutions converge as $`\epsilon\downarrow 0` to the entropy
solution; the proof of convergence needs compactness and stability estimates
beyond the formal perturbation.

Evans (2010, §3.4, pp. 135–161, and Ch. 11, pp. 609–653) develops the
theory; {Informal.citet "lax-1957"}[] and {Informal.citet "oleinik-1957"}[]
gave the foundational entropy conditions.

# Scalar Equations

For $`C^1` speed and data, the transported datum is a classical solution on
the whole strip below the first degeneracy time $`T_*` of the characteristic
Jacobian, and no $`C^1` solution extends past $`T_*`. Weak solutions satisfy
the distributional identity, with the initial datum entering through a
time-zero boundary term or a strong local $`L^1` trace; entropy solutions add
the inequality for every convex entropy pair. For Burgers's equation the
explicit Riemann solution is a shock when the left state exceeds the right
state and a rarefaction fan otherwise, and it is an entropy solution with the
step datum as its strong initial trace.

Beyond Burgers, the scalar theory proves uniqueness twice: in Oleinik's
one-sided class for a convex flux, and for any $`C^1` flux by the local
$`L^1` contraction of {Informal.citet "kruzkov-1970"}[]. For a uniformly convex
flux the Lax–Oleinik formula gives a weak solution for every bounded datum,
the Riemann problem has a
unique solution in the Oleinik class. Under the stated $`C^3` flux and
positive-lobe hypotheses, compactly supported data approach an N-wave at the
rate $`t^{-1/2}` in $`L^1`.

# Systems and Elementary Waves

For a system $`u_t+f(u)_x=0`, hyperbolicity concerns the eigenstructure of the
Jacobian $`Df(u)`. Genuine nonlinearity and linear degeneracy are additional
conditions on characteristic fields. With the required regularity, linearly
degenerate integral curves give contact connections; rarefaction connections
also require increasing speed along the oriented curve. Rankine–Hugoniot
relations describe shocks.

A local wave family supplies transformations with prescribed strict
zero-strength derivatives; elementary-wave admissibility is a separate
hypothesis. When the chosen characteristic vectors at the left state form
a basis, the composed wave map has invertible derivative. The inverse
function theorem then gives a unique strength vector within a source
neighborhood for each nearby right state. For a $`C^2` strictly hyperbolic
flux whose families are each genuinely nonlinear or linearly degenerate,
local shock curves and integral curves supply such a family, and the
strengths assemble into a bounded self-similar weak solution of the Riemann
problem.

Entropy pairs supply a scalar conservation or dissipation law compatible with
the system. For the p-system we verify strict hyperbolicity, mechanical
entropy, Riemann invariants, and diagonal transport form, and construct a
local Riemann solution satisfying the mechanical entropy inequality. For
$`2\times2` systems in Riemann coordinates, compressive data rule out a global
classical solution. For a smooth, strictly hyperbolic, genuinely nonlinear
flux, small jumps admit viscous profiles exactly when they are Lax shocks.
Almost-everywhere limits of bounded viscous solutions are entropy solutions.

# Two Routes, Scalar and System

The scalar route is

$$`\text{characteristics before shock}
\longrightarrow\text{weak formulation}
\longrightarrow\text{entropy inequality}
\longrightarrow\text{uniqueness, Lax–Oleinik, N-wave}.`

The system route is

$$`\text{hyperbolic eigenstructure}
\longrightarrow\text{elementary wave curves}
\longrightarrow\text{local wave map}
\longrightarrow\text{local Riemann solver and entropy}
\longrightarrow\text{viscous limits}.`

{include 0 Blueprint.Chapters.Hyperbolic.ConservationLaws.ScalarCharacteristics}
{include 0 Blueprint.Chapters.Hyperbolic.ConservationLaws.WeakSolutions}
{include 0 Blueprint.Chapters.Hyperbolic.ConservationLaws.Burgers}
{include 0 Blueprint.Chapters.Hyperbolic.ConservationLaws.ScalarTheory}
{include 0 Blueprint.Chapters.Hyperbolic.ConservationLaws.Systems}
{include 0 Blueprint.Chapters.Hyperbolic.ConservationLaws.SystemLimits}
