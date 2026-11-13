/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.Compactness

/-!
# Weak evolution and Galerkin approximation

Weak evolution on a Gelfand triple: foundations, Lions–Magenes time
regularity, integrated solutions, and the Galerkin construction.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Weak Evolution and Galerkin Approximation" =>

# The Evolution Problem at Energy Regularity

For a parabolic equation, the spatial energy often places the solution in a
space $`V`, while the time derivative is meaningful only in the dual
$`V^*`. The initial condition, however, belongs naturally to an intermediate
Hilbert space $`H`. A Gelfand triple

$$`V\hookrightarrow H\hookrightarrow V^*`

places the weak equation in
$`V^*` for almost every time, and the initial value is interpreted through a
continuous $`H`-valued representative.

# From Smooth Evolution to the Gelfand Triple

The starting point is a smooth Hilbert-space model. A bounded bilinear form
is converted by the Riesz theorem into an operator, so the weak equation can
be read as an ordinary affine ODE. Its energy identity explains the estimates
that survive at lower regularity.

The weak time-derivative condition is an
integration-by-parts statement in time. The weak evolution equation
adds the spatial form and forcing. The weak time derivative is unchanged when
a Bochner representative is modified on a null set, and for complete $`V` it is
unique, so it is determined by the trajectory.

# Time Traces and Integrated Solutions

An element of $`L^2(a,b;V)` is an almost-everywhere equivalence class, so its
value at a particular time has no meaning, and an equation in $`V^*` almost
everywhere does not by itself license writing `u 0`. Parabolic initial
conditions and energy identities nevertheless require endpoint values.
Lions–Magenes regularity resolves this for a trajectory square integrable in
$`V` whose weak time derivative is square integrable in $`V^*`. Time
mollification proves the energy identity for smooth approximants, and the
limit selects a unique continuous $`H`-valued representative satisfying the
energy identity. This representative carries the initial trace and the
pointwise-in-time energy estimates.

The integrated formulation moves the time derivative from the trajectory onto
a scalar time test. It makes sense directly for a Bochner $`L^2` class and
records the initial datum through the boundary term created by integration by
parts. It is well suited to weak convergence because it avoids selecting a
pointwise derivative for each approximation, and the Galerkin limit is taken
in this formulation. When the form is strongly measurable and essentially
bounded, a residual theorem recovers $`\ell-B(\cdot)u` as the weak $`V^*`
time derivative, Lions–Magenes supplies the continuous representative with
its initial trace, and the energy identity gives uniqueness and continuous
dependence under coercivity or a Gårding bound.

# Galerkin Construction

Finite-dimensional trial spaces turn the weak PDE into a system of
Carathéodory ODEs with a pivot mass operator. Stability of the projections in
both $`V` and $`H`, together with density, lets their solutions approximate the
infinite-dimensional problem.

The construction has four distinct stages:

1. restrict the form and load to each trial space and solve the finite system;
2. derive energy bounds independent of the trial dimension;
3. extract a weak state limit and pass to the integrated identity;
4. use the energy argument to identify the unique limit.

The quantitative time-Sobolev estimate turns Lions–Magenes regularity into a
bound on the continuous representative; the parabolic regularity theorems and
the weak wave theory use it to control time-dependent forcing and
differentiated Galerkin families. When the energy-to-pivot inclusion is
compact, the Aubin–Lions theorem combines that time regularity with the
spectral Galerkin tail estimate to produce strong compactness in
$`L^2(a,b;H)`.

## Example: The Galerkin Method for the Heat Equation

Fix $`T>0`, $`u_0\in L^2(0,\pi)` and
$`f\in L^2(0,T;H^{-1}(0,\pi))`. Consider the weak Dirichlet heat equation
on $`\Omega=(0,\pi)` for $`0<t<T`:

$$`u_t-u_{xx}=f,\qquad u(0,t)=u(\pi,t)=0,\qquad u(x,0)=u_0(x).`

The Gelfand triple is $`V=H^1_0(0,\pi)\hookrightarrow H=L^2(0,\pi)
\hookrightarrow V^*=H^{-1}(0,\pi)`, and the bilinear form is
$`B(u,v)=\int_0^\pi u_xv_x\,dx`.
For this example, equip $`V` with the equivalent energy norm
$`\|v\|_V=\|v_x\|_{L^2}` and use its corresponding dual norm on $`V^*`.
The graph norm used in the theorems also includes the $`L^2` norm.

*Step 1: Finite-dimensional projection.* Take the trial space
$`V_m=\operatorname{span}\{\sin(kx):1\leq k\leq m\}`. Write
$`u_m(x,t)=\sum_{k=1}^m c_k(t)\sin(kx)`. The Dirichlet eigenfunctions
$`\sin(kx)` are $`L^2`-orthogonal with squared norm $`\pi/2`.
Testing against $`\sin(jx)`
gives the decoupled ODE system

$$`\dot c_j(t)+j^2c_j(t)=f_j(t),\qquad
c_j(0)=\frac{2}{\pi}\int_0^\pi u_0(x)\sin(jx)\,dx.`

Here $`f_j(t)=(2/\pi)\langle f(t),\sin(j\,\cdot)\rangle_{V^*,V}`.
For an $`L^2`-valued force this is
$`(2/\pi)\int_0^\pi f(x,t)\sin(jx)\,dx`.
The coefficients are absolutely continuous and satisfy the ODEs almost
everywhere, with the explicit formula
$`c_j(t)=c_j(0)e^{-j^2t}+\int_0^t e^{-j^2(t-s)}f_j(s)\,ds`.

*Step 2: Energy estimate.* Multiply the $`j`th equation by $`(\pi/2)c_j(t)`,
sum over $`j`, and recognize $`\|u_m\|_H^2=(\pi/2)\sum c_j^2` and
$`\|u_m\|_V^2=(\pi/2)\sum j^2c_j^2`. For almost every $`t\in(0,T)` this gives

$$`\frac12\partial_t\|u_m\|_H^2+\|u_m\|_V^2
\leq\langle f,u_m\rangle
\leq\frac12\|f\|_{V^\ast}^2+\frac12\|u_m\|_V^2.`

After absorbing the $`V`-norm and integrating, one obtains
$`\|u_m(t)\|_H^2+\int_0^t\|u_m\|_V^2\leq\|u_0\|_H^2+\int_0^t\|f\|_{V^\ast}^2`,
independently of $`m`. This uniform bound is the heart of the method.

*Step 3: Weak limit.* The formal compactness argument uses the uniform
$`L^2(0,T;V)` bound on the states to extract a weak limit along an ultrafilter
refining the index filter. Boundedness of the bilinear form and strong
convergence of the trial projections let the integrated equations pass to
this limit. General $`L^2` loads are reached by completing the solution
operator from bounded continuous loads using the energy estimate. The
residual $`g=f-Bu` then supplies the weak derivative in $`L^2(0,T;V^*)`,
and Lions–Magenes regularity constructs the continuous pivot representative.

*Step 4: Identification.* The energy estimate also gives uniqueness of the
weak solution (Evans, 2010, p. 379; Lions and Magenes, 1972, Ch. 3).
Any weak limit obtained by this construction therefore represents the same
integrated weak solution.

Orthogonality and the eigenfunction structure of the sine basis make the
ODE system explicit, but the abstract theory needs neither: any stable dense
family of trial spaces produces the same estimates.

The compact Gram operator supplies stable trial projections for
$`H^1_0(\Omega)\hookrightarrow L^2(\Omega)` on bounded open $`\Omega`.

{include 0 Blueprint.Chapters.Parabolic.WeakEvolution.Foundations}
{include 0 Blueprint.Chapters.Parabolic.WeakEvolution.TimeRegularity}
{include 0 Blueprint.Chapters.Parabolic.WeakEvolution.IntegratedSolutions}
{include 0 Blueprint.Chapters.Parabolic.WeakEvolution.Galerkin}
{include 0 Blueprint.Chapters.Parabolic.WeakEvolution.TimeSobolev}
{include 0 Blueprint.Chapters.Parabolic.WeakEvolution.Compactness}
