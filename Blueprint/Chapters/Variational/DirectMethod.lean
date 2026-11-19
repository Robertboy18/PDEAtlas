/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod.IntegralFunctionals
import Blueprint.Commands.Figures

/-!
# The direct method

The direct method in the calculus of variations: weak compactness, abstract
minimization, the quadratic model, and Sobolev integral functionals.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "The Direct Method" =>

# From an Infimum to a Minimizer

The direct method proves a minimizer exists without ever writing one down. You
start with a sequence $`(u_k)` satisfying

$$`
J(u_k)\longrightarrow\inf_{v\in A}J(v),
`

where $`A` is the admissible class. The sequence need not converge strongly,
and its limit need not be available in closed form. The proof instead chooses a
topology weak enough to provide compactness and strong enough for the energy to
survive passage to the limit.

The old Dirichlet principle assumed that an energy infimum was attained and
then used the minimizer to solve a boundary-value problem. Weierstrass's
objections exposed the missing existence argument: continuity alone on an
infinite-dimensional function space does not force an infimum to be attained.
Hilbert, Tonelli, and later Morrey supplied conditions under which the
principle becomes valid. Evans's Chapter 8 presents the modern Sobolev-space
argument through weak convergence, coercivity, and lower semicontinuity.

In a reflexive space, the argument has the following form:

$$`\text{coercivity}
\longrightarrow\text{bounded minimizing sequence}
\longrightarrow\text{weakly convergent subsequence}
\longrightarrow\text{weak lower semicontinuity}
\longrightarrow\text{minimizer}.`

{leanpde_figure "direct-method"}

The panels isolate two parts of the argument. The scalar energy shows how
coercivity confines a minimizing sequence. The oscillating functions explain
why we may need weak convergence: their norms do not decay, even though
their pairing with the displayed test function tends to zero. That one
pairing illustrates the distinction; weak convergence requires the
corresponding limit against every continuous linear functional.

Coercivity prevents escape to infinity. If

$$`
\lVert u\rVert\longrightarrow\infty
\quad\Longrightarrow\quad
J(u)\longrightarrow+\infty,
`

then every sufficiently low sublevel set is bounded. Reflexivity turns that
bound into a weakly convergent subsequence. Weak closedness keeps the limit
inside $`A`, and weak lower semicontinuity gives

$$`
J(u)\leq\liminf_{j\to\infty}J(u_{k_j})
=\inf_{v\in A}J(v).
`

# Compactness and Lower Semicontinuity

A convex functional that is lower semicontinuous in norm is weakly lower
semicontinuous. Strict convexity adds uniqueness; existence does not need it.

# Concrete Energies

For a quadratic $`L^2` energy, expanding a squared norm gives these
properties directly. For integral functionals

$$`I(u)=\int_\Omega L(x,u(x),Du(x))\,dx`

the hypotheses have to be derived from properties of the density $`L`.

{include 0 Blueprint.Chapters.Variational.DirectMethod.WeakCompactness}
{include 0 Blueprint.Chapters.Variational.DirectMethod.AbstractMinimization}
{include 0 Blueprint.Chapters.Variational.DirectMethod.QuadraticModel}
{include 0 Blueprint.Chapters.Variational.DirectMethod.IntegralFunctionals}
