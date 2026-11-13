/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.WeakProblems.LowerOrder

/-!
# Weak elliptic problems

Weak Dirichlet, principal divergence-form, and lower-order elliptic problems, at three
levels:

* the abstract Hilbert-space Lax–Milgram interface;
* the graph-space Poisson and operator-valued divergence forms; and
* pointwise $`L^\infty` coefficient fields, represented by
  multiplication operators on $`L^2(\Omega)`.

A problem is a distributional PDE after specialization to multiplication
operators on an open domain.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Weak Elliptic Problems" =>

# Why Pass to a Weak Equation?

There is a mismatch at the heart of elliptic theory. A classical solution of a
second-order equation may need two pointwise derivatives, while the energy
attached to that equation controls only one weak derivative. The weak
formulation resolves it by moving a derivative onto a test function and asking
for an identity in $`H^1_0(\Omega)`, which is exactly the level at which
coercivity, compactness, and variational methods can build solutions.

# Main Objects and Hypotheses

An abstract weak problem is a bounded bilinear form $`a` together with a bounded
linear load $`F`, and a solution satisfies

$$`a(u,v)=F(v)\qquad\text{for every test function }v.`

The concrete Poisson solver assumes a bounded domain in positive dimension.
Its Dirichlet form $`a` is built from weak gradients; Poincaré's inequality
promotes gradient control to coercivity on $`H^1_0`. The solver is a bounded
map of the square-integrable load, satisfies an a priori norm estimate, and is
characterized by both the variational equation and minimization of the
Dirichlet energy.

Variable principal coefficients enter first as bounded operators on the gradient
coordinates, with pointwise $`L^\infty` coefficient fields arriving through
multiplication operators. Almost-everywhere uniform ellipticity gives an
integrated lower bound by the Dirichlet form. Combining this bound with the
bounded-domain Poincaré inequality gives the coercivity Lax–Milgram needs.

Lower-order terms can destroy positivity. What survives is a Gårding estimate,
which says the form is coercive up to an $`L^2` error, and adding a large enough
multiple of the pivot inner product turns that into a shifted coercive problem
with a unique weak solution and a quantitative solver bound.

Almost-everywhere uniform ellipticity and integrated uniform ellipticity are different predicates: the
first describes a coefficient field almost everywhere, the second is an
integrated operator inequality, and passing from the first to the second is a
theorem.

{include 0 Blueprint.Chapters.Elliptic.WeakProblems.Dirichlet}
{include 0 Blueprint.Chapters.Elliptic.WeakProblems.DivergenceForm}
{include 0 Blueprint.Chapters.Elliptic.WeakProblems.LowerOrder}
