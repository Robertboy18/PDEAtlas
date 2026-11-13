/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.FiniteTime.KellerSegel.Abnormal3D

/-!
# Finite-time singularities

Blow-up predicates, nonlinear heat profiles, and the parabolic, virial, and
abnormal-scaling Keller–Segel developments.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Finite-Time Growth, Lifespan, and Similarity" =>

# Solutions, Growth, and Continuation

A formula that grows quickly is only a candidate. A finite-time singularity
statement exhibits a solution on times before some finite horizon and proves that
a specified norm or observable becomes unbounded as that horizon approaches. We
formalize the pieces separately: the solution concept, the maximal-time or
norm-divergence predicate, the mechanism forcing the growth, and its application
to the original PDE.

With the pieces kept apart, different arguments can be compared. Explicit
solutions, Riccati comparison, weighted moments, virial identities, and
self-similar profiles all appear, and each proves a different kind of
conclusion.

# Reusable Growth Mechanisms

A Banach-space trajectory blows up when its norm tends to infinity from the
left of a finite time. The associated theorems transfer blow-up through scalar amplitudes,
linear isometries, and bounded remainders, and prove that such a trajectory
cannot have a continuous extension across the singular time.

For spatial fields, the corresponding supremum-norm predicate can be proved
from one diverging sample or from a weighted moment.

The Riccati model $`y'=cy^2`, with $`c>0` and a positive initial value, gives
the basic differential-inequality mechanism. Its explicit solution diverges at
an explicit horizon. A trajectory with the same initial value satisfying
$`y'\ge cy^2` up to that horizon blows up there; if the inequality holds on a
closed interval, the interval ends strictly before the horizon.

# Equation-Specific Branches

The nonlinear heat branch begins on a bounded domain, where a first
Dirichlet eigenfunction moment excludes nonnegative weak solutions with large
initial data on a prescribed interval. On the whole space it contains a
complete example: a nonnegative spatially constant classical solution is
verified directly and its spatial supremum norm is proved to blow up at finite
time. The same chapter derives Type I and scaling-invariant profile equations.
These profile theorems say when an ansatz solves the PDE and when its scale
forces concentration; the profile itself is a hypothesis.

The parabolic Keller–Segel branch derives the density and potential profile
equations under the standard similarity scaling. A pair of $`C^2` profiles
satisfying both equations, with nonnegative density profile, generates a
classical pre-singular solution. A bounded density profile with one nonzero
value makes the density ansatz blow up in the spatial supremum norm.

The virial branch follows a different route. An affine second-moment identity
and nonnegativity constrain the right endpoint of a solution interval by an
explicit horizon. This is a lifespan theorem: it rules out continuation of a
solution retaining the stated moment properties beyond that time.

The abnormal three-dimensional scaling is analyzed as an obstruction
calculation. Its amplitude diverges and its diffusion coefficient vanishes
in rescaled variables, but the physical residual can diverge. Under the
aggregation profile equation, the exact criterion says that the density
residual vanishes everywhere precisely when the density profile is harmonic.

# Types of Conclusion

Four kinds of conclusion serve different purposes:

* a *residual identity* computes the error of an ansatz;
* a *profile equivalence* says the residual vanishes exactly when the reduced
  equations hold;
* a *solution theorem* proves the original PDE on the pre-singular domain;
* a *blow-up or lifespan theorem* proves norm divergence or a finite endpoint.

A singularity result must connect an actual solution to norm divergence or a
proved obstruction to continuation. For an ansatz, a sufficient profile
condition and its analytic hypotheses can establish the solution; a converse
profile equivalence is useful but not required. The explicit nonlinear-heat
theorem is both a solution theorem and a blow-up theorem; the virial and
Riccati theorems are lifespan theorems for intervals carrying their stated
hypotheses.

{include 0 Blueprint.Chapters.Parabolic.FiniteTime.Core}
{include 0 Blueprint.Chapters.Parabolic.FiniteTime.NonlinearHeat}
{include 0 Blueprint.Chapters.Parabolic.FiniteTime.KellerSegel.Similarity}
{include 0 Blueprint.Chapters.Parabolic.FiniteTime.KellerSegel.Virial}
{include 0 Blueprint.Chapters.Parabolic.FiniteTime.KellerSegel.Abnormal3D}
