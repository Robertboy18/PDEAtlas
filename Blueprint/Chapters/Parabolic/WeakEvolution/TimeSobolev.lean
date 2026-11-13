/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.Galerkin
import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev

/-!
# Quantitative time-Sobolev embedding

The explicit endpoint bound for continuous pivot representatives in terms of
the time-Sobolev norm.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Quantitative Time-Sobolev Embedding" =>

For estimates and compactness arguments one needs a numerical bound on the
Lions–Magenes representative in terms of the Bochner norms of the trajectory
and its weak time derivative. The energy formula and one-dimensional
averaging give such a bound on the whole closed time interval.

# Quantitative time embedding

Throughout these estimates, assume $`a<b`.

:::definition "parabolic.time_sobolev.gelfand_bound" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.gelfandTimeSobolevBound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "301-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a Gelfand inclusion $`J:V\hookrightarrow H`, a trajectory
$`u\in L^2(a,b;V)`, and a dual weak derivative
$`g\in L^2(a,b;V^*)`, define

$$`
C_{J,a,b}(u,g)=
\left(
  \frac{\|J\|^2\|u\|_{L^2(V)}^2}{b-a}
  +2\|u\|_{L^2(V)}\|g\|_{L^2(V^*)}
\right)^{1/2}.
`
:::

The two terms of this constant correspond to the two steps of the estimate.
The first dominates the interval average of $`\lVert Ju\rVert_H^2`, a value
that the squared norm of the continuous representative must attain at some
time; the second bounds, through the energy identity, how far the squared
pivot norm can move between that time and any other point of $`[a,b]`.

:::theorem "parabolic.time_sobolev.gelfand_representative_bound" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.norm_representative_le_gelfandTimeSobolevBound, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.norm_representative_le_of_L2_norm_le") (uses := "parabolic.lions_magenes_energy_identity, parabolic.time_sobolev.gelfand_bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "301-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On a nontrivial interval $`a<b`, every Lions–Magenes representative satisfies

$$`\|\widetilde u(t)\|_H\le C_{J,a,b}(u,g)
\qquad(t\in[a,b]).`

Consequently, uniform $`L^2(a,b;V)` and $`L^2(a,b;V^*)` bounds give a
uniform pivot-space bound without an additional $`L^\infty(a,b;H)`
hypothesis.
:::

:::proof "parabolic.time_sobolev.gelfand_representative_bound" (uses := "parabolic.lions_magenes_energy_identity")
Choose a time where the squared pivot norm equals its interval average.
The inclusion operator bounds that average by
$`\|J\|^2\|u\|_{L^2(V)}^2/(b-a)`. Apply the exact energy identity between
that time and $`t`, then use the duality estimate and $`L^2` Hölder to bound
the pairing integral by $`\|u\|_{L^2(V)}\|g\|_{L^2(V^*)}`.
:::

In the identity triple $`V=H`, $`Ju=u`. The Riesz isometry identifies the
dual weak derivative with a Hilbert-valued function $`du\in L^2(a,b;H)`,
giving the familiar one-dimensional Sobolev bound for $`H^1(a,b;H)`.

:::definition "parabolic.time_sobolev.bound" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.timeSobolevBound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "301-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For Hilbert-valued data $`u,u'` in $`L^2(a,b;H)`, the explicit
one-dimensional time-Sobolev bound is

$$`\left(\frac{\lVert u\rVert_{L^2}^2}{b-a}
  +2\lVert u\rVert_{L^2}\lVert du\rVert_{L^2}\right)^{1/2}.`
:::

Because the representative agrees with the Bochner trajectory off a null
set, the bound also has an almost-everywhere form for the trajectory itself,
a statement that makes sense without choosing a representative.

:::theorem "parabolic.time_sobolev.continuous_representative_bound" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn.exists_continuousRepresentative_norm_le_of_identity") (uses := "parabolic.lions_magenes_finite_interval, parabolic.time_sobolev.bound")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "301-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If `du` is the weak time derivative of `u` on a nontrivial finite interval,
then the Lions–Magenes representative for the identity Gelfand triple is continuous
on the closed interval and satisfies

$$`
  \|\widetilde u(t)\|_H
  \leq
  \left(
    \frac{\|u\|_{L^2(a,b;H)}^2}{b-a}
    +2\|u\|_{L^2(a,b;H)}\|du\|_{L^2(a,b;H)}
  \right)^{1/2}
`

for every $`t\in[a,b]`. The original Bochner trajectory satisfies the same
estimate almost everywhere.
:::

:::proof "parabolic.time_sobolev.continuous_representative_bound" (uses := "parabolic.lions_magenes_finite_interval")
Choose an interior time at which the squared norm equals its interval
average.  The exact Hilbert-space energy identity controls the change from
that time to an arbitrary endpoint, and the $`L^2` Hölder inequality bounds
the resulting dual pairing integral.
:::
