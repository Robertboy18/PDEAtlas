/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.Foundations
import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.LionsMagenes.Basic.RegularizedEnergy
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Evolution.Time.Mollification
import PDE.Analysis.Evolution.Time.Mollification.WeakDerivative
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval

/-!
# Weak evolution time regularity

Time mollification, integrated dual derivatives, and the continuous pivot
representative supplied by the Lions–Magenes argument.
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
#doc (Manual) "Time Regularity for Weak Evolution" =>

# Time regularization

:::theorem "parabolic.time_regularization" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.regularizeTime_contDiff, PDE.Analysis.Evolution.regularizeTime, PDE.Analysis.Evolution.regularizeTime_converges_Lp, PDE.Analysis.Evolution.hasDerivAt_regularizeTime_of_hasWeakTimeDerivative") (uses := "sobolev.mollifier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "378-379"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For $`\varepsilon>0`, convolution in time with the normalized
one-dimensional mollifier sends a locally integrable Banach-valued function
on $`\mathbb R` to a smooth trajectory. If $`f\in L^p(\mathbb R;X)` for
$`1\le p<\infty`, the regularizations converge to $`f` in that Bochner
$`L^p` norm along every positive sequence $`\varepsilon\to0`.
If $`g` is the weak time derivative of $`f` on all of $`\mathbb R`, then

$$`\frac{d}{dt}(\rho_\varepsilon*f)(t)
  =(\rho_\varepsilon*g)(t).`

This approximation identity is the mechanism behind the Lions–Magenes
energy identity.
:::

:::proof "parabolic.time_regularization"
Apply Banach-valued mollifier theory to the functions on $`\mathbb R`, using
local integrability for smoothness and global $`L^p` membership for norm
convergence. Applications on a finite interval require a compatible
extension or cutoff before this global derivative identity applies. To
identify the derivative, test the convolution against a continuous linear
functional, move the scalar derivative from the mollifier onto the weak
derivative by the distributional identity, and use separation of points in
the Banach space. This yields
$`(\rho_\varepsilon*f)'=\rho_\varepsilon*g`.
:::

# Lions–Magenes time regularity

:::definition "parabolic.integrated_dual_derivative" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn") (uses := "parabolic.gelfand_triple")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "299-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

A pivot-space trajectory $`u_H:\mathbb R\to H` has integrated dual
derivative $`g:\mathbb R\to V^*` on $`[a,b]` when $`g` is Bochner
integrable there and

$$`J^*u_H(t)=J^*u_H(a)+\int_a^t g(s)\,ds
  \qquad(t\in[a,b]).`

This is endpoint-inclusive data in $`V^*`.  Differentiability of $`u_H` as
an $`H`-valued map would require the stronger assumption that $`g` is
represented by an integrable pivot-space velocity.
:::

Because the defining identity equates $`J^*u_H(t)` with an indefinite
Bochner integral in $`V^*`, the elementary properties of such integrals
transfer to the trajectory at once.

:::theorem "parabolic.integrated_dual_fundamental_theorem" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn.continuousOn_pivotToDual, PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn.pairing_eq_add_integral, PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn.pairing_sub_eq_integral, PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn.norm_pivotToDual_sub_le") (uses := "parabolic.integrated_dual_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "299-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

The integrated identity makes $`J^*u_H` continuous as a $`V^*`-valued map
and gives, for every $`v\in V` and $`s,t\in[a,b]`,

$$`(u_H(t),Jv)_H-(u_H(s),Jv)_H
  =\int_s^t g(r)[v]\,dr.`

For $`s\le t` it also gives

$$`\lVert J^*u_H(t)-J^*u_H(s)\rVert_{V^*}
\le\int_s^t\lVert g(r)\rVert_{V^*}\,dr.`

These are spatially weak forms of the fundamental theorem of calculus;
strong continuity in $`H` is the extra content of Lions–Magenes.
:::

:::proof "parabolic.integrated_dual_fundamental_theorem"
The defining identity writes $`J^*u_H(t)` as a fixed vector plus the
indefinite Bochner integral of $`g`, which is continuous. Subtract the
identities at $`s` and $`t`, then evaluate the resulting $`V^*` equality on
$`v` to obtain the pairing formula. For $`s\le t`, taking the dual norm and
applying the Bochner integral norm estimate gives the final bound.
:::

Strong continuity into $`H` comes from a different mechanism. Time
mollification produces smooth approximants $`u_\varepsilon` for which
$`\frac{d}{dt}\lVert Ju_\varepsilon\rVert_H^2
=2\langle u_\varepsilon',u_\varepsilon\rangle` is an ordinary chain rule.
The energy identity survives the limit $`\varepsilon\to0`, and it is what
upgrades the pointwise limit to a continuous representative.

:::theorem "parabolic.lions_magenes" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.exists_continuous_pivot_representative") (uses := "parabolic.gelfand_triple, parabolic.time_regularization, parabolic.integrated_dual_fundamental_theorem")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "299-304"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "374-379"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%

For a Gelfand inclusion between real Hilbert spaces $`V` and $`H`, if
$`u\in L^2(\mathbb R;V)` has weak derivative
$`u'\in L^2(\mathbb R;V^*)`, then the pivot-space class has a continuous
representative $`u_H:\mathbb R\to H`. It agrees almost everywhere with the
dense inclusion of $`u`, has integrated dual derivative $`u'` on every
finite interval, and satisfies

$$`\lVert u_H(b)\rVert_H^2-\lVert u_H(a)\rVert_H^2
  =2\int_a^b \langle u'(t),u(t)\rangle_{V^*,V}\,dt.`

This is the abstract theorem used by Evans to infer
$`u\in C([0,T];L^2(U))` before interpreting the initial condition in the
parabolic weak problem.
:::

:::proof "parabolic.lions_magenes" (uses := "parabolic.time_regularization, parabolic.integrated_dual_fundamental_theorem")
Regularize both $`u` and its dual derivative in time, prove the energy
identity for the smooth approximants, obtain a pointwise pivot-space limit,
and strengthen it to a continuous representative using the integral energy
formula.
:::

The global theorem asks for square integrability on the whole line, whereas
the parabolic problem lives on $`[a,b]` and its data are Bochner classes on
that interval. The passage to a finite interval is not automatic: the
trajectory and derivative must be cut off and reflected across the endpoints
without creating boundary distributions, and the representatives obtained on
overlapping subintervals must be glued into one. This yields a continuous pivot representative on the finite interval.

:::theorem "parabolic.lions_magenes_finite_interval" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.HasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn, PDE.Analysis.Evolution.ContinuousPivotEvolutionOnOpen, PDE.Analysis.Evolution.ContinuousPivotEvolutionOnOpen.toContinuousPivotEvolutionOn") (uses := "parabolic.gelfand_weak_time_derivative, parabolic.lions_magenes")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "299-304"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "374-379"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%

Under the same Hilbert-space hypotheses, for $`a<b`, an
$`L^2(a,b;V)` trajectory with an
$`L^2(a,b;V^*)` Gelfand weak derivative first has a canonical continuous
pivot representative on $`(a,b)`.  Reflected cutoff extensions at both
endpoints then produce a representative in $`C([a,b];H)` without assuming
pre-existing traces.  The returned structure records almost-everywhere
agreement with $`Ju`, the integrated $`V^*` derivative identity, and the
exact energy identity for all endpoints in $`[a,b]`.
:::

:::proof "parabolic.lions_magenes_finite_interval"
The Gelfand weak derivative gives the distributional derivative of the
dual-valued trajectory through the weak time-derivative condition. Apply the global
theorem to interior cutoff extensions. Their continuous
pivot representatives agree on overlaps because each equals $`Ju` almost
everywhere, so they glue on $`(a,b)`. Reflect the state and dual derivative
compatibly, then choose a cutoff equal to one near $`[a,b]`. The global
theorem for this extension supplies both endpoint traces, and its integrated
derivative and energy identities restrict to the closed interval.
:::

The energy identity is a field of that structure, so for the canonical
representative it holds between any two points of $`[a,b]` with no
continuity assumption on the $`V`-valued representative.

:::theorem "parabolic.lions_magenes_energy_identity" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.energyIdentity, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.absolutelyContinuousOnInterval_norm_sq, PDE.Analysis.Evolution.weakTimeDerivative_energy_identity_at_continuityPoints") (uses := "parabolic.time_regularization, parabolic.lions_magenes_finite_interval")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "299-304"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For the continuous pivot representative $`u_H`, the squared norm is
absolutely continuous and obeys, for all $`s,t\in[a,b]`,

$$`\lVert u_H(t)\rVert_H^2-\lVert u_H(s)\rVert_H^2
  =2\int_s^t g(r)[u(r)]\,dr.`

For $`u,g` square integrable on $`\mathbb R` and satisfying the weak
derivative identity there, the companion theorem gives the corresponding
identity for $`Ju` at two continuity points of $`u`. The finite-interval
evolution instead uses the canonical $`H` representative and needs no such
pointwise assumptions.
:::

:::proof "parabolic.lions_magenes_energy_identity"
For global data, mollify $`u` and $`g` in time; on a finite interval use the
reflected cutoff extensions. For the smooth approximants, the Hilbert chain
rule gives
$`\frac d{dt}\|Ju_\varepsilon\|_H^2
=2\langle g_\varepsilon,u_\varepsilon\rangle`. Integrate from $`s` to $`t`.
The selected sequence converges in $`H` at each endpoint, while strong
$`L^2(V)` convergence of $`u_\varepsilon` and strong $`L^2(V^*)` convergence
of $`g_\varepsilon` pass the duality integrals to the limit. This gives the
endpoint identity. Hölder makes $`r\mapsto g(r)[u(r)]` integrable, so the
squared norm is an indefinite integral of an $`L^1` function and is absolutely
continuous.
:::
