/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.EnergyUniqueness
import PDE.Hyperbolic.HigherRegularity.DivergenceForm.NonsymmetricH2
import PDE.Hyperbolic.HigherRegularity.DivergenceForm.NonsymmetricHigherOrder
import PDE.Hyperbolic.HigherRegularity.Compatibility.Conditions
import PDE.Hyperbolic.HigherRegularity.Data.Forcing
import PDE.Hyperbolic.HigherRegularity.Data.Initial
import PDE.Hyperbolic.HigherRegularity.Estimate.Nonsymmetric
import PDE.Hyperbolic.HigherRegularity.Estimate.Symmetric
import PDE.Hyperbolic.HigherRegularity.Existence.Symmetric
import PDE.Hyperbolic.HigherRegularity.Galerkin.FiniteChain
import PDE.Hyperbolic.HigherRegularity.Galerkin.Nonsymmetric
import PDE.Hyperbolic.HigherRegularity.Galerkin.PairedWeakLimit
import PDE.Hyperbolic.HigherRegularity.Spatial.DivergenceFormH2
import PDE.Hyperbolic.HigherRegularity.Estimate.GardingShift

/-!
# Higher wave regularity

Higher-order energy estimates, compatibility conditions, and elliptic lifting
for the second-order hyperbolic Dirichlet problem.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Higher Regularity and Compatibility" =>

Evans §7.2.3 proves higher regularity for the autonomous second-order
hyperbolic Dirichlet problem. We split his argument into compatibility traces,
differentiated Galerkin chains, weak-limit identification, and elliptic
lifting, which shows which initial traces and spatial estimates each
additional derivative needs.

:::group "hyperbolic.higher_regularity"
Higher wave regularity
:::

# Compatibility and Differentiated Galerkin Chains

Differentiating the wave equation in time creates a finite hierarchy of wave
problems. Compatibility conditions supply the initial data for every level,
and one common compactness extraction is needed so that adjacent weak limits
remain derivatives of each other.

:::definition "hyperbolic.regularity.data" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.SobolevTimeJet, Hyperbolic.HigherRegularity.WaveProblemData, Hyperbolic.HigherRegularity.WaveProblemData.IsCompatible")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

The data consist of a finite Sobolev time jet, initial displacement and
velocity of matching spatial orders, and the formal initial derivatives

$$`
g_0=g,\qquad g_1=h,\qquad
g_{k+2}=\partial_t^k f(0)-Bg_k.
`

Compatibility requires each $`g_k` to lie in the spatial space prescribed for
$`\partial_t^ku(0)`, to have the homogeneous Dirichlet trace when required,
and to satisfy this recurrence. Compatibility thus fixes both the regularity
budget and the boundary values of the formal derivatives.
:::

At order $`m=1`, consider $`u_{tt}-\Delta u=f` with
$`u(0)=g` and $`u_t(0)=h`. Evaluating the equation at time zero gives the
first nontrivial compatibility value

$$`u_{tt}(0)=f(0)+\Delta g.`

Higher regularity requires this expression to lie in the space prescribed for
the second time derivative and to satisfy the corresponding boundary
compatibility. The recursive formal data encode this same calculation at
every later order.

:::theorem "hyperbolic.regularity.forcing_chain" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.SobolevTimeJet.exists_dirichletLoadForcingChain") (uses := "hyperbolic.regularity.data")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

A Sobolev time jet on a nontrivial interval admits coherent dual-valued
representatives $`F_0,\ldots,F_m`, all but the last absolutely continuous, such that

$$`
\partial_tF_k=F_{k+1}\quad\text{for almost every }t,
\qquad 0\leq k<m.
`

Each representative agrees almost everywhere with the Dirichlet load of the matching jet
entry, so later Galerkin systems use one compatible chain rather than
unrelated representatives of the weak derivatives.
:::

:::proof "hyperbolic.regularity.forcing_chain"
Start with a representative of the highest weak time derivative. Descend
through the jet, choosing at each level the Sobolev representative whose weak
derivative is the representative already fixed one level above. The Sobolev
time-derivative identities hold almost everywhere, and the canonical
embeddings into the dual energy space preserve both those identities and the
prescribed Bochner integrability.
:::

The nonterminal forcing representatives have canonical initial traces
$`F_k(0)` for $`0\leq k<m`. These are the values used in the compatibility
recurrence. The highest forcing derivative needs only its Bochner
integrability.

:::theorem "hyperbolic.regularity.compatible_initial_chain" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.WaveProblemData.IsCompatible.exists_ambientInitialDataFamily") (uses := "hyperbolic.regularity.data, hyperbolic.regularity.forcing_chain")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Compatible wave data determine the initial displacement $`g_k` and velocity
$`g_{k+1}` of each differentiated problem, for $`0\leq k\leq m`. Adjacent
levels satisfy the formal acceleration relation

$$`
g_{k+2}+Bg_k=F_k(0),\qquad 0\leq k<m.
`

The equality is interpreted in the dual energy space, using the pivot
embedding for $`g_{k+2}`. It is a compatibility identity for the initial data.
:::

:::proof "hyperbolic.regularity.compatible_initial_chain"
Embed each formal compatibility value $`g_k` into the common ambient energy
space and pair adjacent values as displacement and velocity. The
compatibility recurrence
$`g_{k+2}=F_k(0)-Bg_k` rearranges to the required initial acceleration
equation. Coherence of the forcing representatives ensures that all levels
use the same time-zero data rather than independent choices.
:::

Each differentiated problem could be solved by the Galerkin method for weak
waves, but separate compactness extractions would produce limits with no
relation to one another.

:::theorem "hyperbolic.regularity.galerkin_limit_chain" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.Variational.GelfandGalerkin.exists_finiteWeakWaveChain_of_compatibleData") (uses := "hyperbolic.regularity.forcing_chain, hyperbolic.regularity.compatible_initial_chain, hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Compatible initial jets, stable dense trial spaces, Ritz orthogonality, coherent forcing,
symmetric coercivity, and uniform forcing budgets produce weak-wave limits
$`U_0,\ldots,U_m` along one common filter, with

$$`
\partial_tU_k=U_{k+1},\qquad
\partial_t^2U_k+BU_k=F_k
\quad\text{for }0\leq k<m.
`

:::

:::proof "hyperbolic.regularity.galerkin_limit_chain" (uses := "hyperbolic.weak_wave.finite_dimensional_existence, hyperbolic.weak_wave.projected_initial_data")
Finite-dimensional differentiated trajectories are built first. Uniform
energy bounds provide bounded families at every level. One common compactness
extraction passes all equations and adjacent derivative identities to the
limit, including the convergent projected initial values.
:::

Symmetry of $`B` enters the chain theorem through the Ritz property of the
projected initial data and through the energy identity behind the uniform
bounds. When $`B=A+R` has a nonsymmetric remainder, the energy bounds can
still be run on the symmetric coercive part $`A`, but Ritz orthogonality must
be imposed for the full operator.

:::theorem "hyperbolic.regularity.galerkin_limit_chain_nonsymmetric" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.Variational.GelfandGalerkin.exists_finiteWeakWaveChain_of_compatibleData_nonsymmetric") (uses := "hyperbolic.regularity.forcing_chain, hyperbolic.regularity.compatible_initial_chain, hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let the autonomous operator split as $`B=A+R`, with $`A` symmetric and
coercive and with a possibly nonsymmetric remainder satisfying

$$`
|R(v,w)|\leq L_R\|v\|_V\|Jw\|_H.
`

In addition to compatible data, stable dense trial projections, and a uniform
forcing budget, assume full-operator Ritz orthogonality:

$$`
(A+R)(q-P_kq,w)=0\qquad\text{for every }w\in S_k,
`

for each initial jet entry $`q` used in the adjacent compatibility recurrence.
Here $`P_k` is the restriction of the stable pivot projection to $`V`.
This condition is separate from stability and density, and orthogonality for
$`A` alone does not imply it. Under these hypotheses, the theorem constructs
a common finite chain of weak-wave limits for $`B`, retaining every adjacent
time-derivative identity.
:::

:::proof "hyperbolic.regularity.galerkin_limit_chain_nonsymmetric"
Full-operator Ritz orthogonality makes the projected initial jet satisfy the
differentiated finite-dimensional equations. The uniform energy bounds take
$`A` as the coercive symmetric energy form.
The mixed estimate on $`R` absorbs the remainder in that energy estimate,
at the cost of a larger exponential rate. Apply the common finite-chain compactness extraction
to all differentiated Galerkin trajectories at once; weak convergence passes
both the $`A` and $`R` terms to the limit and preserves every adjacent
time-derivative identity.
:::

# Nonsymmetric Elliptic Lifting

Time differentiation controls the temporal jet. Spatial derivatives are
recovered by reading the wave equation at almost every time as an elliptic
problem. A Gårding shift gives coercivity for lower-order nonsymmetric terms,
and the elliptic regularity theory supplies the two-spatial-derivative lift.

:::theorem "hyperbolic.regularity.nonsymmetric_garding" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.nonsymmetric_garding, Hyperbolic.HigherRegularity.shiftedNonsymmetricOperator_isCoercive, Hyperbolic.HigherRegularity.weakSolution_eq_shiftedSolve") (uses := "elliptic.lax_milgram")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

If the principal form is coercive and the lower-order remainder obeys the
mixed $`V\times H` bound, Young's inequality gives the exact Gårding loss

$$`
\frac c2\|v\|_V^2
\leq (A+R)(v,v)+\frac{L_R^2}{2c}\|Jv\|_H^2.
`

Adding this canonical pivot-mass shift makes the full, possibly
nonsymmetric operator coercive, and identifies an unshifted weak solution
with the shifted Lax–Milgram solution after correcting the load. This is an
abstract Gelfand-triple analogue of the elliptic Gårding construction.
:::

:::proof "hyperbolic.regularity.nonsymmetric_garding"
The remainder estimate and Young's inequality give
$`|R(v,v)|\leq \frac c2\|v\|_V^2+
\frac{L_R^2}{2c}\|Jv\|_H^2`. Subtract this loss from the coercive lower
bound for $`A(v,v)` to obtain the displayed Gårding inequality. Adding the
pivot-mass term therefore makes the shifted form coercive. Moving the same
mass term to the load shows that an unshifted weak solution solves the
shifted Lax–Milgram problem.
:::

The Gårding shift is abstract; its payoff comes from the concrete
divergence-form operator, for which the shifted problem is coercive and the
elliptic regularity theory applies.

:::theorem "hyperbolic.regularity.nonsymmetric_h2" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.DivergenceFormWave.exists_h2_with_norm_of_unshifted_full_weakSolution") (uses := "elliptic.divergence.garding, elliptic.divergence.shifted_exists_unique, elliptic.regularity.h2.global")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`n>0` and let the domain carry the operational `C2BoundaryAtlas`.
Assume uniformly elliptic $`W^{1,\infty}` principal coefficients with global
$`C^1` representatives and bounded first- and zeroth-order coefficients. The
Gårding-shifted homogeneous Dirichlet solver has a bounded $`L^2\to H^2`
lift. Every unshifted weak solution $`u\in H^1_0(\Omega)` with
$`f\in L^2(\Omega)` therefore has an $`H^2` representative satisfying

$$`
\|u\|_{H^2}\leq
C\bigl(\|f\|_{L^2}+|\mu|\,\|u\|_{L^2}\bigr).
`

This supplies the order-two elliptic step in Evans's wave regularity
argument, for a full operator that need not be symmetric.
:::

:::proof "hyperbolic.regularity.nonsymmetric_h2"
Rewrite the unshifted equation as the coercive shifted problem with corrected
load $`f+\mu u`. Lax–Milgram uniqueness identifies the given weak solution
with the shifted solver. Apply the global divergence-form $`H^2` regularity
operator to that load and use its norm bound; the triangle inequality yields
the displayed dependence on $`\|f\|_{L^2}` and $`|\mu|\|u\|_{L^2}`.
:::

Two derivatives at a time is the natural step of elliptic regularity, and
iterating it requires the same shifted solver to map $`H^k` loads to
$`H^{k+2}` solutions for every $`k`. The load at level $`k` is $`f+\mu u` with
$`u` already controlled in $`H^k`, which is why the estimate takes the form of
a two-step recurrence.

:::theorem "hyperbolic.regularity.nonsymmetric_higher" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.DivergenceFormWave.exists_higher_with_norm_of_unshifted_full_weakSolution, Hyperbolic.DivergenceFormWave.fullGarding_hasHigherSolutionLift, Hyperbolic.DivergenceFormWave.fullGardingHigherSolveCLM, Hyperbolic.DivergenceFormWave.fullGardingHigherSolveCLM_base, Hyperbolic.DivergenceFormWave.fullGardingHigherSolveCLM_norm_le") (uses := "hyperbolic.regularity.nonsymmetric_h2, elliptic.regularity.full_operator_bootstrap")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Retain the domain, uniform ellipticity, and homogeneous Dirichlet
hypotheses of the {bpref "hyperbolic.regularity.nonsymmetric_h2"}[order-two lift].
At order $`k`, assume principal coefficients in $`W^{k+1,\infty}` with
global $`C^{k+1}` representatives, lower-order coefficients in
$`W^{k,\infty}`, and an operational boundary atlas whose charts are
$`C^{k+2}` and whose inverse charts are $`C^{k+1}`. The shifted solver is
then bounded from $`H^k` to $`H^{k+2}`. An unshifted weak solution with an
already identified $`H^k` representative receives an $`H^{k+2}` lift, with
a bound in terms of the $`H^k` forcing and solution norms.
:::

:::proof "hyperbolic.regularity.nonsymmetric_higher"
As in the order-two case, shift the equation and correct the load by the
pivot-mass term. The arbitrary-order elliptic bootstrap maps an $`H^k` load
to an $`H^{k+2}` solution under the coefficient and boundary hypotheses.
Uniqueness identifies this lift with the original weak solution, and
boundedness of the solver gives the two-step norm estimate.
:::

# Identifying the Regular Wave

The differentiated weak limits are derivatives of one solution, and elliptic
lifting applies to its spatial slices. Here the time-regularity and
spatial-regularity arguments meet.

:::theorem "hyperbolic.regularity.paired_weak_limits" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.Variational.IsGelfandWeakWaveSolution.higherRegularity_of_paired_weak_limits") (uses := "hyperbolic.weak_wave.solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

For an autonomous operator, suppose the original limit is a weak wave, the
forcing has a weak time derivative, and the original and differentiated
Galerkin families have common weak limits with their exact derivative links.
The theorem identifies $`u_t`, $`u_{tt}`, and a third weak time derivative.
Uniform essential bounds on the differentiated families pass to the limit.
:::

:::proof "hyperbolic.regularity.paired_weak_limits"
Test the Galerkin identity relating each trajectory to its time derivative
against smooth compactly supported time functions. Weak convergence passes
that distributional identity to the paired limits, identifying the latter as
successive weak derivatives of one function. Then differentiate
$`u_{tt}=\ell-Bu`: autonomy gives
$`u_{ttt}=\partial_t\ell-Bu_t` in $`L^2(V^*)`. The almost-everywhere norm-bound
sets are closed and convex in $`L^2`, so their weak closedness preserves the
uniform essential bounds.
:::

For the pivot space $`H=L^2(\Omega)`, the paired-limit theorem identifies
the dual-valued acceleration with the pivot image of an $`L^2(\Omega)`-valued
class and preserves its essential spatial $`L^2` bound. That is the input the
elliptic lift needs at almost every time.

:::theorem "hyperbolic.regularity.spatial_h2" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.Variational.DivergenceFormWave.exists_spatialH2Top_of_ae_weak_wave") (uses := "hyperbolic.weak_wave.solution, elliptic.regularity.h2.principal")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`n>0` and let the domain carry the operational `C2BoundaryAtlas`.
Assume uniformly elliptic $`W^{1,\infty}` principal coefficients with global
$`C^1` representatives. For a time-$`L^2` trajectory in $`H^1_0(\Omega)`
satisfying the weak wave equation with spatial $`L^2` forcing and
acceleration, essential bounds on those two spatial norms give an essentially
bounded $`H^2` lift. The elliptic solver's operator norm gives the quantitative
estimate.
:::

:::proof "hyperbolic.regularity.spatial_h2"
For almost every time, rewrite the wave equation as the elliptic problem
$`Bu(t)=f(t)-u_{tt}(t)`. The global elliptic regularity solver supplies an
$`H^2` representative of that spatial slice, and uniqueness identifies it
with $`u(t)`. Measurability of the bounded solver assembles these slices into
a Bochner representative, while the operator norm and the two essential
$`L^2` bounds give the essential-supremum estimate.
:::

Assembling the pieces gives the existence theorem. Symmetry of the spatial
operator is assumed because the chain theorem invoked is the symmetric one.

:::theorem "hyperbolic.regularity.regular_weak_wave" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.WaveProblemData.IsCompatible.exists_regularWeakWave_of_stableGalerkinScheme") (uses := "hyperbolic.regularity.data, hyperbolic.regularity.forcing_chain, hyperbolic.regularity.compatible_initial_chain, hyperbolic.regularity.galerkin_limit_chain, hyperbolic.regularity.spatial_h2")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Under the explicit compatibility, stable-density, coercivity, Ritz, and
elliptic-lifting hypotheses, and assuming the spatial operator is symmetric,
there exists a weak wave with the prescribed initial data and an essentially
bounded Sobolev time jet of order $`m+1` whose head agrees almost everywhere with
the displacement and whose first time derivative is the velocity. For a nonsymmetric operator,
the corresponding steps are the
{bpref "hyperbolic.regularity.galerkin_limit_chain_nonsymmetric"}[nonsymmetric Galerkin chain]
and the {bpref "hyperbolic.regularity.nonsymmetric_higher"}[higher-order lift].
:::

:::proof "hyperbolic.regularity.regular_weak_wave" (uses := "hyperbolic.regularity.forcing_chain, hyperbolic.regularity.compatible_initial_chain, hyperbolic.regularity.galerkin_limit_chain, hyperbolic.regularity.spatial_h2")
The compatibility data initialize all differentiated Galerkin systems. The
finite common weak-wave chain supplies the time derivatives, and the assumed
elliptic lift raises spatial order two derivatives at a time. Induction
assembles the resulting representatives into one essentially bounded
Sobolev time jet.
:::

# The Higher-Regularity Norm Budget

The higher-regularity bound combines all differentiated energy levels into
one decreasing Sobolev norm sum.

:::theorem "hyperbolic.regularity.estimate64_assembly" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.eLpNormEssSup_solutionSobolevNormSum_le_of_levelBounds") (uses := "hyperbolic.regularity.data")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Consider the decreasing Sobolev norm sum and the forcing and initial-data
budget. If each differentiated level has an almost-everywhere quantitative
energy or elliptic bound and the level constants sum to at most $`C`, then

$$`
\operatorname*{ess\,sup}_{t\in(t_0,t_1)}
\sum_{k=0}^{m+1}\|\partial_t^k u(t)\|_{H^{m+1-k}}
\leq C\left(
\sum_{k=0}^{m}\|\partial_t^k f\|_{L^2_tH^{m-k}_x}
+\|g\|_{H^{m+1}}+\|h\|_{H^m}\right).
`
:::

:::proof "hyperbolic.regularity.estimate64_assembly"
Each assumed level estimate bounds one nonnegative summand almost everywhere.
Intersect the finitely many full-measure sets so that all bounds hold
simultaneously, then sum them pointwise. Monotonicity of the essential
supremum transfers this finite pointwise sum to the left-hand side, and the
assumed upper bound for the sum of level constants produces the single factor
$`C` multiplying the data budget.
:::

:::theorem "hyperbolic.regularity.estimate64_nonsymmetric_recurrence" (parent := "hyperbolic.higher_regularity") (lean := "Hyperbolic.HigherRegularity.eLpNormEssSup_solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence") (uses := "hyperbolic.regularity.estimate64_assembly")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.2.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%

Let $`M_k` be the recursively defined majorant obtained from the two top
differentiated energy bounds and an assumed two-step spatial recurrence,
after factoring out the data budget $`B`. The recurrence bounds the
$`H^{k+2}` entry $`\partial_t^{m-1-k}u(t)` of the norm sum by the forcing, the
$`H^k` entry $`\partial_t^{m+1-k}u(t)`, and a shift term in the $`H^{k+1}`
entry $`\partial_t^{m-k}u(t)`. The resulting bound is

$$`
\operatorname*{ess\,sup}_{t\in(t_0,t_1)}
\sum_{k=0}^{m+1}\|\partial_t^ku(t)\|_{H^{m+1-k}}
\leq \left(\sum_{k=0}^{m+1}M_k\right)B.
`

Here $`B` is the forcing and initial-data budget in the preceding estimate.
Both starting bounds and the recurrence are hypotheses, and the proof
propagates them through the finite derivative hierarchy. The recurrence has a
different shape from the
{bpref "hyperbolic.regularity.nonsymmetric_higher"}[higher-order lift], whose
shift term falls on the level being solved for rather than on the neighbouring
one.
:::

:::proof "hyperbolic.regularity.estimate64_nonsymmetric_recurrence"
Begin with the two highest time-derivative bounds. Strong induction descends
through the Sobolev levels: at each step, the assumed recurrence controls
the next spatial norm from the forcing at that level and the two already
controlled higher time derivatives. This proves the recursive
majorant $`M_k` for every level. The finite assembly theorem then sums these
almost-everywhere estimates into the stated essential-supremum bound.
:::
