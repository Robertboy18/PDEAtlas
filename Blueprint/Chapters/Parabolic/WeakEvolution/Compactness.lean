/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.WeakEvolution.TimeSobolev
import PDE.Analysis.Operator.ClosedRangeFactorization
import PDE.Analysis.TrilinearForm
import PDE.Analysis.WeakCompactness
import PDE.Analysis.Evolution.Bochner.Constraints
import PDE.Analysis.Evolution.Compactness.AubinLions.Compactness
import PDE.Analysis.Evolution.Compactness.AubinLions.TemporalCompactness
import PDE.Analysis.Evolution.Compactness.Lp.Nonlinear

/-!
# Aubin–Lions compactness

The abstract Hilbert-space Aubin–Lions theorem, built from compact spatial
Galerkin approximation and Lions–Magenes time regularity, and the weak-limit
passages used with it.
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
#doc (Manual) "Aubin–Lions Compactness" =>

# Compactness from space and time regularity

Spatial compactness alone leaves an obvious escape route: oscillation in
time. Fix $`0\ne v\in H^1_0(\Omega)` and put
$`u_j(t)=\sin(jt)v` on $`(0,2\pi)` for positive integers $`j`. These
trajectories are uniformly bounded in $`L^2_tH^1_0`, yet for $`j\ne k`,

$$`
\|u_j-u_k\|_{L^2_tL^2_x}^2=2\pi\|v\|_{L^2_x}^2.
`

They have no strongly convergent subsequence in that space. Their time
derivatives grow like $`j` in $`L^2_tH^{-1}_x`, which is exactly the
behavior the second Aubin–Lions bound excludes.

The Aubin–Lions argument has a spatial half and a temporal half. In the
temporal half, Lions–Magenes regularity of the time derivative gives
every finite-dimensional observable of a bounded family a common Hölder
modulus of order one half, and Arzelà–Ascoli then makes those observables
precompact.

:::theorem "parabolic.aubin_lions_temporal" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.isCompact_closure_range_pairingBoundedContinuousFunction, PDE.Analysis.Evolution.isCompact_closure_range_projectionBoundedContinuousFunction, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.abs_pairing_sub_le_sqrt_mul, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.norm_projection_sub_le_sqrt_mul, PDE.Analysis.Evolution.isCompact_closure_boundedContinuousFunction_of_sqrt_modulus, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.pairingBoundedContinuousFunction, PDE.Analysis.Evolution.ContinuousPivotEvolutionOn.projectionBoundedContinuousFunction") (uses := "parabolic.lions_magenes_finite_interval, parabolic.galerkin.stable_trial_system, parabolic.galerkin.pivot_mass_system")
Let $`V\hookrightarrow H` be a Gelfand triple with inclusion $`J`, let
$`a\le b`, and let $`(u_j,g_j)` be a family with $`u_j\in L^2(a,b;V)` and
$`g_j\in L^2(a,b;V^*)`, each equipped with a Lions–Magenes continuous pivot
representative $`\tilde u_j:[a,b]\to H` whose integrated dual derivative is
$`g_j`. For a fixed test vector $`v\in V` and all $`s,t\in[a,b]`,

$$`
\bigl|(\tilde u_j(t),Jv)_H-(\tilde u_j(s),Jv)_H\bigr|
\le|t-s|^{1/2}\,\bigl\lVert\langle g_j(\cdot),v\rangle\bigr\rVert_{L^2(a,b)}.
`

If $`\lVert\tilde u_j(t)\rVert_H\le U` for all $`j` and $`t\in[a,b]`, and
$`\lVert\langle g_j(\cdot),v\rangle\rVert_{L^2(a,b)}\le D` for all $`j`,
then the scalar coefficient curves $`t\mapsto(\tilde u_j(t),Jv)_H`, regarded
as bounded continuous functions on $`[a,b]`, have compact closure in the
uniform norm.

For a finite-dimensional trial space $`S\subseteq V` with a stable trial
projection $`P`, the projected curves satisfy the analogous modulus

$$`
\lVert P\tilde u_j(t)-P\tilde u_j(s)\rVert
\le|t-s|^{1/2}\,\lVert M_S^{-1}g_j|_S\rVert_{L^2(a,b;S)},
`

where $`M_S^{-1}g|_S` is the pivot-mass-inverted restriction of the dual
derivative to $`S`, and under uniform bounds $`U` and $`D` on the two
quantities the family $`t\mapsto P\tilde u_j(t)` has compact closure in
$`C([a,b];S)`. The underlying abstract step is that a uniformly bounded family
of continuous curves into a proper normed space with a common modulus
$`\lVert f(t)-f(s)\rVert\le C|t-s|^{1/2}` is relatively compact in the
uniform norm.
:::

:::proof "parabolic.aubin_lions_temporal" (uses := "parabolic.integrated_dual_fundamental_theorem")
The integrated dual derivative gives the pairing identity
$`(\tilde u(t)-\tilde u(s),Jv)_H=\int_s^t\langle g(r),v\rangle\,dr`, and
Cauchy–Schwarz in time bounds the interval integral of an $`L^2` function
by $`|t-s|^{1/2}` times its $`L^2` norm. For the projection, the increment
$`P\tilde u(t)-P\tilde u(s)` is the Bochner integral of the mass-inverted
restricted dual derivative, and the same estimate applies. The pivot bound
and Cauchy–Schwarz bound the curves uniformly, so they take values in a
compact ball of the finite-dimensional target; the common modulus gives
equicontinuity, and Arzelà–Ascoli yields compact closure.
:::

Now combine the two halves. Compactness of $`J:V\to H` supplies
finite-dimensional projections $`P_N` with

$$`
\|(I-P_N)Jv\|_H\le\varepsilon_N\|v\|_V,
\qquad \varepsilon_N\longrightarrow0.
`

After integrating in time, the discarded spatial tail is uniformly small
for the whole bounded family. Fix $`N` first: the time-derivative bound
controls the finitely many retained coefficient curves, so temporal
compactness makes those curves precompact. Choose a finite approximation for
them and then add back the small tail. This order matters: the temporal
constants may depend on $`N`, while the final conclusion is strong
compactness in $`L^2_tH`; strong compactness in $`L^2_tV` does not follow.

:::theorem "parabolic.aubin_lions_hilbert" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.isCompact_closure_range_inclusionLp") (uses := "parabolic.galerkin.stable_trial_system, parabolic.lions_magenes_finite_interval, parabolic.time_sobolev.gelfand_representative_bound")
%%%
source := {
  document := "simon-compactness"
  spans := #[{
    page := "65-96"
    text := some { path := "Blueprint/Sources/SimonCompactness.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`V,H` be real Hilbert spaces with a Gelfand triple
$`V\hookrightarrow H\hookrightarrow V^*` whose inclusion $`J:V\to H` is compact.
Equip each trajectory $`u_j` and its dual time derivative $`\partial_tu_j`
with a Lions–Magenes continuous pivot evolution.
Suppose

$$`
\sup_j\|u_j\|_{L^2(a,b;V)}<\infty,
\qquad
\sup_j\|\partial_tu_j\|_{L^2(a,b;V^*)}<\infty
`

on a finite interval $`(a,b)` with $`a<b`. Then the family $`Ju_j` has compact
closure in $`L^2(a,b;H)`.
:::

:::proof "parabolic.aubin_lions_hilbert" (uses := "parabolic.aubin_lions_temporal, parabolic.galerkin.stable_trial_system, parabolic.time_sobolev.gelfand_representative_bound")
The compact inclusion produces canonical finite-dimensional spectral trial
spaces. Their pivot projections converge uniformly on the compact image of
the energy unit ball, hence their Bochner lifts make the spatial tails
uniformly small on every $`L^2(a,b;V)`-bounded family.

At one fixed trial dimension, the Lions–Magenes pairing identity expresses
the projected trajectory increment as the interval integral of the
mass-inverted restricted dual derivative. The derivative bound gives a
common one-half Hölder modulus, while the quantitative time-Sobolev estimate
gives a common pivot bound. Finite-dimensional Arzelà–Ascoli therefore makes
the projected family precompact. A finite-net argument combines that compact
projected family with the uniform spatial tail and yields compact closure in
$`L^2(a,b;H)`.
:::

# Linear constraints along trajectories

:::theorem "parabolic.bochner_linear_constraints" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.compLpL_eq_zero_iff_ae, PDE.Analysis.Evolution.isClosed_bochnerWeakConstraintSet, PDE.Analysis.Evolution.satisfiesBochnerConstraints_of_tendsto_weak, PDE.Analysis.Evolution.WeakCompactness.isCompact_inter_bochnerWeakConstraintSet") (uses := "parabolic.galerkin.weak_compactness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "726"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 30, endLine := 33 }
  }]
}
%%%
Let $`A_j:E\to F` be any family of continuous linear spatial constraints.
For a Bochner trajectory $`u\in L^2(\mu;E)`, the conditions

$$`
A_j(u(t))=0\quad\text{for each }j,\text{ almost everywhere in }t
`

are exactly the kernel conditions

$$`
(A_j)_{L^2}u=0
`

for the continuously lifted maps $`(A_j)_{L^2}:L^2(\mu;E)\to L^2(\mu;F)`.
Consequently, constrained trajectories form a weakly closed subset of
$`L^2(\mu;E)`, the constraints survive weak $`L^2` limits, and imposing them
on any weakly compact bounded family preserves weak compactness.

This single result covers every side condition represented by continuous
linear maps, including divergence-free, zero-mean, trace, and conservation
constraints once the corresponding spatial operator has been constructed.
:::

:::proof "parabolic.bochner_linear_constraints" (uses := "parabolic.galerkin.weak_compactness")
Mathlib's lifted map agrees almost everywhere with pointwise composition.
Extensionality of Bochner classes therefore identifies its kernel with
pointwise almost-everywhere vanishing. Each lifted kernel is weakly closed,
arbitrary intersections of those kernels remain weakly closed, and closed
sets contain the weak limits of eventually constrained nets. Intersecting
with an already weakly compact bounded set then preserves compactness.
:::

# Recovering multipliers from constrained tests

:::theorem "parabolic.closed_range_multiplier" (parent := "parabolic.variational") (lean := "ContinuousLinearMap.ClosedRange.factorThroughRange_apply, ContinuousLinearMap.ClosedRange.existsUnique_multiplier_mem_range, ContinuousLinearMap.ClosedRange.adjoint_multiplier_eq") (uses := "parabolic.bochner_linear_constraints, parabolic.hilbert_riesz_ode") (tags := "provenance:leanpde")
Let $`E,F` be real Hilbert spaces and let $`T:E\to F` be continuous linear
with closed range. If $`\ell\in E^*` vanishes on $`\ker T`, then $`\ell`
factors continuously through $`\operatorname{range}T`. Moreover, there is a
unique $`p\in\operatorname{range}T` such that

$$`
\ell(x)=\langle p,Tx\rangle_F\qquad(x\in E).
`

Equivalently, $`p` solves the adjoint equation

$$`
T^*p=R_E^{-1}\ell,
`

where $`R_E:E\to E^*` is the Fréchet–Riesz equivalence.

This is the equation-independent Lagrange-multiplier step behind weak
pressure recovery. When $`T` is a divergence operator with closed range,
$`\ker T` is the divergence-free test space and $`p` is the pressure.
:::

:::proof "parabolic.closed_range_multiplier" (uses := "parabolic.hilbert_riesz_ode")
First descend $`\ell` to the Hilbert quotient $`E/\ker T`. Closedness of the
range identifies this quotient continuously and linearly with
$`\operatorname{range}T`. Fréchet–Riesz representation on that closed
subspace produces $`p`. Testing against every $`Tx` gives the representation
formula. If two range-valued multipliers represent $`\ell`, their difference
is both in the range and orthogonal to the range, hence is zero. The adjoint
identity is the same representation formula rewritten using the defining
property of $`T^*`.
:::

# Quadratic energy bounds in weak limits

:::theorem "parabolic.weak_quadratic_energy_limit" (parent := "parabolic.variational") (lean := "PDE.Analysis.WeakCompactness.weighted_norm_sq_add_le_of_tendsto_weak, PDE.Analysis.WeakCompactness.norm_sq_add_norm_sq_le_of_tendsto_weak") (uses := "parabolic.galerkin.weak_compactness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "726"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 30, endLine := 33 }
  }]
}
%%%
Let $`u_j\rightharpoonup u` in a real Hilbert space $`H` and
$`v_j\rightharpoonup v` in a real Hilbert space $`V`. For nonnegative
weights $`a,b`, if

$$`
a\|u_j\|_H^2+b\|v_j\|_V^2\leq C
`

eventually, then

$$`
a\|u\|_H^2+b\|v\|_V^2\leq C.
`

Thus a Galerkin bound coupling a kinetic component with a dissipation
component passes intact to simultaneous weak limits. Either component may
instead represent any Hilbert-valued state,
derivative, gradient, flux, or auxiliary variable.
:::

:::proof "parabolic.weak_quadratic_energy_limit" (uses := "parabolic.galerkin.weak_compactness")
Test the two weak convergences against $`u` and $`v`. Cauchy–Schwarz and
Young's inequality give

$$`
2\bigl(a\langle u,u_j\rangle+b\langle v,v_j\rangle\bigr)
\leq
a\|u\|^2+b\|v\|^2+a\|u_j\|^2+b\|v_j\|^2.
`

The assumed bound controls the last two terms. Passing to the scalar limit
and subtracting one copy of the limiting energy proves the claim. Zero
weights are allowed, so the statement also contains the usual one-component
weak lower-semicontinuity bound.
:::

# Passing nonlinear terms to the limit

Compactness becomes useful for a nonlinear PDE only after one can identify
the limit of its nonlinear terms. The basic limit passages that follow an
Aubin–Lions argument concern bilinear products, trilinear forms, and duality
pairings.

For scalar functions, the issue is already visible in squaring. The sequence
$`\sin(jt)`, indexed by positive integers, converges weakly to zero in
$`L^2(0,2\pi)`, but its square has integral $`\pi` for every $`j`. A weak
limit therefore cannot simply be substituted into a nonlinear term.
Strong $`L^2` convergence repairs this:

$$`
\|u_j^2-u^2\|_{L^1}
\le\|u_j-u\|_{L^2}\bigl(\|u_j\|_{L^2}+\|u\|_{L^2}\bigr)
\longrightarrow0.
`

Here we used $`u_j^2-u^2=(u_j-u)(u_j+u)` and Cauchy–Schwarz. The same
splitting works for any continuous bilinear map. For a PDE application, the
compactness must occur in the norms needed by its particular nonlinearity.

:::theorem "parabolic.bilinear_l2_l1_limit" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.tendsto_bilinear_product_Lr_of_tendsto_Lp_Lq, PDE.Analysis.Evolution.tendsto_bilinear_product_L1_of_tendsto_L2, PDE.Analysis.Evolution.tendsto_quadratic_product_L1_of_tendsto_L2") (uses := "parabolic.aubin_lions_hilbert")
%%%
source := {
  document := "simon-compactness"
  spans := #[{
    page := "65-96"
    text := some { path := "Blueprint/Sources/SimonCompactness.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`B:E\times F\to G` be a continuous bilinear map, and suppose
$`p,q,r\geq1` satisfy

$$`\frac1p+\frac1q=\frac1r.`

If $`u_j\to u` in $`L^p(\mu;E)` and
$`v_j\to v` in $`L^q(\mu;F)`, then

$$`
B(u_j,v_j)\longrightarrow B(u,v)
\qquad\text{strongly in }L^r(\mu;G).
`

In particular, taking $`p=q=2` and $`r=1`, strong $`L^2` convergence implies
$`B(u_j,u_j)\to B(u,u)` strongly in $`L^1`. This passes quadratic terms to the limit once compactness gives strong
$`L^2` convergence.
:::

:::proof "parabolic.bilinear_l2_l1_limit" (uses := "parabolic.aubin_lions_hilbert")
Split the difference as

$$`
B(u_j,v_j)-B(u,v)
=B(u_j-u,v_j)+B(u,v_j-v).
`

The Bochner Hölder estimate bounds its $`L^r` norm by

$$`
\|B\|\,\|u_j-u\|_{L^p}\|v_j\|_{L^q}
+\|B\|\,\|u\|_{L^p}\|v_j-v\|_{L^q}.
`

Both terms tend to zero. Formally, the Hölder operation is itself a
continuous bilinear map between the three Bochner spaces, so the result is
also an immediate continuity argument. The quadratic $`L^2` statement is the
specialization $`p=q=2`, $`r=1`, and $`v_j=u_j`.
:::

Product limits identify quadratic terms once strong convergence is known.
The convective terms of fluid equations are trilinear, and their first
property is algebraic rather than topological: skew-symmetry in the last two
arguments makes the nonlinearity invisible to the energy identity and yields
a usable difference formula for two states.

:::theorem "parabolic.trilinear_energy_cancellation" (parent := "parabolic.variational") (lean := "PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy.norm_quadratic_dual_sub_le, PDE.Analysis.ContinuousTrilinearForm.IsSkewInLastTwo.diagonal_eq_zero, PDE.Analysis.ContinuousTrilinearForm.IsSkewInLastTwo.energy_eq_zero, PDE.Analysis.ContinuousTrilinearForm.IsSkewInLastTwo.reduce_energy_equation, PDE.Analysis.ContinuousTrilinearForm.IsSkewInLastTwo.quadratic_difference, PDE.Analysis.ContinuousTrilinearForm.IsSkewInLastTwo.norm_quadratic_difference_le") (uses := "parabolic.bilinear_l2_l1_limit")
%%%
source := {
  document := "leray-1934"
  spans := #[{
    page := "193-248"
    text := some { path := "Blueprint/Sources/Leray1934.md", startLine := 1, endLine := 10 }
  }]
}
%%%
Let $`b:V\times V\times V\to\mathbb R` be a continuous trilinear form that
is skew in its last two arguments:

$$`
b(u,v,w)=-b(u,w,v).
`

Then $`b(u,v,v)=0`, and in particular $`b(u,u,u)=0`. Thus a nonlinear
evolution equation tested against its state has the same energy balance as
its linear coercive part. The same cancellation gives the difference
identity

$$`
b(u,u,u-v)-b(v,v,u-v)=b(u-v,v,u-v).
`

If $`|b(x,y,z)|\leq C\|x\|\|y\|\|z\|`, the right-hand side is bounded by
$`C\|u-v\|^2\|v\|`. This is the abstract algebra behind convective energy
cancellation and many weak-uniqueness estimates. The same product bound shows
that the dual-valued quadratic map $`u\mapsto b(u,u,\cdot)` is Lipschitz on
bounded subsets of $`V`.
:::

:::proof "parabolic.trilinear_energy_cancellation" (uses := "parabolic.bilinear_l2_l1_limit")
Skew-symmetry with $`w=v` gives $`b(u,v,v)=-b(u,v,v)`, hence the value is
zero over $`\mathbb R`. Substituting this identity removes the cubic term
from the tested evolution equation. For the difference formula, write
$`u=v+d` with $`d=u-v`, expand by trilinearity, and cancel the terms
$`b(v,d,d)` and $`b(d,d,d)`. The product bound applied to
$`b(d,v,d)` gives the quantitative estimate.
:::

Cancellation controls the energy of the approximations; passing the
trilinear term itself to the limit is a separate question. Aubin–Lions gives
compactness in $`L^2(a,b;H)`, and the limit passage needs strong convergence
of two factors in norms in which the trilinear form is continuous.

:::theorem "parabolic.trilinear_strong_strong_weak_limit" (parent := "parabolic.variational") (lean := "PDE.Analysis.WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak, PDE.Analysis.tendsto_trilinear_apply_of_tendsto_strong_strong_weak, PDE.Analysis.tendsto_quadratic_apply_of_tendsto_strong_weak") (uses := "parabolic.trilinear_energy_cancellation, parabolic.aubin_lions_hilbert")
%%%
source := {
  document := "simon-compactness"
  spans := #[{
    page := "65-96"
    text := some { path := "Blueprint/Sources/SimonCompactness.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`b:E\times F\times G\to\mathbb R` be a continuous trilinear form.
Suppose

$$`
u_j\to u,\qquad v_j\to v,\qquad w_j\rightharpoonup w,
`

with the first two convergences strong and the weakly convergent family
$`w_j` uniformly bounded. Then

$$`
b(u_j,v_j,w_j)\longrightarrow b(u,v,w).
`

In particular, strong convergence of $`u_j` and bounded weak convergence of
$`w_j` identify the quadratic expression $`b(u_j,u_j,w_j)`. This is the
abstract strong–strong–weak passage used after compactness has supplied the
strong factors.
:::

:::proof "parabolic.trilinear_strong_strong_weak_limit" (uses := "parabolic.trilinear_energy_cancellation, parabolic.aubin_lions_hilbert")
The functionals $`b(u_j,v_j,\cdot)` converge strongly in $`G^*` by continuity
of the first two slots. Split

$$`
b(u_j,v_j,w_j)-b(u,v,w)
=\bigl(b(u_j,v_j,\cdot)-b(u,v,\cdot)\bigr)(w_j)
+b(u,v,w_j-w).
`

Uniform boundedness of $`w_j` sends the first term to zero, while weak
convergence tested against the fixed functional $`b(u,v,\cdot)` sends the
second term to zero.
:::

The same weak–strong principle is needed in Bochner form for the duality
pairing between weakly convergent dual derivatives $`g_j` and strongly
convergent states, the pairing that appears when an energy identity is
passed to the limit. The pointwise Riesz map reduces it to a Hilbert-space
inner product of a weakly convergent factor with a strongly convergent one.

:::theorem "parabolic.weak_strong_duality_limit" (parent := "parabolic.variational") (lean := "PDE.Analysis.Evolution.tendsto_integral_dual_pairing_of_tendsto_weak_strong") (uses := "parabolic.galerkin.weak_compactness")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "726"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 30, endLine := 33 }
  }]
}
%%%
Let $`W` be a real Hilbert space. Suppose $`g_j\rightharpoonup g` weakly in
$`L^2(\mu;W^*)`, the Riesz representatives of $`g_j` are uniformly bounded,
and $`u_j\to u` strongly in $`L^2(\mu;W)`. Then

$$`
\int \langle g_j(t),u_j(t)\rangle\,d\mu(t)
\longrightarrow
\int \langle g(t),u(t)\rangle\,d\mu(t).
`

The explicit bound is retained in the formal statement because it is valid
for arbitrary filters; ordinary weakly convergent sequences supply that bound
automatically.
:::

:::proof "parabolic.weak_strong_duality_limit" (uses := "parabolic.galerkin.weak_compactness")
Use the pointwise Riesz map to rewrite each integral as the real
$`L^2` inner product of the Riesz representative of $`g_j` with $`u_j`.
The generic weak–strong inner-product theorem then passes to the limit:
the fixed-test term follows from weak convergence, and the varying-test error
is controlled by the uniform norm bound times $`\|u_j-u\|_{L^2}`.
:::
