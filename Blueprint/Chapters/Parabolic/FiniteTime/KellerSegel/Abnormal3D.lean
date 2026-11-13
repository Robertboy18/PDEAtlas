/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.FiniteTime.KellerSegel.Virial
import PDE.Solution.Singularity.FiniteTime.KellerSegel.Similarity.Abnormal3D

/-!
# Abnormal three-dimensional Keller–Segel scaling

The abnormal similarity exponents, the residual diffusion error, and the
exact obstruction to the leading profile being a full solution.
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
#doc (Manual) "Abnormal Three-Dimensional Keller–Segel Scaling" =>

An abnormal similarity scale is useful only if one distinguishes an
asymptotic profile equation from the exact physical PDE. In the
three-dimensional construction studied here, diffusion carries a coefficient
that vanishes in rescaled variables. The leading aggregation profile can
therefore describe the asymptotic balance without itself being an exact
solution, and the analytic construction adds perturbative correction terms.

:::definition "parabolic.keller_segel_abnormal_scaling" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.abnormalBeta3D, PDE.Solution.Singularity.FiniteTime.KellerSegel.abnormalDiffusionExponent3D")

For modes $`j\ge4`, the Liu–Wang–Zhou abnormal scaling uses

$$`
\beta_j=\frac13+\frac{1}{2j},
\qquad
\delta_j=1-2\beta_j=\frac13-\frac1j>0.
`

The exponent lies strictly between $`1/3` and the parabolic value $`1/2`.
Consequently diffusion enters the rescaled density equation with the
lower-order coefficient $`(T-t)^{\delta_j}`.

The scaling follows {Informal.citet "liu-wang-zhou-2025"}[], Theorem 1.1 and
equations (1.8), (1.12), and (1.13), with $`\mu=0`. The Lean development
treats the leading ansatz, the exponent arithmetic, and the residual
identities.
:::

Positivity of $`\delta_j` is exactly the statement that the abnormal
exponent lies below the parabolic one, and its first consequence is a limit:
the rescaled diffusion coefficient tends to zero at the singular time.

:::theorem "parabolic.keller_segel_abnormal_diffusion_vanishes" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.tendsto_abnormal_diffusion_coefficient_3d") (uses := "parabolic.keller_segel_abnormal_scaling")

For every $`j\ge4`,

$$`(T-t)^{\delta_j}\longrightarrow0\qquad\text{as }t\uparrow T.`

So diffusion is asymptotically lower order in similarity variables; at each
pre-singular time the coefficient is positive.
:::

:::proof "parabolic.keller_segel_abnormal_diffusion_vanishes"
The mode assumption gives
$`\delta_j=\frac13-\frac1j>0`. The base $`T-t` tends to zero as
$`t\uparrow T`, and continuity of $`r\mapsto r^{\delta_j}` at zero for a
positive exponent sends this limit to zero.
:::

The density amplitude is $`(T-t)^{-1}`, the same as in the parabolic
scaling, so the abnormal density ansatz diverges for the same reason. The
mode restriction plays no role here; it matters only for the exponent
estimates.

:::theorem "parabolic.keller_segel_abnormal_ansatz_diverges" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.abnormal_density_ansatz_3d_blows_up_at") (uses := "parabolic.keller_segel_abnormal_scaling")

A bounded density profile that is nonzero at one point makes the abnormal
density ansatz blow up in spatial supremum norm at $`T`: its slices are
finite and their supremum diverges because the amplitude is $`(T-t)^{-1}`.
Without boundedness, the extended supremum still diverges.
:::

:::proof "parabolic.keller_segel_abnormal_ansatz_diverges"
Apply the general backward self-similar blow-up theorem with amplitude
exponent $`1` and spatial exponent $`\beta_j`. A moving spatial sample keeps
the similarity coordinate at a point where $`Q` is nonzero, so its norm is a
fixed positive constant times $`(T-t)^{-1}`. The global profile bound also
bounds each spatial slice by a finite multiple of this amplitude for $`t<T`.
:::

Divergence of the formula says nothing about whether it solves Keller–Segel,
and in general it does not. The residual identity makes this quantitative:
under the diffusion-free aggregation equation, the density residual is the
diffusion term that equation omits.

:::theorem "parabolic.keller_segel_abnormal_diffusion_error" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.density_residual_abnormal_ansatz_3d_eq_diffusion_error") (uses := "parabolic.keller_segel_abnormal_scaling")

Suppose $`Q,\Phi\in C^2`, $`t<T`, and the pair satisfies the diffusion-free
aggregation profile equation at the displayed similarity coordinate. Exact
substitution into the density equation leaves

$$`
\mathcal R_u(x,t)
=(T-t)^{-2}(T-t)^{\delta_j}
\Delta Q\!\left((T-t)^{-\beta_j}(x-x_0)\right).
`

The identity separates the singular physical prefactor from the lower-order
profile error.
:::

:::proof "parabolic.keller_segel_abnormal_diffusion_error"
The exact substitution theorem factors the physical residual as
$`-(T-t)^{-2}` times the abnormal profile residual. Under the diffusion-free
aggregation equation, every term in that profile residual cancels except
$`-(T-t)^{\delta_j}\Delta Q`. Multiplying the two negative factors gives the
displayed diffusion error.
:::

The two factors of the diffusion error pull in opposite directions, and the
exponent arithmetic decides which wins: $`-2+\delta_j=-(1+2\beta_j)<0`.

:::theorem "parabolic.keller_segel_abnormal_physical_residual_diverges" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.tendsto_norm_density_residual_abnormal_ansatz_3d_at_center") (uses := "parabolic.keller_segel_abnormal_diffusion_error")

Assume $`j\ge4`, the profiles are $`C^2`, the diffusion-free aggregation
profile equation holds everywhere, and $`\Delta Q(0)\ne0`. At the similarity
center, the exact residual identity reduces to

$$`
\left|\mathcal R_u(x_0,t)\right|
=
(T-t)^{-(1+2\beta_j)}|\Delta Q(0)|.
`

Since $`1+2\beta_j>0`, this physical residual tends to $`+\infty` as
$`t\uparrow T`, while the rescaled diffusion coefficient tends to zero.
:::

:::proof "parabolic.keller_segel_abnormal_physical_residual_diverges"
At $`x=x_0`, the centered dilation is zero. Combine
$`(T-t)^{-2}` with $`(T-t)^{1-2\beta_j}` to obtain
$`(T-t)^{-(1+2\beta_j)}`. The mode bound implies
$`1+2\beta_j>0`, so this power tends to $`+\infty`; multiplication by the
positive constant $`|\Delta Q(0)|` preserves the limit.
:::

Divergence at the center is a statement about one point and one limit. The
exact criterion is a statement at every fixed pre-singular time.

:::theorem "parabolic.keller_segel_abnormal_exact_obstruction" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.forall_density_residual_abnormal_ansatz_3d_eq_zero_iff_laplacian_eq_zero") (uses := "parabolic.keller_segel_abnormal_diffusion_error, parabolic.keller_segel_abnormal_physical_residual_diverges")

Suppose $`Q,\Phi\in C^2` and the diffusion-free aggregation profile equation
holds at every profile point. At any fixed $`t<T`, the uncorrected abnormal
ansatz has zero density residual at every spatial point if and only if

$$`\Delta Q(y)=0\qquad\text{for every }y\in\mathbb R^3.`

This is an exact no-go theorem for nonharmonic leading profiles. It concerns
the density equation; the elliptic potential equation is a separate
condition.
:::

:::proof "parabolic.keller_segel_abnormal_exact_obstruction"
At a fixed pre-singular time, positivity of the physical prefactor and
inverse dilation reduce global vanishing of the physical residual to global
vanishing of the profile residual. The aggregation equation rewrites that
profile residual as a nonzero positive power of $`T-t` times
$`-\Delta Q(y)`. It therefore vanishes at every profile point exactly when
$`\Delta Q` does.
:::
