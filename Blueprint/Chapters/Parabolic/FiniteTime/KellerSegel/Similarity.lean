/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.FiniteTime.NonlinearHeat
import PDE.Solution.Singularity.FiniteTime.KellerSegel.Classical
import PDE.Solution.Singularity.FiniteTime.KellerSegel.Similarity.Parabolic

/-!
# Parabolic Keller–Segel similarity reduction

Classical parabolic–elliptic Keller–Segel solutions and the exact residual
factorization for the standard parabolic similarity scaling.
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
#doc (Manual) "Parabolic Keller–Segel Similarity Reduction" =>

Similarity variables separate the universal singular scale from the shape of
a possible blow-up profile. For Keller–Segel, the parabolic scale balances
diffusion, chemotactic drift, and the time derivative: space contracts like
$`(T-t)^{1/2}` while density grows like $`(T-t)^{-1}`. Substitution reduces
the physical PDE to a stationary pair of profile residuals.

:::definition "parabolic.keller_segel_solution_on" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.IsNonnegativePointwiseClassicalSolutionOn")

On an open time set $`I`, classical parabolic–elliptic Keller–Segel
solutions use the sign convention

$$`u_t=\operatorname{div}(\nabla u-u\nabla\Phi),\qquad -\Delta\Phi=u.`

The density is nonnegative and jointly $`C^1` in spacetime, the potential is jointly
continuous, and both have $`C^2` spatial slices; joint $`C^{2,1}`
regularity is not required. The elliptic equation alone determines $`\Phi`
only up to a harmonic component, and the definition imposes neither a
Newtonian-potential normalization nor decay at spatial infinity.
:::

The parabolic ansatz has to be matched to these equations one by one.
The density carries the amplitude $`(T-t)^{-1}` and the potential carries
none, because two spatial derivatives of a function of
$`y=(T-t)^{-1/2}(x-x_0)` already produce the factor $`(T-t)^{-1}` that
$`-\Delta\Phi=u` demands.

:::definition "parabolic.keller_segel_parabolic_profile" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.parabolicDensityAnsatz, PDE.Solution.Singularity.FiniteTime.KellerSegel.parabolicPotentialAnsatz, PDE.Solution.Singularity.FiniteTime.KellerSegel.parabolicDensityProfileResidual, PDE.Solution.Singularity.FiniteTime.KellerSegel.potentialResidual") (uses := "parabolic.blowup.self_similar_profile, parabolic.keller_segel_solution_on")

For $`t<T`, write

$$`
y=(T-t)^{-1/2}(x-x_0),\qquad
u_Q(x,t)=(T-t)^{-1}Q(y),\qquad
\Phi_\Psi(x,t)=\Psi(y).
`

The reduced residuals are

$$`
\mathcal R_\Phi[Q,\Psi]=-\Delta\Psi-Q,\qquad
\mathcal R_Q[Q,\Psi]
=\operatorname{div}(\nabla Q-Q\nabla\Psi)
-Q-\frac12 y\mathbin{\cdot}\nabla Q.
`

The two equations are represented by separate residual functions, defined in
every finite dimension without regularity or sign assumptions.
:::

Of the two residual identities the elliptic one is simpler, since the
density enters $`-\Delta\Phi-u` undifferentiated. Not even $`\Psi\in C^2` is
needed, and the common factor is exactly the density amplitude.

:::theorem "parabolic.keller_segel_potential_scaling" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.potential_residual_parabolic_ansatz") (uses := "parabolic.keller_segel_parabolic_profile")

The potential residual identity
for the parabolic ansatz
states that, whether or not $`\Psi` is $`C^2`, for every $`t<T`,

$$`
\mathcal R_\Phi[u_Q,\Phi_\Psi](x,t)
=(T-t)^{-1}\mathcal R_\Phi[Q,\Psi](y).
`
:::

:::proof "parabolic.keller_segel_potential_scaling"
The Laplacian of the scaled potential contributes the square of the spatial
dilation factor. Before $`T`, the identity
$`((T-t)^{-1/2})^2=(T-t)^{-1}` makes this factor equal to the density
amplitude. Expanding the potential residual and collecting the common factor
gives the stated profile residual.
:::

The density residual is assembled from two separate scaling computations,
the time derivative and the flux divergence, which must produce the same
power of $`T-t` for the reduction to close. The time derivative is where the
Euler term $`\frac12 y\cdot\nabla Q` originates.

:::theorem "parabolic.keller_segel_time_derivative" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.deriv_parabolic_density_ansatz") (uses := "parabolic.keller_segel_parabolic_profile")

The density time-derivative identity
for the parabolic ansatz
states that if $`Q` is $`C^1` and $`t<T`, then the density time derivative is
exactly

$$`
\partial_t u_Q(x,t)
=(T-t)^{-2}\left(Q(y)+\frac12 y\mathbin{\cdot}\nabla Q(y)\right).
`
:::

:::proof "parabolic.keller_segel_time_derivative"
Apply the general differentiation formula for a backward self-similar ansatz
with amplitude exponent $`1` and spatial exponent $`1/2`. The derivative of
the amplitude gives $`Q(y)`, while differentiation of the moving coordinate
gives $`\frac12 y\mathbin{\cdot}\nabla Q(y)`. Both terms carry the common
factor $`(T-t)^{-2}`.
:::

The flux $`\nabla u-u\nabla\Phi` is where the scaling of $`\Phi_\Psi`
matters: with no amplitude on the potential, $`u\nabla\Phi` carries the same
factors as $`\nabla u`, so diffusion and drift scale together, and one more
divergence gives the same $`(T-t)^{-2}` as the time derivative.

:::theorem "parabolic.keller_segel_flux_scaling" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.divergence_parabolic_ansatz_flux") (uses := "parabolic.keller_segel_parabolic_profile")

The flux divergence identity
for the parabolic ansatz
states that if both profiles are $`C^2` and $`t<T`, then the conservative
flux satisfies

$$`
\operatorname{div}_x
  \left(\nabla_x u_Q-u_Q\nabla_x\Phi_\Psi\right)(x,t)
=(T-t)^{-2}
\operatorname{div}_y\left(\nabla Q-Q\nabla\Psi\right)(y).
`
:::

:::proof "parabolic.keller_segel_flux_scaling"
The density gradient scales by
$`(T-t)^{-1}(T-t)^{-1/2}`, and the potential gradient by
$`(T-t)^{-1/2}`. Hence both terms in the flux share the first factor.
Taking one more divergence contributes another $`(T-t)^{-1/2}`. The identity
$`((T-t)^{-1/2})^2=(T-t)^{-1}` then combines the factors into
$`(T-t)^{-2}`.
:::

With both pieces carrying $`(T-t)^{-2}`, their difference is the density
residual identity.

:::theorem "parabolic.keller_segel_density_scaling" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.density_residual_parabolic_ansatz") (uses := "parabolic.keller_segel_time_derivative, parabolic.keller_segel_flux_scaling")

The density residual identity
for the parabolic ansatz
combines the time-derivative and flux formulas for $`C^2` profiles and
$`t<T` into the full density residual factorization

$$`
\mathcal R_u[u_Q,\Phi_\Psi](x,t)
=(T-t)^{-2}\mathcal R_Q[Q,\Psi](y),
`

where $`\mathcal R_u=\operatorname{div}(\nabla u-u\nabla\Phi)-\partial_t u`.
Consequently, vanishing profile residuals imply both pointwise
Keller–Segel equations before $`T`.
:::

:::proof "parabolic.keller_segel_density_scaling"
Unfold the physical density residual. Substitute the flux-divergence formula
and the time-derivative formula; each has the same factor
$`(T-t)^{-2}`. Distributing that factor leaves exactly the definition of
$`\mathcal R_Q[Q,\Psi]`.
:::

Both identities have a strictly positive prefactor before $`T`, and inverse
dilation reaches every similarity coordinate, so the residual identities
upgrade to profile equivalences.

:::theorem "parabolic.keller_segel_profile_equivalence" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.parabolic_density_profile_residual_eq_zero_iff, PDE.Solution.Singularity.FiniteTime.KellerSegel.forall_potential_residual_parabolic_ansatz_eq_zero_iff, PDE.Solution.Singularity.FiniteTime.KellerSegel.potential_equation_parabolic_ansatz_iff, PDE.Solution.Singularity.FiniteTime.KellerSegel.forall_density_residual_parabolic_ansatz_eq_zero_iff, PDE.Solution.Singularity.FiniteTime.KellerSegel.density_equation_parabolic_ansatz_iff") (uses := "parabolic.keller_segel_potential_scaling, parabolic.keller_segel_density_scaling")

At every fixed time $`t<T`, the similarity substitution loses no spatial
information. Positivity of the scale and inverse dilation give the two exact
equivalences

$$`
\begin{aligned}
  \mathcal R_\Phi[u_Q,\Phi_\Psi](\mathbin{\cdot},t)=0
    &\quad\Longleftrightarrow\quad
      \mathcal R_\Phi[Q,\Psi]=0,\\
  \mathcal R_u[u_Q,\Phi_\Psi](\mathbin{\cdot},t)=0
    &\quad\Longleftrightarrow\quad
      \mathcal R_Q[Q,\Psi]=0.
\end{aligned}
`

Each physical equation is also equivalent pointwise to its reduced equation
at the corresponding similarity coordinate. The
elliptic direction requires $`\Psi\in C^2`; the density direction requires
$`Q,\Psi\in C^2`.
:::

:::proof "parabolic.keller_segel_profile_equivalence"
The forward direction of each equivalence evaluates the physical residual at
$`x=x_0+s^{-1}y`, where $`s=(T-t)^{-1/2}`. The scale is positive, and the
centered dilation sends this $`x` back to $`y`. The residual factorization
then has a nonzero scalar factor, so the profile residual must vanish. The
reverse direction substitutes the vanishing profile residual directly into
the same factorization.
:::

The equivalences supply the two equations of a classical solution; the
solution theorem adds regularity and the sign of the density.

:::theorem "parabolic.keller_segel_parabolic_solution" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.parabolic_ansatz_is_nonnegative_pointwise_classical_solution_on") (uses := "parabolic.keller_segel_profile_equivalence")

If both profile residuals vanish, the density profile is nonnegative, and
both profiles are $`C^2`, then the parabolic ansatz is a
nonnegative pointwise classical solution on
$`(-\infty,T)`. The density is jointly $`C^1`, the potential is jointly
continuous, and both have $`C^2` spatial slices.
:::

:::proof "parabolic.keller_segel_parabolic_solution"
Generic regularity lemmas for scaled profiles give joint $`C^1` regularity of
the density, joint continuity of the potential, and $`C^2` regularity of
every spatial slice. Positivity of the amplitude transfers
$`Q\geq0` to the physical density. Finally, the two residual
factorizations turn the assumed profile equations into the density and
potential equations at every $`t<T`.
:::

The solution theorem is silent about size and the blow-up theorem is
silent about the equations. A Keller–Segel blow-up solution arises when one
profile pair meets the hypotheses of both theorems.

:::theorem "parabolic.keller_segel_parabolic_ansatz_diverges" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.parabolic_density_ansatz_blows_up_at") (uses := "parabolic.keller_segel_parabolic_profile")

If the density profile is bounded and nonzero at one point, then its
parabolic density ansatz has finite spatial slices and blows up in the
pointwise spatial supremum at $`T`. One nonzero value suffices for divergence
of the extended supremum; boundedness supplies the finite-slice condition.
The theorem uses only the similarity scaling of the density.
:::

:::proof "parabolic.keller_segel_parabolic_ansatz_diverges"
Choose a physical sample whose similarity coordinate is the point where
$`Q` is nonzero. Along this sample the profile value is fixed, while the
amplitude $`(T-t)^{-1}` tends to $`+\infty`. The general backward
self-similar blow-up theorem transfers this sampled divergence to the
extended spatial supremum. A global bound $`|Q(y)|\le C` bounds each slice
by the finite value $`(T-t)^{-1}C` for $`t<T`.
:::
