/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.FiniteTime.Core
import PDE.Parabolic.Heat.Nonlinear.DirichletBlowup
import PDE.Parabolic.Heat.Nonlinear.LargeData
import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.Classical
import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.Concentration
import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.ConstantBlowUp
import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.SelfSimilar

/-!
# Nonlinear heat singularity profiles

A finite-horizon obstruction for nonnegative weak Dirichlet solutions,
an explicit classical whole-space blow-up solution, and the Type I and
concentration-profile residual identities for general similarity ansatzes.
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
#doc (Manual) "Nonlinear Heat Singularity Profiles" =>

# Large data on a bounded domain

On a bounded domain with zero Dirichlet boundary data, a nonzero spatial
constant is unavailable. A positive first eigenfunction instead measures the
part of the solution on which reaction can overcome diffusion. The theorem
constructs this weight from the domain and derives its moment inequality
from the weak PDE.

:::theorem "parabolic.nonlinear_heat_large_data" (parent := "parabolic.blowup") (lean := "HeatEquation.Nonlinear.exists_weight_for_large_data_nonexistence, HeatEquation.Nonlinear.exists_eigenfunction_moment") (uses := "parabolic.blowup.weighted_moment")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 9 (nonlinear heat equation)"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subset\mathbb R^n`, $`n>0`, be nonempty, bounded, connected,
and open, and let $`a<b`. The domain admits a positive first Dirichlet
eigenweight $`w\in H^1_0(\Omega)` with eigenvalue $`\lambda>0` and
$`\int_\Omega w=1`. Suppose $`F`, not necessarily differentiable, is convex on the
nonnegative half-line, with

$$`
F(s)\ge c s^p\quad(s\ge0),\qquad c>0,\quad p>1.
`

For initial datum $`u_a\in L^2(\Omega)`, set
$`M_0=\int_\Omega w u_a`. If $`M_0>0` and

$$`
M_0^{1-p}\le
(p-1)c\,e^{-\lambda(b-a)(p-1)}(b-a),
`

there is no nonnegative weak energy solution of
$`u_t-\Delta u=F(u)` on $`[a,b]` with zero Dirichlet boundary data
and initial datum $`u_a`.

Precisely, the excluded class has
$`u\in L^2((a,b);H^1_0(\Omega))` and a dual forcing
$`\ell\in L^2((a,b);H^{-1}(\Omega))` satisfying the integrated weak
heat equation with that initial trace. For almost every time, $`u\ge0`
almost everywhere in space, and for every $`v\in H^1_0(\Omega)`,
$`vF(u)` is integrable and $`\ell(v)=\int_\Omega vF(u)`.
The threshold is a sufficient condition for nonexistence on the prescribed
interval $`[a,b]`.
:::

:::proof "parabolic.nonlinear_heat_large_data"
The first Dirichlet eigenfunction gives a positive probability weight.
Lions–Magenes regularity supplies the continuous $`L^2` representative of
the weak solution, and pairing its integrated derivative with $`w` gives
an absolutely continuous moment $`M(t)=\int_\Omega w u(t)`, with
$`M(a)=M_0`. The weak eigen-equation identifies diffusion as $`\lambda M`.
The reaction identity and weighted Jensen inequality then give, almost everywhere,

$$`
M'(t)+\lambda M(t)=\int_\Omega wF(u(t))
\ge F(M(t))\ge c M(t)^p.
`

For $`z(t)=e^{\lambda(t-a)}M(t)`, the coefficient in the power inequality
is bounded below by $`c e^{-\lambda(b-a)(p-1)}`. Absolute continuity
justifies integrating the negative-power derivative. Positivity and finiteness
at $`b` force the strict opposite of the displayed threshold, a contradiction.
:::

For classical solutions of $`u_t-\Delta u=u^2` the same moment gives a
lifespan, Kaplan's bound (Kaplan 1963). The moment
$`\eta(t)=\int_\Omega w\,u(t)` satisfies the Riccati inequality
$`\eta'\ge\eta^2-\lambda\eta`, and the solution of
$`\eta'=\eta^2-\lambda\eta` from $`\eta_0>\lambda` blows up at
$`\lambda^{-1}\log(\eta_0/(\eta_0-\lambda))`.

:::theorem "parabolic.nonlinear_heat_kaplan_lifespan" (parent := "parabolic.blowup") (lean := "HeatEquation.Nonlinear.IsInteriorDirichletSquareSolution.lifespan_le, HeatEquation.Nonlinear.not_global_interior_square_solution") (uses := "parabolic.blowup.weighted_moment")
Let $`\Omega\subset\mathbb R^n` be nonempty, bounded and open. Let
$`w\ge0` be $`C^2` in $`\Omega`, continuous on $`\overline\Omega` and zero
on $`\partial\Omega`, with $`-\Delta w=\lambda w` in $`\Omega`,
$`\lambda>0` and $`\int_\Omega w=1`. Let $`g\ge0` on $`\Omega` with

$$`
\eta_0=\int_\Omega w\,g>\lambda.
`

Suppose $`u` is $`C^2` in $`(0,T)\times\Omega`, continuous on
$`[0,T]\times\overline\Omega`, solves $`u_t-\Delta u=u^2` in
$`(0,T)\times\Omega`, vanishes on $`(0,T)\times\partial\Omega` and equals
$`g` at $`t=0`. Then

$$`
T\le\frac1\lambda\log\frac{\eta_0}{\eta_0-\lambda}.
`

In particular there is no such solution for every $`T>0`. No derivative of
$`u` or $`w` on the boundary and no regularity of the boundary are used.
:::

:::proof "parabolic.nonlinear_heat_kaplan_lifespan"
The minimum principle makes $`u` nonnegative. Testing the equation against
$`w`, the diffusion term becomes $`-\lambda\eta`, and Jensen's inequality for
the probability weight $`w` gives $`\int_\Omega w\,u^2\ge\eta^2`, so
$`\eta'\ge\eta^2-\lambda\eta`. Since no boundary derivative of $`u` is
available, the formal proof tests against compactly supported convex
truncations of $`w` and absorbs their error into a slightly larger damping
$`\lambda+\delta`. For $`v=1/\eta` the inequality reads
$`v'\le\lambda v-1`, and comparison with the solution of
$`v'=\lambda v-1` keeps $`v` positive only while
$`1-e^{-\lambda t}<\lambda/\eta_0`. Letting $`\delta\to0` gives
$`1-e^{-\lambda T}\le\lambda/\eta_0`, which is the bound.
:::

# A proved nonlinear-heat blow-up

:::definition "parabolic.nonlinear_heat_constant_blowup" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.constantBlowUp")

For every $`p>1` and finite time $`T`, define the spatially constant field

$$`
u(x,t)=\big((p-1)(T-t)\big)^{-\frac{1}{p-1}},
\qquad t<T.
`

This is the spatially homogeneous solution of the scalar equation $`u_t=u^p`,
viewed as a function on $`\mathbb R^n`. It comes with a complete PDE and
norm-divergence proof.

This whole-space example isolates the spatially homogeneous ODE
blow-up mechanism. Its slices are nonzero constants, so it satisfies no
homogeneous Dirichlet condition and, in positive dimension, does not lie in
$`L^2(\mathbb R^n)`.
:::

For this field the two halves of a blow-up result, the PDE and the
divergence, are independent theorems sharing the hypotheses $`p>1` and
$`t<T`. The PDE half is elementary because the Laplacian of a spatially
constant field vanishes, leaving only the ordinary differential equation
$`u_t=u^p`.

This makes the competition with smoothing precise. Diffusion acts on spatial
variation, and this profile has none; the reaction still raises its height.
For a positive scalar state, separation of variables gives

$$`
\frac{d}{dt}u^{1-p}=1-p,
\qquad
u(t)^{1-p}=u(t_0)^{1-p}-(p-1)(t-t_0).
`

The right-hand side reaches zero in finite time, forcing $`u` to diverge.
The solution stays smooth at every earlier time. Positive-time spatial
smoothing therefore does not, by itself, bound amplitude or guarantee
global existence.

:::theorem "parabolic.nonlinear_heat_constant_equation" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.isNonnegativePointwiseClassicalSolutionOn_constantBlowUp") (uses := "parabolic.nonlinear_heat_constant_blowup")

The constant-profile solution theorem
for the nonlinear heat equation
states that on $`\mathbb R^n\times(-\infty,T)`, the field is a nonnegative
classical solution of

$$`u_t=\Delta u+u^p.`

The `equation` field of the classical-solution proof is
the constant-profile equation theorem, proved without the Type I profile
theory. The formal theorem also checks joint spacetime $`C^1` regularity, $`C^2`
regularity of every spatial slice, and positivity on the entire pre-singular
cylinder.
:::

:::proof "parabolic.nonlinear_heat_constant_equation"
Let $`a=1/(p-1)` and $`s=(p-1)(T-t)>0`. The field is independent of $`x`,
so every spatial derivative and hence $`\Delta u` vanishes. The real-power
chain rule gives $`u_t=s^{-a-1}` after the factor $`p-1` cancels $`a`;
since $`ap=a+1`, this equals $`u^p`. Positivity of $`s` also gives
positivity and the required smoothness on $`t<T`.
:::

Divergence is simpler still, since a constant slice has supremum equal to
its common value. The explicit formula for $`S_u(t)` is what makes the
constant example a complete blow-up solution rather than a profile
calculation.

:::theorem "parabolic.nonlinear_heat_constant_diverges" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.spatialSupNormBlowsUpAt_constantBlowUp") (uses := "parabolic.nonlinear_heat_constant_equation")

The theorem uses the pointwise value at any spatial sample to prove blow-up.
The companion identity for every $`t<T` is

$$`
S_u(t)
=\operatorname{ofReal}\!\left(
  \big((p-1)(T-t)\big)^{-\frac{1}{p-1}}
\right),
`

which is finite for every $`t<T` and tends to $`+\infty` as $`t\uparrow T`.
Thus the field satisfies divergence of the spatial supremum norm at $`T` for every $`p>1`.
:::

:::proof "parabolic.nonlinear_heat_constant_diverges"
The spatial supremum is at least the value at any fixed point and, because
the field is constant, equals that value. As $`t\uparrow T`, the positive
base $`(p-1)(T-t)` tends to zero. The exponent $`-1/(p-1)` is negative, so
the power tends to $`+\infty`. Passing through `ENNReal.ofReal` preserves
this divergence. The displayed supremum identity supplies finiteness at
every preceding time.
:::

Combining the two theorems gives an explicit classical solution whose
spatial supremum norm diverges at the prescribed time.

:::theorem "parabolic.nonlinear_heat_constant_existence_and_blowup" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.exists_isNonnegativePointwiseClassicalSolutionOn_spatialSupNormBlowsUpAt") (uses := "parabolic.nonlinear_heat_constant_equation, parabolic.nonlinear_heat_constant_diverges")
For every $`p>1` and finite $`T`, there exists a nonnegative pointwise
classical whole-space solution on $`t<T` whose spatial supremum norm blows up
at $`T`. The witness is the spatially constant field
$`((p-1)(T-t))^{-1/(p-1)}`.
:::

:::proof "parabolic.nonlinear_heat_constant_existence_and_blowup"
Choose the explicitly defined constant field. The equation theorem supplies
its nonnegative pointwise classical-solution structure on the full
pre-singular cylinder, and the divergence theorem supplies spatial
supremum-norm blow-up at $`T`. Combining those two facts for the same witness
proves the existential statement.
:::

Separation of variables also identifies every solution of the scalar
equation $`u'=u^p` from a positive value, so the blow-up time of the
constant field is the exact lifespan of the ODE.

:::theorem "parabolic.nonlinear_heat_ode_lifespan" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.odeBlowUpTime, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.odeSolution, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.odeSolution_zero, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.hasDerivAt_odeSolution, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.normBlowsUpAt_odeSolution, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.lt_odeBlowUpTime_and_eqOn, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.odeBlowUpTime_two, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.odeSolution_two") (uses := "parabolic.nonlinear_heat_constant_blowup, parabolic.blowup.norm_trajectory")
Let $`p>1` and $`u_0>0`, and set

$$`
T_p(u_0)=\frac{u_0^{1-p}}{p-1},\qquad
u_*(t)=\big((p-1)(T_p(u_0)-t)\big)^{-\frac{1}{p-1}}.
`

Then $`u_*(0)=u_0`, $`u_*'=u_*^p` for $`t<T_p(u_0)`, and $`|u_*(t)|\to\infty`
as $`t\uparrow T_p(u_0)`. Conversely, let $`T\ge0` and let $`u` be
continuous on $`[0,T]` with $`u(0)=u_0` and right derivative $`u(t)^p` at
every $`t\in[0,T)`. Then $`T<T_p(u_0)` and $`u=u_*` on $`[0,T]`. For
$`p=2`, $`T_2(u_0)=1/u_0` and $`u_*(t)=1/(u_0^{-1}-t)`.
:::

:::proof "parabolic.nonlinear_heat_ode_lifespan"
The derivative and the divergence of $`u_*` are those of the constant field
at any spatial point. For the converse, $`u` stays at least $`u_0`, since its
right derivative $`u_0^p` is positive wherever it equals $`u_0`. Then
$`u^{1-p}` has right derivative $`1-p` on $`[0,T)`, so
$`u(t)^{1-p}=u_0^{1-p}-(p-1)t`. The left side is positive on $`[0,T]`,
which is $`T<T_p(u_0)`, and solving for $`u` gives $`u_*`.
:::

# Nonlinear heat profiles

:::definition "parabolic.nonlinear_heat_solution_on" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.IsNonnegativePointwiseClassicalSolutionOn")

For a real exponent $`p` and an open time set $`I`, this structure records a
nonnegative classical solution of

$$`u_t=\Delta u+u^p`

on $`\mathbb R^n\times I`. Its regularity scope is joint spacetime $`C^1`
for $`u` together with $`C^2` regularity of each spatial slice. Time
differentiability is derived from the joint $`C^1` field; joint $`C^{2,1}`
regularity is not required. The equation is imposed only at times in $`I`, so
a solution on $`t<T` says nothing at $`T`.
:::

A profile must satisfy the stated regularity, sign and equation conditions.
The Type I exponents make $`\Delta u`, $`u_t`, and $`u^p` all scale by the same power of
$`T-t`.

:::definition "parabolic.nonlinear_heat_type_i_profile" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.typeIAnsatz, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.typeIProfileResidual, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroTypeIProfileResidual") (uses := "parabolic.blowup.self_similar_profile, parabolic.nonlinear_heat_solution_on")

For the Type I ansatz

$$`u(x,t)=(T-t)^{-1/(p-1)}
 f\!\left(\frac{x-x_0}{\sqrt{T-t}}\right),`

The reduced elliptic residual is

$$`\Delta f-\frac12 y\cdot\nabla f-\frac{1}{p-1}f+f^p=0,`

and the Type I profile equation says exactly that this residual vanishes
pointwise. This is the standard Type I reduction used by Giga–Kohn, *Comm.
Pure Appl. Math.* 38 (1985), DOI 10.1002/cpa.3160380304; the Lean statements
are the exact substitution identities.
:::

The definition only names the two residuals. Substituting the ansatz into the
equation relates them.

:::theorem "parabolic.nonlinear_heat_type_i_factorization" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.equation_residual_type_i_ansatz") (uses := "parabolic.nonlinear_heat_type_i_profile")

Suppose $`t<T`, $`p\ne1`, and the profile is $`C^2` and nonnegative at the
displayed similarity coordinate. Then the exact residual identity is

$$`
\mathcal R_p[u](x,t)
=(T-t)^{-\left(\frac{1}{p-1}+1\right)}
\mathcal R_{\mathrm{prof}}[f]\!
\left((T-t)^{-1/2}(x-x_0)\right).
`

The two balance laws are visible in the formal proof: $`2\beta=1` aligns the
Laplacian scale and $`\alpha p=\alpha+1` aligns the reaction scale. Profile
nonnegativity is used only to split the real power of the amplitude-profile
product.
:::

:::proof "parabolic.nonlinear_heat_type_i_factorization"
Write $`s=T-t`, $`\alpha=1/(p-1)`, and
$`y=s^{-1/2}(x-x_0)`. The backward similarity chain rules give
$`u_t=s^{-\alpha-1}(\alpha f+\frac12y\cdot\nabla f)` and
$`\Delta u=s^{-\alpha-1}\Delta f`, because two spatial scale factors produce
$`s^{-1}`. Nonnegativity permits
$`u^p=s^{-\alpha p}f^p`, and $`\alpha p=\alpha+1`. Factoring
$`s^{-\alpha-1}` leaves the stated profile residual.
:::

Since the prefactor $`(T-t)^{-(1/(p-1)+1)}` is strictly positive for
$`t<T`, the residual identity upgrades at once to a profile equivalence.

:::theorem "parabolic.nonlinear_heat_type_i_equation" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.equation_residual_type_i_ansatz_eq_zero_iff") (uses := "parabolic.nonlinear_heat_type_i_factorization")

Under the factorization hypotheses, the full parabolic residual vanishes at
$`x\in\mathbb R^n` and $`t<T` if and only if the reduced profile residual
vanishes at the corresponding similarity coordinate. Consequently, the ansatz
of a nonnegative $`C^2` profile with $`p\ne1` and zero Type I profile residual
everywhere satisfies

$$`u_t=\Delta u+u^p`

pointwise throughout the pre-singular cylinder.
:::

:::proof "parabolic.nonlinear_heat_type_i_equation"
The factorization writes the full residual as the profile residual multiplied
by $`(T-t)^{-(1/(p-1)+1)}`. For $`t<T`, this prefactor is strictly positive
and hence nonzero. Therefore the product vanishes exactly when the profile
residual at the corresponding similarity point vanishes. Applying this
pointwise to the Type I profile equation hypothesis proves the equation
everywhere.
:::

The pointwise equation is one field of the classical-solution record. The
others, regularity and sign, are inherited from the profile because the
amplitude and the similarity scale are smooth and positive before $`T`.
Assembling all of them needs the global hypotheses, nonnegativity everywhere
and $`p>1`, that the pointwise identity did not.

:::theorem "parabolic.nonlinear_heat_type_i_solution" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroTypeIProfileResidual.is_pointwise_classical_solution_on_pre_singular") (uses := "parabolic.nonlinear_heat_type_i_equation")

If the Type I profile residual vanishes everywhere, then under the same
regularity and sign assumptions, with $`p>1`, the ansatz is a
nonnegative pointwise classical solution on
$`(-\infty,T)`. For a bounded profile with a nonzero value,
the Type I blow-up theorem separately gives finite spatial slices and
supremum-norm blow-up at $`T`.

Under the same regularity and sign hypotheses, the companion theorem
on the profile-solution equivalence
also proves the converse: a Type I ansatz is a pointwise classical solution
on the full pre-singular interval exactly when its profile residual vanishes.
:::

:::proof "parabolic.nonlinear_heat_type_i_solution"
On $`t<T`, the amplitude and similarity scale are smooth and positive.
Composition with the $`C^2` profile gives joint $`C^1` regularity and
$`C^2` regularity of each spatial slice; profile nonnegativity and the
positive amplitude give $`u\geq0`. The Type I profile equation and the
zero-residual equivalence supply $`u_t=\Delta u+u^p` at every point. These
fields assemble the classical-solution structure. The converse evaluates the
same nonzero factorization.
:::

# Equation-scaling concentration and pure-profile rigidity

:::definition "parabolic.nonlinear_heat_scaling_invariant_concentration" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.scalingInvariantConcentrationAnsatz, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.stationaryProfileResidual, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroStationaryProfileResidual") (uses := "parabolic.blowup.self_similar_profile, parabolic.nonlinear_heat_solution_on")

For a positive scale $`\lambda(t)`, the concentration ansatz is

$$`
u(x,t)=\lambda(t)^{-2/(p-1)}
Q\!\left(\lambda(t)^{-1}(x-x_0)\right).
`

Its stationary elliptic residual is

$$`\mathcal R_{\mathrm{stat}}[Q](y)=\Delta Q(y)+Q(y)^p,`

and the stationary profile equation says exactly that this residual
vanishes pointwise.

The exponent is invariant under the nonlinear-heat equation scaling. Whether
that scaling is critical for a particular Sobolev or Lebesgue norm also
depends on the dimension and exponent, hence the name "scaling-invariant"
rather than "critical".

Type II blow-up constructions with this leading profile, such as the
modulation analyses of Schweyer (arXiv:1201.2907v2) and of
{Informal.citet "collot-2017"}[], add correction terms and prove the asymptotic
law of the scale. The residual and rigidity identities here concern the pure
profile.
:::

Replacing the fixed similarity scale $`(T-t)^{1/2}` by a free scale
$`\lambda(t)` costs one thing: the time derivative now produces a term
proportional to $`\lambda'(t)`, so the residual identity acquires a
modulation defect alongside the stationary elliptic residual. At the level
of formulas the choice $`\lambda(t)=(T-t)^{1/2}` recovers the Type I ansatz,
and the modulation defect then reproduces the two lower-order terms of the
Type I profile residual.

:::theorem "parabolic.nonlinear_heat_concentration_factorization" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.equation_residual_scaling_invariant_concentration_ansatz") (uses := "parabolic.nonlinear_heat_scaling_invariant_concentration")

Suppose $`p\ne1`, $`Q` is $`C^2` and nonnegative at
$`y=\lambda(t)^{-1}(x-x_0)`, and the scale is positive and differentiable at
$`t`. Write

$$`\Lambda Q(y)=\frac{2}{p-1}Q(y)+y\mathbin{\cdot}\nabla Q(y).`

The full parabolic residual has the exact factorization

$$`
\mathcal R_p[u](x,t)
=\lambda(t)^{-\left(\frac{2}{p-1}+2\right)}
\left(
  \mathcal R_{\mathrm{stat}}[Q](y)
  +\lambda(t)\lambda'(t)\Lambda Q(y)
\right).
`

Thus the formal identity separates the stationary elliptic error from the
modulation defect.
:::

:::proof "parabolic.nonlinear_heat_concentration_factorization"
Differentiate the ansatz through the similarity coordinate. Each spatial
derivative contributes one factor of $`\lambda^{-1}`, while the time
derivative contributes the scale-velocity term
$`\lambda\lambda'\Lambda Q`. The nonlinear power has the same prefactor as
the Laplacian because
$`\frac{2p}{p-1}=\frac{2}{p-1}+2`. Collecting these terms gives the stated
stationary residual plus modulation defect.
:::

The rigidity statements read the identity for a profile that already solves
the stationary equation $`\Delta Q+Q^p=0`.

:::theorem "parabolic.nonlinear_heat_concentration_modulation_defect" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroStationaryProfileResidual.equation_residual_eq_modulation_defect") (uses := "parabolic.nonlinear_heat_concentration_factorization")

Under the same regularity, sign, exponent, and scale assumptions, a stationary
elliptic profile has vanishing profile residual, and the remaining parabolic
error is exactly

$$`
\lambda(t)^{-\left(\frac{2}{p-1}+2\right)}
\lambda(t)\lambda'(t)\Lambda Q(y).
`

This specialization exposes the additional modulation condition required for
the concentration ansatz to solve the evolution equation.
:::

:::proof "parabolic.nonlinear_heat_concentration_modulation_defect" (uses := "parabolic.nonlinear_heat_concentration_factorization")
Substitute the stationary profile equation
$`\mathcal R_{\mathrm{stat}}[Q]=0` into the exact factorization. The elliptic
term disappears, leaving only the scale derivative multiplied by the scaling
generator.
:::

The modulation defect is a product of a nonzero power of the scale, the
positive scale itself, $`\lambda'(t)`, and $`\Lambda Q(y)`, so it vanishes
exactly when one of the last two factors does.

:::theorem "parabolic.nonlinear_heat_concentration_pointwise_criterion" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroStationaryProfileResidual.equation_residual_eq_zero_iff") (uses := "parabolic.nonlinear_heat_concentration_modulation_defect")

Let $`p\ne1`, let $`Q` be a $`C^2` stationary elliptic profile that is
nonnegative at the relevant similarity coordinate, and let the scale be
positive and differentiable at $`t`. The pure concentration ansatz has zero
residual at $`(x,t)` if and only if

$$`\lambda'(t)=0\quad\text{or}\quad \Lambda Q(y)=0.`
:::

:::proof "parabolic.nonlinear_heat_concentration_pointwise_criterion" (uses := "parabolic.nonlinear_heat_concentration_modulation_defect")
Positivity of $`\lambda(t)` makes the common power of $`\lambda(t)`
nonzero. The residual therefore vanishes exactly when
$`\lambda(t)\lambda'(t)\Lambda Q(y)=0`. Removing the second nonzero scale
factor and splitting the remaining product yields the two alternatives.
:::

At the center $`x=x_0` the similarity coordinate is $`y=0`, the Euler term
of $`\Lambda Q` disappears, and $`\Lambda Q(0)=\frac{2}{p-1}Q(0)`. When
$`Q(0)>0` the second branch of the criterion is unavailable and the first is
forced; positivity at the origin also supplies the sign hypothesis the
criterion needs at that one coordinate.

:::theorem "parabolic.nonlinear_heat_concentration_center_rigidity" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroStationaryProfileResidual.deriv_scale_eq_zero_of_equation_residual_eq_zero_at_center") (uses := "parabolic.nonlinear_heat_concentration_pointwise_criterion")

Suppose $`p\ne1`, $`Q` is a $`C^2` stationary profile with $`Q(0)>0`, and the
scale is positive and differentiable at $`t`. If the pure concentration ansatz
has zero residual at the spatial center $`x=x_0`, then

$$`\lambda'(t)=0.`

This gives a local obstruction without imposing a global nonvanishing
condition on the scaling generator.
:::

:::proof "parabolic.nonlinear_heat_concentration_center_rigidity" (uses := "parabolic.nonlinear_heat_concentration_pointwise_criterion")
At $`x=x_0` the similarity variable is zero, so
$`\Lambda Q(0)=\frac{2}{p-1}Q(0)`. This quantity is nonzero because
$`p\ne1` and $`Q(0)>0`; hence the scaling-generator branch of the pointwise
criterion is impossible, and $`\lambda'(t)=0`.
:::

Center rigidity is infinitesimal: it fixes $`\lambda'` at one time. On an
open connected time set where the center equation holds throughout, the
vanishing derivative integrates to a constant scale, so a pure profile with
positive center admits no nontrivial modulation law at all.

:::theorem "parabolic.nonlinear_heat_concentration_scale_rigidity" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroStationaryProfileResidual.scale_eq_of_equation_residual_eq_zero_at_center") (uses := "parabolic.nonlinear_heat_concentration_center_rigidity")

Let $`p\ne1`, let $`Q` be a $`C^2` stationary profile with $`Q(0)>0`, and let
$`I` be an open, preconnected time set. If the scale is positive and
differentiable on $`I` and the center residual vanishes for every $`t\in I`,
then

$$`\lambda(s)=\lambda(t)\qquad\text{for all }s,t\in I.`
:::

:::proof "parabolic.nonlinear_heat_concentration_scale_rigidity" (uses := "parabolic.nonlinear_heat_concentration_center_rigidity")
Apply center rigidity at every point of $`I` to obtain
$`\lambda'=0` throughout the interval. Since an open connected subset of
$`\mathbb R` is an interval, the mean-value theorem applied between any two
of its points shows that their scale values agree.
:::

The rigidity statements look at one spatial point, the center. Requiring
instead that the residual vanish at every spatial point at a fixed time gives
a global form of the pointwise criterion, because inverse dilation reaches
every similarity coordinate.

:::theorem "parabolic.nonlinear_heat_concentration_global_criterion" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.HasZeroStationaryProfileResidual.forall_equation_residual_eq_zero_iff") (uses := "parabolic.nonlinear_heat_concentration_pointwise_criterion")

Let $`p\ne1`, let $`Q` be a globally nonnegative $`C^2` stationary profile,
and let the scale be positive and differentiable at a fixed time. The residual
vanishes at every spatial point at that time exactly when

$$`
\lambda'(t)=0
\quad\text{or}\quad
\Lambda Q(y)=0\ \text{for every }y\in\mathbb R^n.
`

Thus a moving scale, $`\lambda'(t)\ne0`, forces the scaling generator to
vanish on the whole profile.
:::

:::proof "parabolic.nonlinear_heat_concentration_global_criterion" (uses := "parabolic.nonlinear_heat_concentration_pointwise_criterion")
If $`\lambda'(t)=0`, the pointwise criterion settles every spatial point.
Otherwise it forces $`\Lambda Q` to vanish at every similarity coordinate.
Every $`y\in\mathbb R^n` occurs by choosing
$`x=x_0+\lambda(t)y`, because the positive scale is invertible. Conversely,
either global alternative implies the pointwise disjunction for each $`x`.
:::

None of the residual statements says anything about size. The divergence
theorem is independent of all of them: it concerns the field defined by the
formula and holds whether or not the field solves the equation.

:::theorem "parabolic.nonlinear_heat_concentration_blowup" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.NonlinearHeat.tendsto_spatial_sup_norm_scaling_invariant_concentration_ansatz_nhds_top, PDE.Solution.Singularity.FiniteTime.NonlinearHeat.scaling_invariant_concentration_ansatz_blows_up_at") (uses := "parabolic.nonlinear_heat_scaling_invariant_concentration")

If $`p>1`, the profile is nonzero somewhere, and $`\lambda(t)\to0` through
positive values as $`t\uparrow T`, then the extended pointwise spatial
supremum of the ansatz tends to $`+\infty`. No global boundedness assumption
on the profile is needed for this limit. If the profile is bounded, every
slice has finite supremum and the ansatz satisfies divergence of the spatial supremum norm.

By the global criterion, a moving stationary profile with
$`\Lambda Q\not\equiv0` is not a nonlinear-heat solution, and correction
terms are needed.
:::

:::proof "parabolic.nonlinear_heat_concentration_blowup"
Choose $`y_0` with $`Q(y_0)\ne0` and sample the field at
$`x(t)=x_0+\lambda(t)y_0`. There the profile argument is exactly $`y_0`, so
the absolute value is
$`\lambda(t)^{-2/(p-1)}|Q(y_0)|`. Since $`p>1` and
$`\lambda(t)\to0^+`, this quantity tends to $`+\infty` and is bounded above
by the spatial supremum. If $`|Q(y)|\le C` everywhere, the same formula
bounds the whole slice by the finite number
$`\lambda(t)^{-2/(p-1)}C` whenever $`\lambda(t)>0`. Positivity holds
eventually by the scale-limit hypothesis.
:::
