/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.DivergenceForm
import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.MeasurableForcing
import PDE.Analysis.Evolution.Galerkin.PairedL2Differentiation.Ritz
import PDE.Analysis.Evolution.Galerkin.RitzInitialCompatibility
import PDE.Parabolic.Regularity.Autonomous.Estimate
import PDE.Parabolic.Regularity.Autonomous.Higher
import PDE.Parabolic.Regularity.SpatialH2.WeakResidual
import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.ClassicalBoundaryData
import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Existence

/-!
# Parabolic regularity

Improved time regularity and spatial Sobolev estimates for parabolic equations.
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
#doc (Manual) "Improved Time and Spatial Regularity" =>

The regularity theory follows §7.1.3 of {Informal.citet "evans-2010"}[].

The abstract arguments take place in a real Hilbert Gelfand triple
$`V\hookrightarrow H\hookrightarrow V^*`, with inclusion $`J:V\to H`,
on a finite interval $`[a,b]` with $`a<b`. The Galerkin limit theorems use
finite-dimensional trial spaces that approximate every vector of $`V`,
with pivot-orthogonal projections uniformly bounded in the $`V` norm. The
spatial applications take
$`V=H^1_0(\Omega)` and $`H=L^2(\Omega)` for $`\Omega\subset\mathbb R^n`,
$`n>0`.

The {bpref "parabolic.improved_galerkin_energy"}[Galerkin energy estimate]
first bounds the time derivatives uniformly in $`L^2(H)`. After passing to a
weak limit, the spatial elliptic estimate applies to $`f-u_t` and gives
$`H^2` regularity of almost every time slice. Stronger time regularity needs
one further argument: differentiated Galerkin equations, compatible initial
data, and {bpref "parabolic.paired_l2_differentiation"}[paired compactness]
identify the differentiated limit with the derivative of the original solution.

# Energy Estimates and Elliptic Slices

The fundamental difficulty in parabolic regularity is that time and space
play asymmetric roles. The time derivative $`u_t` lives naturally in the dual
space $`V^*=H^{-1}`, which is *two* spatial derivatives below the energy
space $`V=H^1_0`. Improving from $`u_t\in L^2(V^*)` to $`u_t\in L^2(H)`
(a gain of one spatial derivative for the velocity) can be obtained by
testing the Galerkin equation with its own velocity. For an autonomous
symmetric principal form, the spatial term is an exact energy derivative.
Differentiating the equation itself is a later step, used to control
$`u_{tt}` and improve the regularity of $`u_t`.

Once $`u_t\in L^2(H)` is established, the parabolic equation at almost every
time becomes a *static* elliptic problem:

$$`-\nabla\cdot(A\nabla u(t))=f(t)-u_t(t)\in L^2(\Omega).`

Standard elliptic regularity (Evans, 2010, §6.3;
{Informal.citet "gilbarg-trudinger-2001"}[], Ch. 8) then lifts
$`u(t)` from $`H^1_0` to $`H^2`. This
explains the parabolic regularity mechanism: time regularity feeds spatial
regularity through the equation itself.

The full chain therefore reads:

$$`\text{Galerkin energy}\longrightarrow
u_t\in L^2(H)\longrightarrow
\text{elliptic slice: }u(t)\in H^2\longrightarrow
\text{Bochner lift: }u\in L^2(H^2).`

Each step uses a different tool: energy testing, weak compactness, or
elliptic estimates. The Lions–Magenes framework (1972, Vol. I, Ch. 3) provides the abstract
Gelfand-triple language in which this composition is natural.

:::theorem "parabolic.improved_galerkin_energy" (parent := "parabolic.regularity") (lean := "PDE.Analysis.Evolution.AEGelfandGalerkinApproximation.improved_energy_estimate_of_autonomous_symmetric_principal")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose $`B(t)=A+R(t)`, where $`A:V\to V^*` is bounded, autonomous,
and symmetric, and the remainder satisfies

$$`|R(t)(u,v)|\leq L\lVert u\rVert_V\lVert Jv\rVert_H.`

For a supplied Galerkin trajectory $`u_m` with pivot forcing
$`f\in L^2(a,b;H)`, every $`t\in[a,b]` satisfies

$$`
\frac12 A(u_m(t),u_m(t))
+\frac12\int_a^t\|Ju_m'(s)\|_H^2\,ds
\leq \frac12 A(u_m(a),u_m(a))
+\int_a^t\bigl(\|f(s)\|_H^2+L^2\|u_m(s)\|_V^2\bigr)\,ds.
`

The constants are independent of the trial dimension. When the principal
form is nonnegative, uniform bounds for the initial energy and the remaining
$`L^2(V)` term give the velocity estimate. The existence theorem
{bpref "parabolic.improved_time_regularity"}[] uses the stronger assumption of
principal coercivity.
:::

:::proof "parabolic.improved_galerkin_energy"
Use the Galerkin velocity as test vector. Symmetry and time independence of
$`A` identify $`A(u_m,u_m')` with
$`\frac12\frac d{dt}A(u_m,u_m)`. The equation therefore controls
$`\|Ju_m'\|_H^2` plus this exact principal-energy derivative. Bound the
lower-order term by
$`L\|u_m\|_V\|Ju_m'\|_H` and the forcing term by
$`\|f\|_H\|Ju_m'\|_H`, absorb both velocity factors with Young's inequality,
and integrate. The earlier energy estimate controls the remaining
$`L^2(V)` term uniformly in the trial dimension.
:::

The two coercivity assumptions have different jobs. Coercivity of the
full form $`B(t)` supplies the basic $`L^2(V)` estimate and continuous
dependence on the load. Coercivity of the principal form turns its energy
into a bound for the $`V` norm. Together with stable initial projections,
these estimates bound the Galerkin velocities uniformly in $`L^2(H)`.

The existence theorem also allows the symmetric principal form to vary
absolutely continuously in time. Its derivative contributes one extra term:
$`\frac12 A'(t)(u_m,u_m)`. An operator-norm bound
$`\|A'(t)\|\leq N` controls this term by
$`\frac N2\|u_m\|_V^2`, so the same argument still applies.

:::theorem "parabolic.improved_time_regularity" (parent := "parabolic.regularity") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.exists_of_symmetric_principal_measurable_galerkin_L2_with_remainder") (uses := "parabolic.integrated_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`B(t)=A(t)+R(t)` be strongly measurable almost everywhere and
uniformly bounded in operator norm on $`[a,b]`. Assume $`A` is absolutely
continuous in operator norm, $`A(t)` is symmetric for every $`t\in[a,b]`,
and its supplied almost-everywhere derivative is bounded by $`N\geq0`.
For one $`C>0`, require both

$$`C\|w\|_V^2\leq A(t)(w,w),\qquad
C\|w\|_V^2\leq B(t)(w,w),`

for every $`t\in[a,b]` and $`w\in V`. Suppose also, for all such times
and every $`u,v\in V`,

$$`|R(t)(u,v)|\leq L\lVert u\rVert_V\lVert Jv\rVert_H.`

With trial spaces that approximate every vector of $`V` and pivot projections
uniformly bounded in $`V`, every
$`f\in L^2(a,b;H)` and $`u_0\in V` admit an integrated weak solution
whose time derivative is represented by $`u_t\in L^2(a,b;H)`.
Almost everywhere,

$$`J^*u_t+A(t)u+R(t)u=J^*f.`

The theorem records quantitative $`L^2(H)` derivative and $`L^\infty(V)`
state bounds. Here $`J^*:H\to V^*` is the pivot embedding. The autonomous
case takes $`A'(t)=0` and $`N=0`.
:::

:::proof "parabolic.improved_time_regularity" (uses := "parabolic.improved_galerkin_energy")
First construct Galerkin families for bounded continuous pivot loads.
The principal-energy calculation bounds their velocities in $`L^2(H)`;
for time-dependent $`A`, the additional coefficient is $`N/2`. Pass to a
common weak limit and identify the pivot velocity with the weak derivative
of the state. Finally, approximate an arbitrary Bochner load by bounded
continuous loads. The estimates depend only on their $`L^2(H)` norms, and
full-form coercivity controls the differences, so both state and velocity
pass through the forcing-completion argument.
:::

For the second stage, assume the full form $`B` is autonomous; in the
principal-part application, $`B=A`. For a dual load $`\ell` with derivative
$`\dot\ell`, the formal equation for $`v=u_t` has load $`\dot\ell`.
The construction makes the differentiated Galerkin state equal to the
original coefficient derivative almost everywhere and proves
$`J\widetilde u_m=\partial_t(Ju_m)` as an identity of Bochner classes.
Passing this identity through a common weak limit identifies the
differentiated limit with the weak derivative of the state.

:::theorem "parabolic.differentiated_galerkin_construction" (parent := "parabolic.regularity") (lean := "PDE.Analysis.Evolution.L2DifferentiatedGalerkinApproximation.exists_of_autonomous") (uses := "parabolic.improved_time_regularity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For an autonomous form and an absolutely continuous load whose derivative
belongs to $`L^2(a,b;V^*)`, every finite-dimensional Galerkin approximation
canonically produces an $`L^2`-forced approximation of the differentiated
equation. Its state is the original coefficient derivative almost everywhere,
and the Bochner identity

$$`J\widetilde u_m=\partial_t(Ju_m)`

is proved rather than supplied as a hypothesis.
:::

:::proof "parabolic.differentiated_galerkin_construction"
Write the coefficient equation as $`c_m'=M_mc_m+f_m`. Define its
velocity directly by $`v_m=M_mc_m+f_m`. Absolute continuity of $`c_m` and
$`f_m` makes $`v_m` absolutely continuous, and differentiation gives
$`v_m'=M_mv_m+f_m'` almost everywhere. Its initial value is
$`M_mc_m(a)+f_m(a)`. Thus the original right-hand side itself supplies the
differentiated trajectory and agrees almost everywhere with $`c_m'`.
The $`L^2(V^*)` load-derivative hypothesis gives the required
finite-dimensional $`L^2` bounds. Applying the pivot inclusion identifies
the resulting Bochner classes: $`J\widetilde u_m=\partial_t(Ju_m)`.
:::

The differentiated Galerkin system starts from the velocity defined by
the original right-hand side at $`a`. The energy argument needs these
initial velocities to be bounded in $`H` uniformly in $`m`. Choose
$`u_m(a)` to be the Ritz projection of $`g`; its defining identity then
replaces the form term at the initial time by $`B(g,v)` for every trial
vector $`v`. A pivot-valued compatibility residual gives the uniform bound.

:::theorem "parabolic.ritz_initial_compatibility" (parent := "parabolic.regularity") (lean := "PDE.Analysis.Evolution.RitzInitialCompatibility.initialVelocity_eq_pivotProjection") (uses := "parabolic.differentiated_galerkin_construction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For each finite-dimensional trial space, Lax–Milgram constructs the
Ritz projection for a bounded autonomous coercive form $`B`. It satisfies
Galerkin orthogonality $`B(g-R_mg,v_m)=0`, Céa's estimate, and convergence
along an approximating family of trial spaces. Symmetry is not needed for
these statements.

Suppose a vector $`h_{\mathrm{init}}\in H` represents the initial residual:

$$`\ell(a)(v)=(h_{\mathrm{init}},Jv)_H+B(g,v)\qquad(v\in V).`

With $`u_m(a)=R_mg`, the initial value of the differentiated trajectory is
the pivot projection of that vector:

$$`J\widetilde u_m(a)=P_m^Hh_{\mathrm{init}}.`

Here $`P_m^H` denotes the orthogonal projection in $`H` onto $`JV_m`.
:::

:::proof "parabolic.ritz_initial_compatibility"
Lax–Milgram defines the Ritz projection $`R_mg` by
$`B(R_mg,v_m)=B(g,v_m)` for every trial vector. Evaluate the original
right-hand side at the initial time with $`u_m(a)=R_mg`. The Ritz
identity replaces the form term by $`B(g,v_m)`, and compatibility leaves
$`(J\widetilde u_m(a),Jv_m)_H=(h_{\mathrm{init}},Jv_m)_H`. This is precisely the
characterizing equation for the pivot-orthogonal projection of
$`h_{\mathrm{init}}` onto $`JV_m`.
:::

With both families constructed, the limit must retain their
finite-dimensional relation. The formal proof extracts a weakly convergent
ultrafilter for the state, then refines that same filter for the velocity
and differentiated state. All three limits therefore see the identity
$`J\widetilde u_m=\partial_t(Ju_m)`, which yields $`Jv=\partial_t(Ju)`.
The differentiated load is only assumed square integrable, so its energy
estimate depends on its $`L^2` norm alone.

:::theorem "parabolic.paired_l2_differentiation" (parent := "parabolic.regularity") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.exists_of_paired_l2_differentiated_galerkin_families") (uses := "parabolic.improved_time_regularity, parabolic.differentiated_galerkin_construction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a bounded autonomous coercive form $`B`, suppose the original and
differentiated Galerkin families are supplied with initial pivot data
converging in $`H` and uniformly bounded there, a uniform $`L^2(H)`
velocity bound, and the Bochner identity
$`J\widetilde u_m=\partial_t(Ju_m)`. Assume the supplied original family
also carries its common integrated Galerkin energy bound. Both dual-valued
loads $`\ell,\dot\ell` must lie in $`L^2(a,b;V^*)`.

One common weak compactness filter identifies the differentiated state with
the time derivative of the original limit and gives

$$`u_{tt}=\dot\ell-Bu_t\in L^2(a,b;V^*).`

For a pivot load with $`f_t\in L^2(a,b;H)`, take
$`\dot\ell=J^*f_t`. The second derivative is dual-valued, while the
identified first derivative belongs to $`L^2(a,b;V)`.
:::

:::proof "parabolic.paired_l2_differentiation"
Apply the coercive energy estimate directly to each supplied
differentiated family, using the $`L^2(V^*)` norm of its load. Extract
common weak limits for the original state, its pivot velocity, and the
differentiated state. Testing their Bochner identity with bounded linear
functionals identifies the two limits for the first derivative. Passing
the differentiated weak equation to the limit gives
$`u_{tt}=\dot\ell-Bu_t`; boundedness of $`B:V\to V^*` puts this residual
in $`L^2(V^*)`.
:::

Combining the Ritz initialization with the paired limit removes the
differentiated family from the hypotheses. Given the original
Ritz-initialized family and the uniform velocity bound of the first stage,
the theorem constructs the differentiated approximations, their initial
values, and the bounds that the paired compactness theorem requires; the
compatibility identity is stated once, for the ambient datum $`g` and the
residual $`h_{\mathrm{init}}`. This closes the second stage.

:::theorem "parabolic.ritz_l2_differentiation" (parent := "parabolic.regularity") (lean := "PDE.Analysis.Evolution.IsGelfandIntegratedWeakSolution.exists_of_autonomous_ritz_l2_galerkin_families") (uses := "parabolic.paired_l2_differentiation, parabolic.ritz_initial_compatibility")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a bounded autonomous coercive form $`B`, take an absolutely continuous
load with $`L^2(V^*)` derivative and a pivot-valued initial compatibility
residual as in {bpref "parabolic.ritz_initial_compatibility"}[]. Initialize the
supplied original Galerkin family, with its common integrated energy bound, by
Ritz projections of $`g` and assume
its uniform $`L^2(H)` velocity bound. The Ritz variational identity converts
the compatibility condition at the initial time into the exact pivot projection
of the initial velocity. The paired $`L^2` compactness theorem then constructs
the original solution and its differentiated trajectory on one common limit,
with

$$`Ju_t=\partial_t(Ju),\qquad
u_{tt}=\dot\ell-Bu_t\in L^2(a,b;V^*).`

In the pivot-forcing specialization, $`\dot\ell=J^*f_t` with
$`f_t\in L^2(a,b;H)` supplies the differentiated load bound.
Its pointwise size need not be bounded.
:::

:::proof "parabolic.ritz_l2_differentiation"
Initialize each original Galerkin trajectory with the Ritz projection of
$`g`. Ritz compatibility turns the assumed initial residual into a uniformly
controlled pivot projection, which is valid initial data for the
differentiated Galerkin system. Apply the paired $`L^2` theorem to these two
families. Its common limit identifies the pivot derivative of $`Ju` with
$`Ju_t` and passes the differentiated equation to
$`u_{tt}=\dot\ell-Bu_t`.
:::

The third stage is spatial and, at first, entirely static. Once
$`u_t(t)\in L^2(\Omega)` is known at a fixed time, the parabolic equation at
that time is an elliptic Dirichlet problem for $`u(t)` with right-hand side
$`f(t)-u_t(t)\in L^2(\Omega)`, and the question becomes global elliptic
$`H^2` regularity for the principal part. No time regularity beyond the
pivot-valued derivative is used.

:::theorem "parabolic.spatial_h2_order_one" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.exists_spatial_h2_of_weak_residual_identity") (uses := "parabolic.divergence_form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At a time where $`u(t)\in H_0^1(\Omega)`, $`f(t),u_t(t)\in L^2(\Omega)`, and
the weak residual identity holds, rewrite the parabolic equation as

$$`-\partial_i(a^{ij}\partial_j u(t))=f(t)-u_t(t).`

On a domain equipped with a twice differentiable boundary atlas, assume the
principal coefficients belong to $`W^{1,\infty}(\Omega)` and have global
$`C^1` representatives that are uniformly elliptic on $`\Omega`.
Elliptic regularity then gives an $`H^2(\Omega)` representative with the
same spatial value class as the time slice. The atlas is a hypothesis. For
a bounded open set with $`C^2` graph boundary,
the graph-boundary atlas construction provides one.
:::

:::proof "parabolic.spatial_h2_order_one"
Move the pivot time-derivative term to the forcing side of the weak equation.
The resulting identity is exactly the elliptic Dirichlet weak problem with
right-hand side $`f(t)-u_t(t)\in L^2(\Omega)`. Apply the global
$`H^2` regularity theorem for the operational $`C^2` atlas and the
coefficient hypotheses of the statement. That theorem returns an $`H^2` element whose
order-zero representative agrees almost everywhere with the original
$`H^1_0` time slice.
:::

Applying the slice theorem at almost every time gives a family of $`H^2`
representatives, but a family of slices is not yet an element of
$`L^2(a,b;H^2(\Omega))`. Measurability in time comes from applying the
bounded elliptic solution operator to the Bochner class $`f-u_t`, so that
the lift is the composition of a continuous linear map with a measurable
trajectory rather than an arbitrary choice at each time.

:::theorem "parabolic.spatial_h2_bochner" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.exists_spatial_h2_lp_of_ae_weak_residual_identity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Retain the domain and coefficient hypotheses of the slice theorem.
If $`u\in L^2(a,b;H^1_0(\Omega))`, the weak evolution identity holds almost
everywhere, and $`f,u_t\in L^2(a,b;L^2(\Omega))`, there is a canonical
Bochner lift

$$`U_2\in L^2(a,b;H^2(\Omega))`

whose canonical restriction to $`H^1(\Omega)` agrees almost everywhere with
$`u`. It satisfies the integrated elliptic estimate

$$`\lVert U_2\rVert_{L^2_tH^2_x}\leq \lVert \mathcal{S}_{H^2}\rVert\lVert f-u_t\rVert_{L^2_tL^2_x},`

where $`\mathcal{S}_{H^2}` is the bounded global elliptic solution operator.
:::

:::proof "parabolic.spatial_h2_bochner" (uses := "parabolic.spatial_h2_order_one")
Apply the bounded elliptic $`H^2` solution operator to the measurable residual
`f-u_t`. Its $`H^1` restriction agrees almost everywhere with the weak solution
by elliptic uniqueness, and the operator norm gives the integrated estimate.
:::

The first and third stages combine as soon as the time derivative is placed
on the forcing side of the equation. For an autonomous symmetric principal
operator, the weak solution comes with $`u_t\in L^2(a,b;L^2(\Omega))` and an
almost-everywhere residual identity, which is exactly the hypothesis of the
Bochner lift; the second stage is not needed at this level of regularity.

:::theorem "parabolic.autonomous_h2_bootstrap" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.exists_autonomous_symmetric_solution_with_spatial_h2") (uses := "parabolic.divergence_weak_solution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For autonomous symmetric uniformly elliptic principal coefficients in
$`W^{1,\infty}(\Omega)` with global $`C^1` representatives, on a domain
carrying the twice differentiable boundary atlas, forcing in
$`L^2(a,b;L^2(\Omega))`, and initial data in $`H_0^1(\Omega)`, there exist

$$`u\in L^\infty(a,b;H_0^1(\Omega)),\qquad
u_t\in L^2(a,b;L^2(\Omega)),\qquad
U_2\in L^2(a,b;H^2(\Omega)).`

The theorem simultaneously returns the integrated weak equation, the
almost-everywhere pivot-valued residual, the identification of $`U_2` with
$`u`, and quantitative bounds for both $`u_t` and $`U_2`. The abstract
Galerkin theorem also records the explicit almost-everywhere energy-space
norm bound used to obtain the $`L^\infty` membership.
:::

:::proof "parabolic.autonomous_h2_bootstrap" (uses := "parabolic.improved_time_regularity, parabolic.spatial_h2_bochner")
Construct the autonomous weak solution with the improved pivot-valued time
derivative, rewrite the equation at almost every time as an elliptic problem,
and apply the Bochner-valued spatial $`H^2` lift to $`f-u_t`.
:::

The bootstrap bounds $`U_2` by $`f-u_t`, so a solution quantity still
appears on the right. Obtaining bounds in terms of the data alone means
feeding the first-stage velocity bound,
which involves only $`u_0`, $`f`, and the form constants, into the elliptic
estimate.

:::theorem "parabolic.spatial_h2_data_bounds" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.exists_autonomous_symmetric_solution_with_spatial_h2_data_bounds") (uses := "parabolic.autonomous_h2_bootstrap")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the hypotheses of {bpref "parabolic.autonomous_h2_bootstrap"}[], let $`M\geq0` bound
the form and let $`C>0` be a coercivity constant. Set

$$`Q=M\|u_0\|_V^2+2\|f\|_{L^2_tH}^2.`

The constructed solution and its $`H^2` lift satisfy

$$`
\operatorname*{ess\,sup}_{t\in(a,b)}\|u(t)\|_V\leq\sqrt{Q/C},
\qquad
\|u_t\|_{L^2_tH}\leq\sqrt Q,
`

$$`\|U_2\|_{L^2_tH^2_x}
\leq\|\mathcal S_{H^2}\|\bigl(\|f\|_{L^2_tH}+\sqrt Q\bigr).`

These are data-only bounds for the principal-part problem.
Once the domain, coefficients, and interval are
fixed, their right-hand sides contain only the initial datum and forcing.
:::

:::proof "parabolic.spatial_h2_data_bounds"
The improved Galerkin estimate bounds both the essential supremum of the
principal energy and $`\|u_t\|_{L^2(H)}` solely by the initial energy,
$`\|f\|_{L^2(H)}`, and the form constants $`M,C`. The elliptic solution
operator applied to $`f-u_t` gives
$`\|u\|_{L^2(H^2)}\leq
\|\mathcal S_{H^2}\|(\|f\|_{L^2(H)}+\|u_t\|_{L^2(H)})`. Substituting the
first data-only estimate into this inequality removes every solution
quantity from the right-hand sides.
:::

Stronger data give one more derivative in each direction, and here the
second stage enters. With
$`u_0\in H^2(\Omega)\cap H_0^1(\Omega)` and $`f\in H^1(a,b;L^2(\Omega))`,
the Ritz-initialized paired construction identifies the differentiated
trajectory with $`u_t`, which therefore inherits an
$`L^\infty(L^2)\cap L^2(H_0^1)` bound and a weak time derivative
$`u_{tt}\in L^2(a,b;H^{-1}(\Omega))`. Since $`u_t(t)` is now essentially
bounded in $`L^2(\Omega)`, the elliptic slice estimate upgrades the
$`L^2(a,b;H^2(\Omega))` lift to $`L^\infty(a,b;H^2(\Omega))`.

:::theorem "parabolic.improved_spatial_regularity" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.exists_weak_solution_with_higher_regularity_estimates") (uses := "parabolic.autonomous_h2_bootstrap, parabolic.ritz_l2_differentiation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Retain the operational domain and autonomous symmetric uniformly elliptic
$`W^{1,\infty}` coefficient hypotheses, including the global $`C^1`
representatives. For initial data in $`H^2(\Omega)\cap H_0^1(\Omega)` and forcing in
$`H^1(a,b;L^2(\Omega))`, the paired Ritz–Galerkin construction identifies
the differentiated trajectory with the weak time derivative of the original
trajectory. Combining the differentiated energy and elliptic estimates gives

$$`u\in L^\infty(a,b;H^2(\Omega)),`

$$`u_t\in L^\infty(a,b;L^2(\Omega))
\cap L^2(a,b;H_0^1(\Omega)),`

and

$$`u_{tt}\in L^2(a,b;H^{-1}(\Omega)).`

The assumed time-Sobolev regularity
$`f\in H^1(a,b;L^2(\Omega))` supplies its own
$`L^\infty(a,b;L^2(\Omega))` bound through the closed-interval
Lions–Magenes representative; no separate pointwise forcing bound is an
input. More precisely, the constructed representative satisfies

$$`
\|f(t)\|_{L^2}\leq
\left(
\frac{\|f\|_{L^2_tL^2_x}^2}{b-a}
+2\|f\|_{L^2_tL^2_x}\|f_t\|_{L^2_tL^2_x}
\right)^{1/2}
`

on the closed interval, and the original Bochner trajectory satisfies the
same estimate almost everywhere.

The estimate theorem records data-dependent bounds for the
$`L^\infty_tL^2_x`, $`L^2_tH_0^1`, $`L^2_tH^{-1}_x`, and
$`L^\infty_tH^2_x` components displayed, including the quantitative bound for
$`u_{tt}`. The estimates control the second time derivative in
$`H^{-1}(\Omega)`.
:::

:::proof "parabolic.improved_spatial_regularity" (uses := "parabolic.improved_time_regularity, parabolic.spatial_h2_bochner")
The proof has four steps.

*Step 1: Differentiated energy.* The forcing hypothesis
$`f\in H^1(a,b;L^2(\Omega))` implies $`f_t\in L^2(a,b;L^2(\Omega))`. The
Ritz-compatible initial data give a differentiated Galerkin family whose
energy estimate bounds $`\|u_t\|_{L^\infty(L^2)}` and
$`\|\nabla u_t\|_{L^2(L^2)}` by the initial compatibility residual and
$`\|f_t\|_{L^2(L^2)}`.

*Step 2: Derivative identification.* The paired compactness theorem
extracts a common weak limit for both the original and differentiated
Galerkin families. The finite-dimensional identity
$`J\widetilde u_m=\partial_t(Ju_m)` passes to the limit, proving that the
differentiated weak solution *is* the time derivative of the original rather
than an independently selected function.

*Step 3: Second time derivative.* From the weak equation
$`J^*u_t+Au=J^*f` (almost everywhere in time), differentiate in time:
$`u_{tt}=J^*f_t-Au_t`. Since $`A:V\to V^*` is bounded and
$`u_t\in L^2(V)`, this gives $`u_{tt}\in L^2(V^*)=L^2(H^{-1})`.

*Step 4: Spatial bootstrap.* At almost every time, $`u_t(t)\in L^2` and
the equation gives $`-\nabla\cdot(A\nabla u(t))=f(t)-u_t(t)\in L^2`.
The elliptic $`H^2` theorem uses the operational $`C^2` atlas and the
$`W^{1,\infty}` coefficients with global $`C^1` representatives. It lifts
$`u(t)` to $`H^2(\Omega)`. The differentiated energy estimate bounds
$`u_t` in $`L^\infty(L^2)`, and the time-Sobolev representative bounds
$`f` in the same space. Their difference is therefore essentially bounded
in $`L^2`; applying the bounded elliptic solution operator gives
$`u\in L^\infty(H^2)` (Evans, 2010, §7.1.3).
:::

# Regularity of Every Order

The preceding estimates give finite-order regularity. Evans's §7.1.3
continues by induction: if the data are smoother and satisfy more
compatibility conditions, every weak solution has more derivatives in both
time and space, and with smooth data it is smooth up to the boundary.
{bpref "parabolic.all_order_regularity"}[] and
{bpref "parabolic.smooth_classical_solution"}[] carry this out for the full
operator

$$`Lu=-\sum_{i,j}D_i\bigl(a^{ij}D_ju\bigr)+\sum_ib^iD_iu+cu`

on a bounded open set $`\Omega\subset\mathbb R^n`, $`n\geq1`, with a
$`C^r` graph boundary for every $`r`. The coefficients $`a^{ij}`, $`b^i`, $`c`
are $`C^r` up to the boundary for every $`r`, the matrix $`(a^{ij})` is
symmetric on $`\Omega` with ellipticity constant $`\alpha>0`, and none of
them depends on time.

The compatibility conditions come from the equation itself. If $`u` is
smooth, then $`u_t=f-Lu`, and differentiating in time gives the initial
values of all time derivatives in terms of the data alone:

$$`g_0=g,\qquad g_{k+1}=\partial_t^kf(\cdot,a)-Lg_k.`

Since $`u` vanishes on the lateral boundary for all times, so does each
$`\partial_t^ku`, and therefore each $`g_k` must vanish on $`\partial\Omega`.
This recurrence computes $`g_k` directly from $`f` and $`g`.

:::theorem "parabolic.all_order_regularity" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.exists_all_order_regularity, PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.exists_all_order_regularity_of_finite_family") (uses := "parabolic.improved_spatial_regularity, elliptic.solution_operator.all_orders_estimate")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix $`m\geq0`. There is a constant $`C>0`, depending on $`m`, $`\Omega`,
$`[a,b]` and the coefficients, with the following property. Let

$$`\partial_t^kf\in L^2(a,b;H^{2m-2k}(\Omega))\qquad(0\leq k\leq m),`

where each derivative is the weak time derivative of the previous one, let
$`g\in H^{2m+1}(\Omega)`, and suppose that $`g_0,\dots,g_m` all lie in
$`H_0^1(\Omega)`. Then every weak solution $`u` of $`u_t+Lu=f` in
$`\Omega\times(a,b)` with $`u=0` on the lateral boundary and $`u(a)=g`
satisfies

$$`\partial_t^ku\in L^2(a,b;H^{2m+2-2k}(\Omega))\qquad(0\leq k\leq m+1),`

again with each derivative the weak time derivative of the previous one, and

$$`\sum_{k=0}^{m+1}\bigl\|\partial_t^ku\bigr\|_{L^2(H^{2m+2-2k})}
\leq C\Bigl(\|g\|_{H^{2m+1}}+\sum_{k=0}^m\bigl\|\partial_t^kf\bigr\|_{L^2(H^{2m-2k})}\Bigr).`
:::

:::proof "parabolic.all_order_regularity" (uses := "parabolic.improved_spatial_regularity, elliptic.solution_operator.all_orders_estimate")
The proof is by induction on $`m`. For $`m=0` it is the $`H^2` theorem for
the full operator: $`u\in L^2(H^2)` and $`u_t\in L^2(L^2)`.

For the step from $`m` to $`m+1`, let $`v` be the weak solution with forcing
$`f_t` and initial value $`g_1=f(a)-Lg`. The data of $`v` satisfy the
hypotheses at order $`m`, with the compatibility conditions shifted by one,
so the induction hypothesis gives $`v` its derivatives. The primitive
$`g+\int_a^tv\,ds` solves the original problem, so uniqueness of weak
solutions identifies it with $`u`, and $`v=u_t`. At almost every time the
equation then reads $`Lu(t)=f(t)-u_t(t)`, whose right side lies in
$`H^{2m+2}`, and the elliptic estimate of every order lifts $`u(t)` to
$`H^{2m+4}`. The norms combine into the stated bound, with the trace constant
for $`f(a)` and the operator norm of $`L` entering $`C`.

The induction works with weak solutions only. After the base case no
Galerkin approximation is differentiated: the order-$`m` theorem is applied
to the data $`(f_t,g_1)` directly, and the identification $`v=u_t` comes
from uniqueness.
:::

The forcing derivatives $`(\partial_t^kf)_k` and the corresponding solution
derivatives are linked by weak time derivatives.

Smooth data give a smooth solution. The derivative jets of every order
place each $`\partial_t^ku` in $`L^2(a,b;H^s(\Omega))` for every $`s`, and the
Sobolev embedding in space and time gives a single function that is smooth
up to the boundary of the cylinder.

:::theorem "parabolic.smooth_classical_solution" (parent := "parabolic.regularity") (lean := "PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth.exists_unique_classical_solution_with_bounds") (uses := "parabolic.all_order_regularity, elliptic.regularity.smooth_boundary")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§7.1.3"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the standing hypotheses on $`\Omega` and $`L`, there are constants
$`C_m>0`, $`m\geq0`, chosen before the data, with the following property.
Let $`f` be $`C^k` up to the boundary of $`\Omega\times(a,b)` for every $`k`,
let $`g` be $`C^r` up to the boundary of $`\Omega` for every $`r` and
continuous on $`\overline\Omega`, and suppose that every $`g_k` vanishes on
$`\partial\Omega`. Then there is a function $`U` with these properties.

1. $`U` is continuous on $`\overline\Omega\times[a,b]` and $`C^k` up to the
   boundary of $`\Omega\times(a,b)` for every $`k`. It satisfies
   $`U_t+LU=f` in $`\Omega\times(a,b)`, $`U(\cdot,a)=g` on $`\overline\Omega`,
   and $`U=0` on $`\partial\Omega\times[a,b]`.
2. For every $`m`, the Sobolev norms of its time derivatives obey the bound of
   {bpref "parabolic.all_order_regularity"}[] with constant $`C_m`.
3. $`\partial_t^kU(\cdot,a)=g_k` on $`\overline\Omega` for every $`k`.
4. If $`f` is continuous on the closed cylinder, the equation holds on
   $`\Omega\times[a,b]`, end times included.
5. Every other function with the properties in item 1 equals $`U` on
   $`\overline\Omega\times[a,b]`.
6. Every weak solution with data $`(f,g)` agrees with $`U` almost everywhere.
:::

:::proof "parabolic.smooth_classical_solution" (uses := "parabolic.all_order_regularity, parabolic.divergence_existence_energy")
The Galerkin theorem supplies a weak solution $`u`, and smooth data satisfy
the hypotheses of {bpref "parabolic.all_order_regularity"}[] at every order.
For fixed orders $`s` and $`d`, the jets place $`u,\dots,\partial_t^du` in one
common space $`L^2(a,b;H^s(\Omega))` with weak time derivatives between
consecutive entries. A function whose time derivatives up to order $`d` lie in
$`L^2(H^s)` with $`s` large has a representative that is $`C^k` in space and
time up to the boundary. The representatives for different choices agree,
which gives a single $`U`. It satisfies the equation, the initial condition
and the lateral condition pointwise, because it agrees with the weak solution
almost everywhere and all three sides are continuous.

For uniqueness, a classical solution with data $`(f,g)` is also a weak
solution with these data. Weak solutions are unique by the energy estimate
with the Gårding shift, so every classical solution agrees with $`u` almost
everywhere, which gives item 6, and by continuity two classical solutions
agree on the closed cylinder, end times included.
:::
