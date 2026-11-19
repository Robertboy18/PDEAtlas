/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.Representations.Separation
import PDE.Hyperbolic.ConservationLaw.Burgers.Similarity
import PDE.Hyperbolic.Models.Transport.TravelingWave
import PDE.Hyperbolic.Models.KdV.Soliton
import PDE.Parabolic.Heat.Kernel.Scaling
import PDE.Parabolic.PorousMedium.InitialTrace
import PDE.Parabolic.PorousMedium.WeakSolution
import PDE.Representations.Similarity.Calculus
import PDE.Representations.Similarity.Dynamic
import PDE.Solution.Singularity.FiniteTime.Norm.Similarity

/-!
# Traveling waves and similarity

Pointwise traveling-wave and self-similar ansatzes, their chain rules, and
heat-kernel, KdV, Barenblatt, and Burgers examples.
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
#doc (Manual) "Traveling Waves and Similarity" =>

A traveling wave is the simplest change of independent variables: the single
coordinate $`x-ct` follows a profile moving at constant speed $`c`, so any
equation the profile satisfies is an ordinary differential equation in that
coordinate. The construction imposes no equation by itself; it is a total
function of the profile and the speed, with time in coordinate $`0` and
space in coordinate $`1` of $`\mathbb R^2`.

:::definition "methods.similarity.traveling" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.travelingWave1D")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "176-185"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The traveling-wave construction sends a profile $`f` and speed $`c` to

$$`
u(t,x)=f(x-ct).
`
:::

Differentiating $`f(x-ct)` in $`t` and in $`x` produces the same
$`f'(x-ct)` with factors $`-c` and $`1`, so the traveling ansatz is exactly
adapted to the transport operator $`\partial_t+c\,\partial_x`. The
conclusion is a pointwise identity between totalized partial derivatives on
$`\mathbb R^2`.

:::theorem "methods.similarity.traveling.transport" (parent := "methods.representations") (lean := "TransportEquation.traveling_wave_1d_satisfies_transport") (uses := "methods.similarity.traveling")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "176-185"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every differentiable traveling-wave profile satisfies the one-dimensional
transport equation $`u_t+c u_x=0`.
:::

:::proof "methods.similarity.traveling.transport"
Apply the chain rule to $`u(t,x)=f(x-ct)`. It gives
$`u_t=-c f'(x-ct)` and $`u_x=f'(x-ct)`. Therefore
$`u_t+c u_x=(-c+c)f'(x-ct)=0`.
:::

# A localized nonlinear wave

Transport carries any differentiable profile at the prescribed speed. The
KdV equation imposes an equation on the profile itself:

$$`u_t+a u u_x+b u_{xxx}=0,\qquad
bU'''-cU'+aUU'=0\quad\text{for }u(t,x)=U(x-ct-x_0).`

The nonlinear steepening and third-order dispersion can balance in a
localized pulse. We construct that pulse and verify the original PDE, not
only the profile equation.

:::theorem "methods.similarity.kdv_soliton" (parent := "methods.representations") (uses := "methods.similarity.traveling") (lean := "KdVEquation.soliton_satisfies_kdv, KdVEquation.soliton_isSolution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.2.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`a\ne0`, $`b>0`, $`c>0`, and $`x_0\in\mathbb R`, the smooth field

$$`u(t,x)=\frac{3c}{a}\operatorname{sech}^2
\left(\frac{\sqrt{c/b}}{2}(x-ct-x_0)\right)`

solves $`u_t+a u u_x+b u_{xxx}=0` at every spacetime point.
Its profile tends to zero at both spatial infinities. The center value is
$`3c/a`, positive when $`a>0`. Thus the coefficient convention matters:
$`a=b=1` gives center value $`3c`, whereas $`a=6`, $`b=1` gives $`c/2`.
:::

:::proof "methods.similarity.kdv_soliton"
Put $`U(z)=A\operatorname{sech}^2(kz)`. Direct differentiation gives
$`U''=4k^2U-(6k^2/A)U^2`. With
$`A=3c/a` and $`k=\sqrt{c/b}/2`, the identities
$`c=4bk^2` and $`aA=12bk^2` give
$`bU''-cU+(a/2)U^2=0`. Differentiate this identity once and apply the
traveling-wave chain rule to obtain the KdV residual. Positivity of
$`b,c` makes $`k>0`, so decay of the hyperbolic secant gives localization.
:::

# Dilation instead of translation

Self-similarity replaces translation by dilation. Where a traveling wave is
invariant under $`(t,x)\mapsto(t+s,x+cs)`, a self-similar field is invariant
up to the amplitude factor $`\mu^\alpha` under the scaling
$`(t,x-x_0)\mapsto(\mu t,\mu^\beta(x-x_0))`, and its profile $`f` depends
only on the invariant combination $`t^{-\beta}(x-x_0)`.

:::definition "methods.similarity.scaling" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.forwardSelfSimilarAnsatz")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "185-187"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The forward self-similar ansatz is

$$`
u(t,x)=t^\alpha
f\!\left(t^{-\beta}(x-x_0)\right).
`

The function is total in Lean; analytic theorems state domains such as
$`t>0` explicitly.
:::

Every similarity reduction rests on one time derivative. The amplitude
$`t^\alpha` contributes $`\alpha t^{\alpha-1}F`, and the moving coordinate
$`y=t^{-\beta}(x-x_0)` has velocity $`-\beta y/t`, contributing
$`-\beta t^{\alpha-1}DF(y)y`. The combination $`\alpha F-\beta DF(y)y` is the
infinitesimal generator of the scaling, and it is what a model equation later
sets equal to the spatial terms.

:::theorem "methods.similarity.forward_chain_rule" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.hasDerivAt_scaled_profile_ansatz, PDE.Representations.Similarity.hasDerivAt_forward_self_similar_ansatz") (uses := "methods.similarity.scaling")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "185-186"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The time derivative of a scaled profile splits into the derivative of its
amplitude and the derivative of its moving similarity coordinate. In
particular, for positive time the forward ansatz satisfies the generator
identity

$$`
\frac{d}{dt}\left[t^\alpha F\!\left(t^{-\beta}(x-x_0)\right)\right]
=t^{\alpha-1}\left(\alpha F(y)-\beta DF(y)y\right),
\qquad y=t^{-\beta}(x-x_0).
`

The theorem is vector-valued and assumes differentiability only at the
similarity point used in the calculation.
:::

:::proof "methods.similarity.forward_chain_rule"
Differentiate the amplitude $`t^\alpha` and the similarity coordinate
$`y(t)=t^{-\beta}(x-x_0)` separately. The power rule gives
$`(t^\alpha)'=\alpha t^{\alpha-1}` and
$`y'=-\beta t^{-1}y`. The product and Fréchet chain rules then give
$`\alpha t^{\alpha-1}F(y)-\beta t^{\alpha-1}DF(y)y`, which is the stated
generator formula.
:::

Spatial derivatives are simpler, because at fixed $`t` the dilation
$`x\mapsto L(t)(x-x_0)` is affine with derivative $`L(t)I`, and the amplitude
$`A(t)` passes through as a constant. For the forward ansatz,
$`A=t^\alpha` and $`L=t^{-\beta}`; these factors account for the powers
of $`t` in a reduced profile equation.

:::theorem "methods.similarity.spatial_chain_rules" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.gradient_scaled_profile_ansatz, PDE.Representations.Similarity.divergence_smul_comp_centered_dilation, PDE.Representations.Similarity.laplacian_scaled_profile_ansatz") (uses := "methods.similarity.scaling")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "185-186"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Centered dilation contributes one spatial-scale factor to a gradient or
divergence and two factors to a Laplacian. Thus a scalar ansatz with
amplitude $`A(t)` and spatial scale $`L(t)` obeys

$$`
\nabla_x u=A(t)L(t)\nabla F(y),\qquad
\Delta_x u=A(t)L(t)^2\Delta F(y).
`

The gradient identity requires differentiability of $`F` at $`y`; the
divergence identity requires differentiability of each vector-field component
there. The Laplacian identity holds without assuming $`F\in C^2(\mathbb R^n)`.
No time regularity of $`A` or $`L` is needed for these fixed-time identities.
:::

:::proof "methods.similarity.spatial_chain_rules"
At fixed time, the map $`x\mapsto y=L(t)(x-x_0)` has derivative
$`L(t)I`. The Euclidean chain rule therefore contributes one factor of
$`L(t)` to each first spatial derivative and leaves the scalar amplitude
$`A(t)` unchanged. For the Laplacian, translation commutes with each partial
derivative and the dilation contributes $`L(t)^2`, for any profile; the divergence identity
is the same coordinate calculation componentwise.
:::

The forward and backward ansatzes prescribe their scales as fixed powers of
time. Dynamically rescaled formulations, such as the Chen–Hou treatment of
the Boussinesq equations, leave the amplitude $`A(\tau)`, the spatial scale
$`L(\tau)`, and the physical time $`t(\tau)` as unknown functions of a new
time $`\tau`, to be fixed by normalization conditions rather than by
exponents.

:::definition "methods.similarity.dynamic_pullback" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.dynamicPullback") (uses := "methods.similarity.scaling")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1, equations (2.4)–(2.7)"
    text := some {
      path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 14, endLine := 26
    }
  }]
}
%%%
For time-dependent amplitude $`A(\tau)`, spatial scale $`L(\tau)`, physical
time $`t(\tau)`, and a field $`f`, the dynamic pullback is

$$`
\widetilde f(x,\tau)=A(\tau)f(L(\tau)x,t(\tau)).
`

The construction is purely kinematic: no PDE and no law for the three scale
functions enters.
:::

With three time-dependent scales, the $`\tau` derivative of the pullback has
three contributions: the amplitude term $`A'f`, the physical-time term
$`A\,t'\,\partial_tf`, and the moving-coordinate term $`A\,Df[L'x]`. The
last is where the dilation velocity $`L'x` enters, and it is what produces
the $`x\cdot\nabla` advection terms of a rescaled equation.

:::theorem "methods.similarity.dynamic_chain_rule" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.hasDerivAt_dynamicPullback, PDE.Representations.Similarity.hasDerivAt_dynamicPullback_expanded, PDE.Representations.Similarity.advectiveDerivative_smul_id_dynamicPullback") (uses := "methods.similarity.dynamic_pullback, methods.similarity.spatial_chain_rules")
%%%
source := {
  document := "chen-hou-boussinesq"
  spans := #[{
    page := "Section 2.1, equations (2.4)–(2.7)"
    text := some {
      path := "Blueprint/Sources/ChenHouBoussinesq.md", startLine := 14, endLine := 26
    }
  }]
}
%%%
Assume the three scale functions are differentiable at $`\tau` and $`f` is
jointly differentiable at $`(L(\tau)x,t(\tau))`. The time derivative
splits into amplitude, physical-time, and moving-coordinate terms:

$$`
\partial_\tau\widetilde f
=A'f+A\bigl(t'\partial_t f+Df[L'x]\bigr).
`

The companion spatial theorem states that advection by $`a x` contributes
$`A L\,Df[a x]`. These two identities are the chain rules behind the
dynamically rescaled Boussinesq equations.
:::

:::proof "methods.similarity.dynamic_chain_rule"
Differentiate the scalar amplitude and the space-time composition separately.
The derivative of $`(L(\tau)x,t(\tau))` is $`(L'(\tau)x,t'(\tau))`; applying
the Fréchet chain rule and then the product rule gives the displayed formula.
At fixed time, differentiating $`x\mapsto A f(Lx,t)` in the direction $`a x`
gives $`A\,Df[L(a x)]`, which is $`A L\,Df[a x]` by linearity.
:::

The heat kernel is the model forward self-similar field, with amplitude
exponent $`\alpha=-n/2` and spatial exponent $`\beta=1/2`: the exponent
$`-\|x\|^2/(4t)` depends on $`x/\sqrt t` alone, and the prefactor
$`(4\pi t)^{-n/2}` is the amplitude. The scaling law is the finite form of
that invariance, stated directly for the Lean kernel rather than derived
from the chain rules.

:::theorem "methods.similarity.heat_kernel_scaling" (parent := "methods.representations") (lean := "HeatEquation.fundamentalSolutionHeat_scaling") (uses := "methods.similarity.scaling, parabolic.heat_kernel")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "47-49"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "185-186"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
For $`a>0` and $`t>0`, the Euclidean heat kernel obeys the exact parabolic
scaling law

$$`
\Gamma_n(ax,a^2t)=a^{-n}\Gamma_n(x,t).
`

Positivity excludes the totalized nonpositive-time branch and removes every
ambiguity in the real powers.
:::

:::proof "methods.similarity.heat_kernel_scaling"
Insert $`ax` and $`a^2t` into
$`\Gamma_n(x,t)=(4\pi t)^{-n/2}\exp(-\|x\|^2/(4t))`. The quotient in the
exponent is unchanged because both $`\|ax\|^2` and the time denominator gain
$`a^2`. Positivity of $`a` lets the prefactor simplify as
$`(a^2)^{-n/2}=a^{-n}`, yielding the stated scaling law.
:::

# A nonlinear density with a free boundary

For slow porous-medium diffusion $`u_t=\Delta(u^m)`, $`m>1`, mass
preservation and diffusion balance fix the exponents

$$`\beta=\frac1{n(m-1)+2},\qquad \alpha=n\beta,\qquad
k=\frac{(m-1)\beta}{2m}.`

The Barenblatt profile $`F_C(y)=(C-k|y|^2)_+^{1/(m-1)}` is compactly
supported. Its edge moves as the profile dilates. This makes a pointwise
calculation inside the positivity region insufficient: the weak equation
must also cross the moving edge.

:::theorem "methods.similarity.barenblatt" (parent := "methods.representations") (uses := "methods.similarity.scaling") (lean := "PorousMedium.barenblatt_weak_pde_deriv_gradient, PorousMedium.integral_barenblatt_prescribed_mass, PorousMedium.tendsto_barenblatt_prescribed_dirac")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§4.2.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`m>1` and $`M>0`. There is an explicit $`C>0` such that

$$`u(t,x)=t^{-\alpha}F_C(t^{-\beta}x),\qquad t>0,\ x\in\mathbb R^n,`

has mass $`M` at every positive time and solves the weak porous-medium
equation through its free boundary. For every $`0<a\le b` and every
$`C^1` spacetime test $`\psi`,

$$`\int_a^b\int_{\mathbb R^n}
\bigl(u\psi_t-\nabla(u^m)\cdot\nabla\psi\bigr)\,dx\,dt
=\int_{\mathbb R^n}u(b,x)\psi(b,x)\,dx
-\int_{\mathbb R^n}u(a,x)\psi(a,x)\,dx.`

For every bounded continuous $`\varphi`,

$$`\lim_{t\downarrow0}\int_{\mathbb R^n}u(t,x)\varphi(x)\,dx=M\varphi(0).`

This is the prescribed Dirac initial trace $`M\delta_0` of the explicit
solution.
:::

:::proof "methods.similarity.barenblatt"
The potential $`u^m` is $`C^1` across the edge and its actual gradient is
$`\nabla(u^m)=-(\beta/t)xu`. Under $`x=t^\beta y`, the identity
$`\alpha=n\beta` cancels the Jacobian against the amplitude. The test
pairing becomes $`\int F_C(y)\psi(t,t^\beta y)\,dy`. Differentiate on this
fixed compact profile domain and use the flux identity to obtain the weak
PDE, including its time endpoints. No classical derivative of the density
at the edge is required.

The mass scales as
$`M(C)=C^{1/(m-1)+n/2}M(1)`, with $`0<M(1)<\infty`, so choosing
$`C=(M/M(1))^{1/(1/(m-1)+n/2)}` gives mass $`M`. Finally
$`t^\beta y\to0`; the integrable bound $`F_C(y)\|\varphi\|_\infty`
permits dominated convergence and gives the initial trace.
:::

# Scaling toward a finite singular time

Blow-up profiles use the time remaining to a singular time. Reverse time by
$`t\mapsto T-t` and replace the forward amplitude exponent $`\alpha` by
$`-\alpha`, so that the amplitude is $`(T-t)^{-\alpha}`. In the derivative,
the amplitude term keeps its sign because the exponent and the time direction
both flip, while the coordinate term flips once, so the generator is
$`\alpha F+\beta y\cdot\nabla F` rather than $`\alpha F-\beta DF(y)y`.

:::theorem "methods.similarity.backward_generator" (parent := "methods.representations") (lean := "PDE.Representations.Similarity.backward_power_scale_pos, PDE.Representations.Similarity.tendsto_backward_power_scale_at_top, PDE.Representations.Similarity.deriv_backward_self_similar_ansatz") (uses := "methods.similarity.forward_chain_rule, methods.similarity.spatial_chain_rules")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "185-186"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`t<T`, the backward scale $`(T-t)^{-\alpha}` is positive, and it
diverges as $`t\uparrow T` when $`\alpha>0`. If the profile is differentiable
at $`y=(T-t)^{-\beta}(x-x_0)`, differentiating the backward self-similar field
produces the common factor $`(T-t)^{-\alpha-1}` and the
scaling generator $`\alpha F+\beta y\cdot\nabla F`. This is the kinematic
identity used before a model-specific profile equation is imposed.
:::

:::proof "methods.similarity.backward_generator"
Set $`s=T-t>0`. Then $`s^{-\alpha}\to+\infty` as $`s\downarrow0` for
$`\alpha>0`. Differentiating $`s^{-\alpha}F(s^{-\beta}(x-x_0))` uses
$`s'=-1`: the two minus signs turn the amplitude contribution positive, and
the similarity-coordinate derivative contributes
$`\beta y\cdot\nabla F`. Both terms contain the common factor
$`s^{-\alpha-1}`.
:::

The generator identity concerns the reduced equation. Whether the backward
field is singular at $`T` is a separate, norm-theoretic question:
since the dilation is onto, the spatial supremum of the field at time $`t`
is $`|A(t)|` times the supremum of the profile. If the profile takes a nonzero
value, divergence of $`|A(t)|` forces divergence of the supremum norm,
whatever the spatial exponent does.

:::theorem "methods.similarity.backward_blowup" (parent := "methods.representations") (lean := "PDE.Solution.Singularity.FiniteTime.backward_self_similar_ansatz_blows_up_at, PDE.Solution.Singularity.FiniteTime.tendsto_spatial_sup_norm_backward_self_similar_ansatz_nhds_top, PDE.Solution.Singularity.FiniteTime.spatial_sup_norm_scaled_profile_ansatz, PDE.Solution.Singularity.FiniteTime.tendsto_spatial_sup_norm_scaled_profile_ansatz_nhds_top") (uses := "parabolic.blowup.self_similar_profile, parabolic.blowup.generic_solution")
Let $`u(x,t)=A(t)\,F\bigl(L(t)(x-x_0)\bigr)` be a scaled profile ansatz on a
real vector space $`V` with values in a normed space $`E`. At every time
with $`L(t)\neq0`, the extended spatial supremum of $`u` is the amplitude
times that of the profile,

$$`
S_u(t)=\operatorname{ofReal}|A(t)|
\cdot\sup_{y\in V}\operatorname{ofReal}\lVert F(y)\rVert,
`

including the case of an unbounded profile. In that case both sides are
$`+\infty` when $`A(t)\neq0`, and both are zero when $`A(t)=0`. If along
a filter of times $`L(t)\neq0` eventually and
$`\lVert A(t)F(y)\rVert\to+\infty` at one fixed similarity coordinate $`y`,
then $`S_u(t)\to+\infty` along that filter. In particular, the backward
self-similar field
$`u(x,t)=(T-t)^{-\alpha}F\bigl((T-t)^{-\beta}(x-x_0)\bigr)` with
$`\alpha>0` and a profile taking at least one nonzero value satisfies

$$`
S_u(t)\longrightarrow+\infty\qquad(t\uparrow T),
`

with no boundedness assumption on the profile. If the profile is bounded,
then the spatial supremum is also finite for every $`t<T`, so the field
satisfies `SpatialSupNormBlowsUpAt` at $`T`. The spatial exponent
$`\beta` is unrestricted: it moves the sampled point but not the amplitude.
The first two statements need only a norm and a compatible real scaling on
$`E`; the backward-field statements take $`E` to be a real normed space.
:::

:::proof "methods.similarity.backward_blowup" (uses := "methods.similarity.backward_generator, parabolic.blowup.sample_transfer")
For fixed $`t` with $`L(t)\neq0`, the centered dilation
$`x\mapsto L(t)(x-x_0)` is onto $`V`, so the supremum of
$`\lVert F(L(t)(x-x_0))\rVert` over $`x` equals the supremum of
$`\lVert F(y)\rVert` over $`y`, and the amplitude factors out of the norm
and then out of the supremum. For the sampled growth statement, follow the
moving point $`x(t)=x_0+L(t)^{-1}y`, where the ansatz equals $`A(t)F(y)`;
divergence of its norm forces divergence of the supremum. For the backward
field, the amplitude $`(T-t)^{-\alpha}` is positive for $`t<T` and tends to
$`+\infty` as $`t\uparrow T` when $`\alpha>0`, so
$`\lVert A(t)F(y)\rVert=(T-t)^{-\alpha}\lVert F(y)\rVert` diverges at any
coordinate with $`F(y)\neq0`. A global profile bound $`\lVert F(y)\rVert\le C`
gives $`S_u(t)\le\operatorname{ofReal}((T-t)^{-\alpha}C)<+\infty` for
each $`t<T`, which supplies the finite-slice condition.
:::

Not every similarity solution decays or concentrates. The Burgers
rarefaction $`x/t` has amplitude exponent $`\alpha=0` and spatial exponent
$`\beta=1`, so its amplitude neither grows nor shrinks, and the profile
$`F(\xi)=\xi` is the linear function that makes $`u_t+uu_x` vanish
identically inside the fan.

:::theorem "methods.similarity.burgers_rarefaction" (parent := "methods.representations") (lean := "BurgersEquation.Similarity.rarefaction_interior_eq_forward_self_similar_on_positive_time") (uses := "methods.similarity.scaling")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "153-156"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "185-187"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
On positive time, the smooth interior Burgers rarefaction

$$`u(t,x)=\frac{x}{t}`

is the similarity profile $`F(x/t)` with $`F(\xi)=\xi`. The positive-time
domain is explicit because the profile is singular at $`t=0`.
:::

:::proof "methods.similarity.burgers_rarefaction"
Choose amplitude exponent $`\alpha=0`, spatial exponent $`\beta=1`, center
$`x_0=0`, and profile $`F(\xi)=\xi`. The forward ansatz becomes
$`F(t^{-1}x)=x/t` whenever $`t>0`, exactly the rarefaction interior.
:::

Identifying $`x/t` as a similarity profile is a statement about its form.
That it solves Burgers is a separate statement, and the conservation form
$`u_t+\partial_x(u^2/2)=0` is the one relevant to weak solutions;
integrating the pointwise residual over a subdomain of positive time is the
first step toward the integral identities a weak solution must satisfy.

:::theorem "methods.similarity.burgers_flux_integral" (parent := "methods.representations") (lean := "BurgersEquation.Similarity.rarefaction_interior_flux_residual_integral_eq_zero") (uses := "methods.similarity.burgers_rarefaction")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "153-156"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "185-187"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
For every subdomain of positive spacetime, the conservation-law residual

$$`u_t+\partial_x\!\left(\frac{u^2}{2}\right)`

of the smooth rarefaction interior integrates to zero. The theorem combines
the ordinary similarity statement with a CAS-checked pointwise residual.
:::

:::proof "methods.similarity.burgers_flux_integral"
On $`t>0`, differentiate $`u=x/t` to obtain
$`u_t=-x/t^2` and
$`\partial_x(u^2/2)=\partial_x(x^2/(2t^2))=x/t^2`. The verified symbolic
calculation proves these terms cancel pointwise. Integrating the zero residual
over any subdomain of positive spacetime gives zero.
:::
