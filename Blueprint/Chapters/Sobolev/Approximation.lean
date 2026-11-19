/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Sobolev.Core
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Weighted.Density
import PDE.Spaces.Sobolev.Weighted.Hilbert
import PDE.Spaces.Sobolev.Weighted.Interpolation
import PDE.Spaces.Sobolev.Weighted.Reflection
import PDE.Spaces.Sobolev.Weighted.Representation
import PDE.Spaces.Sobolev.Weighted.Measure
import PDE.Spaces.Sobolev.Weighted.Anisotropic
import PDE.Spaces.Sobolev.Weighted.Parity
import PDE.Spaces.Sobolev.Weighted.CompletedParity
import PDE.Spaces.Sobolev.Weighted.JetLimits
import PDE.Spaces.Sobolev.Weighted.EndpointNorm
import PDE.Spaces.Sobolev.Weighted.SelectedEnergy
import PDE.Spaces.Sobolev.Weighted.WorkEnvelope
import PDE.Spaces.Sobolev.Weighted.SingularDensity
import PDE.Spaces.Sobolev.Weighted.HomogeneousInterpolation
import PDE.Spaces.Sobolev.Weighted.InterpolationRecursion
import PDE.Spaces.Sobolev.Weighted.InterpolationCertificate
import PDE.Spaces.Sobolev.Weighted.IntegrationByParts.Basic
import PDE.Spaces.Sobolev.Weighted.IntegrationByParts
import PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation.Basic
import PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation
import PDE.Spaces.Sobolev.Weighted.MixedDerivatives.Basic
import PDE.Spaces.Sobolev.Weighted.MixedDerivatives
import PDE.Spaces.Sobolev.Weighted.PlanarReflection.Basic
import PDE.Spaces.Sobolev.Weighted.PlanarReflection

/-!
# Approximation and density

Smooth approximation and density results in Sobolev spaces.
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
#doc (Manual) "Approximation and Density" =>

Smooth approximation lets classical identities pass to weak Sobolev limits.
Three separate statements are often compressed into the phrase “mollify the function”:

1. a Banach-valued approximate identity converges in $`L^p(\mathbb R^n)`;
2. mollification commutes with scalar weak derivatives, globally or away from
   the boundary of a domain;
3. an expanding cutoff upgrades whole-space mollifications to smooth,
   compactly supported Sobolev approximants.

The first is proved here. Mathlib's smooth-bump approximate identity gives
pointwise convergence. The distinction from
$`L^p` convergence is discussed in
[Mollification theorem in L^p?](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Mollification.20theorem.20in.20L.5Ep.3F.html).

Two mistakes come from merging these layers. Zero-extension mollification on
a domain is only an *interior* approximation:
its derivative formula is valid once the kernel lies inside the domain, and
the resulting convergence is proved on compact subsets
$`K\Subset\Omega`. It does not by itself produce functions supported in
$`\Omega` or convergence on all of $`\Omega`. Conversely, the whole-space
density theorem needs an expanding cutoff because mollification alone does not
make a general function compactly supported.

Consider the constant function $`u=1` on $`(0,1)`. Its derivative inside
the interval is zero. Its zero extension to the line is
$`\mathbf1_{(0,1)}`, whose distributional derivative is
$`\delta_0-\delta_1`: for a test function,
$`-\int_0^1\varphi'=\varphi(0)-\varphi(1)`.
Mollifying this extension therefore gives

$$`
\frac{d}{dx}(\rho_\varepsilon*\mathbf1_{(0,1)})(x)
=\rho_\varepsilon(x)-\rho_\varepsilon(x-1).
`

If the kernel is supported in $`[-\varepsilon,\varepsilon]`, the extra
derivatives live near the two endpoints. They disappear from any fixed
interior compact set once $`\varepsilon` is small enough, but they do not
justify convergence of derivatives on the whole interval. This is the
boundary obstruction behind the word “interior” in the local theorem.

All norm-convergence results below assume $`1\leq p<\infty`.
Lean expresses this as `[Fact (1 ≤ p)]` together with `p ≠ ∞`. This exclusion
is essential in positive dimension: for example, the constant function $`1` belongs to
$`W^{k,\infty}(\mathbb R^n)` but no compactly supported function can approach
it in the $`L^\infty` norm.

:::group "sobolev.approximation"
Sobolev approximation
:::

:::definition "sobolev.mollifier" (parent := "sobolev.approximation") (lean := "SobolevSpace.Approximation.Mollifier, SobolevSpace.Approximation.standardMollifier, SobolevSpace.Approximation.scaled, SobolevSpace.Approximation.mollify")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-265"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A `Mollifier n` consists of a scalar kernel
$`\rho:\mathbb R^n\to\mathbb R` together with proofs that it is
$`C^\infty`, compactly supported, nonnegative, and normalized by

$$`
  \int_{\mathbb R^n}\rho(x)\,dx=1.
`

For positive $`\varepsilon`, `scaled μ ε` is the usual kernel

$$`
  \rho_\varepsilon(x)=\varepsilon^{-n}\rho(\varepsilon^{-1}x).
`

The definition sets this function to zero when
$`\varepsilon\leq0`; every analytic theorem below therefore carries a
strict-positivity hypothesis on the scale. `mollify μ ε f` is convolution
$`\rho_\varepsilon*f`. Mathlib's normalized smooth bump supplies
`standardMollifier n`, so applications need not construct a kernel by hand,
while theorems retain an explicit mollifier parameter and hence do not depend
on a particular choice.
:::

Only the kernel in $`\rho_\varepsilon*f` is scalar. The function being
regularized may take values in any real normed space, since $`f(x-y)` is
merely multiplied by the real number $`\rho_\varepsilon(y)` and integrated.
The $`L^p` convergence theorem is proved at this generality, so the
vector-valued operation is the basic one.

:::definition "sobolev.vector_mollification" (parent := "sobolev.approximation") (lean := "SobolevSpace.Approximation.mollifyVector") (uses := "sobolev.mollifier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-265"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The same scalar kernel regularizes functions with values in a real normed
space $`X` by the Bochner convolution

$$`
  (\rho_\varepsilon*f)(x)
    =\int_{\mathbb R^n}\rho_\varepsilon(y)\,f(x-y)\,dy.
`

The scalar definition `mollify` is the specialization $`X=\mathbb R`.
Keeping the Banach-valued operation primitive makes the analytic core
reusable for vector-valued Sobolev functions and for time regularization of
evolution trajectories taking values in a space such as $`V` or $`V^*`.
:::

The first of the three statements is that this convolution is an
approximate identity in $`L^p`. Finiteness of $`p` enters
through the density of continuous compactly supported functions
in $`L^p(\mathbb R^n;X)`, which fails at $`p=\infty`.

:::theorem "sobolev.mollification_lp" (parent := "sobolev.approximation") (lean := "SobolevSpace.Approximation.mollifyVector_converges_Lp, SobolevSpace.Approximation.mollify_converges_Lp") (uses := "sobolev.mollifier, sobolev.vector_mollification")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-265"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`X` be a complete real normed space with the required Borel measurable
structure, let $`1\leq p<\infty`, and let
$`f\in L^p(\mathbb R^n;X)`. For every positive sequence
$`\varepsilon_m\to0`,

$$`
  \|\rho_{\varepsilon_m}*f-f\|_{L^p(\mathbb R^n;X)}
    \longrightarrow 0.
`

In Lean the conclusion is convergence to zero of the extended seminorm
`eLpNorm`, whose values lie in $`\mathbb R_{\geq0}\cup\{\infty\}`.
The companion scalar theorem is obtained from this Banach-valued result by
specializing $`X` to $`\mathbb R`.
:::

:::proof "sobolev.mollification_lp"
First approximate $`f` in $`L^p` by a continuous compactly supported
function $`g`. Mollification is an $`L^p` contraction, while
$`\rho_{\varepsilon_m}*g\to g` follows from pointwise approximate-identity
convergence, compact support, and dominated convergence. A three-term
triangle estimate for

$$`
  \rho_{\varepsilon_m}*f-f
  =\rho_{\varepsilon_m}*(f-g)
    +(\rho_{\varepsilon_m}*g-g)+(g-f)
`

then gives the result. The proof includes the endpoint $`p=1`.
:::

Convergence of $`\rho_\varepsilon*f` to $`f` controls the function alone.
Control of the derivatives reduces to the same theorem once the derivatives of
the mollification are known to be mollifications of the weak derivatives,
which is the second statement. Its domain-local form is where the interior
character of the approximation originates.

:::theorem "sobolev.mollification_weak_derivative" (parent := "sobolev.approximation") (lean := "SobolevSpace.Approximation.iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ, SobolevSpace.Approximation.iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn") (uses := "sobolev.weak_derivative, sobolev.mollifier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "265-266"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose $`\alpha` is a nonempty derivative word and $`g` is the
$`\alpha`th weak derivative of a locally integrable scalar function $`f`.
On the whole space, every positive mollification scale satisfies the
pointwise identity

$$`
  D^\alpha(\rho_\varepsilon*f)
    =\rho_\varepsilon*g.
`

For the domain-local form, suppose $`g` is the weak derivative of $`f` on
$`\Omega` and the zero extension $`\mathbf1_\Omega f` is locally integrable
on $`\mathbb R^n`. Extend both functions by zero, and choose $`R` with
$`\operatorname{tsupp}\rho\subseteq\overline B(0,R)`. At a point $`x`, the
same identity holds provided

$$`
  \overline B(x,\varepsilon R)\subseteq\Omega.
`

The ball condition is the formal version of “stay away from the boundary.”
Zero extension need not preserve weak derivatives across $`\partial\Omega`,
as the example of $`\mathbf1_{(0,1)}` above shows.
:::

:::proof "sobolev.mollification_weak_derivative"
Differentiate the convolution on its smooth-kernel side. For fixed $`x`, use
$`y\mapsto\rho_\varepsilon(x-y)` as the test function in the weak-derivative
identity. Iterated differentiation of $`x-y` supplies the sign
$`(-1)^{|\alpha|}`, which cancels the sign in weak integration by parts.
For a proper domain, the closed-ball hypothesis ensures that this translated
kernel is an admissible test function supported inside $`\Omega`.
:::

On a domain only the local form of the commutation is available, so the
derivative convergence it yields holds on compact subsets of $`\Omega`.

:::theorem "sobolev.interior_approximation" (parent := "sobolev.approximation") (lean := "SobolevSpace.Approximation.interiorApproximation_Wkp") (uses := "sobolev.representative_space, sobolev.mollification_lp, sobolev.mollification_weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "265-267"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open, let
$`u\in W^{k,p}(\Omega)` in the representative model, and assume
$`1\leq p<\infty`. For every compact set $`K\subseteq\Omega`, there are
globally smooth functions $`u_m:\mathbb R^n\to\mathbb R` such that

$$`
  \|u_m-u\|_{L^p(K)}\longrightarrow0,
`

and, for every derivative word $`\alpha` of length at most $`k`, there is a
chosen weak derivative $`g_\alpha\in L^p(\Omega)` for which

$$`
  \|D^\alpha u_m-g_\alpha\|_{L^p(K)}\longrightarrow0.
`

The approximants are the mollifications of the zero extension
$`\mathbf1_\Omega u` at scales $`\varepsilon_m=1/(m+1)`. They need not have
compact support or be supported in $`\Omega`.
:::

:::proof "sobolev.interior_approximation"
Global $`L^p` convergence of the zero-extension mollifications restricts to
$`K`. Compactness of $`K` inside the open set $`\Omega` gives a positive
collar. Eventually the scaled kernel lies within that collar, so the local
commutation theorem identifies $`D^\alpha u_m` on $`K` with the mollification
of the zero-extended weak derivative. Applying the approximate-identity
theorem to that derivative completes the proof.
:::

On the whole space the global form of the commutation holds at every point, so
mollification alone converges in every derivative word. What it does not
produce is compact support, and this is where the third ingredient, an
expanding cutoff, enters.

:::theorem "sobolev.global_approximation" (parent := "sobolev.approximation") (lean := "SobolevSpace.Approximation.globalApproximation_Wkp") (uses := "sobolev.representative_space, sobolev.mollification_lp, sobolev.mollification_weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-268"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Assume $`1\leq p<\infty`.  For every representative-level
$`u\in W^{k,p}(\mathbb R^n)`, there is a sequence
$`u_m\in C_c^\infty(\mathbb R^n)` such that

$$`
  \|u_m-u\|_{L^p(\mathbb R^n)}\longrightarrow0.
`

For each derivative word $`\alpha` with $`|\alpha|\leq k`, the theorem also
chooses a function $`g_\alpha\in L^p(\mathbb R^n)`, proves that it is an
$`\alpha`th weak derivative of $`u`, and proves

$$`
  \|D^\alpha u_m-g_\alpha\|_{L^p(\mathbb R^n)}
    \longrightarrow0.
`

In Lean the conclusions are `eLpNorm → 0`. Smoothness and compact support
are separate predicates on each approximating function rather than
membership in a bundled test-function type.
:::

:::proof "sobolev.global_approximation"
Choose scales $`\varepsilon_m\to0`, mollify $`u`, and multiply by smooth
cutoffs $`\eta_m` that equal one on expanding balls. Mollification controls
the local smoothing error. The tails of every $`L^p` weak derivative vanish
outside large balls, while Leibniz terms involving derivatives of
$`\eta_m` carry inverse powers of the cutoff radius. These estimates give
convergence of every derivative word and also make
$`\eta_m(\rho_{\varepsilon_m}*u)` compactly supported.
:::

The preceding theorem is stated for one representative and chooses a
derivative $`g_\alpha` for each derivative word. The graph-space version uses
the derivative coordinates stored in the element instead.

:::theorem "sobolev.global_density" (parent := "sobolev.approximation") (lean := "SobolevSpace.GraphSpace.globalApproximation_WkpSpace, SobolevSpace.GraphSpace.mkWkpSpaceOnOfContDiff") (uses := "sobolev.graph_space, sobolev.global_approximation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-268"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`1\leq p<\infty` and arbitrary finite order $`k`, the same construction
gives convergence in the ordinary real norm of the Banach space
$`W^{k,p}(\mathbb R^n)`. Each approximant is built by
`mkWkpSpaceOnOfContDiff` from a globally smooth compactly supported function
and its classical derivative bundle:

$$`
  \left\|\operatorname{mk}(u_m)-U\right\|_{W^{k,p}(\mathbb R^n)}
    \longrightarrow0.
`

This is sequential density in the graph model, stated with explicit
approximants rather than as `DenseRange` or a closure equality.
:::

:::proof "sobolev.global_density"
Convert the graph-space element to its selected representative and apply
{uses "sobolev.global_approximation"}[]. For each symmetric derivative index,
weak-derivative uniqueness on the open set $`\mathbb R^n` identifies the
chosen derivative from the representative theorem with the coordinate stored
by the graph element. The finite `PiLp` index type then turns coordinatewise
$`L^p` convergence into convergence of the Sobolev graph norm.
:::

# Weighted graph spaces

Degenerate and singular elliptic problems measure each derivative against its
own density: $`\int|\partial^\alpha u|^2w_\alpha\,dx` with $`w_\alpha\geq0`.
The naive definition, all Sobolev functions for which these integrals are
finite, is not always complete. If some $`w_\alpha` vanishes on a set, a
sequence can converge in the weighted norm while its base functions drift
apart where the weight is zero. The library therefore starts from the
completion and proves separately when that completion consists of functions.
This is the question studied by {Informal.citet "kufner-opic-1984"}[]; the
conditions proved here are elementary sufficient ones.

:::definition "sobolev.weighted_completion" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.CompletedHkSpaceOn, SobolevSpace.Weighted.completedHkSubmoduleOn, SobolevSpace.Weighted.L2Rows, SobolevSpace.Weighted.DerivativeL2RowsOn, SobolevSpace.Weighted.derivativeL2RowsLinearMap, SobolevSpace.Weighted.CompletedHkSpaceOn.denseRange_ofGraph, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_sq_eq_sum") (uses := "sobolev.graph_space")
Let $`\Omega\subseteq\mathbb R^n`, $`k\in\mathbb N`, and assign a density
$`w_\alpha\geq0` to every derivative index $`|\alpha|\leq k`. The weighted
row space is the Hilbert direct sum
$`\bigoplus_{|\alpha|\leq k}L^2(\Omega,w_\alpha\,dx)`. A graph element
$`u\in W^{k,2}(\Omega)` whose derivatives have finite weighted energy maps
linearly to its rows $`(\partial^\alpha u)_\alpha`. The completed weighted
space is the closure of the image of this map. It is a real Hilbert space
for arbitrary nonnegative densities, the realized graph elements are dense in
it, and

$$`
\|U\|^2=\sum_{|\alpha|\leq k}\int_\Omega|U_\alpha|^2w_\alpha\,dx .
`
:::

Completion always works; what can fail is the passage back to functions.
Positivity of the zeroth weight is enough for the realized elements, and
lower bounds on all the weights are enough for the whole completion.

:::theorem "sobolev.weighted_completion_functions" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul_injective, SobolevSpace.Weighted.CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul, SobolevSpace.Weighted.CompletedHkSpaceOn.ofGraph_injective, SobolevSpace.Weighted.weightedJetOperator, SobolevSpace.Weighted.weightedJetOperator_isClosable_of_ae_lower_bound, SobolevSpace.Weighted.CompletedHkSpaceOn.exists_closedOperator_representation, SobolevSpace.Weighted.completedHkSubmoduleOn_eq_range_of_ae_bounds") (uses := "sobolev.weighted_completion")
Let $`\Omega` be open.

1. If $`w_0>0` almost everywhere, the map from weighted-integrable graph
   elements into the completion is injective.
2. If each row measure controls Lebesgue measure,
   $`dx\leq D_\alpha\,w_\alpha\,dx` with $`D_\alpha<\infty`, forgetting the
   weights gives a bounded injective map from the completion into
   $`W^{k,2}(\Omega)`. The weights may be unbounded.
3. If $`w_\alpha\geq c_\alpha>0` almost everywhere, the weighted derivative
   operator, which sends the zeroth row to the full jet, is closable. When
   in addition $`w_0>0` almost everywhere, every element of the completion
   is the value of the closed operator at its zeroth row, an $`L^2(w_0)`
   function.
4. If $`c_\alpha\leq w_\alpha\leq C_\alpha` with
   $`0<c_\alpha` and $`C_\alpha<\infty`, the completion is exactly the set of
   realized rows of $`W^{k,2}(\Omega)`.
:::

:::proof "sobolev.weighted_completion_functions"
On an open set a Sobolev function determines its weak derivatives, so
positivity of $`w_0` makes the zeroth row, and hence the whole row tuple,
determine the graph element. The lower measure comparison bounds each
unweighted $`L^2` norm by a weighted one; the forgetful map is therefore
bounded on the realized rows, lands in the closed graph subspace of
$`W^{k,2}(\Omega)`, and extends to the closure. Its injectivity is
injectivity of the forgetful map on row tuples. Closability is the same
bound read on the graph of the derivative operator. With upper bounds as
well, the weighted and unweighted norms are equivalent on realized rows, so
the realized range is closed and equals its closure.
:::

On all of $`\mathbb R^n` smooth functions are dense under upper bounds
alone, and there the weights may vanish.

:::theorem "sobolev.weighted_smooth_core" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.hasSmoothCoreOn_univ_of_ae_upper_bound, SobolevSpace.Weighted.HasSmoothCoreOn, SobolevSpace.Weighted.smoothCoreOn") (uses := "sobolev.weighted_completion, sobolev.global_density")
Let $`w_\alpha\leq C_\alpha<\infty` almost everywhere on $`\mathbb R^n`.
Then the test functions whose rows have finite weighted energy are dense in
the completed weighted space.
:::

:::proof "sobolev.weighted_smooth_core"
With finite upper bounds the weighted norm of a row is at most a constant
times its $`L^2` norm. Realized graph elements are dense in the completion
by definition, and each of them is approximated in $`W^{k,2}(\mathbb R^n)`
by smooth compactly supported functions, by {uses "sobolev.global_density"}[].
The upper bound carries that approximation into the weighted norm.
:::

Two further estimates are the measure-theoretic parts of weighted arguments
elsewhere. The first is the $`L^2` bound behind reflection across a
coordinate hyperplane, the step used in the half-space extension of
{Informal.citet "evans-2010"}[], section 5.4, with a weight on the half-space.

:::theorem "sobolev.weighted_reflection" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.integral_reflection_sq_le_of_integrable_sq_mul, SobolevSpace.Weighted.memLp_reflection_of_integrable_sq_mul, SobolevSpace.Weighted.integrable_integral_le_twice_of_nonneg_even") (uses := "sobolev.weighted_completion_functions")
Let $`H=\{x:x_i\geq0\}`, let $`w\geq c>0` almost everywhere on $`H`, and let
$`\int_Hf^2w<\infty`. For either sign $`\sigma=\pm1`, the reflection
$`Rf(x)=f(x)` on $`H` and $`Rf(x)=\sigma f(x^*)` off $`H`, where $`x^*`
flips the sign of $`x_i`, belongs to $`L^2(\mathbb R^n)` and

$$`
\int_{\mathbb R^n}(Rf)^2\,dx\leq\frac2c\int_Hf^2w\,dx .
`

A continuous nonnegative density even in $`x_i` and integrable on $`H` is
integrable on $`\mathbb R^n`, with at most twice the half-space integral.
:::

:::proof "sobolev.weighted_reflection"
Integrability is derived first: on $`H` the lower bound gives
$`f^2\leq f^2w/c`, and the reflection is measure preserving, so the two
halves each contribute at most $`\frac1c\int_Hf^2w`. The even-density
statement applies this to $`\sqrt f` with weight one.
:::

The second is Hölder's inequality in the form used to interpolate between
weights.

:::theorem "sobolev.weighted_interpolation" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.lintegral_le_geometric_interpolation, SobolevSpace.Weighted.geometricDensity, SobolevSpace.Weighted.coordinatePowerEnergyWithDensity_geometricDensity_le") (uses := "sobolev.weighted_completion")
Let $`0\leq\theta\leq1` and let $`F_0,F_1,F_\theta\geq0` with
$`F_\theta\leq F_0^{1-\theta}F_1^\theta` almost everywhere. Then

$$`
\int F_\theta\leq\Bigl(\int F_0\Bigr)^{1-\theta}\Bigl(\int F_1\Bigr)^\theta .
`

Consequently the energy $`\int|\partial^\alpha u|^qw_\theta` of a Sobolev
graph coordinate against the geometric density
$`w_\theta=w_0^{1-\theta}w_1^\theta` is at most the product of the endpoint
energies raised to the powers $`1-\theta` and $`\theta`.
:::

:::proof "sobolev.weighted_interpolation"
Monotonicity of the integral reduces the first statement to Hölder's
inequality with exponents $`1/(1-\theta)` and $`1/\theta`. The second is
the first with $`F_j=|\partial^\alpha u|^qw_j`.
:::

This is the log-convexity step of weighted interpolation. The rest of the
chapter supplies the other ingredients from which weighted interpolation
arguments of Caffarelli–Kohn–Nirenberg type are assembled: parity classes,
energies that count only some rows, and one-dimensional and planar
integration by parts with explicit constants.

A weighted Sobolev condition is a statement about individual derivative
rows, so the first objects are predicates on rows.

:::definition "sobolev.weighted_coordinate_classes" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.CoordinateMemLpWithDensity, SobolevSpace.Weighted.CoordinatesMemLpWithDensity, SobolevSpace.Weighted.CoordinateMemLpWithDensity.mono_density, SobolevSpace.Weighted.CoordinatesMemLpWithDensity.mono_density, SobolevSpace.Weighted.derivativeIndexDegree, SobolevSpace.Weighted.derivativeIndexDegree_mono_cost, SobolevSpace.Weighted.anisotropicDerivativeFamily, SobolevSpace.Weighted.anisotropicDerivativeFamily_mono_budget, SobolevSpace.Weighted.anisotropicDerivativeFamily_antitone_cost, SobolevSpace.Weighted.mem_anisotropicDerivativeFamily_one_iff, SobolevSpace.Weighted.AnisotropicCoordinatesMemLpWithDensity, SobolevSpace.Weighted.AnisotropicCoordinatesMemLpWithDensity.mono_budget, SobolevSpace.Weighted.AnisotropicCoordinatesMemLpWithDensity.mono_cost, SobolevSpace.Weighted.AnisotropicCoordinatesMemLpWithDensity.mono_density") (uses := "sobolev.graph_space")
Let $`u\in W^{k,p}(\Omega)` and let $`w\ge0` be a density. The row
$`\partial^\alpha u` lies in $`L^p_w` when it is $`p`-integrable for the
measure $`w\,dx`, and $`u` has all its rows in $`L^p_w` when this holds for
every $`|\alpha|\le k`. Both conditions are monotone in the density: if
$`w'\le Cw` then a row in $`L^p_w` is in $`L^p_{w'}`.

For anisotropic problems each coordinate direction gets a cost
$`c_i\in\mathbb N`, and a derivative index gets the degree
$`\sum_i c_i\alpha_i`. The anisotropic family of budget $`b` consists of the
indices of degree at most $`b`. It grows with the budget and shrinks when the
costs grow, and with all costs equal to one it is the usual family
$`|\alpha|\le b`. An anisotropic weighted condition asks for $`L^p_w`
membership of the rows in that family only.
:::

No doubling, Muckenhoupt or Poincaré hypothesis is part of these
definitions. Theorems that need such a condition state it.

Axisymmetric and odd-even problems restrict attention to functions with a
fixed parity under a coordinate reflection $`\sigma_i(x)=(\dots,-x_i,\dots)`.
Differentiating in $`x_i` flips the parity and tangential derivatives keep
it, which fixes the parity of every row.

:::theorem "sobolev.weighted_parity" (parent := "sobolev.approximation") (lean := "PDE.Common.IsReflectionEigenfunctionOn.classicalDerivativeRow, PDE.Common.IsReflectionEigenfunctionOn.iteratedPartialDeriv, PDE.Common.IsReflectionEigenfunctionOn.partialDeriv_same, PDE.Common.IsReflectionEigenfunctionOn.partialDeriv_of_ne, PDE.Common.IsReflectionEigenfunctionOn.mono, PDE.Common.IsReflectionEigenfunctionOn, SobolevSpace.Weighted.IsEvenUnderCoordinateReflectionOn, SobolevSpace.Weighted.IsOddUnderCoordinateReflectionOn, SobolevSpace.Weighted.reflectionEigenfunctionSubmoduleOn, SobolevSpace.Weighted.evenFunctionSubmoduleOn, SobolevSpace.Weighted.oddFunctionSubmoduleOn, SobolevSpace.Weighted.IsDerivativeRowUnderCoordinateReflectionOn, SobolevSpace.Weighted.classicalDerivativeRow, SobolevSpace.Weighted.coordinateReflectionLpLinearIsometry, SobolevSpace.Weighted.lpReflectionEigenspace, SobolevSpace.Weighted.sobolevReflectionParitySubmodule, SobolevSpace.Weighted.evenSobolevSubmodule, SobolevSpace.Weighted.oddSobolevSubmodule, SobolevSpace.Weighted.isClosed_sobolevReflectionParitySubmodule, SobolevSpace.Weighted.coordinatesMemLpWithDensitySubmodule, SobolevSpace.Weighted.weightedSobolevReflectionParitySubmodule, SobolevSpace.Weighted.weightedEvenHkSubmodule, SobolevSpace.Weighted.weightedOddHkSubmodule") (uses := "sobolev.weighted_coordinate_classes")
Say that $`f:\mathbb R^n\to\mathbb R` is a reflection eigenfunction with
eigenvalue $`c` in the direction $`i` if $`f\circ\sigma_i=cf`; the cases
$`c=1` and $`c=-1` are even and odd functions.

1. If $`f\in C^k(\mathbb R^n)` has eigenvalue $`c`, then $`\partial_if` has
   eigenvalue $`-c`, $`\partial_jf` has eigenvalue $`c` for $`j\ne i`, and
   in general $`\partial^\alpha f` has eigenvalue $`c(-1)^{\alpha_i}` for
   $`|\alpha|\le k`.
2. The map $`u\mapsto u\circ\sigma_i` is a linear isometry of
   $`L^p(\mathbb R^n)`. The set of $`u\in W^{k,p}(\mathbb R^n)` whose row
   $`\partial^\alpha u` lies in the $`c(-1)^{\alpha_i}` eigenspace of this
   isometry, for every $`\alpha`, is a closed subspace. For $`c=\pm1` it is
   the even or odd Sobolev space.
3. Intersecting with the rows in $`L^2_{w_\alpha}` gives the weighted even
   and odd subspaces of $`H^k(\mathbb R^n)`.
:::

:::proof "sobolev.weighted_parity"
The first part is the chain rule for $`f\circ\sigma_i`, whose derivative in
$`x_i` carries a sign and whose other derivatives do not, iterated along the
index. For the second, each row condition says that two continuous maps into
$`L^p` agree, the row itself and $`c(-1)^{\alpha_i}` times its reflection, so
it cuts out a closed subspace, and the intersection of closed subspaces is
closed. The parity of each row is imposed as a separate condition. For
Sobolev functions on the whole space the parity of $`u` already forces the
parity of the weak derivatives, but that implication is not used.
:::

In a weighted completion the parity is first imposed on the smooth
generating functions. When the weights are bounded below it survives the
completion.

:::theorem "sobolev.weighted_completed_parity" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.completedReflectionParitySubmodule.toHk_mem_sobolevReflectionParitySubmodule, SobolevSpace.Weighted.completedReflectionParitySubmodule, SobolevSpace.Weighted.reflectionParitySmoothCore, SobolevSpace.Weighted.completedReflectionParitySubmodule.instCompleteSpace, SobolevSpace.Weighted.completedReflectionParitySubmodule.ofCoreLinearMap, SobolevSpace.Weighted.completedReflectionParitySubmodule.denseRange_ofCore, SobolevSpace.Weighted.completedReflectionParitySubmodule.continuous_ext") (uses := "sobolev.weighted_parity, sobolev.weighted_completion_functions, sobolev.weighted_smooth_core")
Let $`w_\alpha` be the row weights on $`\mathbb R^n`. The eligible test
functions whose derivative rows have the parity of the previous theorem form
a subspace of the smooth core, and its closure in the weighted completion is
a complete space in which the core is dense. If every row measure is bounded
below, $`dx\le D_\alpha\,w_\alpha\,dx`, then each element of this closure,
viewed as a function in $`H^k(\mathbb R^n)`, has every row in the
prescribed eigenspace. The weights may grow or be singular.
:::

:::proof "sobolev.weighted_completed_parity"
The lower bounds make the map from the completion to $`H^k(\mathbb R^n)`
continuous, as in {uses "sobolev.weighted_completion_functions"}[]. It sends
the parity core into the closed parity subspace of $`H^k`, so it sends the
closure of the core there as well.
:::

An energy estimate for an evolution equation often controls the function and
its top derivatives, with weights, and nothing in between. For a Galerkin
scheme the inner product used to project must be the one whose norm the
estimate differentiates. So it matters that the selected rows define a
Hilbert norm equivalent to the full one.

:::theorem "sobolev.weighted_selected_energy" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.CompletedHkSpaceOn.exists_pos_norm_sq_le_selected_energy, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_toHk_le_base_add_sum_top, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_toHk_coordinate_le, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_coordinate_le_toHk, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_le_sum_coordinate, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_le_selected_rows, SobolevSpace.Weighted.CompletedHkSpaceOn.selectedRows, SobolevSpace.Weighted.CompletedHkSpaceOn.norm_selectedRows_sq, SobolevSpace.Weighted.CompletedHkSpaceOn.selectedRows_injective, SobolevSpace.Weighted.CompletedHkSpaceOn.exists_antilipschitz_selectedRows, SobolevSpace.Weighted.CompletedHkSpaceOn.isClosed_range_selectedRows, SobolevSpace.Weighted.CompletedHkSpaceOn.completeSpace_range_selectedRows, SobolevSpace.Weighted.CompletedHkSpaceOn.selectedEnergyEquiv") (uses := "sobolev.weighted_completion_functions")
Let $`k\ge1` and let $`w_\alpha` be row weights on $`\mathbb R^n` with a
common lower bound, $`dx\le D\,w_\alpha\,dx` for all $`\alpha`. Let $`s` be a
set of rows that contains the base row and the pure top rows
$`\partial_i^k`, and assume the rows outside $`s` have bounded weights,
$`w_\alpha\,dx\le C\,dx` for $`\alpha\notin s`. Then there is $`B>0` with

$$`
\|U\|^2\le B\sum_{\alpha\in s}\|U_\alpha\|_{L^2_{w_\alpha}}^2
`

for every $`U` in the weighted completion. Consequently the projection onto
the rows in $`s` is injective with closed range, and the completion is
linearly homeomorphic to that range, a Hilbert space whose squared norm is
exactly the selected energy.
:::

:::proof "sobolev.weighted_selected_energy"
Forgetting a weight costs at most $`D^{1/2}` in each row. On the whole space,
Fourier interpolation bounds every intermediate unweighted row by the base
row and the pure top rows. Each row outside $`s` has a bounded weight, so its
weighted norm is at most $`C^{1/2}` times its unweighted norm. Adding the rows
and applying Cauchy–Schwarz to the finite sum gives the inequality. An
injective bounded operator with a bound from below has closed range, and it
is a linear homeomorphism onto that range.
:::

Two small facts are used with these completions. Convergence and continuity
can be tested row by row, and a finite family of weighted work terms has an
integrable majorant as soon as each factor has one.

:::theorem "sobolev.weighted_row_limits" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.CompletedHkSpaceOn.exists_of_coordinate_tendsto, SobolevSpace.Weighted.CompletedHkSpaceOn.continuous_iff_coordinate") (uses := "sobolev.weighted_completion")
A map into the weighted completion is continuous if and only if each of its
rows is continuous into its weighted $`L^2` space. If a family $`U_j` in the
completion has rows converging to limits $`R_\alpha`, then there is $`U` in
the completion with rows $`R_\alpha` and $`U_j\to U`. No comparison between
the row measures is needed.
:::

:::proof "sobolev.weighted_row_limits"
The completion is a closed subspace of the finite product of the weighted
$`L^2` spaces with the product topology. Row limits give a limit in the
product, and a closed set contains the limits of its sequences.
:::

:::theorem "sobolev.weighted_work_envelope" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.integrable_work_envelope_of_memLp") (uses := "sobolev.weighted_completion")
Let $`\iota` be finite, $`\Phi_i\ge0` almost everywhere, and
$`W_i,V_i\in L^2(\mu)`. Suppose that outside a single null set, for every
parameter $`t\in S` and every $`i`,

$$`
|w_i(t,x)|\,\Phi_i(x)^{1/2}\le|W_i(x)|,\qquad
|v_i(t,x)|\,\Phi_i(x)^{1/2}\le|V_i(x)| .
`

Then $`\sum_i|V_iW_i|` is integrable, and outside a null set, for all
$`t\in S`,
$`\bigl|\sum_iv_i(t,x)\,w_i(t,x)\,\Phi_i(x)\bigr|\le\sum_i|V_i(x)W_i(x)|`.
:::

:::proof "sobolev.weighted_work_envelope"
Write $`vw\Phi=(v\Phi^{1/2})(w\Phi^{1/2})`, bound each factor, and use
Hölder's inequality for the integrability of $`V_iW_i`. The null set does not
depend on $`t`, which is the order of quantifiers that dominated
differentiation in time asks for.
:::

For singular weights, where the upper bound in the
{bpref "sobolev.weighted_smooth_core"}[smooth-core theorem] fails, density of the smooth core is
usually proved by localizing, comparing with a bounded weight, and
mollifying. The next statement records that argument in a fixed shape.

:::theorem "sobolev.weighted_singular_localization" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.exists_testFunction_localizedDerivativeL2Rows_dist_lt, SobolevSpace.Weighted.dist_localizedDerivativeL2Rows_le, SobolevSpace.Weighted.exists_testFunction_dist_lt_of_localized_measure_comparison, SobolevSpace.Weighted.EventuallyDistLeWeightedDistAdd, SobolevSpace.Weighted.HasLocallyComparableExhaustion, SobolevSpace.Weighted.HasLocallyComparableExhaustion.exists_testFunction_dist_lt, SobolevSpace.Weighted.HasLocallyComparableExhaustion.hasSmoothCoreOn, SobolevSpace.Weighted.HasLocallyComparableExhaustion.weightedJetOperator_closure_hasSmoothCore") (uses := "sobolev.weighted_smooth_core, sobolev.global_density")
Let $`v_\alpha` be bounded row weights, $`v_\alpha\le B_\alpha`, and let
$`q_\alpha\le C_\alpha v_\alpha`.

1. Distances measured with the weights $`q` are at most a constant times
   distances measured with $`v`, and every element of $`H^k(\mathbb R^n)`
   is a limit of test functions in the $`q`-weighted row norm.
2. Suppose that for every realizable $`U` and every $`\varepsilon>0` there is
   such a pair $`(v,q)`, a function $`V` within $`\varepsilon/3` of $`U` in the
   $`w`-norm, and test functions converging to $`V` in the $`v`-norm whose
   $`w`-distance to $`V` eventually exceeds their $`q`-distance by at most
   $`\varepsilon/3`. Then the smooth core is dense in the $`w`-completion.

Because $`q=v=0` and $`V=U` are allowed, the hypothesis of the second part
is equivalent to plain approximation of every realizable $`U` by test
functions in the $`w`-norm. The theorem fixes the shape of a density proof;
the approximation itself has to be supplied for each singular weight.
:::

:::proof "sobolev.weighted_singular_localization"
The first part follows from the operator bound for the change of weights and
{uses "sobolev.global_density"}[]. The second is an $`\varepsilon/3`
argument: $`U` is close to $`V`, the test functions are eventually close to
$`V` in the $`q`-norm by the first part, and the distance comparison converts that
into closeness in the $`w`-norm.
:::

# Weighted interpolation inequalities

An interpolation inequality bounds an intermediate derivative by a small
multiple of a higher one plus a large multiple of a lower one. On the whole
space without weights it comes from the Fourier transform, and the Fourier
side reduces to an inequality for integrals against a homogeneous density.

:::theorem "sobolev.weighted_homogeneous_interpolation" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.lintegral_homogeneous_density_interpolation, SobolevSpace.Weighted.lintegral_homogeneous_density_interpolation_sqrt, SobolevSpace.Weighted.lintegral_fourier_homogeneous_interpolation_sqrt, SobolevSpace.Weighted.ennreal_interpolation_toReal, SobolevSpace.Weighted.lintegral_homogeneous_density_interpolation_sqrt_toReal, SobolevSpace.Weighted.weightedGeometricMean_le_young, SobolevSpace.Weighted.lintegral_homogeneous_density_interpolation_young_toReal, SobolevSpace.Weighted.lintegral_homogeneous_density_interpolation_eta_toReal, SobolevSpace.Weighted.youngInterpolationConstant, SobolevSpace.Weighted.youngInterpolationConstant_pos, SobolevSpace.Weighted.aggregateYoungInterpolationConstant, SobolevSpace.Weighted.aggregateYoungInterpolationConstant_pos, SobolevSpace.Weighted.aggregateYoungInterpolationConstant_eq, SobolevSpace.Weighted.aggregateDerivativeSymbol2D, SobolevSpace.Weighted.aggregateDerivativeSymbol2D_le_radialSymbol, SobolevSpace.Weighted.radialSymbol_le_twoPow_mul_aggregateDerivativeSymbol2D") (uses := "sobolev.weighted_interpolation")
Let $`r,F\ge0` be measurable on a measure space and $`0<j<k` integers. Then

$$`
\int r^{2j}F\le\Bigl(\int r^{2k}F\Bigr)^{j/k}\Bigl(\int F\Bigr)^{1-j/k},
`

as an inequality in $`[0,\infty]`. If both integrals on the right are finite,
then for every $`\eta>0`

$$`
\Bigl(\int r^{2j}F\Bigr)^{1/2}\le\eta\Bigl(\int r^{2k}F\Bigr)^{1/2}
  +K(j,k,\eta)\Bigl(\int F\Bigr)^{1/2},\qquad
K(j,k,\eta)=\frac{k-j}{k}\Bigl(\frac{j}{k\eta}\Bigr)^{j/(k-j)} .
`

Taking $`r=|\xi|` and $`F=|\hat f(\xi)|^2` on $`\mathbb R^2` gives the
Fourier form. In the plane the aggregate symbol
$`\sum_{q=0}^m\xi_r^{2q}\xi_z^{2(m-q)}` of all mixed derivatives of order
$`m` lies between $`2^{-m}|\xi|^{2m}` and $`|\xi|^{2m}`.
:::

:::proof "sobolev.weighted_homogeneous_interpolation"
The first inequality is the log-convexity of
{uses "sobolev.weighted_interpolation"}[] applied to the densities $`F` and
$`r^{2k}F` with $`\theta=j/k`. Young's inequality
$`a^{\theta}b^{1-\theta}\le\theta\chi a+(1-\theta)\chi^{-\theta/(1-\theta)}b`,
with $`\chi` chosen to make the top coefficient $`\eta`, gives the additive
form and the constant $`K`. The symbol bounds follow from the binomial
expansion of $`(\xi_r^2+\xi_z^2)^m`.
:::

With weights there is no Fourier transform, and the estimates come from
integration by parts one step at a time. Stored bounds can be interpolated
between weights, and a system of one-step bounds can be solved.

:::theorem "sobolev.weighted_gauge_certificates" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.derivativeFamilyPowerGaugeWithDensity_geometricDensity_le, SobolevSpace.Weighted.derivativeFamilyPowerEnergyWithDensity_geometricDensity_le, SobolevSpace.Weighted.derivativeFamilyPowerGaugeWithDensity, SobolevSpace.Weighted.WeightedGaugeCertificate, SobolevSpace.Weighted.WeightedGaugeCertificate.sound, SobolevSpace.Weighted.WeightedGaugeCertificate.toReal_le, SobolevSpace.Weighted.DerivativeFamilyGaugeCertificate.interpolate, SobolevSpace.Weighted.SobolevGaugeCertificate.interpolate, SobolevSpace.Weighted.AnisotropicGaugeCertificate.interpolate, SobolevSpace.Weighted.EventualFiniteGaugeCertificate, SobolevSpace.Weighted.EventualFiniteGaugeCertificate.interpolateDerivativeFamily") (uses := "sobolev.weighted_interpolation, sobolev.weighted_coordinate_classes")
For a finite family $`A` of derivative indices, $`q>0` and a density $`w`,
let

$$`
G_w(u)=\Bigl(\sum_{\alpha\in A}\int|\partial^\alpha u|^q\,w\Bigr)^{1/q}.
`

For $`0\le\theta\le1`,
$`G_{w_0^{1-\theta}w_1^\theta}(u)\le G_{w_0}(u)^{1-\theta}G_{w_1}(u)^\theta`.
A certificate is a stored upper bound for such a gauge. Certificates for
$`w_0` and $`w_1` combine into one for every geometric mean
$`w_0^{1-\theta}w_1^\theta`. This holds for arbitrary families, for the full
Sobolev family and for anisotropic families, and for bounds that hold
eventually along a filter.
:::

:::proof "sobolev.weighted_gauge_certificates"
The energy is an integral against the sum of the row powers, so the first
statement is log-convexity of the integral in the density followed by the
$`q`-th root. The certificate statements then multiply the endpoint bounds.
:::

:::theorem "sobolev.weighted_interpolation_recursion" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.le_endpoint_combination_of_left_inverse, SobolevSpace.Weighted.mulVec_le_endpoint_combination, SobolevSpace.Weighted.FiniteInterpolationRecursionCertificate, SobolevSpace.Weighted.FiniteInterpolationRecursionCertificate.internal_le_endpointCombination, SobolevSpace.Weighted.FiniteInterpolationRecursionCertificate.gauge_le_sqrt_endpointCombination, SobolevSpace.Weighted.interpolationRecursionMatrix, SobolevSpace.Weighted.FiniteInterpolationRecursionCertificate.ofTridiagonal") (uses := "sobolev.weighted_gauge_certificates")
Let $`Q` be a square matrix with a left inverse $`Q^{-1}` whose entries are
nonnegative, and let $`b_0,b_1\ge0` be vectors. If

$$`
(Qy)_i\le b_{0,i}\,y_0+b_{1,i}\,y_1\quad\text{for all }i,
`

then $`y_j\le(Q^{-1}b_0)_j\,y_0+(Q^{-1}b_1)_j\,y_1`. Applied to the squares of
nonnegative gauges $`g_j` with endpoint values $`L,H\ge0` it gives

$$`
g_j\le\sqrt{(Q^{-1}b_0)_j}\,L+\sqrt{(Q^{-1}b_1)_j}\,H .
`

The nearest-neighbour recursion $`g_j^2\le\beta_jg_{j-1}^2+\phi_jg_{j+1}^2`
has the tridiagonal matrix with $`1` on the diagonal, $`-\phi_j` above it and
$`-\beta_j` below it, with sources in the first and last rows.
:::

:::proof "sobolev.weighted_interpolation_recursion"
A matrix with nonnegative entries preserves componentwise inequalities, so
applying $`Q^{-1}` to both sides and using $`Q^{-1}Qy=y` gives the first
bound. The second uses $`\sqrt{a+b}\le\sqrt a+\sqrt b`. Whether the inverse
of a given recursion matrix is nonnegative is data supplied with the
certificate.
:::

The one-step inequalities come from integrating by parts against a weight.
On an interval the basic identity trades the weight for its primitive.

:::theorem "sobolev.weighted_square_ibp" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.weightedSquareEnergy_eq_neg_two_cross, SobolevSpace.Weighted.weightedSquareEnergy, SobolevSpace.Weighted.weightedPrimitiveCross, SobolevSpace.Weighted.IsSquareIBPAdmissibleOn, SobolevSpace.Weighted.weightedSquareEnergyIoi_eq_neg_two_cross, SobolevSpace.Weighted.energy_le_young, SobolevSpace.Weighted.energy_le_integral_majorant, SobolevSpace.Weighted.weighted_transport_integral_identity_Ioi, SobolevSpace.Weighted.weighted_transport_integral_bound_Ioi, SobolevSpace.Weighted.weighted_transport_integral_identity_real, SobolevSpace.Weighted.weighted_transport_integral_bound_real, SobolevSpace.Weighted.weighted_transport_integral_identity_R2, SobolevSpace.Weighted.weighted_transport_integral_bound_R2, SobolevSpace.Weighted.linearPrincipalTransportModel, SobolevSpace.Weighted.weightedInterpolation_integral_identity_real") (uses := "sobolev.weighted_completion")
1. Let $`a<b`, $`P'=w` and $`f'=g` on $`(a,b)`, with $`wf^2` and $`Pfg`
   integrable and $`Pf^2\to0` at both ends. Then

   $$`
   \int_a^bw\,f^2=-2\int_a^bP\,f\,g .
   `

   The same holds on $`(0,\infty)`. If $`|P|\le|AB|`, Young's inequality
   bounds the right side by the energies of $`Af` and $`Bg`.
2. For $`G,\Phi,f\in C^1`, $`f` compactly supported with $`f(0)=0`,

   $$`
   \int_0^\infty(-Gf')\,f\,\Phi\,dr=\frac12\int_0^\infty f^2\,(G\Phi)'\,dr,
   `

   and if $`|(G\Phi)'|\le C\Phi` on $`(0,\infty)` the left side is at most
   $`\frac C2\int_0^\infty f^2\Phi`. The analogous identity and bound hold on
   $`\mathbb R` and on $`\mathbb R^2` for the transport field
   $`(-G_r,-G_z)`.
3. For $`u\in C^2` with compact support and $`\Phi\in C^1`,
   $`\int u'^2\Phi=-\int u\,u''\,\Phi-\int u\,u'\,\Phi'`.
:::

:::proof "sobolev.weighted_square_ibp"
Each identity is the fundamental theorem of calculus for a product,
$`(Pf^2)'=wf^2+2Pfg`, $`(G\Phi f^2)'`, or $`(uu'\Phi)'`, integrated with
the boundary terms removed by the stated limits, compact support, or the zero
value at the origin.
:::

Combining the last identity with a comparison between adjacent weights gives
the one-step estimate. The weights $`\Phi_{\mathrm{prev}}`,
$`\Phi_{\mathrm{mid}}`, $`\Phi_{\mathrm{next}}` belong to orders
$`j-1`, $`j`, $`j+1`.

:::theorem "sobolev.weighted_adjacent_interpolation" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.weightedInterpolation_oneStep_integral_real, SobolevSpace.Weighted.weightedInterpolationStepConstant, SobolevSpace.Weighted.weightedInterpolation_row_base_integral_real, SobolevSpace.Weighted.weightedInterpolation_finite_family_integral_real, SobolevSpace.Weighted.weightedInterpolation_finite_family_integral_Ioi, SobolevSpace.Weighted.interpolation_row_axial_of_tendsto, SobolevSpace.Weighted.interpolation_row_radial_of_tendsto") (uses := "sobolev.weighted_square_ibp, sobolev.weighted_interpolation_recursion")
Let $`u\in C^2(\mathbb R)` have compact support, let the three weights be
nonnegative and $`C^1`, and suppose

$$`
|\Phi_{\mathrm{mid}}|\le A_0\sqrt{\Phi_{\mathrm{prev}}\Phi_{\mathrm{next}}},\qquad
|\Phi_{\mathrm{mid}}'|\le A_1\sqrt{\Phi_{\mathrm{prev}}\Phi_{\mathrm{mid}}} .
`

Then for $`\eta>0` and $`0<\theta<1`

$$`
\int u'^2\Phi_{\mathrm{mid}}\le\eta\int u''^2\Phi_{\mathrm{next}}
  +\Bigl(\frac{A_0^2}{4(1-\theta)^2\eta}+\frac{A_1^2}{4\theta(1-\theta)}\Bigr)
   \int u^2\Phi_{\mathrm{prev}} .
`

For a finite family $`u_1,\dots,u_d` the same estimate holds for the sums
$`\bigl(\sum_i\|u_i'\|_{\mathrm{mid}}\bigr)^2` and their analogues, with
$`A_0^2` and $`A_1^2` multiplied by $`d^2`. There are
versions on $`(0,\infty)`, and axial and radial row versions on the half
plane in which compact support is replaced by the vanishing of the boundary
products in the limit.
:::

:::proof "sobolev.weighted_adjacent_interpolation"
By the last identity of {uses "sobolev.weighted_square_ibp"}[], the left side
is bounded by $`\int|u||u''|\Phi_{\mathrm{mid}}+\int|u||u'||\Phi_{\mathrm{mid}}'|`.
The weight comparisons turn these into
$`A_0\|u\|_{\mathrm{prev}}\|u''\|_{\mathrm{next}}` and
$`A_1\|u\|_{\mathrm{prev}}\|u'\|_{\mathrm{mid}}`. Young's inequality with
parameters chosen from $`\eta` and $`\theta` and absorption of the
$`\|u'\|_{\mathrm{mid}}^2` term into the left side give the constant.
:::

In the half plane $`\{(r,z):r>0\}` of an axisymmetric problem, the mixed
derivatives $`\partial_r^a\partial_z^{j-a}` of order $`j` are handled
together. Write

$$`
X_j(f)=\sum_{a=0}^j\Bigl(\int_{r>0}|\partial_r^a\partial_z^{j-a}f|^2\,\Phi_j\Bigr)^{1/2} .
`

:::theorem "sobolev.weighted_planar_interpolation" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.weightedInterpolation_twoDimensional_halfPlane, SobolevSpace.Weighted.weightedInterpolation_twoDimensional_halfPlane_of_tendsto, SobolevSpace.Weighted.weightedInterpolation_twoDimensional_halfPlane_of_continuous_compactSupport, SobolevSpace.Weighted.weightedInterpolation_twoDimensional_from_coordinate_rows, SobolevSpace.Weighted.weightedMixedDerivativeEnergy2D, SobolevSpace.Weighted.weightedMixedDerivativeSum2D, SobolevSpace.Weighted.mixedDerivative2D, PDE.Analysis.derivX, PDE.Analysis.derivY") (uses := "sobolev.weighted_adjacent_interpolation")
Suppose the rows of $`f` of order $`n`, whose line derivatives give orders $`n+1`, $`n+2`, are
$`C^2` along the lines they are differentiated on and compactly supported
there, that every row of order $`n` vanishes on the axis $`r=0`, that the
three weights satisfy the hypotheses of the previous theorem in both the
$`r` and the $`z` direction, and that the relevant weighted squares and cross
terms are integrable on the half plane. Then for $`\eta>0` and $`0<\theta<1`

$$`
X_{n+1}(f)^2\le\eta\,X_{n+2}(f)^2+K\,X_n(f)^2,
`

with $`K` the one-step constant for $`d=n+2`. A second version drops compact
support and the axis condition. It asks instead for $`C^2` regularity on
$`r>0`, weighted $`L^2` membership of the rows, and vanishing limits of the
boundary products.
:::

:::proof "sobolev.weighted_planar_interpolation"
The row with no $`r` derivative is interpolated in $`z`, and each row with
$`a>0` is interpolated in $`r` against its predecessor of order $`n` that has
one fewer $`r` derivative. These are the axial and radial cases of
{uses "sobolev.weighted_adjacent_interpolation"}[]. The successor identities
identify the derivatives without commuting mixed partials. Summing over the
$`n+2` rows gives the factor $`d=n+2`.
:::

The vanishing condition on the axis matters: for $`n\ge1` it excludes even
profiles, whose even-order rows need not vanish there. Such profiles are
handled by reflection across the axis, which turns a half-plane function into
a function on all of $`\mathbb R^2`.

:::theorem "sobolev.weighted_planar_reflection" (parent := "sobolev.approximation") (lean := "SobolevSpace.Weighted.contDiff_one_evenRadialReflection, SobolevSpace.Weighted.contDiff_one_oddRadialReflection, SobolevSpace.Weighted.contDiff_two_evenRadialReflection, SobolevSpace.Weighted.contDiff_two_oddRadialReflection, SobolevSpace.Weighted.oddRadialReflection_swapped_globalH2, SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_all_mixed_orders, SobolevSpace.Weighted.integral_mixedIteratedDeriv2D_evenReflection_sq_mul_evenWeight, SobolevSpace.Weighted.integral_mixedIteratedDeriv2D_oddReflection_sq_mul_evenWeight, SobolevSpace.Weighted.evenReflection2D, SobolevSpace.Weighted.oddReflection2D, SobolevSpace.Weighted.hasDerivAt_evenReflection2D_axis, SobolevSpace.Weighted.hasDerivAt_oddReflection2D_axis") (uses := "sobolev.weighted_reflection, sobolev.weighted_parity")
Let $`Ef(r,z)=f(|r|,z)` be the even reflection and $`Of` the odd one.

1. If $`F\in C^1(\mathbb R^2)` and $`\partial_rF=0` on the axis, then $`EF`
   is $`C^1`. The same condition gives $`C^2` when $`F\in C^2`. The odd
   reflection of $`F` is $`C^1` when $`F` vanishes on the axis, and $`C^2`
   when in addition $`\partial_r^2F` vanishes there.
2. If $`A\in C^2(\mathbb R^2)` vanishes on the axis and its derivatives up to order two
   are in $`L^2` of the half plane, its odd reflection agrees almost
   everywhere, up to swapping the coordinates, with an element of $`W^{2,2}(\mathbb R^2)`.
3. If the radial derivatives of $`\partial_z^\ell f` exist along each line
   and the odd-order ones vanish on the axis, then
   $`\partial_r^{2m}\partial_z^\ell Ef=E(\partial_r^{2m}\partial_z^\ell f)`
   and
   $`\partial_r^{2m+1}\partial_z^\ell Ef=O(\partial_r^{2m+1}\partial_z^\ell f)`.
4. For all $`q,\ell` and any $`f,\Phi`,

   $$`
   \int\!\!\int(\partial_r^q\partial_z^\ell Ef)^2\,E\Phi
     =2\int\!\!\int_{r>0}(\partial_r^q\partial_z^\ell f)^2\,\Phi,
   `

   as an identity of iterated integrals, and the same holds for the odd
   reflection.
:::

:::proof "sobolev.weighted_planar_reflection"
Away from the axis the reflection is a composition with $`r\mapsto-r`, so
its derivatives are those of $`f` with a sign $`(-1)^q`. On the axis the
one-sided derivatives agree exactly when the odd-order radial derivatives
vanish, which is the gluing hypothesis. The axis has measure zero, so the
integral identity needs only the off-axis formula and the symmetry of the
integrand under $`r\mapsto-r`. The identity does not by itself give Sobolev
membership.
:::
