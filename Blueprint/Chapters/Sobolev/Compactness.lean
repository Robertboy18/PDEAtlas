/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.DifferenceQuotients
import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.CompactEmbedding
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Subcritical.CompactEmbedding
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.ZeroBoundaryFiniteExponent
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction

/-!
# Sobolev compactness

Rellich and Rellich–Kondrachov compact embedding theorems.
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
#doc (Manual) "Rellich Compactness" =>

Sobolev embedding and Rellich compactness answer different questions.
A continuous embedding sends every norm-bounded set to a norm-bounded set.
A compact embedding sends every norm-bounded sequence to a sequence having a
strongly convergent subsequence in the target. The second conclusion is the
one needed when a weakly convergent approximation must pass through a
nonlinear expression.

In $`L^2(0,2\pi)`, the sequence $`u_j(x)=\sin(jx)` converges weakly to
zero: its pairing with each fixed $`L^2` test function tends to zero.
It does not converge strongly, since $`\|u_j\|_2=\sqrt{\pi}`. Moreover,

$$`
u_j^2=\frac12-\frac12\cos(2jx)
`

converges weakly to $`1/2`, whereas the square of the weak limit is zero.
The oscillation disappears from linear tests and survives squaring.
Strong $`L^2` convergence avoids this problem because

$$`
\|u_j^2-u^2\|_{L^1}
\leq(\|u_j\|_{L^2}+\|u\|_{L^2})\|u_j-u\|_{L^2}.
`

The unscaled sine sequence has unbounded derivative energy. Dividing it by
$`j` gives a bounded $`H^1` sequence that converges strongly to zero in
$`L^2`, while its derivatives $`\cos(jx)` still do not converge strongly
in $`L^2`. Compactness gains convergence in a weaker norm; it does not
make the highest controlled derivatives converge strongly.

On a domain carrying the bounded $`C^1` extension atlas used below, the
critical Sobolev estimate bounds each norm-bounded sequence in
$`W^{1,p}(\Omega)`, $`1\le p<n`, in $`L^{p^*}(\Omega)`, where

$$`
p^*=\frac{np}{n-p}.
`

Because $`1<p^*<\infty`, one can extract weakly convergent subsequences in
the critical target. That weak convergence alone does not commute with
products or nonlinear compositions. Rellich–Kondrachov gives strong
convergence in every strictly smaller $`L^q` space,
$`1\le q<p^*`. It is this loss in exponent that converts boundedness into
compactness.

Each compact embedding below concerns a concrete continuous linear map $`T`
whose image of the unit ball has compact closure. In the Banach spaces used
here, this operator statement yields the familiar sequential formulation:
every bounded sequence has a subsequence whose images converge strongly.

Fréchet–Kolmogorov first gives compactness in a lower $`L^s` space:
$`s=2` in the Hilbert proof and $`s=1` at the endpoint. Convergence in
measure, uniform integrability, and the critical $`L^{p^*}` bound then give
strong convergence in every $`L^q` with $`q<p^*`.

The Hilbert proof uses explicit approximation operators. Zero
extension gives a globally defined $`L^2` function with common bounded
support. Translation by $`h` changes it by at most
$`\|h\|\,\|u\|_{H^1}`. Finite grid averages are compact operators and
approximate the zero-extended unit ball uniformly. A general topological
criterion then makes that image totally bounded.

The $`p=1` endpoint follows the same plan with its own $`L^1` translation
estimate and finite-cell averaging operator, independent of the Hilbert
case. Once
$`W^{1,1}(\Omega)\to L^1(\Omega)` is known, finite measure continuously
lowers every $`W^{1,p}` source to $`W^{1,1}`, and the transfer theorem
recovers the whole range $`1\le p<n`.

For $`W^{1,p}_0(\Omega)`, zero extension gives compactness into $`L^p(\Omega)`
for every finite $`p\geq1` when $`\Omega` is measurable and bounded. The
unrestricted $`W^{1,p}(\Omega)` results below use the
{bpref "sobolev.extension.atlas"}[extension atlas]: boundary-flattening charts,
cutoffs, and quantitative estimates that give a bounded extension operator.
This lets the same translation argument work across the boundary without
introducing a jump. Every bounded open set with $`C^1` graph boundary admits such an atlas.

In applications, compactness supplies subsequences. On an atlas domain, a
bounded Galerkin sequence in $`H^1(\Omega)` has a subsequence converging
strongly in $`L^2(\Omega)`. The same conclusion holds for a bounded
$`H^1_0(\Omega)` sequence when $`\Omega` is measurable and bounded.
These estimates alone do not give convergence of the entire Galerkin scheme.
For evolution equations they give only spatial compactness; spacetime
compactness also needs time regularity and an Aubin–Lions–Simon argument.

:::group "sobolev.compactness"
Sobolev compactness
:::

For unrestricted spaces, the extension-atlas theorem family covers
$`1\le p<n` and $`1\le q<p^*`, including the source endpoint $`p=1` and
target endpoint $`q=1`. The proofs use the inclusion operator and an
exponent-restriction operator, defined first.

:::definition "sobolev.rellich_inclusion_operator" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.baseRepresentative, SobolevSpace.GraphSpace.RellichKondrachov.inclusion, SobolevSpace.GraphSpace.RellichKondrachov.inclusion_apply_ae") (uses := "sobolev.c1_critical_membership, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`1\le p<n`, let $`1\le q\le p^*`, and let
$`\Omega` carry the operational bounded $`C^1` atlas. The canonical
inclusion is the continuous linear map

$$`
J_{p,q}:W^{1,p}(\Omega)\longrightarrow L^q(\Omega)
`

that retains the order-zero coordinate and forgets the weak-derivative
coordinates. If $`U` is the Sobolev graph-space value and $`u` is its chosen
base representative, then

$$`
(J_{p,q}U)(x)=u(x)
\quad\text{for almost every }x\in\Omega.
`

The target $`L^q` class is built from the proved Sobolev membership
$`u\in L^q`. Continuity is then obtained from the closed graph theorem:
source convergence gives convergence in measure through the $`L^p` base
coordinate, target convergence gives convergence in measure through
$`L^q`, and uniqueness of limits in measure identifies the graph limit.
Thus later compactness theorems all concern the same concrete operator.
:::

The inclusion $`J_{p,q}` is defined for a fixed source exponent $`p`. The
proofs below move between source exponents, lowering $`W^{1,p}` to
$`W^{1,2}` or $`W^{1,1}` before a compactness theorem is applied, so an
operator that changes the exponent of every coordinate while keeping the
same representatives is needed. Its most general form assumes only that all
coordinates vanish outside a set of finite measure.

:::definition "sobolev.finite_measure_support_exponent_restriction" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.HasCoordinateSupportIn, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupport, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupport_apply_ae, SobolevSpace.GraphSpace.finiteMeasureSupportExponentRestrictionNormBound, SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureSupport_le, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupportLinearMap, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupportCLM, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureSupportCLM_apply, SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureSupportCLM_apply_le, SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureSupportCLM_le, MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_of_support_subset, PiLp.eLpNorm_coordinate_norm_count_eq_enorm, PiLp.norm_le_card_rpow_mul_of_coordinate_norm_le") (uses := "sobolev.graph_space_order_restriction")
Let $`k\in\mathbb N`, let $`1\le q\le p\le\infty`, and suppose every
coordinate of $`U\in W^{k,p}(\Omega)` vanishes almost everywhere outside one
set $`S` of finite restricted measure. The same coordinate representatives
define an element $`R_{p,q,S}^{(k)}U\in W^{k,q}(\Omega)`. In particular,

$$`
\bigl(R_{p,q,S}^{(k)}U\bigr)_\alpha
  = U_\alpha
\quad\text{almost everywhere on }\Omega
`

for every symmetric multi-index $`\alpha` of order at most $`k`.

Set

$$`
\delta_{p,q}=\frac1q-\frac1p,
\qquad
N_{n,k}=\#\{\alpha:\lvert\alpha\rvert\le k\},
`

with $`1/\infty=0`, and write $`\mu_\Omega` for Lebesgue measure restricted
to $`\Omega`. Then

$$`
\left\|R_{p,q,S}^{(k)}U\right\|_{W^{k,q}}
\le
N_{n,k}^{\delta_{p,q}}\,
\mu_\Omega(S)^{\delta_{p,q}}\,
\|U\|_{W^{k,p}}.
`

The proof has two reusable layers. On each coordinate, the finite-measure
$`L^p\to L^q` estimate is applied after restricting the measure to a
measurable hull of $`S`; consequently $`S` itself need not be measurable.
The coordinate estimates are assembled by the sharp finite-dimensional
$`\ell^p\to\ell^q` comparison, producing the factor
$`N_{n,k}^{\delta_{p,q}}`.

More generally, let $`T:X\to W^{k,p}(\Omega)` be bounded linear and suppose
all coordinates of every $`Tx` share the same support set $`S`. Exponent
restriction then composes with it to give a bounded linear map

$$`
R_{p,q,S}^{(k)}\circ T:X\longrightarrow W^{k,q}(\Omega),
`

with operator-norm estimate

$$`
\left\|R_{p,q,S}^{(k)}\circ T\right\|
\le
N_{n,k}^{\delta_{p,q}}\,
\mu_\Omega(S)^{\delta_{p,q}}\,
\|T\|.
`

This operator form is what turns smooth cutoff localization into a map
$`W^{1,p}(\mathbb R^n)\to W^{1,1}(\mathbb R^n)` without rebuilding
linearity or continuity for that special case.
:::

On a domain of finite measure the common support can be the whole space.
This special case lowers $`W^{1,p}(\Omega)` to $`W^{1,2}(\Omega)` and
$`W^{1,1}(\Omega)` on bounded atlas domains.

:::definition "sobolev.finite_measure_exponent_restriction" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.finiteMeasureExponentRestrictionNormBound, SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasure_le, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM_apply, SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureCLM_apply_le, SobolevSpace.GraphSpace.norm_lowerExponentOfFiniteMeasureCLM_le, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM_refl, SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasureCLM_trans, SobolevSpace.GraphSpace.lowerOrderCLM_comp_lowerExponentOfFiniteMeasureCLM") (uses := "sobolev.finite_measure_support_exponent_restriction, sobolev.graph_space_order_restriction")
Let $`k\in\mathbb N`, let $`1\le q\le p\le\infty`, and assume the restricted
domain measure of $`\Omega` is finite. There is a continuous linear map

$$`
R_{p,q}^{(k)}:W^{k,p}(\Omega)\longrightarrow W^{k,q}(\Omega)
`

that changes only the exponent attached to each derivative coordinate.
For every symmetric multi-index $`\alpha` of order at most $`k`,

$$`
\bigl(R_{p,q}^{(k)}U\bigr)_\alpha
  = U_\alpha
\quad\text{almost everywhere on }\Omega.
`

Set

$$`
\delta_{p,q}=\frac1q-\frac1p,
\qquad
N_{n,k}=\#\{\alpha:\lvert\alpha\rvert\le k\},
`

with $`1/\infty=0`, and write $`\mu_\Omega` for Lebesgue measure restricted
to $`\Omega`. Specializing the common support in
{uses "sobolev.finite_measure_support_exponent_restriction"}[] to the whole ambient
space gives the quantitative estimate

$$`
\left\|R_{p,q}^{(k)}U\right\|_{W^{k,q}}
\le
N_{n,k}^{\delta_{p,q}}\,
\mu_\Omega(\mathbb R^n)^{\delta_{p,q}}\,
\|U\|_{W^{k,p}},
`

and the same expression bounds the operator norm. The volume factor is the
standard finite-measure $`L^p\to L^q` estimate on each weak-derivative
coordinate; the $`N_{n,k}` factor is inherited from the finite
$`\ell^p\to\ell^q` comparison for the graph-space coordinates.

The construction works at every order, and Rellich uses it directly.
Exponent restriction is the identity when $`p=q`, composes transitively
across intermediate exponents, and commutes with forgetting higher Sobolev
derivatives.
:::

The compactness proofs themselves rest on one abstract principle: a bounded
set that can be approximated uniformly, to any accuracy, by the images of
compact operators is totally bounded. The Fréchet–Kolmogorov arguments below
produce those approximating compact operators as finite grid averages.

:::theorem "sobolev.compact_uniform_approximation" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.totallyBounded_of_uniform_compact_approximation")
Let $`E` be a real normed space and let $`S\subseteq E` be bounded. Suppose
that for every $`\varepsilon>0` there is a compact continuous linear operator
$`A_\varepsilon:E\to E` satisfying

$$`
\sup_{x\in S}\|A_\varepsilon x-x\|<\varepsilon.
`

Then $`S` is totally bounded.
:::

:::proof "sobolev.compact_uniform_approximation"
Choose $`A=A_{\varepsilon/2}`. Compactness of $`A` places $`A(S)` inside a
compact set, hence inside finitely many balls of radius $`\varepsilon/2`.
Every $`x\in S` is within $`\varepsilon/2` of $`Ax`, so the same finite set of
centers covers $`S` by balls of radius $`\varepsilon`.
:::

The approximation error of a grid average is governed by how much a function
changes under small translations, so the analytic input is an estimate on
translation defects $`\tau_hu-u`. Translation is first set up as an isometry
of the global $`L^p` model, with the algebraic properties that the defect
computations use.

:::definition "sobolev.rellich_translation" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.translateLp, SobolevSpace.GraphSpace.Rellich.translateLp_apply_ae, SobolevSpace.GraphSpace.Rellich.norm_translateLp, SobolevSpace.GraphSpace.Rellich.translateLp_zero, SobolevSpace.GraphSpace.Rellich.translateLp_add, SobolevSpace.GraphSpace.Rellich.translateLp_lpSMul, SobolevSpace.GraphSpace.Rellich.translateLp_sub_apply_ae, SobolevSpace.GraphSpace.Rellich.translationMeasurePreserving") (uses := "sobolev.graph_ambient")
For $`1\leq p\leq\infty` and $`h\in\mathbb R^n`, the map $`x\mapsto x+h`
preserves Lebesgue measure, so composition with it is a linear isometry of
the whole-space coordinate $`L^p` space of the graph model:

$$`
\tau_h:L^p(\mathbb R^n)\longrightarrow L^p(\mathbb R^n),
\qquad
(\tau_hu)(x)=u(x+h)\ \text{a.e.},
\qquad
\|\tau_hu\|_{L^p}=\|u\|_{L^p} .
`

Translations form an additive action, $`\tau_0=\mathrm{id}` and
$`\tau_a\tau_b=\tau_{a+b}`. Translating a product translates both the
$`L^\infty` coefficient and the field:
$`\tau_h(a\,u)=(\tau_ha)(\tau_hu)`. The translation defect has the
representative
$`(\tau_hu-u)(x)=u(x+h)-u(x)` almost everywhere. Translation defects of
zero-extended $`H^1_0` functions and of $`W^{1,1}` functions are the
quantities estimated in the two Fréchet–Kolmogorov layers below.
:::

For fixed $`h`, the isometry gives continuity in the function being
translated. This is what passes smooth estimates to Sobolev limits in the
density arguments. Integrating over shifts uses a second property:
continuity in $`h` makes the translation defect continuous on the compact
shift box. The next theorem proves this for finite exponents; it can fail
in $`L^\infty`.

:::theorem "sobolev.rellich_translation_continuity" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.continuous_translateLp") (uses := "sobolev.rellich_translation")
Let $`1\leq p<\infty` and $`u\in L^p(\mathbb R^n)`. The translation map

$$`
\mathbb R^n\longrightarrow L^p(\mathbb R^n),
\qquad
h\longmapsto\tau_hu,
`

is continuous. In particular, $`h\mapsto\|\tau_hu-u\|_{L^p}` is continuous. In the
$`L^2` grid argument, its square is therefore integrable on the compact
box of within-cell shifts.
:::

:::proof "sobolev.rellich_translation_continuity"
Every $`\tau_h` is an isometry, so it suffices to check continuity on a dense
class and use equicontinuity: for $`g` close to $`u` in $`L^p`,
$`\|\tau_hu-\tau_{h'}u\|_p\leq2\|u-g\|_p+\|\tau_hg-\tau_{h'}g\|_p`. For
$`p<\infty`, bounded continuous functions with compact support are dense,
and for such $`g` the last term tends to zero as $`h\to h'` by uniform
continuity and bounded support. The formal proof invokes Mathlib's joint
continuity of composition with a continuously varying measure-preserving
map at finite exponent, applied to the continuous family
$`h\mapsto(x\mapsto x+h)` in the compact-open topology.
:::

We first carry out the Hilbert-space argument for zero-trace functions.
This is the cleanest case because zero extension introduces no artificial
boundary derivative.

:::theorem "sobolev.rellich_zero_trace_translation" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.translationDefectCLM.norm_le") (uses := "sobolev.graph_space, sobolev.zero_extension_h10, sobolev.rellich_translation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be measurable, let
$`u\in H^1_0(\Omega)`, and write $`\widetilde u` for its zero extension to
$`\mathbb R^n`. For every translation vector $`h`,

$$`
\|\widetilde u(\,\cdot+h)-\widetilde u\|_{L^2(\mathbb R^n)}
\le \|h\|\,\|u\|_{H^1_0(\Omega)}.
`

The constant is exactly one relative to the graph norm used in the
development. The estimate is uniform on every norm-bounded subset of
$`H^1_0(\Omega)`.
:::

:::proof "sobolev.rellich_zero_trace_translation"
For restrictions of global test functions, integrate the gradient along the
line segment from $`x` to $`x+h`, then use Cauchy–Schwarz and translation
invariance of Lebesgue measure. Test functions are dense in
$`H^1_0(\Omega)`, zero extension is isometric, and the inequality defines a
closed condition. Density therefore extends the smooth estimate to every
zero-trace Sobolev value.
:::

The translation estimate converts directly into a grid-averaging estimate:
two points of a cell of width $`\delta` differ by a shift of length at most
$`\sqrt n\,\delta`, so the cell-average error is controlled by translation
defects at that scale. For bounded $`\Omega` the zero extension vanishes
outside finitely many cells, which is the support hypothesis of the
estimate, and the averaging operator then has finite rank.

:::theorem "sobolev.rellich_l2_grid_approximation" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.euclideanGridAverageOperator.norm_sub_le") (uses := "sobolev.rellich_zero_trace_translation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be measurable. Fix a grid width $`\delta>0` and a radius
$`R`. Assume the zero extension of $`u\in H^1_0(\Omega)` vanishes almost
everywhere outside the finite union of
cells in the finite grid cover selected for the ball of radius $`R`.
Let $`A_{\delta,R}` replace the function on each retained cell by its cell
average. Then

$$`
\|A_{\delta,R}\widetilde u-\widetilde u\|_{L^2(\mathbb R^n)}
\le
\sqrt{2^n n}\,\delta\,\|u\|_{H^1_0(\Omega)}.
`

For fixed $`\delta` and $`R`, the operator $`A_{\delta,R}` has
finite-dimensional range and is therefore compact.
:::

:::proof "sobolev.rellich_l2_grid_approximation"
The squared cell-average error is bounded by the average of
$`|\widetilde u(x)-\widetilde u(y)|^2` over pairs of points in the same
cell. Write $`h=y-x`. Such shifts lie in the box
$`[-\delta,\delta]^n`, where $`\|h\|^2\le n\delta^2`. The translation
estimate bounds the integrated defect by

$$`
(2\delta)^n n\delta^2\|u\|^2.
`

Dividing by the cell volume $`\delta^n` gives
$`2^n n\delta^2\|u\|^2`; taking square roots yields the stated estimate.
Only finitely many cells are retained, so the range is spanned by finitely
many cell indicators.
:::

The grid estimate supplies exactly the hypotheses of the uniform compact
approximation criterion, and the Hilbert case of Rellich's theorem follows in
its global form.

:::theorem "sobolev.rellich_zero_extension_global" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.zeroExtendedBaseL2.isCompactOperator") (uses := "sobolev.compact_uniform_approximation, sobolev.rellich_l2_grid_approximation, sobolev.zero_extension_h10")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`\Omega` is measurable and bounded, then zero extension followed by the
base-coordinate projection is a compact operator

$$`
H^1_0(\Omega)\longrightarrow L^2(\mathbb R^n).
`
:::

:::proof "sobolev.rellich_zero_extension_global"
Boundedness of $`\Omega` places the support of every zero-extended base
coordinate in one fixed ball. Apply the grid estimate to the image of the
closed unit ball. Its error tends to zero uniformly as $`\delta\downarrow0`,
while every grid-average operator is compact. The uniform compact
approximation criterion makes the image totally bounded; completeness of
$`L^2` then gives compact closure.
:::

Restriction from $`\mathbb R^n` back to $`\Omega` is continuous, so the global
$`L^2` result gives compactness on the domain. The same conclusion holds at
every finite exponent. Zero extension again supplies bounded support and a
uniform translation estimate; a reduction to the $`L^1` compactness criterion
handles the remaining exponents.

:::theorem "sobolev.rellich_zero_trace" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.baseCoordCLM.eq_restrict_comp_zeroExtendedBaseL2, SobolevSpace.GraphSpace.baseCoordCLM.isCompactOperator_of_bounded, SobolevSpace.GraphSpace.RellichKondrachov.wkp0BaseCoordinate_isCompactOperator_of_bounded") (uses := "sobolev.rellich_zero_extension_global")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be measurable and bounded and let
$`1\leq p<\infty`. The canonical base-coordinate map

$$`
W^{1,p}_0(\Omega)\longrightarrow L^p(\Omega)
`

is compact. Here $`W^{1,p}_0` is the closure of smooth functions compactly
supported in $`\Omega`, taken in the Sobolev graph norm. On open sets
this gives the usual zero-boundary space. No boundary regularity is required,
and the theorem has no lower bound on $`n`; in particular it includes
$`n=1`. Taking $`p=2` recovers the $`H^1_0\to L^2` statement above.
:::

:::proof "sobolev.rellich_zero_trace"
Zero extension sends the unit ball of $`W^{1,p}_0(\Omega)` to a bounded
family in $`L^p(\mathbb R^n)` supported in one fixed ball. Its translations
satisfy a uniform bound $`\|\tau_h u-u\|_p\leq C\|h\|`.

At $`p=1`, the finite-grid criterion makes this family totally bounded. For
$`p>1`, apply the signed power $`u\mapsto\operatorname{sgn}(u)|u|^p`.
Hölder's inequality gives the transformed family a uniform $`L^1` translation
bound. The same grid criterion gives compact closure in $`L^1`, and the
continuous inverse signed power sends that compact set back into $`L^p`.
Thus the original zero-extended family has compact closure. Continuous
restriction to $`\Omega` proves compactness of the base-coordinate map.
For $`p=2`, the preceding Hilbert grid argument also proves this conclusion
directly.
:::

For an unrestricted $`H^1(\Omega)` value, literal zero extension need not
belong to global $`H^1`. The operational atlas instead supplies an extension,
after which a cutoff creates a zero-trace value on one bounded ball.

:::theorem "sobolev.rellich_c1" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.Rellich.baseCoordinateL2_isCompactOperator_of_c1Domain") (uses := "sobolev.c1_extension, sobolev.rellich_zero_extension_global")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0` and let $`\Omega\subseteq\mathbb R^n` carry the operational
bounded $`C^1` atlas. The base-coordinate map

$$`
H^1(\Omega)\longrightarrow L^2(\Omega)
`

is compact.
:::

:::proof "sobolev.rellich_c1"
Apply the bounded extension operator
$`H^1(\Omega)\to H^1(\mathbb R^n)`. Choose a smooth cutoff equal to one on
$`\overline\Omega` and supported in a ball $`B`. Multiplication by the cutoff
and restriction to $`B` give a continuous map into $`H^1_0(B)`. Compose this
map with the compact zero-extension theorem on $`B`, then restrict the
resulting global $`L^2` function back to $`\Omega`. Extension agreement and
the fact that the cutoff is one on $`\Omega` identify this compact composite
with the original base-coordinate map.
:::

Compactness in one Lebesgue space suffices for the strict-subcritical transfer.

:::theorem "sobolev.rellich_subcritical_transfer" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.inclusion_isCompactOperator_of_compact_lower, SobolevSpace.GraphSpace.RellichKondrachov.inclusion_isCompactOperator_of_compact_base") (uses := "sobolev.rellich_inclusion_operator, sobolev.c1_critical_membership")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` carry the operational bounded $`C^1` atlas, let
$`1\le p<n`, and choose exponents

$$`
1\le s\le p^*,
\qquad
1\le q<p^*.
`

If

$$`
J_{p,s}:W^{1,p}(\Omega)\longrightarrow L^s(\Omega)
`

is compact, then

$$`
J_{p,q}:W^{1,p}(\Omega)\longrightarrow L^q(\Omega)
`

is compact. Taking $`s=p` gives the base-exponent specialization.
:::

:::proof "sobolev.rellich_subcritical_transfer"
Start with a sequence in the closure of the image of the Sobolev unit ball.
Approximate it by actual images $`J_{p,q}U_m`. Compactness of $`J_{p,s}`
gives a subsequence for which the base representatives converge in $`L^s`,
hence in measure. The critical inclusion $`J_{p,p^*}` uniformly bounds the
same representatives in $`L^{p^*}`.

Because $`q<p^*`, the critical bound makes the $`q`th powers uniformly
integrable. On the finite domain measure, tightness is automatic by choosing
the whole space. Vitali convergence upgrades convergence in measure to
convergence in $`L^q`. The original closure sequence differs from the actual
images by an error tending to zero, so the selected subsequence also
converges. Thus the closure of the image of the unit ball is sequentially
compact and hence compact.
:::

The Hilbert theorem is a short consequence of the concrete
$`H^1\to L^2` compact operator and the transfer theorem.

:::theorem "sobolev.rellich_subcritical_hilbert" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.inclusion_fromH1_isCompactOperator_of_c1Domain") (uses := "sobolev.rellich_c1, sobolev.rellich_subcritical_transfer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>2`, let $`\Omega` carry the operational bounded $`C^1` atlas, and
let $`1\le q<2^*`. Then

$$`
H^1(\Omega)\longrightarrow L^q(\Omega)
`

is compact. The target endpoint $`q=1` is included.
:::

:::proof "sobolev.rellich_subcritical_hilbert"
At $`q=2`, the general inclusion operator agrees with the compact
base-coordinate map. Apply strict-subcritical transfer with lower target
$`s=2` and the critical $`H^1\to L^{2^*}` bound.
:::

:::theorem "sobolev.rellich_subcritical_general" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.inclusion_toL2_isCompactOperator_of_two_le") (uses := "sobolev.finite_measure_exponent_restriction, sobolev.rellich_c1, sobolev.rellich_subcritical_transfer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`2\le p<n` and let $`\Omega` carry the operational bounded $`C^1`
atlas. Then the canonical inclusion

$$`
W^{1,p}(\Omega)\longrightarrow L^2(\Omega)
`

is compact.
:::

:::proof "sobolev.rellich_subcritical_general"
Finite measure gives the continuous coordinate-preserving map
$`W^{1,p}(\Omega)\to H^1(\Omega)`. Compose it with the compact
$`H^1(\Omega)\to L^2(\Omega)` base map. This proves compactness into
$`L^2`. Compactness into every $`L^q` with $`1\le q<p^*` is the separate
theorem {bpref "sobolev.rellich_full_subcritical"}[proved below].
:::

To reach $`1\le p<2`, the development proves the endpoint translation
estimate directly in $`W^{1,1}(\mathbb R^n)`.

:::theorem "sobolev.rellich_l1_translation" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.globalTranslationDefectL1.norm_le") (uses := "sobolev.global_density, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`U\in W^{1,1}(\mathbb R^n)` and $`h\in\mathbb R^n`,

$$`
\|U(\,\cdot+h)-U\|_{L^1(\mathbb R^n)}
\le \|h\|\,\|U\|_{W^{1,1}(\mathbb R^n)}.
`
:::

:::proof "sobolev.rellich_l1_translation"
For a smooth compactly supported function $`\varphi`, the fundamental theorem
of calculus along $`t\mapsto x+th` gives

$$`
|\varphi(x+h)-\varphi(x)|
\le
\|h\|\int_0^1 |\nabla\varphi(x+th)|\,dt.
`

Integrate in $`x`, use translation invariance and Fubini, and bound the
$`L^1` gradient by the graph norm. Global finite-exponent density approximates
an arbitrary $`W^{1,1}` value by smooth compactly supported functions.
Continuity of translation and closedness of the inequality pass the estimate
to the limit.
:::

The $`L^1` translation estimate takes the place of the zero-trace estimate
of the Hilbert case. The literal zero extension of an unrestricted
$`W^{1,1}(\Omega)` function need not be a global Sobolev function, so the
operational atlas extension, localized in a ball containing
$`\overline\Omega`, supplies a global function with bounded support instead.

:::theorem "sobolev.rellich_supported_l1" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.supportedExtensionBaseCoordinateL1_isCompactOperator") (uses := "sobolev.compact_uniform_approximation, sobolev.rellich_l1_translation, sobolev.c1_extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let the operational $`C^1` extension of $`W^{1,1}(\Omega)` be localized
inside one ball. The map taking a Sobolev value to the global order-zero
coordinate of this supported extension is compact into
$`L^1(\mathbb R^n)`.
:::

:::proof "sobolev.rellich_supported_l1"
The supported extension operator uniformly bounds the global
$`W^{1,1}` norm and places every base coordinate in one fixed ball. Finite
grid-cell averages have finite-dimensional range. The global translation
estimate bounds their approximation error by a constant times the grid
width, uniformly on the source unit ball. The compact-approximation
criterion gives total boundedness of the image and therefore compactness.
:::

Restricting to $`\Omega` gives the endpoint $`p=1`, which the Hilbert route
above does not reach because it needs $`p\geq2`.

:::theorem "sobolev.rellich_endpoint_one" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.baseCoordinateL1_isCompactOperator_of_c1Domain, SobolevSpace.GraphSpace.RellichKondrachov.inclusion_toL1_isCompactOperator_of_c1Domain") (uses := "sobolev.rellich_supported_l1")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0` and let $`\Omega\subseteq\mathbb R^n` carry the operational
bounded $`C^1` atlas. Then the base-coordinate map

$$`
W^{1,1}(\Omega)\longrightarrow L^1(\Omega)
`

is compact. Stated through the general subcritical inclusion, the theorem
acquires the additional condition $`1<n`, because that inclusion assumes the
source exponent satisfies $`p<n`.
:::

:::proof "sobolev.rellich_endpoint_one"
Choose a supported global extension inside a fixed ball. Its global
base-coordinate map is compact by the preceding theorem. Restriction
$`L^1(\mathbb R^n)\to L^1(\Omega)` is continuous, and the extension agrees
almost everywhere with the original function on $`\Omega`. The resulting
compact composite is therefore exactly the domain base-coordinate map.
:::

Exponent restriction and the transfer theorem carry the endpoint to every
source exponent.

:::theorem "sobolev.rellich_w11_reduction" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.inclusion_isCompactOperator_of_compact_w11") (uses := "sobolev.finite_measure_exponent_restriction, sobolev.rellich_endpoint_one, sobolev.rellich_subcritical_transfer")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` carry the operational bounded $`C^1` atlas, and let
$`1\le p<n` and $`1\le q<p^*`. If the endpoint inclusion

$$`
W^{1,1}(\Omega)\longrightarrow L^1(\Omega)
`

is compact, then

$$`
W^{1,p}(\Omega)\longrightarrow L^q(\Omega)
`

is compact.
:::

:::proof "sobolev.rellich_w11_reduction"
The finite-measure restriction operator continuously lowers
$`W^{1,p}(\Omega)` to $`W^{1,1}(\Omega)` without changing any derivative
representative. Composing with the compact endpoint map gives compactness of
$`W^{1,p}(\Omega)\to L^1(\Omega)`. Apply the strict-subcritical transfer
theorem with lower target $`s=1`.
:::

Combining the endpoint theorem with the $`W^{1,1}` reduction gives the
Rellich–Kondrachov theorem on operational $`C^1` domains in its full
subcritical range.

:::theorem "sobolev.rellich_full_subcritical" (parent := "sobolev.compactness") (lean := "SobolevSpace.GraphSpace.RellichKondrachov.inclusion_isCompactOperator_of_c1Domain") (uses := "sobolev.rellich_endpoint_one, sobolev.rellich_w11_reduction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`1\le p<n`, let $`\Omega` carry the operational bounded $`C^1` atlas,
and let $`1\le q<p^*`. Then the canonical inclusion

$$`
W^{1,p}(\Omega)\longrightarrow L^q(\Omega)
`

is compact.

This includes both endpoints $`p=1` and $`q=1`.
:::

:::proof "sobolev.rellich_full_subcritical"
From $`1\le p<n` one obtains $`1<n`, so the endpoint inclusion is available
through the general inclusion. Its compactness was proved by
supported extension, the global $`L^1` translation estimate, and finite-cell
averaging. Apply the $`W^{1,1}` reduction theorem to obtain the desired
target exponent $`q`.
:::

The inequality $`q<p^*` is essential. At $`q=p^*`, rescaled bumps can keep
their critical norm while concentrating near one point; no strongly
convergent critical subsequence need exist. The library proves continuity at
the critical exponent and compactness below it; the computation below, which
shows the failure at $`q=p^*`, is an informal calculation.

Here is the scaling behind that counterexample. Choose an interior point
$`x_0` and a nonzero smooth function $`\phi` supported in the unit ball.
For $`1\leq p<n` and sufficiently small $`\varepsilon>0`, the functions

$$`
u_\varepsilon(x)
  =\varepsilon^{1-n/p}\phi\!\left(\frac{x-x_0}{\varepsilon}\right)
`

are supported inside the domain. Changing variables gives

$$`
\begin{aligned}
\|\nabla u_\varepsilon\|_p&=\|\nabla\phi\|_p,\\
\|u_\varepsilon\|_p&=\varepsilon\|\phi\|_p,\\
\|u_\varepsilon\|_q&=\varepsilon^{1-n/p+n/q}\|\phi\|_q.
\end{aligned}
`

At $`q=p^*`, the last exponent is zero: the critical norm stays positive,
although $`u_\varepsilon(x)\to0` at every $`x\ne x_0`. A strongly convergent
critical subsequence would therefore have limit zero, contradicting its
constant norm. Below $`p^*`, the exponent is positive and the same sequence
does converge strongly to zero. The strict inequality in the theorem is
exactly what makes this concentration disappear in the target norm.
