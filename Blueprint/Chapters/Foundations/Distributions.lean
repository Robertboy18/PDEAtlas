/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Foundations.Coordinates
import Blueprint.Commands.Figures
import PDE.Analysis.Calculus.CompactCurry
import PDE.DistributionTheory.Distribution.Convolution
import PDE.DistributionTheory.Distribution.Convolution.ConstantCoefficient
import PDE.DistributionTheory.Distribution.Convolution.Derivative
import PDE.DistributionTheory.Distribution.FixedSupport
import PDE.DistributionTheory.Distribution.Heaviside
import PDE.DistributionTheory.Distribution.Operator.Commutation
import PDE.DistributionTheory.Distribution.Operator.FundamentalSolution
import PDE.DistributionTheory.Distribution.Operator.Laplacian
import PDE.DistributionTheory.Distribution.Regular
import PDE.DistributionTheory.Distribution.SliceFamily
import PDE.DistributionTheory.Distribution.Support.ConstantCoefficient
import PDE.DistributionTheory.Distribution.Support.LocalizedPushforward
import PDE.DistributionTheory.Distribution.Support.ProperPushforward
import PDE.DistributionTheory.Distribution.Support.SmoothMultiplier
import PDE.DistributionTheory.Distribution.Support.TensorProduct
import PDE.DistributionTheory.Distribution.TensorProduct
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.DistributionTheory.TestFunction.Rellich
import PDE.Elliptic.Semilinear.Pohozaev
import PDE.DistributionTheory.TestFunction.Slice
import PDE.DistributionTheory.TestFunction.TensorProduct

/-!
# Distributions

Test functions, distributions, and canonical distributional operations.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Canonical distributions" =>

# Why distributions matter

Solutions of hyperbolic PDEs can develop shocks (discontinuities in finite time), elliptic
regularity theory must handle forcing terms in $`L^p` rather than $`C^\infty`,
and fundamental solutions like the Newtonian potential are singular at the
origin. The theory of distributions, created by Laurent Schwartz (1950,
*Théorie des distributions*), extends differentiation to all these objects by
replacing the pointwise derivative with a duality pairing against smooth test
functions.

The starting point is integration by parts. If $`f` is smooth and $`\varphi` is
compactly supported, then $`\int f'\varphi=-\int f\varphi'` with no boundary
terms. The right-hand side makes sense even when $`f` is merely locally
integrable, or even when it is not a function at all but only a linear
functional on test functions. By declaring the right-hand side to be the
*definition* of the distributional derivative, one obtains a differentiation
theory that:

- applies to every locally integrable function, including those with jumps;
- produces the Dirac mass as the derivative of the Heaviside step function;
- supplies the language in which singular fundamental solutions are stated;
- supports Fourier analysis after passing to tempered distributions.

A test function is a smooth, localized probe. The Dirac mass records its
value at one point: $`\delta_0(\varphi)=\varphi(0)`. Its derivative records
the negative slope there:
$`D\delta_0(\varphi)=-\varphi'(0)`. Neither operation asks for a pointwise
value of the distribution itself. Equality of distributions means agreement
on every such probe.

Approximation is the other route to the same objects. Convolve a rough
function with a smooth kernel of shrinking width and you get smooth
functions converging to it, which is how the Sobolev chapter carries
classical calculus into the weak setting.

{leanpde_figure "mollification"}

At the jump, each smoothed profile is continuous while the limiting step is
not. We therefore need a mode of convergence that tolerates this discrepancy:
local integral convergence, or convergence after pairing with a test function.
This is why the weak-derivative argument later estimates the approximation
in a norm instead of requiring uniform agreement at every point.

{Informal.citet "evans-2010"}[] treats mollification in Appendix C.5;
the theory of distributions is due to Schwartz (1950, 1951). We follow Mathlib's
formalization, which constructs test functions as smooth compactly supported
functions and distributions as their continuous dual.

# Test functions and their topology

The topology on these probes makes “continuous linear functional” an
analytic condition. First fix a compact set $`K` containing every support.
Convergence of test functions with support in $`K` requires uniform
convergence of every derivative, measured by the seminorms

$$`
p_m(\varphi)=\max_{|\alpha|\leq m}\sup_{x\in K}|D^\alpha\varphi(x)|
\qquad(m=0,1,2,\ldots).
`

A seminorm measures size but may vanish on a nonzero vector. The family
records all derivative orders. The test-function topology, the *LF topology*,
joins these fixed-support spaces as $`K` grows. On each fixed support,
continuity of a scalar distribution gives an estimate
$`|T(\varphi)|\leq C_Kp_m(\varphi)` for some finite order $`m` and constant
$`C_K`. Dirac needs order zero; its first derivative needs order one.

Regular distributions embed locally integrable functions into the dual
space, while Dirac masses represent evaluation at a point. Here
*regular distribution* means one represented by a locally integrable
function, through $`T_f(\varphi)=\int f\varphi`; it does not mean a smooth
function. The Heaviside function is regular in this sense, but its derivative
$`\delta_0` has no locally integrable density. By comparison, $`|x|` has
weak derivative $`\operatorname{sign}(x)`, an actual bounded function. This
distinction is the entry point to Sobolev spaces:
every distribution can be differentiated, but Sobolev membership asks that
the derivatives be represented by functions with specified integrability.

Almost all of the difficulty here sits upstream of the distributions. The Zulip
thread [Distribution theory](https://leanprover-community.github.io/archive/stream/116395-maths/topic/Distribution.20theory.html)
spent most of 2022 not on distributions but on the locally convex topology that
test functions carry, and on whether a locally convex space should hold a chosen
family of seminorms as data or merely assert that one exists. The conclusion
there was that the family is not canonical and should not be data. We inherit
that decision. The test-function space therefore appears as
`𝓓((⊤ : Opens (ℝ^n)), ℝ)` with its topology already fixed, and the
continuity of a distribution is a hypothesis we can state rather than a
construction we have to build.

Tensor products and convolutions are built in three steps. First, the external
tensor product $`\varphi\otimes\psi` of test functions and the restriction
$`\Phi\mapsto\Phi_x` of a test function on a product to a coordinate fiber are
continuous for the test-function topology. Second, applying a fixed
distribution $`T` to the moving fibers gives a test function
$`x\mapsto\langle T,\Phi_x\rangle` that depends continuously on $`\Phi`;
transposing this map defines $`S\otimes T`, with its elementary-tensor, Dirac,
and derivative laws. Third, for compactly carried distributions on a
finite-dimensional real normed space, pushing $`S\otimes T` forward along
addition, after a cutoff, defines the convolution $`S*T`, with its
compact-carrier, support, and Dirac laws.

:::group "foundations.distributions"
Distributions
:::

:::definition "foundations.distributions.test_function" (parent := "foundations.distributions") (lean := "TestFunction.lineDerivCLM") (uses := "foundations.euclidean_space.type, foundations.derivatives.partial")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "256"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The test-function space is

$$`
  \mathcal D(\mathbb R^n)=C_c^\infty(\mathbb R^n;\mathbb R).
`

Mathlib bundles smoothness, compact support, and the canonical LF topology in
`𝓓((⊤ : Opens (ℝ^n)), ℝ)`. Directional differentiation
$`\varphi\mapsto D_v\varphi` is a continuous linear endomorphism of this
space; choosing $`v=e_i` gives the coordinate derivative.
:::

Because $`D_v` is a continuous linear endomorphism of
$`\mathcal D(\mathbb R^n)`, its transpose acts on the continuous dual. That
transpose, with a sign, is the distributional derivative, and continuity of
$`D_v` for the LF topology is exactly what makes the transposed operator
continuous for the dual topology.

:::definition "foundations.distributions.distribution" (parent := "foundations.distributions") (lean := "Distribution.lineDerivCLM") (uses := "foundations.distributions.test_function")
A distribution is a continuous linear functional

$$`
  T:\mathcal D(\mathbb R^n)\longrightarrow\mathbb R,
  \qquad
  \mathcal D'(\mathbb R^n):=\mathcal D(\mathbb R^n)'.
`

Mathlib's `𝓓'((⊤ : Opens (ℝ^n)), ℝ)` is this compact-convergence dual.
For the smooth test-function space, compact convergence agrees with bounded
convergence, but it is stronger than mere pointwise convergence for general
filters. Distributional differentiation is the negative transpose of
test-function differentiation.
:::

Before any dual construction, one product identity on the test-function side is
needed. The Leibniz rule for $`D_v` on products of test functions is used
twice: once for the coordinate derivatives of external tensor products,
and once, after transposition, for the Leibniz law of smooth multipliers.

:::theorem "foundations.distributions.test_derivative_leibniz" (parent := "foundations.distributions") (lean := "TestFunction.lineDerivCLM_mul") (uses := "foundations.distributions.test_function")
For every direction $`v`, test-function differentiation satisfies

$$`
  D_v(\varphi\psi)
  =(D_v\varphi)\psi+\varphi(D_v\psi).
`

Specializing $`v=e_i` gives the coordinate Leibniz rule.
:::

:::proof "foundations.distributions.test_derivative_leibniz"
The ordinary directional derivative satisfies the product rule pointwise.
Both products retain compact support and smoothness, so the pointwise identity
lifts to equality in the bundled test-function space and hence to the
continuous linear derivative operator.
:::

Tensor products of distributions are defined by transposing an operation on test
functions on a product space. The first ingredient is the pointwise product of a
test function in $`x` with one in $`y`, which is again smooth with compact
support on $`E\times F`.

:::definition "foundations.distributions.test_tensor_product" (parent := "foundations.distributions") (lean := "TestFunction.tensorProduct") (uses := "foundations.distributions.test_function")
For scalar test functions $`\varphi\in\mathcal D(E)` and
$`\psi\in\mathcal D(F)`, their external tensor product is

$$`
  (\varphi\otimes\psi)(x,y)=\varphi(x)\psi(y)
  \in\mathcal D(E\times F).
`
:::

The pointwise formula alone does not make the tensor product usable in dual
constructions; for that, the product must be continuous in each factor for the
LF topologies, and its support must be controlled by the factor supports. Both
facts hold without any finiteness assumption on $`E` or $`F`.

:::theorem "foundations.distributions.test_tensor_product_topology" (parent := "foundations.distributions") (lean := "TestFunction.tsupport_tensorProduct_subset, TestFunction.tensorProductRightCLM_apply, TestFunction.tensorProductLeftCLM_apply") (uses := "foundations.distributions.test_tensor_product")
The external tensor product has the support bound

$$`
  \operatorname{supp}(\varphi\otimes\psi)
  \subseteq\operatorname{supp}\varphi\times\operatorname{supp}\psi.
`

For fixed $`\psi`, the map $`\varphi\mapsto\varphi\otimes\psi` is continuous
linear between the canonical LF test-function spaces, and the analogous
statement holds with the left factor fixed.
:::

:::proof "foundations.distributions.test_tensor_product_topology"
The pointwise product vanishes off the product of the two closed compact
supports. On a fixed support stage $`K`, the iterated product rule bounds the
$`k`th derivative seminorm by $`2^k` times a finite maximum of seminorms of
the fixed factor and the source seminorm on $`K`. The seminorm criterion gives
a continuous linear map on every stage, and `TestFunction.limitCLM` lifts it
to the LF topology. Swapping the coordinates proves continuity in the other
factor.
:::

Directional derivatives on $`E\times F` split into a component along $`E` and
one along $`F`. On an elementary tensor each component differentiates only its
own factor, which is the test-function form of the derivative laws proved later
for $`S\otimes T`.

:::theorem "foundations.distributions.test_tensor_product_derivatives" (parent := "foundations.distributions") (lean := "TestFunction.lineDerivCLM_tensorProduct_fst, TestFunction.lineDerivCLM_tensorProduct_snd") (uses := "foundations.distributions.test_tensor_product, foundations.distributions.test_derivative_leibniz")
Directional differentiation in either coordinate acts on the corresponding
factor:

$$`
  D_{(v,0)}(\varphi\otimes\psi)=(D_v\varphi)\otimes\psi,
  \qquad
  D_{(0,w)}(\varphi\otimes\psi)=\varphi\otimes(D_w\psi).
`
:::

:::proof "foundations.distributions.test_tensor_product_derivatives"
Apply the Fréchet product and chain rules to the two coordinate projections.
In the first identity the derivative of the second projection vanishes on
$`(v,0)`; in the second identity the derivative of the first projection
vanishes on $`(0,w)`.
:::

Slicing is the operation dual to forming tensor products: instead of building a
function on $`E\times F` from two factors, one fixes a coordinate of a function
on $`E\times F` and reads off a test function in the remaining variable.
Applying a distribution to such slices is how the tensor product of
distributions is eventually defined.

:::definition "foundations.distributions.test_slice" (parent := "foundations.distributions") (lean := "TestFunction.sliceRight, TestFunction.sliceLeft") (uses := "foundations.distributions.test_function")
For $`\Phi\in\mathcal D(E\times F)`, every fixed coordinate determines test
functions

$$`
  \Phi_x(y):=\Phi(x,y)\in\mathcal D(F),
  \qquad
  \Phi^y(x):=\Phi(x,y)\in\mathcal D(E).
`

These are the right and left coordinate slices of $`\Phi`.
:::

Each slice is the pullback of $`\Phi` along a coordinate inclusion
$`y\mapsto(x,y)` or $`x\mapsto(x,y)`. These inclusions are closed embeddings,
hence proper.

:::theorem "foundations.distributions.test_slice_topology" (parent := "foundations.distributions") (lean := "TestFunction.sliceRightCLM_apply, TestFunction.sliceLeftCLM_apply, TestFunction.tsupport_sliceRight_subset, TestFunction.tsupport_sliceLeft_subset") (uses := "foundations.distributions.test_slice")
For fixed $`x` or $`y`, slicing is a continuous linear map between the
canonical LF test-function spaces. Its support lies in the corresponding
fiber of the original support:

$$`
  \operatorname{supp}\Phi_x
  \subseteq\{z:(x,z)\in\operatorname{supp}\Phi\},
  \qquad
  \operatorname{supp}\Phi^y
  \subseteq\{z:(z,y)\in\operatorname{supp}\Phi\}.
`
:::

:::proof "foundations.distributions.test_slice_topology"
Each coordinate-fiber inclusion is a smooth proper map: it is a closed
embedding with range $`\{x\}\times F` or $`E\times\{y\}`. Proper
precomposition therefore gives the continuous linear slice map in the LF
topology. The general support bound for composition gives the stated fiber
inclusions.
:::

Two computational rules for slices are what the later derivative and
elementary-tensor laws for $`S\otimes T` reduce to: a derivative in the retained
variable can be taken before or after slicing, and slicing an elementary tensor
$`\varphi\otimes\psi` returns the fixed factor scaled by a value of the other.

:::theorem "foundations.distributions.test_slice_calculus" (parent := "foundations.distributions") (lean := "TestFunction.lineDerivCLM_sliceRight, TestFunction.lineDerivCLM_sliceLeft, TestFunction.sliceRight_tensorProduct, TestFunction.sliceLeft_tensorProduct") (uses := "foundations.distributions.test_slice, foundations.distributions.test_tensor_product_derivatives")
Coordinate differentiation commutes with slicing:

$$`
  D_w\Phi_x=(D_{(0,w)}\Phi)_x,
  \qquad
  D_v\Phi^y=(D_{(v,0)}\Phi)^y.
`

For an external tensor product, slicing evaluates the fixed factor:

$$`
  (\varphi\otimes\psi)_x=\varphi(x)\psi,
  \qquad
  (\varphi\otimes\psi)^y=\psi(y)\varphi.
`
:::

:::proof "foundations.distributions.test_slice_calculus"
The derivative identities follow from the Fréchet chain rule for the two
affine coordinate inclusions. The tensor identities are pointwise
evaluations of $`(\varphi\otimes\psi)(x,y)=\varphi(x)\psi(y)`.
:::

Applying a distribution $`T` to the moving slices $`\Phi_x` produces a function
of $`x`, and its smoothness is not automatic: the pairing must be differentiated
under a distribution rather than under an integral. The abstract tool is a
differentiability statement for compactly indexed families in the supremum norm,
with no finite-dimensionality assumed on $`E`, $`F`, or $`G`.

:::theorem "foundations.distributions.compact_curry_derivative" (parent := "foundations.distributions") (lean := "BoundedContinuousFunction.hasFDerivAt_compactCurry") (uses := "foundations.distributions.test_slice")
Let $`K\subseteq F` be compact. Suppose that $`f:E\times F\to G` is
continuous, that for every $`x\in E` and $`y\in F` the map
$`z\mapsto f(z,y)` has Fréchet derivative $`D(x,y)` at $`x`, and that
$`D:E\times F\to(E\to_{\mathrm{cont}}G)` is jointly continuous. Then the
compactly indexed family

$$`
  x\longmapsto \bigl(y\mapsto f(x,y)\bigr)\big|_K
`

is Fréchet differentiable as a map from $`E` into the supremum-norm space
$`C(K,G)`, with derivative $`h\mapsto(y\mapsto D(x,y)h)`.
:::

:::proof "foundations.distributions.compact_curry_derivative"
Joint continuity of $`D` is uniform on a compact fiber near the base
parameter. The Banach-space mean-value estimate therefore bounds the
first-order remainder simultaneously for every $`y\in K`; taking the
supremum gives the required little-$`o` estimate in $`C(K,G)`.
:::

The second ingredient is quantitative. A distribution need not have finite
global order, but once test functions are confined to a fixed compact $`K` the
restriction is controlled by finitely many derivative seminorms. This
finite-order bound is what turns compact-uniform differentiability into
smoothness of the applied slice family.

:::theorem "foundations.distributions.fixed_support_restriction" (parent := "foundations.distributions") (lean := "Distribution.restrictToSupportedInCLM_apply, Distribution.exists_norm_restrictToSupportedIn_le_supSeminorm") (uses := "foundations.distributions.distribution")
Let $`K\subseteq E` be compact and let $`T\in\mathcal D'(E;G)`. Restriction
to test functions supported in $`K` is a continuous linear map

$$`
  T_K:\mathcal D_K(E)\longrightarrow G.
`

There are an order $`k` and a constant $`C>0` such that

$$`
  \lVert T_K\varphi\rVert
  \leq C\max_{0\leq i\leq k}
    \sup_{x\in K}\lVert D^i\varphi(x)\rVert
`

for every $`\varphi\in\mathcal D_K(E)`.
:::

:::proof "foundations.distributions.fixed_support_restriction"
Compose the continuous functional $`T` with the canonical inclusion of the
fixed-support Fréchet stage into the LF test-function space. Pulling back the
norm seminorm gives a continuous seminorm, hence a bound by finitely many
defining derivative seminorms. Their largest order is dominated by the
cumulative derivative seminorm in the statement.
:::

With the compact-uniform derivative and the finite-order bound in hand, the
moving pairing $`x\mapsto\langle T,\Phi_x\rangle` becomes a test function in
$`x`. The hypothesis that $`E` be finite-dimensional is part of the Lean
construction and is inherited by every tensor product built from it.

:::definition "foundations.distributions.applied_slice_family" (parent := "foundations.distributions") (lean := "TestFunction.applyDistributionToSliceRight, TestFunction.applyDistributionToSliceRight_apply") (uses := "foundations.distributions.distribution, foundations.distributions.test_slice, foundations.distributions.compact_curry_derivative, foundations.distributions.fixed_support_restriction")
Let $`T\in\mathcal D'(F;G)` and
$`\Phi\in\mathcal D(E\times F)`, with $`E` finite-dimensional. Applying
$`T` to the moving right slices defines a $`G`-valued test function

$$`
  x\longmapsto \langle T,\Phi_x\rangle
  \in\mathcal D(E;G).
`
:::

For the transpose to produce a distribution, the assignment
$`\Phi\mapsto(x\mapsto\langle T,\Phi_x\rangle)` must be well defined and
continuous for the LF topologies. Continuity is checked stage by stage on
fixed compact supports and then assembled through the universal property of the
inductive limit.

:::definition "foundations.distributions.applied_slice_family_continuous" (parent := "foundations.distributions") (lean := "TestFunction.applyDistributionToSliceRightCLM, TestFunction.applyDistributionToSliceRightCLM_apply") (uses := "foundations.distributions.applied_slice_family, foundations.distributions.fixed_support_restriction")
For fixed $`T\in\mathcal D'(F;G)`, the applied-slice assignment is a
continuous linear map for the canonical LF topologies,

$$`
  \mathcal D(E\times F)
  \longrightarrow
  \mathcal D(E;G),
  \qquad
  \Phi\longmapsto
  \bigl(x\longmapsto\langle T,\Phi_x\rangle\bigr).
`
:::

Two properties of the applied slice family are transposed later into properties
of $`S\otimes T`: its support is confined to the projection of
$`\operatorname{supp}\Phi`, which gives the support law for tensor products, and
differentiation in the parameter passes through $`T`, which gives the derivative
law in the first factor.

:::theorem "foundations.distributions.applied_slice_family_calculus" (parent := "foundations.distributions") (lean := "TestFunction.tsupport_applyDistributionToSliceRight_subset, TestFunction.lineDerivCLM_applyDistributionToSliceRight") (uses := "foundations.distributions.applied_slice_family, foundations.distributions.test_slice_calculus")
The applied slice family is supported in the first-coordinate projection of
the original support,

$$`
  \operatorname{supp}\bigl(x\mapsto\langle T,\Phi_x\rangle\bigr)
  \subseteq \pi_E(\operatorname{supp}\Phi),
`

and differentiation in the retained coordinate passes through $`T`:

$$`
  D_h\bigl(x\mapsto\langle T,\Phi_x\rangle\bigr)
  =
  x\mapsto\langle T,(D_{(h,0)}\Phi)_x\rangle.
`
:::

:::proof "foundations.distributions.applied_slice_family_calculus"
All slices and their parameter derivatives lie in one compact-support
Fréchet stage, obtained by projecting $`\operatorname{supp}\Phi` to $`F`.
The finite-order distribution bound reduces the Taylor remainder to finitely
many fiber-derivative seminorms. Compact-uniform differentiation makes each
remainder little-$`o`, yielding smoothness by induction. Outside the
first-coordinate support projection every slice vanishes, and the derivative
formula follows by differentiating $`\Phi` in its first coordinate before
applying $`T`.
:::

Transposing the continuous applied-slice map against $`S` defines the tensor
product. The formula is a distributional Fubini formula in a fixed order: $`T`
is applied in the $`F` variable before $`S` is applied in the $`E` variable.

:::definition "foundations.distributions.distribution_tensor_product" (parent := "foundations.distributions") (lean := "Distribution.tensorProduct, Distribution.tensorProduct_apply, Distribution.tensorProductRightCLM") (uses := "foundations.distributions.distribution, foundations.distributions.applied_slice_family_continuous")
Let $`S\in\mathcal D'(E)` and $`T\in\mathcal D'(F)`, with $`E`
finite-dimensional. Their tensor product is the distribution on $`E\times F`
defined by

$$`
  \langle S\otimes T,\Phi\rangle
  =
  \left\langle S,\,
    x\longmapsto\langle T,\Phi_x\rangle
  \right\rangle.
`

For fixed $`T`, the map $`S\mapsto S\otimes T` is continuous linear for the
compact-convergence distribution topologies.
:::

On an elementary tensor the iterated pairing factors, so the transposed
construction agrees with the naive product on such test functions. The Dirac
identity uses the point-evaluation formula for $`\delta`.

:::theorem "foundations.distributions.distribution_tensor_product_elementary" (parent := "foundations.distributions") (lean := "Distribution.tensorProduct_apply_testFunction_tensorProduct, Distribution.tensorProduct_delta_delta") (uses := "foundations.distributions.distribution_tensor_product, foundations.distributions.test_tensor_product, foundations.distributions.dirac_action")
On elementary test functions the pairing factors,

$$`
  \langle S\otimes T,\varphi\otimes\psi\rangle
  =
  \langle S,\varphi\rangle\langle T,\psi\rangle.
`

In particular,

$$`
  \delta_x\otimes\delta_y=\delta_{(x,y)}.
`
:::

:::proof "foundations.distributions.distribution_tensor_product_elementary"
Slicing $`\varphi\otimes\psi` at $`x` gives $`\varphi(x)\psi`. Linearity of
$`T` therefore turns the applied-slice family into
$`\langle T,\psi\rangle\varphi`, and applying $`S` gives the product of the
two pairings. For two point masses, unfolding the definition on any test function gives
evaluation at $`(x,y)`.
:::

Derivatives of $`S\otimes T` in a direction $`(v,0)` or $`(0,w)` fall on the
corresponding factor, exactly as they do for test-function tensors. The first
identity transposes the parameter-derivative formula for the applied slice
family; the second transposes the commutation of slicing with derivatives in the
fiber variable.

:::theorem "foundations.distributions.distribution_tensor_product_derivatives" (parent := "foundations.distributions") (lean := "Distribution.lineDerivCLM_tensorProduct_left, Distribution.lineDerivCLM_tensorProduct_right") (uses := "foundations.distributions.distribution_tensor_product, foundations.distributions.applied_slice_family_calculus, foundations.distributions.derivative_action")
Distributional differentiation acts on the corresponding tensor factor:

$$`
  D_{(v,0)}(S\otimes T)=(D_vS)\otimes T,
  \qquad
  D_{(0,w)}(S\otimes T)=S\otimes(D_wT).
`
:::

:::proof "foundations.distributions.distribution_tensor_product_derivatives"
For the first identity, transpose the parameter derivative formula for the
applied-slice family. For the second, commute the fiber derivative with
slicing. In each case the negative sign from distributional differentiation
appears on both sides and the defining pairings agree.
:::

Support behaves multiplicatively as well. The statement also covers
{bpref "foundations.distributions.compact_carrier"}[compact carriers], compact
sets outside of which a distribution vanishes. The carrier form is the one the
convolution construction uses.

:::theorem "foundations.distributions.distribution_tensor_product_support" (parent := "foundations.distributions") (lean := "Distribution.IsVanishingOn.tensorProduct_left, Distribution.IsVanishingOn.tensorProduct_right, Distribution.dsupport_tensorProduct_subset, Distribution.HasCompactCarrier.tensorProduct") (uses := "foundations.distributions.distribution_tensor_product, foundations.distributions.applied_slice_family_calculus, foundations.distributions.compact_carrier")
The distributional support of a tensor product is contained in the product of
the factor supports:

$$`
  \operatorname{supp}(S\otimes T)
  \subseteq
  \operatorname{supp}(S)\times\operatorname{supp}(T).
`

Moreover, if $`K` and $`L` are compact carriers of $`S` and $`T`, then
$`K\times L` is a compact carrier of $`S\otimes T`.
:::

:::proof "foundations.distributions.distribution_tensor_product_support"
If $`S` vanishes on $`U`, then $`S\otimes T` vanishes on
$`U\times F` because the applied-slice family is supported in the first
projection of the original test-function support. If $`T` vanishes on $`V`,
then every right slice of a test function supported in $`E\times V` lies in
$`V`, so the applied-slice family is zero. A point outside the product of the
factor supports has one coordinate in such an open vanishing neighborhood,
which gives an open product neighborhood on which $`S\otimes T` vanishes.
For compact carriers, the generalized tube lemma enlarges $`K` and $`L` to
product neighborhoods disjoint from the support of a given test function.
The same slicing argument then proves vanishing outside $`K\times L`.
:::

Two families of examples make the dual space concrete: locally integrable
functions and point masses. Regular distributions are the embedding through
which classical functions enter the theory.

:::definition "foundations.distributions.regular" (parent := "foundations.distributions") (lean := "Distribution.ofFun") (uses := "foundations.distributions.distribution")
Let $`E` be a normed real vector space with measurable open sets,
$`\Omega\subseteq E` open, $`\mu` a measure on $`E`, and $`F` a normed real
vector space. Every $`F`-valued function $`f` locally integrable on $`\Omega`
defines the regular distribution

$$`
  T_f\in\mathcal D'(\Omega;F),
  \qquad
  T_f(\varphi):=\int_E\varphi(x)f(x)\,d\mu(x).
`

Here juxtaposition denotes the scalar action of $`\varphi(x)\in\mathbb R` on
$`f(x)\in F`; Lean writes the integrand as `φ x • f x`. The integral may be
taken over all of $`E` because every test function on $`\Omega` is extended
by zero off $`\Omega`.

We use Mathlib's `Distribution.ofFun` at test-function order $`\infty`.
Local integrability is the hypothesis that identifies its action with this
integral.
:::

The constructor goes through Mathlib's bilinear integral map, so the action
formula is stated separately. Computations such as the Heaviside pairing
unfold it.

:::theorem "foundations.distributions.regular_action" (parent := "foundations.distributions") (lean := "Distribution.ofFun_apply") (uses := "foundations.distributions.regular, foundations.distributions.test_function")
When the function is locally integrable on the domain, for every test function $`\varphi`,

$$`
  \langle T_f,\varphi\rangle
  =\int_E\varphi(x)f(x)\,d\mu(x).
`

This fixes the sign and measure conventions of the pairing used by later weak
and distributional equations.
:::

:::proof "foundations.distributions.regular_action"
Unfold the regular-distribution constructor. Its underlying continuous linear
functional is Mathlib's continuous integral pairing of the scalar test
function with the vector-valued density, so evaluation gives the stated
formula.
:::

The Dirac mass is the standard example of a distribution not given by a density.
It is also the right-hand side in the definition of a fundamental solution, so
its exact normalization matters.

:::definition "foundations.distributions.dirac" (parent := "foundations.distributions") (lean := "Distribution.delta") (uses := "foundations.distributions.distribution")
The Dirac distribution at $`a\in\mathbb R^n` is evaluation at that point:

$$`
  \delta_a:\varphi\longmapsto\varphi(a).
`

Mathlib defines it as the continuous evaluation functional.
:::

Because $`\delta_a` is evaluation itself, its action formula holds by
definition rather than through a limit of approximate identities. The absence
of any normalizing factor is what makes
$`\delta_x\otimes\delta_y=\delta_{(x,y)}` and $`\delta_x*\delta_y=\delta_{x+y}`
hold exactly.

:::theorem "foundations.distributions.dirac_action" (parent := "foundations.distributions") (lean := "Distribution.delta_apply") (uses := "foundations.distributions.dirac, foundations.distributions.test_function")
For every test function $`\varphi`,

$$`
  \langle\delta_a,\varphi\rangle=\varphi(a).
`
:::

:::proof "foundations.distributions.dirac_action"
The Dirac distribution is the continuous evaluation functional at $`a`.
Evaluating that functional on $`\varphi` therefore reduces definitionally to
$`\varphi(a)`.
:::

The last basic formula fixes the sign convention of the distributional
derivative. The negative transpose is the sign for which the regular
distribution of a differentiable function is differentiated in the classical
way.

:::theorem "foundations.distributions.derivative_action" (parent := "foundations.distributions") (lean := "Distribution.lineDerivCLM_apply") (uses := "foundations.distributions.distribution")
For a distribution $`T`, test function $`\varphi`, and direction $`v`,

$$`
  \langle D_vT,\varphi\rangle
  =-\langle T,D_v\varphi\rangle.
`

At $`v=e_i`, this is the integration-by-parts identity
$`\langle\partial_iT,\varphi\rangle
=-\langle T,\partial_i\varphi\rangle` used to define weak derivatives.
:::

:::proof "foundations.distributions.derivative_action"
Distributional differentiation is defined as the negative transpose of the
continuous derivative operator on test functions. Applying this transpose to
$`\varphi` gives exactly $`-\langle T,D_v\varphi\rangle`.
:::

# Integration by parts

The sign in the distributional derivative is chosen so that it agrees with
the classical integration by parts formula.

:::theorem "foundations.distributions.integration_by_parts" (parent := "foundations.distributions") (lean := "PDE.Analysis.integral_smul_partialDeriv_eq_neg_of_contDiffAt, PDE.Analysis.integral_mul_partialDeriv_eq_neg_of_contDiffAt, PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport") (uses := "foundations.derivatives.partial, foundations.distributions.derivative_action")
Let $`f:\mathbb R^n\to\mathbb R` be $`C^1` with compact support, and let
$`g:\mathbb R^n\to E` take values in a real normed space and be $`C^1` near
every point of the closed support of $`f`. Then for each coordinate $`i`,

$$`
\int_{\mathbb R^n}f\,\partial_ig\,dx=-\int_{\mathbb R^n}\partial_if\;g\,dx .
`

Taking $`g=1` gives $`\int\partial_iF\,dx=0` for every compactly supported
$`C^1` function $`F`.
:::

:::proof "foundations.distributions.integration_by_parts"
Compact support makes $`f\,g` and its derivative pairings integrable for $`C^1` data, though $`g` is
only regular near the support of $`f`, because $`f` vanishes on a
neighbourhood of every other point. Along the $`i`-th coordinate the product derivative
is $`\partial_if\,g+f\,\partial_ig`, and Mathlib's integration by parts for integrable
pairings applies. As in the classical proof for compactly supported $`C^1` maps, it works on each
line parallel to $`e_i`, where an integrable derivative of an integrable function
has integral zero.
:::

Applying the formula twice moves a second derivative across, and summing over
the coordinates shows that the Laplacian is symmetric against compactly
supported functions. This is the identity behind the distributional Laplacian
and the weak formulation of the Poisson equation.

:::theorem "foundations.distributions.laplacian_symmetric" (parent := "foundations.distributions") (lean := "PDE.DistributionTheory.integral_mul_laplacian_eq, PDE.DistributionTheory.integral_smul_secondPartialDeriv_eq") (uses := "foundations.distributions.integration_by_parts, foundations.operators.laplacian")
If $`f,g:\mathbb R^n\to\mathbb R` are $`C^2` and $`f` has compact support, then

$$`
\int_{\mathbb R^n}f\,\Delta g\,dx=\int_{\mathbb R^n}\Delta f\;g\,dx .
`

The coordinatewise form $`\int f\,\partial_i^2g=\int\partial_i^2f\,g` holds
for $`E`-valued $`g` that is $`C^2` near the support of $`f`.
:::

:::proof "foundations.distributions.laplacian_symmetric"
Integrate by parts once to move one $`\partial_i` from $`g` to $`f`, and
again with $`\partial_if` in place of $`f`, whose support lies in that of
$`f`. The two signs cancel. Sum over $`i`.
:::

On distributions there is nothing to assume. The derivative of $`T` is
defined by moving the derivative onto the test function, and derivatives of
test functions commute, so distributional derivatives commute as well. For a
function whose classical mixed partials fail to agree, both distributional
mixed partials still exist and coincide.

:::theorem "foundations.distributions.derivatives_commute" (parent := "foundations.distributions") (lean := "Distribution.lineDerivCLM_commute, Distribution.mapCLM_lineDerivCLM") (uses := "foundations.distributions.derivative_action")
On an open subset of a real normed space, the directional
derivatives $`D_v` and $`D_w` of distributions commute for any constant
directions $`v` and $`w`. Composing a distribution with a continuous linear
map $`A` of its values commutes with every $`D_v`.
:::

:::proof "foundations.distributions.derivatives_commute"
Pair both sides with a test function $`\varphi`. The two minus signs from the
definition cancel, leaving $`T(D_wD_v\varphi)` and $`T(D_vD_w\varphi)`,
which agree because $`\varphi` is smooth. For the value map, $`A` is linear,
so it passes through the minus sign and the evaluation.
:::

# Dilation identities

The field $`x\mapsto x` generates the dilations $`x\mapsto\lambda x`, and
the derivative of $`u` along it is $`x\cdot\nabla u(x)`, the rate at which
$`u(\lambda x)` changes at $`\lambda=1`. In PDEAtlas this is the
{bpref "foundations.operators.advection"}[advective derivative] along the
identity field. Integrating it against the equation is the idea behind the
identities of Rellich and Pohozaev. The equation $`-\Delta u=f(u)` is the
Euler–Lagrange equation of an energy with two terms, and the two terms scale
with different powers of $`\lambda` under $`u(x)\mapsto u(\lambda x)`. A
solution is a critical point of the energy for every variation, and in
particular for the variation by dilation. That forces a linear relation
between the two terms, and the relation often has no nonzero solution.
{Informal.citet "evans-2010"}[] uses this argument in §9.4.2 to rule out
solutions of supercritical power equations on star-shaped domains. The
statements here are the boundary-free versions, for compactly supported
functions on $`\mathbb R^n`; the versions with boundary terms belong to the
boundary calculus.

:::theorem "foundations.distributions.dilation_integral" (parent := "foundations.distributions") (lean := "PDE.DistributionTheory.integral_dilation_eq") (uses := "foundations.distributions.integration_by_parts, foundations.operators.advection")
If $`v:\mathbb R^n\to\mathbb R` is $`C^1` with compact support, then

$$`
\int_{\mathbb R^n}x\cdot\nabla v(x)\,dx=-n\int_{\mathbb R^n}v(x)\,dx .
`
:::

:::proof "foundations.distributions.dilation_integral"
Write $`x\cdot\nabla v=\sum_ix_i\,\partial_iv`. For each $`i`, integrate by
parts with the coordinate function $`x_i` as the second factor. It is smooth
everywhere, and compact support of $`v` removes the boundary term, so
$`\int x_i\,\partial_iv=-\int v\,\partial_ix_i=-\int v`. There are $`n`
coordinates. The same result follows from the change of variables
$`\int v(\lambda x)\,dx=\lambda^{-n}\int v` by differentiating at
$`\lambda=1`.
:::

Applied to $`v=u^2` this gives $`\int(x\cdot\nabla u)\,u=-\tfrac n2\int u^2`.
The Rellich identity is the same computation carried out for the gradient of
$`u` against the Laplacian.

:::theorem "foundations.distributions.rellich_compact" (parent := "foundations.distributions") (lean := "PDE.DistributionTheory.integral_dilation_mul_laplacian_eq") (uses := "foundations.distributions.dilation_integral, foundations.distributions.laplacian_symmetric, foundations.derivatives.mixed_commutation")
If $`u:\mathbb R^n\to\mathbb R` is $`C^2` with compact support, then

$$`
\int_{\mathbb R^n}(x\cdot\nabla u)\,\Delta u\,dx
=\frac{n-2}{2}\int_{\mathbb R^n}\lvert\nabla u\rvert^2\,dx .
`

No condition on $`n` is needed. For $`n=2` both sides vanish, and for
$`n=1` the right side is nonpositive.
:::

:::proof "foundations.distributions.rellich_compact"
Fix a coordinate $`i` and integrate
$`(x\cdot\nabla u)\,\partial_i^2u` by parts once in $`x_i`. The derivative
falls on the multiplier, and

$$`
\partial_i(x\cdot\nabla u)=\partial_iu+x\cdot\nabla(\partial_iu),
`

where symmetry of the Hessian of the $`C^2` function $`u` exchanges the two
derivatives in the second term. The first term contributes
$`-\int(\partial_iu)^2`. The second is $`-\int(x\cdot\nabla w)\,w` with
$`w=\partial_iu`, which is $`\tfrac n2\int(\partial_iu)^2` by the dilation
integral applied to $`w^2`. So each coordinate gives
$`\tfrac{n-2}2\int(\partial_iu)^2`, and summing over $`i` gives the
identity. All integrands are continuous with compact support, so every
integral is finite.
:::

The simpler multiplier $`u` itself gives the energy identity used alongside
it.

:::theorem "foundations.distributions.dirichlet_energy_compact" (parent := "foundations.distributions") (lean := "PDE.DistributionTheory.integral_mul_laplacian_self_eq") (uses := "foundations.distributions.integration_by_parts, foundations.operators.laplacian")
If $`u:\mathbb R^n\to\mathbb R` is $`C^2` with compact support, then
$`\int u\,\Delta u\,dx=-\int\lvert\nabla u\rvert^2\,dx`.
:::

:::proof "foundations.distributions.dirichlet_energy_compact"
Integrate $`u\,\partial_i^2u` by parts once in each coordinate and sum.
:::

For a solution of $`-\Delta u=F'(u)`, the chain rule turns
$`(x\cdot\nabla u)\,F'(u)` into $`x\cdot\nabla(F\circ u)`, whose integral the
dilation identity computes. Comparing with the Rellich identity gives the
Pohozaev identity.

:::theorem "foundations.distributions.pohozaev_compact" (parent := "foundations.distributions") (lean := "PDE.Elliptic.Semilinear.integral_pohozaev_eq") (uses := "foundations.distributions.rellich_compact, foundations.distributions.dilation_integral")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§9.4.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`F:\mathbb R\to\mathbb R` be $`C^1` with $`F(0)=0`, and let
$`u:\mathbb R^n\to\mathbb R` be $`C^2` with compact support and
$`-\Delta u=F'(u)` at every point. Then

$$`
(n-2)\int_{\mathbb R^n}\lvert\nabla u\rvert^2\,dx
=2n\int_{\mathbb R^n}F(u(x))\,dx .
`
:::

:::proof "foundations.distributions.pohozaev_compact"
The normalization $`F(0)=0` makes $`F\circ u` a compactly supported
$`C^1` function, so the dilation integral gives
$`\int x\cdot\nabla(F\circ u)=-n\int F(u)`. By the chain rule and the
equation, $`x\cdot\nabla(F\circ u)=(x\cdot\nabla u)F'(u)=-(x\cdot\nabla u)\Delta u`.
The Rellich identity evaluates the integral of the right side as
$`-\tfrac{n-2}2\int\lvert\nabla u\rvert^2`. Multiplying by $`2` gives
the result.
:::

The identity already has content. If $`n\ge3` and $`F\le0`, the left side
is nonnegative and the right side nonpositive, so $`\nabla u=0` and the
compactly supported $`u` is zero. On a bounded domain the identity carries a
radial boundary integral ({Informal.citet "evans-2010"}[] §9.4.2). There the
equation holds only inside $`\Omega`, the data vanish on
$`\partial\Omega`, and the boundary term has a sign when $`\Omega` is star-shaped.
That version is
{bpref "foundations.boundary_calculus.pohozaev_boundary"}[proved in the boundary calculus chapter].
In the compact-support version, the equation holds on all of $`\mathbb R^n`,
including where $`u=0`. In positive dimension this forces $`F'(0)=0`.

# Constant-coefficient differential operators

:::definition "foundations.distributions.constant_coefficient_operator" (parent := "foundations.distributions") (lean := "PDE.Analysis.constantCoeffLineDerivCLM") (uses := "foundations.distributions.derivative_action")
Let $`I` be a finite index set. For each $`i\in I`, choose a coefficient
$`a_i`, an order $`k_i`, and directions
$`m_i=(v_{i,1},\ldots,v_{i,k_i})`. The associated constant-coefficient
operator is

$$`
  P(D)=\sum_{i\in I}a_iD_{v_{i,1}}\cdots D_{v_{i,k_i}}.
`

Whenever the ambient topological module carries continuous line derivatives,
$`P(D)` is a continuous linear endomorphism.
:::

:::theorem "foundations.distributions.constant_coefficient_operator_action" (parent := "foundations.distributions") (lean := "PDE.Analysis.constantCoeffLineDerivCLM_apply") (uses := "foundations.distributions.constant_coefficient_operator")
For every admissible $`x`,

$$`
  P(D)x
  =\sum_{i\in I}a_iD_{v_{i,1}}\cdots D_{v_{i,k_i}}x.
`
:::

:::proof "foundations.distributions.constant_coefficient_operator_action"
Mathlib provides each iterated directional derivative as
`LineDeriv.iteratedLineDerivOpCLM`. Fixed scalar multiplication and finite
sums of continuous linear maps assemble these terms into $`P(D)`. Evaluation
of the finite sum gives the displayed action formula.
:::

# Fundamental solutions

:::definition "foundations.distributions.fundamental_solution" (parent := "foundations.distributions") (lean := "Distribution.IsFundamentalSolutionAt") (uses := "foundations.distributions.constant_coefficient_operator, foundations.distributions.dirac")
Let $`\Omega\subseteq E` be open, let $`P:\mathcal D'(\Omega)\to
\mathcal D'(\Omega)` be continuous and linear, and let $`T\in
\mathcal D'(\Omega)`. The distribution $`T` is a fundamental solution for
$`P` at $`x` precisely when

$$`
  x\in\Omega
  \qquad\text{and}\qquad
  P T=\delta_x
  \quad\text{in }\mathcal D'(\Omega).
`

The membership condition is mathematically essential. Mathlib defines
$`\delta_x` on $`\Omega` by evaluation of test functions at $`x`; because
every such test function vanishes off $`\Omega`, this functional is zero when
$`x\notin\Omega`. Recording $`x\in\Omega` prevents the homogeneous equation
$`PT=0` from being mislabeled as a point-source equation at an exterior pole.
The predicate otherwise states only the distribution equation and is
independent of any representative of $`T`.
:::

:::theorem "foundations.distributions.fundamental_solution_action" (parent := "foundations.distributions") (lean := "Distribution.IsFundamentalSolutionAt.apply, Distribution.isFundamentalSolutionAt_iff") (uses := "foundations.distributions.fundamental_solution, foundations.distributions.dirac_action")
The fundamental-solution predicate is equivalent to the conjunction

$$`
  x\in\Omega
  \qquad\text{and}\qquad
  \langle P T,\varphi\rangle=\varphi(x)
  \quad\text{for every }\varphi\in\mathcal D(\Omega).
`

Thus a proved fundamental-solution predicate supplies both a valid interior
pole and the action formula. Conversely, interiority together with the family
of test-function identities determines the distribution equality.
:::

:::proof "foundations.distributions.fundamental_solution_action"
The forward implication projects the interiority condition and applies the
distribution equality to an arbitrary test function. The Dirac action formula
reduces the right side to $`\varphi(x)`. Conversely, retain the supplied proof
that $`x\in\Omega` and use extensionality: continuous linear functionals are
equal when they agree on every test function.
:::

# Smooth multiplication

:::definition "foundations.distributions.smooth_test_multiplier" (parent := "foundations.distributions") (lean := "TestFunction.smoothMultiplierCLM") (uses := "foundations.distributions.test_function")
Every smooth scalar coefficient $`g` defines a continuous linear operator on
the LF test-function space,

$$`
  M_g:\mathcal D(E)\longrightarrow\mathcal D(E),
  \qquad
  M_g\varphi=g\varphi.
`

Multiplication does not enlarge the test function's topological support.
:::

Two facts about $`M_g` are needed downstream. Its Leibniz rule is what becomes
the product rule for $`gT` after transposition, and its support inclusion is
what allows smooth multiplication to preserve vanishing regions of
distributions.

:::theorem "foundations.distributions.smooth_test_multiplier_calculus" (parent := "foundations.distributions") (lean := "TestFunction.smoothMultiplierCLM_apply, TestFunction.tsupport_smoothMultiplier_subset, TestFunction.lineDerivCLM_smoothMultiplierCLM") (uses := "foundations.distributions.smooth_test_multiplier, foundations.distributions.test_derivative_leibniz")
For every direction $`v`,

$$`
  D_v(g\varphi)
  =gD_v\varphi+(D_vg)\varphi,
  \qquad
  \operatorname{supp}(g\varphi)\subseteq\operatorname{supp}\varphi.
`
:::

:::proof "foundations.distributions.smooth_test_multiplier_calculus"
Mathlib's `ContDiffMapSupportedIn.bilinLeftCLM` supplies continuous
multiplication on each fixed compact-support stage. The LF universal property
`TestFunction.limitCLM` assembles those operators into $`M_g`. The support
inclusion follows from the support of a pointwise product, while Mathlib's
Fréchet product rule gives the displayed directional-derivative identity.
:::

A distribution is multiplied by a smooth coefficient by moving the coefficient
onto the test function. Continuity of $`M_g` on the LF space makes the
transposed operator continuous.

:::definition "foundations.distributions.smooth_distribution_multiplier" (parent := "foundations.distributions") (lean := "Distribution.smoothMultiplierCLM") (uses := "foundations.distributions.distribution, foundations.distributions.smooth_test_multiplier")
The compact-convergence transpose of $`M_g` defines multiplication of
distributions by smooth coefficients:

$$`
  gT:\varphi\longmapsto\langle T,g\varphi\rangle.
`

The construction applies to distributions valued in any real topological
module satisfying Mathlib's standard continuity assumptions.
:::

The product rule for $`gT` follows from the test-function Leibniz rule and the
sign convention of the distributional derivative; the term $`(D_vg)T` appears
because $`D_v` acting on $`g\varphi` also differentiates the coefficient.

:::theorem "foundations.distributions.smooth_distribution_multiplier_calculus" (parent := "foundations.distributions") (lean := "Distribution.smoothMultiplierCLM_apply_apply, Distribution.lineDerivCLM_smoothMultiplierCLM") (uses := "foundations.distributions.smooth_distribution_multiplier, foundations.distributions.smooth_test_multiplier_calculus, foundations.distributions.derivative_action")
The multiplier has the expected pairing and distributional Leibniz laws:

$$`
  \langle gT,\varphi\rangle=\langle T,g\varphi\rangle,
  \qquad
  D_v(gT)=gD_vT+(D_vg)T.
`
:::

:::proof "foundations.distributions.smooth_distribution_multiplier_calculus"
The action formula is the defining formula of Mathlib's compact-convergence
transpose. Apply the distributional derivative to a test function and use the
test-function Leibniz rule. The negative-transpose convention moves the
derivative from the distribution to the test function and yields the two
terms in the displayed formula.
:::

Multiplying by $`g` can only shrink support. An operation on test functions
that does not enlarge supports transposes to an operation on distributions that
preserves every vanishing region, and the same mechanism applies to
constant-coefficient operators.

:::theorem "foundations.distributions.smooth_distribution_multiplier_support" (parent := "foundations.distributions") (lean := "Distribution.IsVanishingOn.smoothMultiplierCLM, Distribution.dsupport_smoothMultiplierCLM_subset, Distribution.HasCompactCarrier.smoothMultiplierCLM") (uses := "foundations.distributions.smooth_distribution_multiplier, foundations.distributions.compact_carrier")
Smooth multiplication preserves every vanishing region and every compact
carrier. In particular,

$$`
  \operatorname{supp}(gT)\subseteq\operatorname{supp}T.
`
:::

:::proof "foundations.distributions.smooth_distribution_multiplier_support"
If a test function is supported in a vanishing region for $`T`, multiplication
by $`g` keeps its support in the same region. The transpose action formula
therefore makes $`gT` vanish there as well. The intrinsic-support inclusion
follows from Mathlib's vanishing characterization, and the same compact carrier
can be reused unchanged.
:::

# Proper smooth transport

:::definition "foundations.distributions.proper_test_pullback" (parent := "foundations.distributions") (lean := "TestFunction.precompProperCLM") (uses := "foundations.distributions.test_function")
Let $`f:D\to E` be smooth and proper. Precomposition defines a continuous
linear map between the canonical LF test-function spaces,

$$`
  f^*:\mathcal D(E)\longrightarrow\mathcal D(D).
`

Properness ensures that the inverse image of the compact support of
$`\varphi` is compact.
:::

Continuity is the content of the definition, since the underlying map is simply
composition with $`f`. Properness is what keeps $`\varphi\circ f` compactly
supported. The
{bpref "foundations.distributions.localized_test_pullback"}[localized pullback]
drops this hypothesis by inserting a cutoff.

:::theorem "foundations.distributions.proper_test_pullback_action" (parent := "foundations.distributions") (lean := "TestFunction.precompProperCLM_apply") (uses := "foundations.distributions.proper_test_pullback")
For every test function $`\varphi`,

$$`
  f^*\varphi=\varphi\circ f.
`
:::

:::proof "foundations.distributions.proper_test_pullback_action"
On each fixed compact-support stage, the iterated chain rule bounds every
derivative seminorm of $`\varphi\circ f` by finitely many derivative seminorms
of $`\varphi`. The derivatives of $`f` are uniformly bounded on the compact
inverse image of the support. Mathlib's seminorm criterion therefore gives a
continuous linear map on each compact stage, and the LF universal property
`TestFunction.limitCLM` assembles these maps into the stated continuous
operator.
:::

Transposing the pullback gives a pushforward of distributions, the analogue of
the image measure. The transpose of a continuous linear map needs no structure
on the value space beyond continuity of the module operations, so vector values
cost nothing.

:::definition "foundations.distributions.proper_pushforward" (parent := "foundations.distributions") (lean := "Distribution.pushforwardProperCLM") (uses := "foundations.distributions.distribution, foundations.distributions.proper_test_pullback")
The transpose of proper test-function pullback is a continuous pushforward
of distributions,

$$`
  f_\#:\mathcal D'(D;F)\longrightarrow\mathcal D'(E;F).
`

The construction works for distributions valued in any real topological
module $`F` satisfying Mathlib's standard continuity assumptions.
:::

The action formula is the distributional change of variables. For a regular
distribution with density $`u` it is the pushforward of the measure $`u\,d\mu`
under $`f`, and no Jacobian factor appears because the pairing never chooses
coordinates on the target.

:::theorem "foundations.distributions.proper_pushforward_action" (parent := "foundations.distributions") (lean := "Distribution.pushforwardProperCLM_apply_apply") (uses := "foundations.distributions.proper_pushforward, foundations.distributions.proper_test_pullback_action")
For every distribution $`T` and test function $`\varphi`,

$$`
  \langle f_\#T,\varphi\rangle
  =\langle T,\varphi\circ f\rangle.
`
:::

:::proof "foundations.distributions.proper_pushforward_action"
Apply Mathlib's compact-convergence transpose
`ContinuousLinearMap.precompCompactConvergenceCLM` to the continuous
test-function pullback. Evaluation of the transposed operator is exactly the
displayed pairing formula.
:::

Functoriality allows a pushforward along a composite map to be computed in
stages, for instance along a linear map followed by a translation. Both
identities are consequences of the action formula and extensionality.

:::theorem "foundations.distributions.proper_pushforward_functorial" (parent := "foundations.distributions") (lean := "Distribution.pushforwardProperCLM_id, Distribution.pushforwardProperCLM_comp") (uses := "foundations.distributions.proper_pushforward_action")
Proper smooth pushforward is functorial:

$$`
  (\operatorname{id})_\#T=T,
  \qquad
  g_\#(f_\#T)=(g\circ f)_\#T.
`
:::

:::proof "foundations.distributions.proper_pushforward_functorial"
Evaluate both sides on an arbitrary test function. Identity reduces to
$`\varphi\circ\operatorname{id}=\varphi`, while composition reduces to
$`(\varphi\circ g)\circ f=\varphi\circ(g\circ f)`. Extensionality of
continuous linear functionals gives the two distribution identities.
:::

Support theory for distributions in this book is organized around carriers
rather than around the intrinsic support. A carrier is any set outside of which
the distribution vanishes, and a compact carrier is the hypothesis that the
convolution construction later takes as input.

:::definition "foundations.distributions.compact_carrier" (parent := "foundations.distributions") (lean := "Distribution.HasCompactCarrier") (uses := "foundations.distributions.distribution")
A distribution $`T` has a *compact carrier* if there is a compact set $`K`
such that $`T` vanishes on every test function supported in $`K^c`.
:::

The intrinsic support is the intersection of all closed carriers, and a
compact carrier can be strictly larger than the support.

:::theorem "foundations.distributions.compact_carrier_support" (parent := "foundations.distributions") (lean := "Distribution.dsupport_subset_of_isVanishingOn_compl, Distribution.HasCompactCarrier.isCompact_dsupport") (uses := "foundations.distributions.compact_carrier")
If $`T` vanishes outside a closed set $`K`, then

$$`
  \operatorname{supp}T\subseteq K.
`

Consequently, a compact carrier makes the intrinsic distributional support
compact.
:::

:::proof "foundations.distributions.compact_carrier_support"
The distributional support lies in every closed carrier. For a compact carrier,
the intrinsic support is therefore a closed subset of a compact set and is
compact.
:::

The first application of the carrier notion is to differential operators.
Directional derivatives, hence every finite constant-coefficient operator
$`P(D)`, keep the support of a test function inside any region containing it,
and after transposition this becomes preservation of vanishing regions.

:::theorem "foundations.distributions.constant_coefficient_operator_support" (parent := "foundations.distributions") (lean := "Distribution.IsVanishingOn.constantCoeffLineDerivCLM, Distribution.dsupport_constantCoeffLineDerivCLM_subset, Distribution.HasCompactCarrier.constantCoeffLineDerivCLM") (uses := "foundations.distributions.constant_coefficient_operator_action, foundations.distributions.compact_carrier_support")
For ordinary distributions, $`P(D)` preserves every vanishing region. Hence

$$`
  \operatorname{supp}(P(D)T)\subseteq\operatorname{supp}T.
`

If $`T` has a compact carrier, then $`P(D)T` has the same compact carrier.
:::

:::proof "foundations.distributions.constant_coefficient_operator_support"
Mathlib proves that every iterated directional derivative preserves a
vanishing region. Scalar multiples and finite sums preserve the same property,
so the finite operator does as well. The support inclusion follows from the
vanishing characterization of distributional support, and a compact carrier
can be reused unchanged.
:::

The same argument applies to tempered distributions, with complex coefficients
and Schwartz probes.

:::theorem "foundations.distributions.constant_coefficient_operator_tempered_support" (parent := "foundations.distributions") (lean := "Distribution.TemperedDistribution.IsVanishingOn.constantCoeffLineDerivCLM, Distribution.TemperedDistribution.dsupport_constantCoeffLineDerivCLM_subset") (uses := "foundations.distributions.constant_coefficient_operator_action")
For tempered distributions and complex coefficients, $`P(D)` preserves every
vanishing region and cannot enlarge support:

$$`
  \operatorname{supp}(P(D)T)\subseteq\operatorname{supp}T.
`
:::

:::proof "foundations.distributions.constant_coefficient_operator_tempered_support"
Mathlib's tempered iterated-derivative support theorem applies term by term.
The vanishing identity is stable under complex scalar multiplication and
finite sums, and the intrinsic support inclusion follows from the same
vanishing characterization.
:::

Pushforward interacts with carriers through images: a test function supported
away from $`f(K)` pulls back to one supported away from $`K`. Because proper
maps are closed, the image of a closed carrier is again a closed carrier, and
the support inclusion follows.

:::theorem "foundations.distributions.proper_pushforward_support" (parent := "foundations.distributions") (lean := "Distribution.IsVanishingOn.pushforwardProperCLM, Distribution.dsupport_pushforwardProperCLM_subset_image") (uses := "foundations.distributions.proper_pushforward_action, foundations.distributions.compact_carrier_support")
Suppose $`T` vanishes outside a closed set $`K` and $`f` is smooth and proper.
Then $`f_\#T` vanishes outside $`f(K)`, and

$$`
  \operatorname{supp}(f_\#T)\subseteq f(K).
`
:::

:::proof "foundations.distributions.proper_pushforward_support"
If a test function $`\varphi` is supported outside $`f(K)`, its pullback
$`\varphi\circ f` is supported outside $`K`; the pushforward action formula therefore makes its pairing with
$`T` vanish. Proper maps are closed maps, so $`f(K)` is a closed carrier.
The distributional support therefore lies inside that carrier.
:::

Addition $`E\times E\to E` is not proper when $`E\ne0`, so the convolution
construction cannot use proper pushforward directly. For compactly carried
distributions a cutoff removes the properness hypothesis.

:::theorem "foundations.distributions.proper_pushforward_compact_carrier" (parent := "foundations.distributions") (lean := "Distribution.HasCompactCarrier.pushforwardProperCLM") (uses := "foundations.distributions.proper_pushforward_support, foundations.distributions.compact_carrier_support")
Smooth proper pushforward preserves compact carriers. In particular, if $`T`
has a compact carrier, then $`f_\#T` has compact distributional support.
:::

:::proof "foundations.distributions.proper_pushforward_compact_carrier"
Choose a compact carrier $`K` for $`T`. The preceding theorem transports the
vanishing property to $`f(K)`, while continuity of $`f` makes $`f(K)` compact.
The intrinsic support is closed and lies in this compact carrier, hence is
compact.
:::

# Compact-carrier smooth transport

:::theorem "foundations.distributions.compact_test_cutoff" (parent := "foundations.distributions") (lean := "TestFunction.exists_eq_one_on_compact_finiteDimensional, TestFunction.exists_eq_one_on_compact") (uses := "foundations.distributions.test_function")
If $`K\subset U\subset E`, where $`E` is a finite-dimensional real normed
space, $`K` is compact, and $`U` is open,
then there is a test function $`\chi` such that

$$`
  0\leq\chi\leq1,\qquad
  \operatorname{supp}\chi\subseteq U,
`

and $`\chi=1` on a neighborhood of every point of $`K`.
:::

:::proof "foundations.distributions.compact_test_cutoff"
Choose a compact set $`L` with $`K` in its interior and $`L\subseteq U`.
Mathlib's smooth separation theorem gives a smooth function with values in
$`[0,1]` that equals one on a neighborhood of $`K` and vanishes outside $`L`.
Its support lies in the compact set $`L\subseteq U`, so it is a test function
with the stated properties.
:::

The cutoff compensates for the failure of properness. When $`f` is not proper,
the composite $`\varphi\circ f` generally loses compact support. Multiplying by
a fixed test function $`\chi` restores it at the price of a dependence on
$`\chi`.

:::definition "foundations.distributions.localized_test_pullback" (parent := "foundations.distributions") (lean := "TestFunction.precompLocalizedCLM") (uses := "foundations.distributions.test_function, foundations.distributions.compact_test_cutoff")
Let $`f:D\to E` be an arbitrary smooth map between real normed spaces and let
$`\chi\in\mathcal D(D)` be fixed. Localized precomposition is the continuous
linear map

$$`
  f_\chi^*:\mathcal D(E)\longrightarrow\mathcal D(D),
  \qquad
  f_\chi^*\varphi=\chi\,(\varphi\circ f).
`

Here $`f` need not be proper.
:::

The output support is controlled by $`\chi` alone rather than by
$`f^{-1}(\operatorname{supp}\varphi)`, and this uniform support bound is what
makes the seminorm estimates behind continuity possible without properness.

:::theorem "foundations.distributions.localized_test_pullback_action" (parent := "foundations.distributions") (lean := "TestFunction.precompLocalizedCLM_apply, TestFunction.tsupport_precompLocalized_subset") (uses := "foundations.distributions.localized_test_pullback")
For every test function $`\varphi`,

$$`
  f_\chi^*\varphi=\chi\,(\varphi\circ f),
  \qquad
  \operatorname{supp}(f_\chi^*\varphi)
  \subseteq\operatorname{supp}\chi.
`
:::

:::proof "foundations.distributions.localized_test_pullback_action"
Multiplication by $`\chi` fixes the output support inside one compact set.
On every compact input stage, Mathlib's iterated product and composition
estimates bound the output seminorms by finitely many input seminorms.
These seminorm bounds prove continuity on each stage. The inductive-limit
topology then gives continuity on the full test-function space.
:::

Transposition again produces an operator on distributions, this time for
arbitrary smooth $`f`.

:::definition "foundations.distributions.localized_pushforward" (parent := "foundations.distributions") (lean := "Distribution.pushforwardLocalizedCLM") (uses := "foundations.distributions.distribution, foundations.distributions.localized_test_pullback")
Transposing localized test-function pullback defines

$$`
  f_{\#,\chi}:
  \mathcal D'(D;F)\longrightarrow\mathcal D'(E;F)
`

for every smooth map $`f` and fixed cutoff $`\chi`.
:::

The pairing formula differs from the proper case only by the factor $`\chi`
inside the test function. When $`\chi` equals one near a carrier of $`T`,
changing $`\chi` alters the test function only where $`T` cannot see it.

:::theorem "foundations.distributions.localized_pushforward_action" (parent := "foundations.distributions") (lean := "Distribution.pushforwardLocalizedCLM_apply_apply") (uses := "foundations.distributions.localized_pushforward, foundations.distributions.localized_test_pullback_action")
The localized pushforward acts by

$$`
  \langle f_{\#,\chi}T,\varphi\rangle
  =\langle T,\chi\,(\varphi\circ f)\rangle.
`
:::

:::proof "foundations.distributions.localized_pushforward_action"
The operator is the compact-convergence transpose of
$`f_\chi^*`. Evaluating the transpose on a test function gives the displayed
pairing formula directly.
:::

Cutoff independence makes the pushforward of a compactly carried tensor product
along addition canonical, and this is how convolution is defined.

:::theorem "foundations.distributions.compact_carrier_smooth_pushforward" (parent := "foundations.distributions") (lean := "Distribution.IsVanishingOn.pushforwardLocalizedCLM, Distribution.dsupport_pushforwardLocalizedCLM_subset_image, Distribution.HasCompactCarrier.pushforwardLocalizedCLM, Distribution.pushforwardLocalizedCLM_eq_of_eq_one_near") (uses := "foundations.distributions.localized_pushforward_action, foundations.distributions.compact_carrier, foundations.distributions.compact_test_cutoff")
Suppose $`T` vanishes outside a compact set $`K`. Then
$`f_{\#,\chi}T` vanishes outside $`f(K)`, and

$$`
  \operatorname{supp}(f_{\#,\chi}T)\subseteq f(K).
`

It therefore has a compact carrier. Moreover, if both $`\chi` and $`\psi`
equal one near $`K`, then

$$`
  f_{\#,\chi}T=f_{\#,\psi}T.
`

Thus compactly carried distributions have a cutoff-independent pushforward
along arbitrary smooth maps.
:::

:::proof "foundations.distributions.compact_carrier_smooth_pushforward"
A target test function supported outside $`f(K)` vanishes on a neighborhood
of $`f(K)`. Its pullback therefore vanishes on a neighborhood of $`K`, as
does its product with the cutoff.
The localized action formula therefore transports the carrier to $`f(K)`,
which is compact by continuity of $`f`. For cutoff independence, the
difference $`(\chi-\psi)(\varphi\circ f)` vanishes on a neighborhood of
$`K`, so the carrier hypothesis makes its pairing with $`T` zero.
:::

# Convolution with compact carriers

:::definition "foundations.distributions.compact_carrier_convolution" (parent := "foundations.distributions") (lean := "Distribution.convolution, Distribution.convolutionWithCutoff, Distribution.convolutionWithCutoff_apply, Distribution.convolution_eq_convolutionWithCutoff_tensorProduct") (uses := "foundations.distributions.distribution_tensor_product_support, foundations.distributions.compact_test_cutoff, foundations.distributions.compact_carrier_smooth_pushforward")
Let $`S,T\in\mathcal D'(E)` have compact carriers, where $`E` is a
finite-dimensional real normed space. Their convolution is the
cutoff-localized pushforward of $`S\otimes T` along addition:

$$`
  \langle S*T,\varphi\rangle
  =
  \left\langle S\otimes T,\,
    \chi_1(x)\chi_2(y)\varphi(x+y)\right\rangle,
`

where $`\chi_1` and $`\chi_2` equal one near compact carriers of $`S` and
$`T`, respectively. Thus $`\chi_1\otimes\chi_2` equals one near their product.
The resulting distribution is independent of the chosen carrier witnesses and
of the cutoffs $`\chi_1,\chi_2`; the cutoff on $`E\times E` is always of this
product form.
:::

The support law for convolution is the theorem of supports in its inclusion
form. It combines the product-carrier law for tensor products with the image law
for localized pushforward, since the image of $`K\times L` under addition is the
Minkowski sum.

:::theorem "foundations.distributions.compact_carrier_convolution_support" (parent := "foundations.distributions") (lean := "Distribution.HasCompactCarrier.convolution, Distribution.dsupport_convolution_subset_add_image") (uses := "foundations.distributions.compact_carrier_convolution, foundations.distributions.compact_carrier_support")
If compact sets $`K` and $`L` carry $`S` and $`T`, respectively, then $`S*T`
has a compact carrier and

$$`
  \operatorname{supp}(S*T)
  \subseteq
  \{x+y:x\in K,\ y\in L\}.
`
:::

:::proof "foundations.distributions.compact_carrier_convolution_support"
The product $`K\times L` is a compact carrier of $`S\otimes T`. Localized
pushforward along the continuous addition map sends this carrier to its
compact image, the Minkowski sum of $`K` and $`L`. Cutoff independence
identifies that presentation with the canonical convolution.
:::

Differentiation passes to either factor. The cutoff is differentiated too, but
its derivative vanishes near the carrier $`K\times L`, so that term is
annihilated by $`S\otimes T`; what remains is the coordinate derivative law for
tensor products.

:::theorem "foundations.distributions.compact_carrier_convolution_derivative" (parent := "foundations.distributions") (lean := "Distribution.lineDerivCLM_convolution_left, Distribution.lineDerivCLM_convolution_right") (uses := "foundations.distributions.compact_carrier_convolution, foundations.distributions.distribution_tensor_product_derivatives, foundations.distributions.compact_carrier_convolution_support")
For every direction $`v\in E`, distributional differentiation commutes with
compact-carrier convolution in either factor:

$$`
  D_v(S*T)=(D_vS)*T=S*(D_vT).
`
:::

:::proof "foundations.distributions.compact_carrier_convolution_derivative"
Use compact carriers $`K,L` and product cutoffs equal to one near
$`K\times L`. Differentiating the localized pullback along addition gives the
pullback of $`D_v\varphi` plus a term where the cutoff is differentiated.
The tensor product kills the latter term because the cutoff derivative
vanishes near $`K\times L`. The coordinate derivative laws for
$`S\otimes T` identify the remaining term with differentiation of either
factor.
:::

Iterating the single-derivative law gives the same commutation for every
iterated directional derivative, and linearity extends it to finite
constant-coefficient operators. This is the algebraic step behind solving
$`P(D)u=T` by convolution with a fundamental solution.

:::theorem "foundations.distributions.compact_carrier_convolution_constant_coefficient" (parent := "foundations.distributions") (lean := "Distribution.HasCompactCarrier.iteratedLineDerivOp, Distribution.iteratedLineDerivOp_convolution_left, Distribution.iteratedLineDerivOp_convolution_right, Distribution.constantCoeffLineDerivCLM_convolution_left, Distribution.constantCoeffLineDerivCLM_convolution_right") (uses := "foundations.distributions.compact_carrier_convolution_derivative, foundations.distributions.constant_coefficient_operator_support")
Arbitrary iterated directional derivatives preserve compact carriers and
commute with compact-carrier convolution in either factor. Consequently, every
finite constant-coefficient differential operator $`P(D)` satisfies

$$`
  P(D)(S*T)=(P(D)S)*T=S*(P(D)T).
`
:::

:::proof "foundations.distributions.compact_carrier_convolution_constant_coefficient"
Iterate the one-direction commutation law, using preservation of the same
compact carrier at each derivative. Expand $`P(D)` as its defining finite
linear combination. Present every convolution using the same carrier cutoffs;
linearity of tensor products and localized pushforward then moves the finite
sum through convolution in either factor.
:::

The Dirac mass at the origin plays the role it has for convolution of finite
measures. The theorem is the left identity, and its proof is where cutoff
independence is used in earnest, because $`\delta_0` and $`T` come with
different carriers.

:::theorem "foundations.distributions.convolution_dirac" (parent := "foundations.distributions") (lean := "Distribution.hasCompactCarrier_delta, Distribution.convolution_delta_zero_left, Distribution.convolution_delta_delta") (uses := "foundations.distributions.compact_carrier_convolution, foundations.distributions.distribution_tensor_product_elementary, foundations.distributions.dirac_action")
The Dirac mass at the origin is a left identity for compact-carrier
convolution, and Dirac masses convolve by addition:

$$`
  \delta_0*T=T,
  \qquad
  \delta_x*\delta_y=\delta_{x+y}.
`
:::

:::proof "foundations.distributions.convolution_dirac"
For the left identity, choose a cutoff equal to one near $`\{0\}` and another
equal to one near a compact carrier of $`T`. Evaluation by $`\delta_0`
reduces the localized tensor pairing to $`T` applied to the second cutoff
times the test function; their difference vanishes near the carrier. For two
Dirac masses, the tensor product is $`\delta_{(x,y)}`, so localized pushforward
along addition evaluates every test function at $`x+y`.
:::

:::theorem "foundations.distributions.compact_carrier_fundamental_solution_convolution" (parent := "foundations.distributions") (lean := "Distribution.IsFundamentalSolutionAt.constantCoeff_convolution_eq") (uses := "foundations.distributions.fundamental_solution, foundations.distributions.compact_carrier_convolution_constant_coefficient, foundations.distributions.convolution_dirac")
Let $`P(D)` be a finite constant-coefficient differential operator. If
$`G` and $`T` have compact carriers and $`P(D)G=\delta_0`, then

$$`
  P(D)(G*T)=T.
`

The compact carrier of $`G` forces $`P(D)` to have order zero. The
Fourier–Laplace transform of a compactly carried $`G` is entire by
Paley–Wiener–Schwartz, so $`p(\zeta)\hat G(\zeta)=1` makes the symbol $`p` a
polynomial without complex zeros, hence a nonzero constant, and then $`G` is
a multiple of $`\delta_0`. The Newtonian and logarithmic fundamental solutions
are supported on all of space; their solution formula is a convolution in
which only one factor, normally the datum $`T`, has compact support.
:::

:::proof "foundations.distributions.compact_carrier_fundamental_solution_convolution"
Commute $`P(D)` through convolution in the left factor, substitute the
fundamental-solution equation $`P(D)G=\delta_0`, and use
$`\delta_0*T=T`.
:::

# Example: the Heaviside function and the Dirac delta

:::definition "foundations.distributions.heaviside" (parent := "foundations.distributions") (lean := "Distribution.heaviside, Distribution.heaviside_locallyIntegrable, Distribution.heavisideDistribution") (uses := "foundations.distributions.regular")
The Heaviside function on the real line is

$$`
H(x)=
\begin{cases}
0,&x<0,\\
1,&x\geq0.
\end{cases}
`

It is locally integrable and therefore defines a regular distribution
$`T_H\in\mathcal D'(\mathbb R)`.
:::

Because $`H` is the indicator of $`[0,\infty)`, the general regular-distribution
pairing collapses to an integral over the half-line, and the jump at $`0` is
invisible to the integral since a point has measure zero.

:::theorem "foundations.distributions.heaviside_action" (parent := "foundations.distributions") (lean := "Distribution.heavisideDistribution_apply") (uses := "foundations.distributions.heaviside, foundations.distributions.test_function")
For every test function $`\varphi\in C_c^\infty(\mathbb R)`,

$$`
\langle T_H,\varphi\rangle
=\int_{[0,\infty)}\varphi(x)\,dx.
`
:::

:::proof "foundations.distributions.heaviside_action"
The Heaviside function is the indicator of $`[0,\infty)`. Substituting this
density into the regular-distribution pairing restricts the integral to that
measurable half-line.
:::

The Heaviside function has no classical derivative at $`0`, and its derivative
in the sense of distributions is not a function at all. The computation is the
one-dimensional fundamental theorem of calculus, with the boundary term at $`0`
surviving as a point evaluation.

:::theorem "foundations.distributions.heaviside_derivative" (parent := "foundations.distributions") (lean := "Distribution.heavisideDistribution_lineDerivCLM") (uses := "foundations.distributions.heaviside_action, foundations.distributions.derivative_action, foundations.distributions.dirac")
The distributional derivative of the Heaviside distribution is the Dirac
mass at the origin:

$$`
D_1T_H=\delta_0.
`
:::

:::proof "foundations.distributions.heaviside_derivative"
For any test function $`\varphi`, distributional differentiation and the
Heaviside action formula give

$$`
\langle D_1T_H,\varphi\rangle
=-\int_{[0,\infty)}\varphi'(x)\,dx.
`

The endpoint $`\{0\}` has Lebesgue measure zero, so this equals the integral
over $`(0,\infty)`. Mathlib's fundamental theorem of calculus on a
semi-infinite interval applies because $`\varphi` is smooth and compactly
supported, yielding

$$`
-\int_{(0,\infty)}\varphi'(x)\,dx
=\varphi(0)
=\langle\delta_0,\varphi\rangle.
`

Extensionality of continuous linear functionals gives $`D_1T_H=\delta_0`.
:::

Smoothing makes the computation visible. Convolving $`H` with the mollifier
$`\eta_\varepsilon` gives a smooth step $`H_\varepsilon` whose classical
derivative is $`\eta_\varepsilon`, and pairing that derivative with a test
function gives $`\int\eta_\varepsilon\varphi`, which tends to
$`\varphi(0)` as $`\varepsilon\to0`. The figure follows this limit. The
distributional computation needs no limit at all.

{leanpde_figure "heaviside-dirac"}

The Heaviside computation shows what distributional differentiation adds. The
comparison with classical derivatives is the starting point for weak Sobolev
derivatives.

:::theorem "foundations.distributions.regular_derivative" (parent := "foundations.distributions") (lean := "Distribution.lineDerivCLM_ofFun") (uses := "foundations.distributions.regular, foundations.distributions.distribution")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "256-257"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`f` and $`g` be locally integrable, with $`f` Fréchet differentiable
everywhere and $`g=\partial_i f`. Then

$$`
  \partial_iT_f=T_g=T_{\partial_i f}.
`

Thus distributional differentiation extends classical coordinate
differentiation under the explicit regularity used by integration by parts,
and no information is lost by passing to $`\mathcal D'`.
:::

:::proof "foundations.distributions.regular_derivative"
Apply the distributional derivative to a test function $`\varphi`:

$$`
\langle\partial_i T_f,\varphi\rangle
=-\langle T_f,\partial_i\varphi\rangle
=-\int_{\mathbb R^n}f(x)\,\partial_i\varphi(x)\,dx.
`

Since $`f` is Fréchet differentiable and $`\varphi` is compactly supported and
smooth, integration by parts applies with no boundary contribution (the
integrand vanishes outside a compact set). This yields

$$`
-\int_{\mathbb R^n}f\,\partial_i\varphi\,dx
=\int_{\mathbb R^n}(\partial_i f)(x)\,\varphi(x)\,dx
=\langle T_{\partial_i f},\varphi\rangle.
`

As the identity holds for every test function,
$`\partial_i T_f=T_{\partial_i f}` in $`\mathcal D'(\mathbb R^n)`.
:::

Higher-order operators follow the same transposition rule as first derivatives,
with the signs cancelling in pairs. For the Dirac mass this yields an explicit
action formula for $`\Delta\delta_a`, which checks the operator
conventions.

:::theorem "foundations.distributions.dirac_laplacian" (parent := "foundations.distributions") (lean := "Distribution.laplacianCLM_delta_apply") (uses := "foundations.distributions.derivative_action, foundations.distributions.dirac_action")
The distributional Laplacian of the Dirac mass acts by

$$`
  \langle\Delta\delta_a,\varphi\rangle
  =(\Delta\varphi)(a).
`
:::

:::proof "foundations.distributions.dirac_laplacian"
By basis independence, the distributional Laplacian equals
$`\Delta T=\sum_i\partial_i^2 T`. For the Dirac mass at $`a`, apply the derivative
action formula twice in each coordinate:

$$`
\langle\partial_i^2\delta_a,\varphi\rangle
=-\langle\partial_i\delta_a,\partial_i\varphi\rangle
=\langle\delta_a,\partial_i^2\varphi\rangle
=\partial_i^2\varphi(a).
`

The two minus signs cancel, leaving point evaluation of the second derivative.
Summing over $`i=1,\ldots,n` gives
$`\langle\Delta\delta_a,\varphi\rangle=\sum_i\partial_i^2\varphi(a)=\Delta\varphi(a)`.
The operators act on $`\delta_a` although it has no pointwise representative
to differentiate.
:::
