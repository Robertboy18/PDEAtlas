/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Sobolev.Trace
import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ZeroTrace
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Exponent
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.SmoothCompactSupport
import PDE.Spaces.Sobolev.Inequalities.Sobolev.SecondOrder.Planar

/-!
# Sobolev embeddings

The critical exponent, the first-order global inequality, and the
higher-order subcritical and finite critical embeddings obtained by
iteration and extension.
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
#doc (Manual) "Sobolev Embeddings" =>

Sobolev embedding asks how much integrability follows from control of weak
derivatives. Below the dimension threshold, the first-order answer is governed
by the Sobolev conjugate $`p^*=np/(n-p)`. At order $`k`, the same gain produces
$`p_k=np/(n-kp)` while $`kp<n`. At the critical relation $`kp=n`, the
finite-target theorems assume $`n\geq1` and $`1\leq p`. On bounded
operational domains they give membership in every $`L^q` with
$`1\leq q<\infty`; a general $`L^\infty` conclusion fails, as a
two-dimensional $`W^{1,2}` example shows. The one-dimensional $`W^{1,1}`
endpoint is stronger and belongs to the Morrey theory.

The exponent $`p^*` is the one forced by scaling, and the
Gagliardo–Nirenberg–Sobolev inequality shows that it is attained (Evans,
2010, §5.6.1, Theorem 1; {Informal.citet "adams-fournier-2003"}[],
Theorem 4.12).

For a useful numerical instance, $`n=3` and $`p=2` give $`p^*=6`.
Thus an $`H^1` function on the whole space, or on a bounded operational
$`C^1` domain, belongs to $`L^6`. Its cubic nonlinearity is then square
integrable:

$$`
\|u^3\|_{L^2}
=\left(\int |u|^6\right)^{1/2}
=\|u\|_{L^6}^3.
`

This is a common reason to use an embedding: the equation contains $`u^3`,
while the energy estimate initially controls only $`u` and its first
derivatives in $`L^2`.

On $`\mathbb R^n`, a closed-graph argument makes the subcritical inclusion a
continuous linear map. On domains, either a supplied extension operator
transfers the global theorem, or a concrete $`C^1` atlas is used one
first-order slice at a time; the atlas iteration produces continuous linear
maps between completed graph spaces whose rows agree almost everywhere with
the original derivatives.

:::group "sobolev.inequalities"
Sobolev inequalities
:::

# First-Order Critical Exponents

The first-order proof has three steps: the global smooth estimate, density
in the completed Sobolev space, and restriction from a global extension back
to the domain.

:::definition "sobolev.critical_exponent" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.pStar")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "276"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`0<p<n`, the critical Sobolev exponent is

$$`
p^*=\frac{np}{n-p},\qquad
\frac1{p^*}=\frac1p-\frac1n.
`

The Lean definition is totalized through `Real.toNNReal`, so it has a value
even outside the analytic range. The formula for its real coercion requires
$`n>0` and $`p<n`; the reciprocal identity additionally requires $`p>0`.
Sobolev inequalities use the Banach range $`1\leq p<n`.
:::

The Gagliardo–Nirenberg–Sobolev inequality is a smooth compact-support
estimate on all of $`\mathbb R^n`.

:::theorem "sobolev.gns" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.eLpNorm_le_eLpNorm_fderiv_pStar, SobolevSpace.Inequalities.lintegral_pow_le_pow_sum_lintegral_partialDeriv, SobolevSpace.Inequalities.eLpNorm_le_sum_eLpNorm_partialDeriv_one, SobolevSpace.Inequalities.eLpNorm_le_eLpNorm_fderiv_of_endpoint, SobolevSpace.Inequalities.eLpNorm_le_explicit_mul_eLpNorm_fderiv_pStar") (uses := "sobolev.critical_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "276-279"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u\in C_c^1(\mathbb R^n)` and $`1\leq p<n`. The
Gagliardo–Nirenberg–Sobolev estimate gives

$$`\lVert u\rVert_{L^{p^*}}\le C_{n,p}\lVert Du\rVert_{L^p},`

where $`C_{n,p}` depends only on dimension and exponent. For $`p=1` and
$`n\ge2`, a coordinate version has the explicit bound

$$`\lVert u\rVert_{L^{n/(n-1)}}\le
\sum_{i=1}^n\lVert\partial_i u\rVert_{L^1}.`

The coordinate endpoint holds for functions into any real normed space.
For $`1<p<n`, the power argument gives an explicit sufficient constant for
functions into a real inner product space:

$$`\lVert u\rVert_{L^{p^*}}\le
\frac{np(n-1)}{n-p}\lVert Du\rVert_{L^p}.`

For example, $`n=3` and $`p=2` give
$`\lVert u\rVert_{L^6}\le12\lVert Du\rVert_{L^2}`. This bound is not
claimed to be sharp; its value is available for a numerical residual budget.
Passing from smooth functions to weak Sobolev representatives uses
compactly supported smooth approximation.
:::

:::proof "sobolev.gns"
The proof specializes Mathlib's finite-dimensional
Gagliardo–Nirenberg–Sobolev theorem to Euclidean space and rewrites the
exponent using {uses "sobolev.critical_exponent"}[].
For the coordinate endpoint bound, pull back along the canonical volume-preserving
coordinate map and apply Mathlib's grid-lines inequality. The operator norm of the
derivative on the maximum-norm coordinate space is bounded by the sum of the
coordinate derivative norms. Integration and the endpoint root give the stated estimate.

To obtain the subcritical estimate, first bound the coordinate sum by
$`n\lVert Du\rVert_{L^1}`. Apply this scalar endpoint bound to
$`\lVert u\rVert^\gamma`, with
$`\gamma=p(n-1)/(n-p)`, and use Hölder on its derivative. Cancelling the
common power of $`\lVert u\rVert_{L^{p^*}}` leaves the coefficient
$`n\gamma`. The lifting theorem accepts a supplied endpoint constant,
so a better endpoint bound can be used without repeating the power argument.
:::

Zero boundary values give another route to an estimate on a domain: prove the
bound on supported test functions, then use their density in the zero-boundary
space. This route does not require an extension atlas.

:::theorem "sobolev.h10_explicit_critical" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.norm_h10LpEmbedding_apply_le_of_testFunction_bound, SobolevSpace.GraphSpace.norm_h10LpEmbedding_le_of_testFunction_bound, SobolevSpace.GraphSpace.norm_h10LpEmbedding_le_critical, SobolevSpace.GraphSpace.norm_h10LpEmbedding_apply_le_of_le, SobolevSpace.GraphSpace.norm_h10LpEmbedding_le_of_le") (uses := "sobolev.gns, sobolev.h10_space")
Let $`n>2` and let $`\Omega\subseteq\mathbb R^n` be measurable with finite
volume. The inclusion from the supported-core closure $`H^1_0(\Omega)`
into $`L^{2n/(n-2)}(\Omega)` has the explicit bound

$$`\lVert u\rVert_{L^{2n/(n-2)}}\le
\frac{2n(n-1)}{n-2}\lVert u\rVert_{H^1}.`

Thus in three dimensions its operator norm is at most $`12`. The domain may
have corners; openness and boundary regularity are not needed for this
closure-space estimate. On an open domain the closure is the usual
$`H^1_0(\Omega)`.

More generally, for $`C\geq0`, a supplied bound
$`\lVert\varphi\rVert_{L^q}\le C\lVert D\varphi\rVert_{L^2}`
for supported smooth test functions transfers to
$`\lVert u\rVert_{L^q}\le C\lVert\nabla u\rVert_{L^2}`
throughout the supported finite-exponent range. The inclusion's operator norm
is then at most $`C` for the full $`H^1` norm.

Hölder lowers the target exponent with its explicit volume factor. For
two supported exponents $`2\leq q\leq r`,

$$`\lVert u\rVert_{L^q(\Omega)}\leq
|\Omega|^{1/q-1/r}\lVert u\rVert_{L^r(\Omega)}.`

In three dimensions, taking $`q=4` and $`r=6` therefore gives
$`\lVert u\rVert_{L^4}\leq12|\Omega|^{1/12}\lVert u\rVert_{H^1}`.
For a unit-volume domain, including the unit cube, the coefficient is $`12`.
:::

:::proof "sobolev.h10_explicit_critical"
On a test function, restriction does not change either global norm because
the function and its derivative are supported in $`\Omega`. For a scalar
function, the Euclidean norm of the gradient equals the operator norm of the
Fréchet derivative. The weak gradient of the test-function inclusion agrees
with this classical gradient almost everywhere.

Both norms are continuous on the completed space, so the inequality defines
a closed set. Density of the test functions extends the bound with the same
constant. The explicit critical coefficient is the case $`p=2` of
{uses "sobolev.gns"}[].
:::

The smooth estimate reaches Sobolev functions on a bounded domain in two
steps: extension to a global $`W^{1,p}` function through the $`C^1` atlas,
then smooth approximation, which carries the global $`L^{p^*}` bound to the
completed space.

:::theorem "sobolev.c1_critical_membership" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Extension.C1.memLp_pStar_of_sobolevSpaceOn, SobolevSpace.Inequalities.memLp_firstOrderSobolevExponent_of_c1ExtensionAtlas, SobolevSpace.Inequalities.memLp_of_le_firstOrderSobolevExponent_of_c1ExtensionAtlas") (uses := "sobolev.critical_exponent, sobolev.representative_space, sobolev.graph_space, sobolev.mollifier, sobolev.c1_extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "279-280"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be an operational bounded $`C^1` domain,
let $`n>0`, and let $`1\leq p<n`.  Every representative in
$`W^{1,p}(\Omega)` belongs to $`L^{p^*}(\Omega)`.

The graph-space endpoint is written with
`higherOrderExponent n 1 p`; the exponent algebra identifies it with $`p^*`.
Because the atlas is bounded, the restricted volume measure is finite, and
Mathlib's exponent monotonicity also gives `MemLp` at every extended
nonnegative exponent $`r\leq p^*`. No lower bound on $`r` is needed for that
raw predicate, although $`1\leq r` is needed to interpret the target as a
Banach $`L^r` space.
:::

:::proof "sobolev.c1_critical_membership"
Use {uses "sobolev.c1_extension"}[] to obtain a global Sobolev function, apply
the density upgrade of {uses "sobolev.gns"}[], and restrict the resulting
$`L^{p^*}` representative to $`\Omega`. Almost-everywhere agreement of the
extension with the original base row transfers `MemLp` back to the domain.
:::

# Higher Orders by Iteration

For $`k>1`, there are three related but different constructions: an explicit
smooth-core inequality, a global completed-space embedding, and two
bounded-domain routes. One domain route uses a supplied order-$`k` extension
operator; the other repeatedly applies the first-order operational extension
theorem to derivative slices.

:::definition "sobolev.higher_order_exponent" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.higherOrderExponent") (uses := "sobolev.critical_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`k p<n`, the higher-order Sobolev exponent is

$$`
q=\frac{np}{n-kp},
\qquad
\frac1q=\frac1p-\frac{k}{n}.
`

The analytic theorems carry the strict subcritical hypothesis explicitly.
The definition itself is totalized through `Real.toNNReal`. Under $`n>0`,
$`p>0`, and $`kp<n`, the library proves both the closed formula and

$$`
\frac1{p_k}=\frac1p-\frac{k}{n}.
`

It also proves $`p_0=p`, $`p\leq p_k`,
$`p^*(p_k)=p_{k+1}` whenever one more step is subcritical, and
$`p_{k-1}=n` when $`kp=n` and $`k>0`.
:::

The identity $`p^*(p_k)=p_{k+1}` is what makes the higher-order theory an
iteration of the first-order one: applying the first-order inequality at
exponent $`p_k` trades one derivative for one step of integrability. The
smooth-core inequality carries this out for $`C^k_c` functions, with an
explicit constant assembled from the first-order constants at the
intermediate exponents $`p_0,\ldots,p_{k-1}`.

:::theorem "sobolev.higher_order_smooth_core" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.eLpNorm_le_higherDerivativeSum, SobolevSpace.Inequalities.higherDerivativeSum, SobolevSpace.Inequalities.higherOrderConstant") (uses := "sobolev.higher_order_exponent, sobolev.gns")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u\in C_c^k(\mathbb R^n)`, $`1\leq p`, and $`kp<n`. Then

$$`
\|u\|_{L^{p_k}}
\leq C(n,k,p)
\sum_{(i_1,\ldots,i_k)\in\{1,\ldots,n\}^k}
\|\partial_{i_1}\cdots\partial_{i_k}u\|_{L^p}.
`

Lean implements the right-hand side recursively as `higherDerivativeSum`.
It sums over ordered coordinate words. Consequently, a mixed derivative may
occur more than once; this finite multiplicity is harmless and differs from a
multi-index sum only by a dimension-and-order comparison constant. The
constant `higherOrderConstant` is also recursive: each step multiplies the
previous constant by Mathlib's first-order Sobolev constant at the current
exponent.
:::

:::proof "sobolev.higher_order_smooth_core"
Induct on $`k`. The successor step applies {uses "sobolev.gns"}[] at exponent
$`p_k` to $`u`, applies the induction hypothesis to every first partial
derivative, and uses compact-support stability under differentiation. The
identity $`p^*(p_k)=p_{k+1}` closes the exponent calculation.
:::

On the completed space $`W^{k,p}(\mathbb R^n)` the same iteration runs on the
weak-derivative rows instead of classical derivatives, using the first-order
theorem's density upgrade at each stage.

:::theorem "sobolev.higher_order_embedding" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.memLp_higherOrderExponent, SobolevSpace.Inequalities.memLp_derivativeWord_higherOrderExponent") (uses := "sobolev.higher_order_exponent, sobolev.gns, sobolev.graph_space, sobolev.mollifier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`u\in W^{k,p}(\mathbb R^n)`, $`1\leq p`, and $`kp<n`, then
$`u\in L^q(\mathbb R^n)` for the exponent in
{uses "sobolev.higher_order_exponent"}[].  The proof iterates the first-order
Sobolev inequality through compatible weak-derivative slices.

The reusable derivative-family form is more general. If
$`U\in W^{m,p}(\mathbb R^n)`, a derivative word $`\alpha` satisfies
$`|\alpha|+r\leq m`, and $`rp<n`, then its chosen representative
$`D^\alpha U` belongs to $`L^{p_r}`. Later arguments use this form when they
need integrability of lower derivatives and not only of the base row.
:::

:::proof "sobolev.higher_order_embedding"
Induct on $`k`. At each step, apply the first-order Sobolev inequality to all
weak derivatives of the current order, replacing the exponent $`p_j` by its
Sobolev conjugate $`p_{j+1}`. The relation
$`1/p_{j+1}=1/p_j-1/n` shows after $`k` steps that
$`1/q=1/p-k/n`. The strict inequality $`kp<n` keeps every intermediate
exponent finite, and the graph-space compatibility identifies the final base
row with $`u`.
:::

Membership in $`L^{p_k}` for each $`U` defines a linear inclusion of
$`W^{k,p}(\mathbb R^n)` into $`L^{p_k}`, but says nothing about its
continuity.

:::theorem "sobolev.subcritical_embedding_operator" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.norm_subcriticalEmbeddingCLM_le, SobolevSpace.Inequalities.subcriticalEmbeddingCLM") (uses := "sobolev.higher_order_embedding, sobolev.graph_space_complete")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same subcritical hypotheses, with source and target exponents at
least one, the global inclusion

$$`
I_{n,k,p}:W^{k,p}(\mathbb R^n)\longrightarrow L^{p_k}(\mathbb R^n)
`

is a continuous linear map. Therefore

$$`
\|I_{n,k,p}U\|_{L^{p_k}}
\leq \|I_{n,k,p}\|\,\|U\|_{W^{k,p}}.
`

The constant is the operator norm of $`I_{n,k,p}`, which is finite because
the closed graph theorem makes the inclusion continuous.
:::

:::proof "sobolev.subcritical_embedding_operator"
First use {uses "sobolev.higher_order_embedding"}[] to define the algebraic
linear inclusion into Mathlib's `Lp` space. If a source sequence converges in
the graph-space norm, its base rows converge in $`L^p` and hence in measure.
If their images converge in $`L^{p_k}`, they converge in measure to the target
limit as well. Uniqueness of limits in measure identifies the two limits
almost everywhere, proving that the graph is sequentially closed. The closed
graph theorem for Banach spaces supplies continuity; the norm inequality is
the standard continuous-linear-map operator bound.
:::

The global results move to a domain as soon as a bounded extension operator
$`W^{k,p}(\Omega)\to W^{k,p}(\mathbb R^n)` is available.

:::theorem "sobolev.higher_order_embedding_extension" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.memLp_higherOrderExponent_of_extension, SobolevSpace.Inequalities.memLp_of_le_higherOrderExponent_of_extension") (uses := "sobolev.higher_order_embedding, sobolev.extension_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u\in W^{k,p}(\Omega)`, with $`1\leq p` and $`kp<n`, and supply a
bounded order-$`k` extension operator that agrees with $`u` almost everywhere
on $`\Omega`. Then $`u\in L^q(\Omega)` for
$`1/q=1/p-k/n`. If $`\Omega` is bounded, finite-measure monotonicity also
gives every usual target exponent $`1\leq r\leq q`; the Lean declaration in
fact accepts any extended nonnegative exponent $`r\leq q`.

Nothing else about $`\Omega` is used; boundedness enters only for the lower
target exponents, through finite measure.
:::

:::proof "sobolev.higher_order_embedding_extension"
Apply the supplied bounded extension operator to obtain a global
$`W^{k,p}(\mathbb R^n)` representative. The global higher-order embedding
places that extension in $`L^q`, and its almost-everywhere agreement with
$`u` transfers the result to $`\Omega`. On a bounded domain, finite-measure
monotonicity gives $`L^r` membership for every $`r\leq q`.
:::

Since both the global inclusion and the supplied extension are continuous
linear maps, the same route also yields a quantitative statement.

:::theorem "sobolev.higher_order_embedding_extension_norm" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.norm_extended_subcritical_le") (uses := "sobolev.subcritical_embedding_operator, sobolev.higher_order_embedding_extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a supplied bounded extension
$`E:W^{k,p}(\Omega)\to W^{k,p}(\mathbb R^n)`, the quantitative estimate is

$$`
\|I_{n,k,p}(EU)\|_{L^{p_k}(\mathbb R^n)}
\leq
\|I_{n,k,p}\|\,\|E\|\,\|U\|_{W^{k,p}(\Omega)}.
`

Both constants are operator norms of continuous linear maps. The estimate
measures the global extension; restriction to $`\Omega` and
almost-everywhere agreement give the corresponding estimate for the domain
representative.
:::

:::proof "sobolev.higher_order_embedding_extension_norm"
Apply the operator-norm bound for
{uses "sobolev.subcritical_embedding_operator"}[] to $`EU`, then apply the
operator-norm bound for $`E`, and reassociate the three nonnegative factors.
:::

The operational $`C^1` atlas directly yields a first-order extension
operator; an order-$`k` operator needs more. Applying the first-order
extension and embedding to each derivative row in turn obtains the same base
integrability without any order-$`k` operator.

:::theorem "sobolev.higher_order_embedding_domain" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.Embedding.base_memLp_iterated, SobolevSpace.GraphSpace.Embedding.coordinate_memLp_iterated, SobolevSpace.GraphSpace.Embedding.iteratedStep, SobolevSpace.GraphSpace.Embedding.iteratedStep_apply_ae") (uses := "sobolev.higher_order_embedding, sobolev.extension.atlas, sobolev.c1_critical_membership, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-285"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` carry the operational bounded $`C^1` atlas, let
$`u\in W^{k+j,p}(\Omega)` with $`1\leq p`, and suppose $`jp<n`. Repeated use
of the concrete first-order extension theorem gives

$$`
W^{k+j,p}(\Omega)\longrightarrow W^{k,p_j}(\Omega),
\qquad \frac1{p_j}=\frac1p-\frac jn.
`

The target retains the original weak-derivative coordinates almost
everywhere. Taking $`k=0` gives bounded-domain higher-order integrability
without assuming an order-$`j` extension operator.

This continuous linear map has norm at most the number of retained
coordinates times an explicit recursive constant built from the first-order
GNS constants, the extension norm, and the coordinate counts.
On the whole space, by contrast, the bound of
{uses "sobolev.subcritical_embedding_operator"}[] is the operator norm itself.
:::

:::proof "sobolev.higher_order_embedding_domain"
Starting from the order-$`k+j` graph-space element, apply the operational
first-order extension and Sobolev embedding to each derivative row of order
at most $`k+j-1`. This consumes one derivative and changes $`p_\ell` to
$`p_{\ell+1}` with $`1/p_{\ell+1}=1/p_\ell-1/n`. Iterating $`j` times is
valid because $`jp<n`; the retained rows remain almost everywhere equal to
the original weak derivatives. The resulting element therefore lies in
$`W^{k,p_j}(\Omega)` and has the same base function.
:::

In dimension five, the order-two Hilbert case makes the iteration concrete.
Starting from $`u\in W^{2,2}(\Omega)` with $`n=5` and $`p=2`, the first
application of the Sobolev embedding consumes one derivative and replaces
$`p=2` by its Sobolev conjugate $`2^*=5\cdot2/(5-2)=10/3`. The
second application consumes the remaining derivative and replaces $`10/3` by
$`(10/3)^*=5\cdot(10/3)/(5-10/3)=10`:

$$`
W^{2,2}(\Omega)
  \longrightarrow W^{1,10/3}(\Omega)
  \longrightarrow L^{10}(\Omega).
`

In reciprocals, $`3/10=1/2-1/5` at the first step and $`1/10=3/10-1/5` at
the second, and the final exponent agrees with $`np/(n-kp)=10` for $`k=2`.
The strict subcritical condition $`kp<n`, here $`4<5`, holds. In dimension
four, $`kp=4=n` is the critical case, which gives every finite $`L^q` but not
$`L^\infty` ({Informal.citet "adams-fournier-2003"}[], Theorem 4.12, Part I).

This iteration is one ingredient in the supercritical reduction used by the
regularity chapter. The smooth-boundary theorem uses the non-sharp hypothesis
$`u\in W^{m+n+1,2}`. For $`n\geq2`, it first lowers the exponent to one,
performs $`n-1` subcritical embedding steps to reach exponent $`n`, and then
uses the critical embedding with target exponent $`2n`. For $`n=1`, exponent
$`2` is already supercritical, so the proof simply restricts the derivative
order from $`m+2` to $`m+1`. Both branches then use closure-level Morrey
reconstruction to obtain a $`C^m` representative. The surplus $`n+1` is
uniform bookkeeping for this route, not a sharp derivative threshold.

:::theorem "sobolev.critical_finite_embedding" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.memLp_critical_firstOrder_of_c1ExtensionAtlas") (uses := "sobolev.c1_critical_membership, sobolev.extension.atlas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\geq1` and let $`\Omega` carry the operational bounded $`C^1`
extension atlas. Every $`W^{1,n}(\Omega)` field belongs to
$`L^q(\Omega)` for every finite $`1\leq q<\infty`. When $`n=1`, extension
to $`\mathbb R` and the bounded representative of a $`W^{1,1}(\mathbb R)`
function also give membership in $`L^\infty(\Omega)`.

Here `q` is an `NNReal`, so finiteness is built into its type. The linked
theorem is a `MemLp` statement.
:::

:::proof "sobolev.critical_finite_embedding"
The operational atlas supplies the extension operator. In dimension one,
its $`W^{1,1}(\mathbb R)` extension has a bounded representative;
restriction and finite measure give every finite $`L^q(\Omega)` norm.
For $`n\geq2`, fix a finite $`q`. If $`q\leq n`, finite-measure monotonicity lowers the
base $`L^n` coordinate directly to $`L^q`. If $`q>n`, set
$`s=nq/(n+q)`. Then $`1\leq s<n` and $`1/q=1/s-1/n`. A cutoff equal to one near
the domain gives the global extension finite-measure support, lowering it from $`L^n` to $`L^s`,
producing a global $`W^{1,s}` field; the whole-space first-order Sobolev
theorem places its base function in $`L^q` on the domain.
:::

# The Critical Higher-Order Case

The failure of a general boundedness conclusion is already visible in two
dimensions at first order. Near $`r=|x|=0`, take
$`u(r)=\log\log(e/r)` and multiply it by a smooth cutoff supported inside
the unit disk. It is unbounded, yet its gradient has finite square integral
near zero, because

$$`
|u'(r)|=\frac1{r\log(e/r)},\qquad
\int_0^{1/2}|u'(r)|^2r\,dr
=\int_0^{1/2}\frac{dr}{r\log^2(e/r)}<\infty.
`

The function itself is square integrable as well. To check the weak
derivative at the missing point, integrate by parts outside a disk of radius
$`\varepsilon`. The boundary term is bounded by a constant times
$`\varepsilon\log\log(e/\varepsilon)`, which tends to zero. Thus the
displayed derivative is also the weak derivative across the origin.
The cutoff adds only regular terms away from zero, giving an $`H^1`
example with no bounded representative. This explains why the critical
finite-$`q` conclusions cannot in general be replaced by an
$`L^\infty` conclusion.

When $`kp=n`, iteration reaches $`W^{1,n}` rather than an $`L^\infty`
endpoint. The bounded-domain first-order critical theorem then supplies every
finite target exponent.

:::theorem "sobolev.critical_higher_order_extension" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Inequalities.memLp_critical_dimension_of_extension, SobolevSpace.Inequalities.memLp_critical_of_le_dimension_of_extension, SobolevSpace.Inequalities.memLp_critical_finite_of_extension") (uses := "sobolev.critical_finite_embedding, sobolev.higher_order_embedding_extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\geq1`, $`k>0`, $`1\leq p`, and $`kp=n`. Suppose $`\Omega` is
bounded and admits a bounded order-$`k` extension operator; no atlas is
assumed. Then every $`W^{k,p}(\Omega)` field belongs
to $`L^q(\Omega)` for every finite $`1\leq q<\infty`. The closed graph
theorem makes each inclusion a continuous linear map.

For the integrability assertion,
the supplied extension gives $`L^n` membership without any boundedness
assumption on $`\Omega`; boundedness then lowers that result to every extended
exponent $`r\leq n`; finally, the Sobolev-conjugate preimage argument reaches finite
$`q>n`.
:::

:::proof "sobolev.critical_higher_order_extension"
If $`q\leq n`, the supplied extension gives the critical $`L^n` membership
and finite-measure monotonicity lowers it to $`L^q`. If $`q>n`, set
$`s=nq/(n+q)`, so $`1\leq s<n` and $`1/q=1/s-1/n`. The extension and the
critical relation $`kp=n`, with a cutoff, produce a global first-order $`W^{1,s}` field
localized near $`\Omega`; the whole-space first-order Sobolev theorem then gives
$`L^q` membership. Almost-everywhere agreement on the domain identifies the extension
with the original base field.
:::

On an atlas domain the supplied order-$`k` extension operator can be
dispensed with.

:::theorem "sobolev.critical_higher_order_domain" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.Embedding.toCriticalFirstOrder_base_ae, SobolevSpace.GraphSpace.Embedding.toCriticalFirstOrder, SobolevSpace.GraphSpace.Embedding.memLp_critical_finite_of_c1ExtensionAtlas") (uses := "sobolev.critical_finite_embedding, sobolev.higher_order_embedding_domain")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an operational bounded $`C^1` atlas domain, the extra order-$`k` extension
hypothesis can be removed. Iterating $`k-1` subcritical first-order steps
produces a $`W^{1,n}` representative with the same base function almost
everywhere; the critical first-order theorem then gives

$$`
W^{k,p}(\Omega)\subset L^q(\Omega)
\quad\text{for every finite }1\leq q<\infty
`

whenever $`n\geq1`, $`k>0`, $`1\leq p`, and $`kp=n`. As in Evans, the
endpoint $`q=\infty` is excluded. The iteration defines a bounded operator
on graph space with an explicit operator-norm bound.
:::

:::proof "sobolev.critical_higher_order_domain"
Use the operational atlas iteration directly for $`k-1` steps. Since
$`kp=n`, the exponent recurrence reaches $`n` exactly while leaving one weak
derivative, producing a $`W^{1,n}` element whose base row agrees almost
everywhere with $`u`. The critical first-order theorem gives membership in
every finite $`L^q`, and almost-everywhere equality transfers that membership
back to the original field.
:::

In the plane with $`p=2` the critical relation $`kp=n` holds already at first
order, and the critical theorem gives every finite $`L^q` for $`H^1(\Omega)`.
The planar second-order theorem adds an operator.

:::theorem "sobolev.planar_second_order_embedding" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.norm_h2ToW1pOfC1ExtensionAtlas_le, SobolevSpace.GraphSpace.h2ToW1pOfC1ExtensionAtlasCLM, SobolevSpace.GraphSpace.h2ToW1pOfC1ExtensionAtlas, SobolevSpace.GraphSpace.h2ToW1pOfC1ExtensionAtlas_apply_ae, SobolevSpace.GraphSpace.h2ToW1pOfC1ExtensionAtlasCLM_apply, SobolevSpace.GraphSpace.memLp_orderOneCoordinate_of_c1ExtensionAtlas, SobolevSpace.GraphSpace.H1SpaceOn.memLp_of_le_pStar_of_c1ExtensionAtlas") (uses := "sobolev.graph_space, sobolev.h1_space, sobolev.extension.atlas, sobolev.critical_exponent, sobolev.mollifier")
Let $`\Omega\subseteq\mathbb R^2` carry the operational bounded $`C^1`
extension atlas, and let $`1\leq q<2` and
$`1\leq p\leq q^*=2q/(2-q)`. Since $`q\mapsto q^*` maps $`[1,2)` onto
$`[2,\infty)`, every finite $`p\geq1` is admissible for a suitable $`q`,
while $`p=\infty` is not.

For $`V\in H^1(\Omega)` the base coordinate lies in $`L^p(\Omega)`, and for
$`U\in H^2(\Omega)=W^{2,2}(\Omega)` every coordinate of order at most one,
namely $`U_0`, $`U_1`, and $`U_2`, lies in $`L^p(\Omega)`. These coordinates
assemble into an element of $`W^{1,p}(\Omega)` with the same rows almost
everywhere, and the assembly is a continuous linear map

$$`
J_p:H^2(\Omega)\longrightarrow W^{1,p}(\Omega),
\qquad
(J_pU)_a=U_a\ \text{a.e. on }\Omega\ \text{for }|a|\leq1,
\qquad
\|J_pU\|_{W^{1,p}(\Omega)}\leq\|J_p\|\,\|U\|_{H^2(\Omega)} .
`

This is the planar instance of the first-order embedding on bounded $`C^1`
domains, applied to each derivative row of $`U`; it reaches every finite
exponent because $`p=2` is the critical exponent in dimension two. The bound
is in terms of the operator norm $`\|J_p\|`. The Lean operator takes the
exponent data as arguments, and its values are determined by the rows of
$`U`.
:::

:::proof "sobolev.planar_second_order_embedding" (uses := "sobolev.c1_critical_membership, sobolev.graph_space_order_restriction, sobolev.first_order_derivative_slice")
A bounded atlas domain has finite measure, so an $`H^1(\Omega)` element
lowers to $`W^{1,q}(\Omega)` with the same coordinates for every $`q<2`.
The operational extension theorem and the first-order Sobolev inequality
place its base representative in $`L^{q^*}(\Omega)`, and finite measure
lowers this to every $`p\leq q^*`. For $`U\in H^2(\Omega)` and an index
$`a` of order at most one, apply this to the first-order derivative slice
representing $`U_a`, whose base coordinate is $`U_a` almost everywhere. The
weak-derivative identities of the assembled bundle are those of the
order-one restriction $`\pi_{2,1}U`. Linearity holds coordinatewise almost
everywhere. Continuity comes from the closed graph theorem: convergence in
either graph norm implies convergence in measure of every coordinate, and
source and target coordinates agree almost everywhere, so the graph is
sequentially closed.
:::
