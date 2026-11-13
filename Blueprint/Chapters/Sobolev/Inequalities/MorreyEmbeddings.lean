/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Inequalities.SobolevEmbeddings
import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.InfiniteExponent
import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.OneDimensionalCritical
import PDE.Spaces.Sobolev.Inequalities.Morrey.Exponent
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Embedding
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Holder
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.Estimate
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.Estimate
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding

/-!
# Morrey embeddings

This module records the Morrey exponent, one- and multidimensional pointwise
estimates, bounded Hölder representatives, higher-order embeddings, their
weak-to-classical reconstruction in the interior and on a smooth-domain
closure, and the critical one-dimensional endpoint.
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
#doc (Manual) "Morrey Embeddings" =>

When the integrability exponent exceeds the spatial dimension, a first weak
derivative controls oscillation as well as integrability.
Morrey's inequality makes this quantitative on $`\mathbb R^n`, and on domains
equipped with a suitable extension operator: a $`W^{1,p}` function with $`p>n`
has a representative that is Hölder continuous with exponent $`1-n/p`. We
follow Evans (2010, §5.6.2, Theorems 4 and 5); see also
{Informal.citet "adams-fournier-2003"}[] (Theorem 4.12) and
{Informal.citet "brezis-2011"}[] (Theorem 9.12).

Line-segment and polar-coordinate estimates first prove smooth scalar-valued
inequalities. The finite-exponent construction then controls the full Hölder
norm, uses density to obtain a bounded linear map on the completed Sobolev
graph space, and transports that map to a domain by extension and
restriction. The smooth $`p=\infty` Lipschitz estimate, higher derivative
words, reconstruction of classical derivatives up to the boundary, and the
critical one-dimensional $`W^{1,1}` endpoint are treated separately.

The embedding constructs a bounded continuous representative that agrees
almost everywhere with the Sobolev function. Point evaluation is then
well-defined, and a uniform Hölder bound gives the equicontinuity needed
for Arzelà–Ascoli ({Informal.citet "adams-fournier-2003"}[], Section 4.5).

# Morrey and endpoint embeddings

:::definition "sobolev.morrey_exponent" (parent := "sobolev.inequalities") (lean := "SobolevSpace.morreyExponent, SobolevSpace.morreyExponent_pos")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The Morrey exponent is

$$`
\gamma(n,p)=1-\frac{n}{p}.
`

Lean implements this as $`1-n/p_{\mathrm{real}}`, where
`ENNReal.toReal` sends $`\infty` to zero. Thus
$`\gamma(n,\infty)=1`. Totalized real division also makes
$`\gamma(n,0)=1`; the latter is a formal artifact and is not an analytic
endpoint. In the analytic range $`0<n<p\leq\infty`, the exponent is strictly positive.
The completed finite-exponent embeddings use $`0<n<p<\infty`.
:::

In one dimension the exponent is $`1-1/p`, and the one-dimensional case
already includes the Lipschitz endpoint.

:::theorem "sobolev.morrey_one_dimensional" (parent := "sobolev.inequalities") (lean := "SobolevSpace.enorm_sub_le_eLpNorm_deriv_mul_rpow, SobolevSpace.norm_sub_le_eLpNorm_deriv_toReal_mul_rpow, SobolevSpace.holderWith_morreyExponent_one, SobolevSpace.memHolder_morreyExponent_one") (uses := "sobolev.morrey_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`1<p\leq\infty`, let $`u:\mathbb R\to\mathbb R` be continuously
differentiable, and suppose $`u'` has finite $`L^p` norm. Then

$$`
|u(y)-u(x)|
\leq \|u'\|_{L^p}\,|y-x|^{1-1/p}.
`

No compact-support hypothesis occurs in the linked declaration. The theorem
is scalar-valued, is the one-dimensional specialization of Morrey's
line-segment estimate, and includes the $`p=\infty` endpoint. The extended
norm form needs no finiteness assumption; the real-valued form assumes that
the derivative seminorm is finite. The same estimate is also stated with
Mathlib's `HolderWith` and `MemHolder` predicates.
:::

:::proof "sobolev.morrey_one_dimensional"
Assume first that $`x\leq y`. The fundamental theorem of calculus bounds
$`|u(y)-u(x)|` by the $`L^1` norm of $`u'` on $`[x,y]`. Hölder's inequality
lowers this local norm from $`L^p` to $`L^1`, contributing the interval-length
factor $`|y-x|^{1-1/p}`. Restriction can only decrease the global
$`L^p` norm, and exchanging $`x` and $`y` handles the remaining order.
:::

At $`p=\infty` the Morrey exponent equals $`1` in every dimension, and the
estimate becomes a Lipschitz bound that needs no potential estimate.

:::theorem "sobolev.morrey_infinite_exponent" (parent := "sobolev.inequalities") (lean := "SobolevSpace.enorm_fderiv_le_eLpNorm_top, SobolevSpace.norm_sub_le_of_fderiv_bound, SobolevSpace.norm_sub_le_eLpNorm_fderiv_top_toReal_mul_norm") (uses := "sobolev.morrey_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
In every dimension, a global $`C^1` function whose Fréchet derivative has
finite $`L^\infty` norm is Lipschitz:

$$`
|u(y)-u(x)|
\leq \|Du\|_{L^\infty(\mathbb R^n)}\,\|y-x\|.
`

The statement is for continuously differentiable scalar functions. The completed Morrey embedding
uses finite $`p`. Smooth functions are not norm-dense in $`W^{1,\infty}`, so
the completed $`p=\infty` endpoint is proved separately, from a Lipschitz
representative: every $`U\in W^{1,\infty}(\mathbb R^n)` has one with
Hölder-one norm at most $`(n+1)\|U\|`. Higher-order domain embeddings
likewise reconstruct Lipschitz representatives of the derivative coordinates.
:::

:::proof "sobolev.morrey_infinite_exponent"
Continuity of $`Du` upgrades its almost-everywhere $`L^\infty` bound to the
pointwise estimate $`\lVert Du(z)\rVert\leq\lVert Du\rVert_{L^\infty}` at
every $`z`. The convex mean-value inequality on the segment from $`x` to
$`y` then gives the stated Lipschitz bound.
:::

For finite $`p>n`, a bound in ambient $`L^p` does not give a pointwise
bound on the gradient along a prescribed segment. In dimensions above one,
that segment even has zero ambient volume. The proof therefore averages
the fundamental theorem of calculus over segments: the difference between a
point value and a ball average is bounded by a Riesz potential of the gradient, which Hölder's
inequality controls by $`\|Du\|_{L^p}` times a power of the radius. This is
where the exponent $`1-n/p` and the dimension-dependent constant come from.

:::theorem "sobolev.morrey_multidimensional" (parent := "sobolev.inequalities") (lean := "SobolevSpace.enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_ballPotential, SobolevSpace.enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_potentialBound, SobolevSpace.enorm_sub_le_eLpNorm_fderiv_mul_rpow, SobolevSpace.norm_sub_le_eLpNorm_fderiv_toReal_mul_rpow") (uses := "sobolev.morrey_exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`1\leq n<p<\infty` and a global $`C^1` real-valued function,

$$`
|u(y)-u(x)|
\leq C(n,p)\,\|Du\|_{L^p(\mathbb R^n)}
  |y-x|^{1-n/p}.
`

The principal linked theorem is unconditional: it derives a Riesz-potential
estimate from a point value to a ball average by integration along line
segments in polar coordinates and then applies Hölder's inequality and the
exact radial kernel integral. It is stated with extended norms, so it needs
neither compact support nor a separate finiteness hypothesis. Its explicit
constant includes enlarged-ball factors.

Two conditional factorized versions are also proved, useful when a
different point-to-average estimate or kernel estimate is available. The
finite real-valued corollary uses compact support only to prove finiteness of
the global derivative seminorm.
:::

:::proof "sobolev.morrey_multidimensional"
Compare each endpoint with the average of $`u` on a ball of radius
$`R=\lVert y-x\rVert`. Line-segment integration in polar coordinates bounds
each point-to-average difference by the gradient paired with the radial
kernel $`\lVert z-a\rVert^{1-n}` on an enlarged ball. Hölder's inequality
separates the $`L^p` gradient norm from the conjugate-power kernel integral.
The exact polar-coordinate evaluation of that integral contributes
$`R^{1-n/p}`. The triangle inequality combines the estimates at $`x` and
$`y`.
:::

The pointwise estimate controls the Hölder seminorm of a $`C^1` function but
not its supremum. For compactly supported functions boundedness is
automatic, so these functions define elements of the Hölder space
$`C^{0,1-n/p}(\mathbb R^n)`, and the completed embedding is built from them.

:::definition "sobolev.morrey_holder_bundle" (parent := "sobolev.inequalities") (lean := "SobolevSpace.compactSupportToMorreyHolder") (uses := "sobolev.morrey_multidimensional, sobolev.holder.c0gamma") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`0<n<p<\infty`, every compactly supported global $`C^1` function
defines an element of $`C^{0,1-n/p}(\mathbb R^n)`.

`finiteMorreyHolderExponent` carries the inequalities
$`0<1-n/p\leq1`, while `finiteMorreyHolderConstant` is the explicit finite
constant obtained from the multidimensional Morrey theorem. Compact support
is not needed for the extended pointwise oscillation estimate; it is used
here to obtain a bounded continuous function and to prove the coefficient
finite.
:::

Extending this map from compactly supported smooth functions to all of
$`W^{1,p}(\mathbb R^n)` requires a bound on the full Hölder norm, supremum
included, by the Sobolev graph norm; with that bound, density produces the
bounded operator.

:::theorem "sobolev.morrey_embedding_global" (parent := "sobolev.inequalities") (lean := "SobolevSpace.finiteMorreyEmbedding_ae, SobolevSpace.finiteMorreyEmbeddingConstant, SobolevSpace.norm_compactSupportToMorreyHolder_le_embeddingConstant, SobolevSpace.finiteMorreyEmbedding, SobolevSpace.norm_morreyHolderRepresentative_le") (uses := "sobolev.morrey_holder_bundle, sobolev.graph_space, sobolev.global_density") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`0<n<p<\infty`. There is a bounded linear map

$$`
W^{1,p}(\mathbb R^n)\longrightarrow C^{0,1-n/p}(\mathbb R^n)
`

whose value agrees almost everywhere with the Sobolev base coordinate.
Its operator norm has an explicit bound in the finite-coordinate Sobolev
norm. This is the completed-space version of Morrey's
inequality (Evans, 2010, §5.6.2, Theorems 4 and 5), a bounded operator between
Banach spaces.

The full target norm is the sum of the uniform norm and the Hölder seminorm.
Accordingly, the explicit constant has two analytic sources: the base
$`L^p` coordinate controls one value on each unit ball, while the first
derivative coordinates control oscillation. The construction takes a real
Hölder-conjugate exponent $`q` together with the proof
`p.HolderConjugate q`; hence this operator is the finite-$`p` branch.
:::

:::proof "sobolev.morrey_embedding_global"
Approximate a Sobolev element by compactly supported smooth functions. The
smooth Morrey estimate makes their Hölder representatives Cauchy in the
$`C^{0,1-n/p}` norm, so completeness gives a Hölder limit, which is also their pointwise limit. A
subsequence converges almost everywhere to the base coordinate, so the two agree. Continuous
representatives that agree almost everywhere are equal, which proves
additivity and homogeneity; the uniform smooth estimate then makes the map
continuous.
:::

To see the embedding at work, consider a concrete function
$`u\in W^{1,5}(\mathbb R^3)`. The Morrey exponent is

$$`
\gamma(3,5)=1-\frac np=1-\frac35=\frac25,
`

so the smooth estimate reads
$`|u(y)-u(x)|\leq C(3,5)\lVert Du\rVert_{L^5}|y-x|^{2/5}`. The density argument
therefore selects a representative of $`u` in
$`C^{0,2/5}(\mathbb R^3)`, and the global embedding sends $`u` to precisely
that representative. Concretely, if $`\lVert Du\rVert_{L^5}=1`, then the
oscillation of $`u` on any ball of radius $`r` is at most $`C(3,5)(2r)^{2/5}`.
A function in $`W^{1,3+\epsilon}(\mathbb R^3)` with $`\epsilon>0` is therefore
Hölder continuous with exponent $`\epsilon/(3+\epsilon)`. At the critical
exponent, membership in $`W^{1,3}(\mathbb R^3)` alone does not imply
continuity.

The domain version uses an extension operator to obtain one Hölder
representative with a uniform estimate up to the boundary. Interior cutoff
arguments control compactly contained subsets, but by themselves do not
compare pairs of points whose connecting geometry approaches or crosses the
boundary. The operational $`C^1` extension atlas provides the geometric data
needed to carry out extension, embedding, and restriction as one composed
bounded operator (Evans, 2010, §5.6.2, Theorem 5;
{Informal.citet "adams-fournier-2003"}[], Theorem 4.12, Part II).

:::theorem "sobolev.morrey_embedding_domain" (parent := "sobolev.inequalities") (lean := "SobolevSpace.finiteMorreyEmbeddingOn_ae, SobolevSpace.finiteMorreyEmbeddingOn, SobolevSpace.norm_finiteMorreyEmbeddingOn_le") (uses := "sobolev.morrey_embedding_global, sobolev.c1_extension") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-284"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` carry the operational bounded $`C^1`
extension atlas and let $`0<n<p<\infty`. Extension, the global Morrey map, and
restriction define a bounded linear map

$$`
W^{1,p}(\Omega)\longrightarrow C^{0,1-n/p}(\Omega).
`

Its output agrees almost everywhere on $`\Omega` with the original Sobolev
base coordinate. The quantitative theorem is

$$`
\|\mathcal M_\Omega U\|_{C^{0,1-n/p}}
\leq C_{\mathrm{Morrey}}(n,p,q)\,
  \|E_\Omega\|\,\|U\|_{W^{1,p}(\Omega)}.
`

Restriction has operator norm at most one, so the only domain-dependent
factor is the norm of the selected $`C^1` extension operator.
:::

:::proof "sobolev.morrey_embedding_domain"
Apply the bounded $`C^1` extension operator, use the global Morrey embedding,
and restrict the resulting Hölder function to $`\Omega`. Restriction does not
increase the Hölder norm. The extension's almost-everywhere agreement on the
domain, composed with the global representative theorem, identifies the
restricted function with the original Sobolev base coordinate.
:::

The higher-order Morrey embedding supplies continuous derivative
representatives needed to interpret a weak solution classically. This is the
bridge between the variational world (where solutions are energy classes) and
the pointwise world (where maximum principles and classical uniqueness
operate). For $`p>n` it is the corresponding case of Evans's general Sobolev
inequality (2010, §5.6.3, Theorem 6(ii)), whose proof applies the
first-order estimate to the weak derivatives.

The derivative order still matters. For Poisson's equation, continuity of
$`u` alone does not make $`\Delta u` a classical expression. If a separate
regularity estimate gives $`u\in W^{3,p}` with finite $`p>n`, the
higher-order embedding and derivative reconstruction give a $`C^2`
representative in the interior. If $`f` is continuous and
$`-\Delta u=f` holds distributionally, the continuous residual
$`-\Delta u-f` has zero pairing with every test function, hence vanishes
at every interior point. This last argument is the passage from the weak
equation to the classical one; an embedding by itself does not prove that
equation.

:::theorem "sobolev.morrey_embedding_higher_order" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.finiteMorreyDerivativeEmbedding_ae, SobolevSpace.GraphSpace.finiteMorreyDerivativeEmbedding, SobolevSpace.GraphSpace.finiteMorreyDerivativeEmbeddingOn, SobolevSpace.GraphSpace.finiteMorreyDerivativeRepresentativeOn_ae, SobolevSpace.GraphSpace.norm_finiteMorreyDerivativeEmbeddingOn_le") (uses := "sobolev.morrey_embedding_domain, sobolev.graph_space") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`0<n<p<\infty` and let $`\Omega` carry the operational bounded $`C^1`
extension atlas. For every derivative word $`\alpha` with
$`|\alpha|+1\leq m`, there is a bounded linear map

$$`
W^{m,p}(\Omega)\longrightarrow C^{0,1-n/p}(\Omega)
`

whose value represents $`D^\alpha u` almost everywhere.
There is also a global derivative-word operator on $`\mathbb R^n`. Each
coordinate has an explicit norm estimate, the product of the
first-order Morrey constant, the extension norm in the domain case, and the
first-order Sobolev norm of the extracted derivative-word slice of the input.
:::

:::proof "sobolev.morrey_embedding_higher_order"
For each derivative word $`\alpha`, the derivative-slice map sends
$`W^{m,p}` continuously into $`W^{1,p}` whenever
$`|\alpha|+1\leq m`. Compose that map with the first-order domain Morrey
embedding. Almost-everywhere agreement of derivative slices identifies the
result with $`D^\alpha u`.
:::

:::theorem "sobolev.morrey_jet_embedding" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.finiteMorreyJetEmbeddingOn_coordinate_ae, SobolevSpace.GraphSpace.finiteMorreyJetEmbeddingOn") (uses := "sobolev.morrey_embedding_higher_order") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Keep the same exponent and extension-atlas assumptions. For
$`u\in W^{k+1,p}(\Omega)`, these maps form one bounded linear map into a finite Hölder product.
Each coordinate agrees almost everywhere on $`\Omega` with its weak derivative.
:::

:::proof "sobolev.morrey_jet_embedding"
Collecting the finitely many derivative indices of order at most $`k` produces
a continuous linear map into the completed finite-product Hölder jet.
The coordinate agreement follows from the derivative representative's
almost-everywhere agreement theorem.
:::

Each coordinate of the Hölder jet is a continuous representative of one weak
derivative, but so far the jet is only a family of functions. The continuous
weak-derivative bridge turns it into classical calculus: when consecutive
representatives are continuous and satisfy the weak-derivative relation, the
longer word is the ordinary derivative of the shorter one. Openness of
$`\Omega` is used in this interior step, since differentiation at a point
needs a neighbourhood inside $`\Omega`.

:::theorem "sobolev.morrey_weak_to_classical" (parent := "sobolev.inequalities") (lean := "SobolevSpace.GraphSpace.finiteMorreyDerivativeRepresentativeOn_hasWeakDerivativeOn, SobolevSpace.GraphSpace.finiteMorreyDerivativeRepresentativeOn_hasFDerivAt, SobolevSpace.GraphSpace.finiteMorreyDerivativeRepresentativeOn_contDiffOn") (uses := "sobolev.morrey_embedding_higher_order, sobolev.continuous_weak_derivatives_are_classical") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "284-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The domain $`\Omega` is open, since openness is part of the atlas. Adjacent
Hölder representatives in the Morrey jet satisfy the weak-derivative
relation. If $`|\alpha|+2\leq m`, those adjacent representatives assemble
pointwise into the ordinary Fréchet derivative of the representative of
$`D^\alpha u`.

More generally, if

$$`
|\alpha|+r+1\leq m,
`

then the representative of $`D^\alpha u` is `ContDiffOn` of order $`r` on
$`\Omega`. In particular, for $`u\in W^{k+1,p}(\Omega)` with $`p>n`, the
selected representative of $`u` is classically $`C^k` in the interior, and
its classical derivatives are the adjacent Morrey representatives.
:::

:::proof "sobolev.morrey_weak_to_classical"
Almost-everywhere agreement transfers the graph-space weak-derivative
certificate to each adjacent pair of continuous Morrey representatives. The
general weak-to-classical bridge localizes near an interior point with a
compactly supported cutoff, mollifies the function and its continuous weak
gradient, and applies the locally uniform limit theorem for Fréchet
derivatives. This identifies the first classical derivative. Induction on
$`r`, together with the corresponding statement for every appended
coordinate direction, yields the `ContDiffOn` theorem.
:::

Differentiability at boundary points cannot come from the interior argument,
because a neighbourhood of a boundary point leaves $`\Omega`. The atlas
charts supply the missing structure: in a boundary chart the domain becomes
a convex upper half-ball, and continuity of the representative and of its
derivative field extend the derivative to the closure, in the sense of
derivatives within the closed set.

:::theorem "sobolev.morrey_weak_to_classical_closure" (parent := "sobolev.inequalities") (lean := "SobolevSpace.Boundary.Regularity.hasFDerivWithinAt_closure_of_continuous_derivative, SobolevSpace.GraphSpace.finiteMorreyDerivativeRepresentativeOn_hasFDerivWithinAt_closure, SobolevSpace.GraphSpace.finiteMorreyDerivativeRepresentativeOn_contDiffOn_closure") (uses := "sobolev.morrey_weak_to_classical, sobolev.extension.atlas") (autoDeps := true)
Let $`\Omega` carry the operational $`C^1` extension atlas. If
$`u\in W^{k+1,p}(\Omega)` with $`0<n<p<\infty`, then its selected Morrey
representative is classically $`C^k` within $`\overline\Omega`. More
generally, for $`u\in W^{m,p}(\Omega)` and a derivative word $`\alpha`
with $`|\alpha|+r+1\leq m`, the representative of $`D^\alpha u` is
`ContDiffOn` of order $`r` on the closure.

The derivatives are taken within the closed set $`\overline\Omega`; the
theorem concerns the closure, not an open neighbourhood of it.
:::

:::proof "sobolev.morrey_weak_to_classical_closure"
At an interior point, use the ordinary weak-to-classical theorem. At a
boundary point, flatten the domain with an operational chart. The chart image
is locally a convex upper half-ball. Continuity of the Morrey representative
and its derivative field, together with Mathlib's derivative-extension
theorem, identifies the limiting derivative on the closed half-ball.
Transport this derivative back by composing with the chart and induct on the
requested differentiability order.
:::

The one-dimensional critical endpoint deserves separate treatment because the
Morrey argument degenerates when $`p=n=1`: the exponent $`1-n/p` becomes zero,
and PDEAtlas's `HolderSpace.Exponent` requires a strictly
positive exponent. A formal exponent-zero oscillation bound would not by
itself imply continuity. The bounded continuous conclusion instead comes
from the one-dimensional weak fundamental theorem: compactly supported smooth $`W^{1,1}`
functions are uniformly bounded by the derivative's norm, and density extends this. The result is
a bounded linear map from the completed Sobolev space to
$`C^0_b`. There is no higher-dimensional analogue at the critical exponent:
a function in $`W^{1,n}(\mathbb R^n)` for $`n\geq2` need not be bounded
({Informal.citet "brezis-2011"}[], Remark 9.4).

:::theorem "sobolev.critical_one_dimensional_global" (parent := "sobolev.inequalities") (lean := "SobolevSpace.CriticalOneDimensional.criticalEmbedding_ae, SobolevSpace.CriticalOneDimensional.criticalEmbedding, SobolevSpace.CriticalOneDimensional.norm_boundedContinuousRepresentative_le") (uses := "sobolev.global_density, sobolev.graph_space") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
At the one-dimensional critical endpoint there is a bounded linear
contraction

$$`
W^{1,1}(\mathbb R)\longrightarrow C^0_b(\mathbb R).
`

Its value agrees almost everywhere with the Sobolev base coordinate. The
core estimate is $`\|u\|_\infty\leq\|u'\|_{L^1}` for compactly supported
smooth functions. Since the derivative coordinate is bounded by PDEAtlas's
finite `PiLp` graph norm, the completed operator has norm at most one.
:::

:::proof "sobolev.critical_one_dimensional_global"
For a compactly supported smooth function, integrate the derivative from a
point outside the support to obtain
$`\lVert u\rVert_\infty\leq\lVert u'\rVert_{L^1}`. Smooth density and this
uniform estimate produce a bounded continuous representative for every
$`W^{1,1}` element. Almost-everywhere agreement identifies it with the base
coordinate, and uniqueness of continuous almost-everywhere representatives
proves linearity. The same estimate makes the resulting map a contraction.
:::

:::theorem "sobolev.critical_one_dimensional_domain" (parent := "sobolev.inequalities") (lean := "SobolevSpace.CriticalOneDimensional.criticalEmbeddingOn_ae, SobolevSpace.CriticalOneDimensional.criticalEmbeddingOn, SobolevSpace.CriticalOneDimensional.norm_criticalEmbeddingOn_le") (uses := "sobolev.critical_one_dimensional_global, sobolev.c1_extension") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "280-286"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`\Omega\subseteq\mathbb R` carries the operational $`C^1` extension
atlas, extension followed by the global critical embedding and restriction
gives a bounded linear map

$$`
W^{1,1}(\Omega)\longrightarrow C^0_b(\Omega).
`

The output agrees almost everywhere with the original Sobolev base
coordinate, and

$$`
\|\mathcal C_\Omega U\|_\infty
\leq \|E_\Omega\|\,\|U\|_{W^{1,1}(\Omega)}.
`
:::

:::proof "sobolev.critical_one_dimensional_domain"
Extend the domain element to a global $`W^{1,1}` function, apply the global
critical embedding, and restrict the bounded continuous representative to
$`\Omega`. The global representative theorem and the extension agreement
combine to give almost-everywhere agreement with the original base
coordinate; restriction, the global contraction and the extension norm give the bound.
:::
