/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Fourier
import Blueprint.Chapters.Sobolev.Holder
import Blueprint.Chapters.Sobolev.WeakCalculus

/-!
# Sobolev theory scope

How the Sobolev theorem families fit together and where
their present hypotheses lead.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Sobolev Coverage and Open Problems" =>

:::group "sobolev.chapter_guide"
Sobolev theory
:::

# The two Sobolev models

PDEAtlas uses two complementary analytic models.

## Weak-derivative graph spaces

The graph-space model stores a finite family of $`L^p` classes indexed by
symmetric multi-indices, including the base coordinate. Compatibility is
expressed by the distributional integration-by-parts identity. The completed bundle stores
the base coordinate and every weak derivative through order $`k`.

This model is the one used for:

* local and domain Sobolev spaces $`W^{k,p}(\Omega)`;
* weak formulations and energy estimates;
* extension and trace;
* difference quotients and Rellich compactness;
* Nemytskii operations, multiplier rules, and coordinate changes;
* zero-boundary closures such as $`H^1_0` and $`W^{k,2}_0`.

Weak-derivative identities are stated using ordered lists of coordinate
directions, because iterated distributional derivatives compose in a
specified order.  The completed graph-space bundle is instead indexed by
symmetric multi-indices: derivative words that differ only by a permutation
share one coordinate.  A chosen list representative connects each symmetric
index to the ordered weak-derivative calculus, and permutation invariance
shows that the resulting weak derivative is independent of that choice.

For finite $`p`, the finite `PiLp` graph norm combines the $`L^p` coordinate
norms in the expected $`\ell^p` manner.  At $`p=\infty`, it takes their
maximum.  This is equivalent to the finite sum norm often written in analysis
texts, but every quantitative PDEAtlas estimate is stated for the actual
`PiLp` norm.

## Fourier Bessel-potential spaces

The Fourier model is a whole-space Hilbert scale
$`H^s(\mathbb R^n)` for every real order $`s`.  Its elements are tempered
distributions whose Fourier transforms become square integrable after
multiplication by

$$`
J_s(\xi)=(1+\|\xi\|^2)^{s/2}.
`

This model is the one used for:

* fractional and negative regularity;
* a Hilbert space at every real order;
* exact scale inclusions and Bessel-potential shifts;
* distributional weak derivatives at arbitrary real order;
* the comparison with integer-order $`W^{k,2}(\mathbb R^n)`.

The two models are not definitionally the same.  At every natural order $`k`,
the real physical subspace of $`H^k` is continuously real-linearly equivalent
to the integer graph space $`W^{k,2}(\mathbb R^n)`.  The equivalence has
explicit bounds in both directions. The norms differ, because Mathlib's
Fourier transform has derivative multiplier
$`2\pi i\xi_j` while PDEAtlas uses the unscaled Bessel symbol $`J_s`.

# Weak derivatives, completeness, and approximation

Weak derivatives are defined by the distributional identity

$$`
\int_\Omega u\,\partial_i\varphi
=-\int_\Omega v\,\varphi
`

for every compactly supported smooth test function.  On open domains the weak
derivative is unique almost everywhere.  The graph-space compatibility
conditions are closed under limits, which makes the bundled graph space
complete and supports bounded-operator arguments.

The weak-derivative relation also accepts values in any real Banach space.
The test function remains real-valued, and the integrals are Bochner integrals.
On every open Euclidean domain, the derivative is unique almost everywhere
and its graph in $`L^p\times L^p` is closed for every
$`1\leq p\leq\infty`. The scalar relation is recovered exactly when the
codomain is $`\mathbb R`.

This closed graph also gives the complete space $`W^{k,p}(\Omega;F)` for
every natural order $`k`, every open Euclidean domain, and every real Banach
space $`F`, including infinite-dimensional codomains. At $`F=\mathbb R`,
the scalar identification preserves every derivative coordinate and the
graph norm exactly. A continuous linear map $`F\to G` acts on these spaces
by composition and commutes with their weak derivatives.

For $`1\leq p<\infty`, smooth functions are dense in this graph norm.
On the whole space, we convolve with a scalar mollifier and prove that each
weak derivative passes through the convolution. On an arbitrary open set,
we first localize with a smooth partition and mollify each piece inside the
domain. The locally finite sum gives a smooth approximation without imposing
regularity on the boundary. The argument works for any real Banach codomain;
it does not require finite dimension.

For scalar-valued functions, the approximation layer has several distinct scopes.

* On the whole space and at finite exponent, convolution with standard
  mollifiers gives smooth approximation in the Sobolev graph norm.
* On a domain, zero extension followed by convolution gives an interior
  approximation.  It is not automatically a global approximation up to the
  boundary.
* On any open domain, a locally finite partition and interior mollification
  prove smooth density in the full $`W^{k,p}` norm for $`1\leq p<\infty`.
  The approximating functions are smooth on the domain; they need not extend
  smoothly across its boundary.
* A representative-level extension hypothesis transfers whole-space
  approximation back to a domain.
* An operational first-order extension operator gives density for the
  corresponding completed domain graph space.
* The zero-boundary spaces are defined as closures of the compactly supported
  smooth core, so density is part of their construction.

Norm density at $`p=\infty` is false in general, and density up to the
boundary requires the appropriate extension or zero-boundary hypothesis.

# Operational domain geometry

First-order extension, trace, chart localization, Morrey transport, and
Rellich compactness use the same
{bpref "sobolev.extension.atlas"}[finite extension atlas].
It supplies the boundary cover, charts, flattening maps,
cutoffs, Jacobian bounds, derivative bounds, and overlap data consumed by the
analytic proofs.

For a bounded open set with local $`C^1` graph boundary, the geometric
construction supplies this atlas: local graph flattening gives the charts,
compactness gives a finite cover, and a smooth partition assembles their
cutoffs. We keep the atlas in the analytic interface so that successive
theorems can use the same charts and refer to their quantitative bounds.

Concrete instances include:

* the interval $`(-1,1)\subset\mathbb R`, by affine endpoint charts;
* every positive-dimensional Euclidean unit ball, by signed caps and explicit
  graph flattening;
* a $`C^2` atlas for the unit ball, which supplies the inherited $`C^1`
  extension atlas needed by first-order theory.

A supplied extension of any order can also be multiplied by a smooth cutoff
to obtain support in any prescribed open neighborhood of $`\overline\Omega`,
which gives a new bounded extension of the same order.

# Extension: present level of generality

The extension results answer three increasingly quantitative questions.

1. A {bpref "sobolev.representative_extension"}[representative extension]
   extends a measurable function and its weak derivatives, with almost-everywhere
   agreement on the original domain.
2. A {bpref "sobolev.extension_operator"}[bounded extension operator]
   makes this choice linear and controls its norm on the completed spaces.
3. A {bpref "sobolev.supported_extension_operator"}[supported extension operator]
   also makes the extended function vanish almost everywhere outside a chosen
   ambient set, as needed for compactness arguments.

Bridges convert an operator-level extension into the representative data
needed by mollification. The $`C^1` construction supplies a first-order
extension for every $`1\leq p\leq\infty`, together with a variant of prescribed
support.

For every positive integer $`k` and $`1\leq p\leq\infty`, a bounded open domain
with local $`C^k` graph boundary also has a bounded linear
$`W^{k,p}` extension. The proof flattens the boundary, applies weighted
reflection, and assembles the pieces with a partition of unity. Its action
on the base function agrees with a bounded operator on all of $`L^p(\Omega)`;
restriction recovers every weak derivative. This compatibility lets an
evolution argument use the same extension for a trajectory and a less regular
time derivative. At $`p=\infty`, preservation of null sets controls chart
pullback in the essential-supremum norm. The weak chain rule is obtained
locally at finite exponent, so this construction does not require the false
claim that smooth functions are norm-dense in $`W^{k,\infty}`.

# Trace: flat, curved, Hilbert, and finite exponent

Trace is never pointwise evaluation of an arbitrary $`L^p` representative.
The construction starts on a smooth core, proves an estimate, and extends by
density to the completed graph space.

The completed trace theory contains:

* endpoint evaluation on the positive half-line;
* the flat upper-half-space trace;
* a chart-assembled trace on every operational $`C^1` domain, independent of
  the atlas and characterized by literal restriction on functions continuous
  up to the boundary;
* the same trace for Banach-valued functions, commuting with bounded linear
  maps of the target and reducing to the scalar trace for real values;
* convergence of strip averages $`\varepsilon^{-1}\int_0^\varepsilon u(y,t)\,dt`
  to the flat trace for $`p>1`, with an explicit rate;
* a Hilbert trace quotient and its canonical minimal-energy extension;
* identification of the half-space Hilbert trace quotient with real
  $`H^{1/2}(\mathbb R^n)`, with a bounded lifting;
* on operational $`C^1` domains, identification of the Hilbert trace quotient
  with chartwise $`H^{1/2}` boundary data, a bounded lifting, and
  equivalence of the chartwise spaces of two atlases;
* a finite-exponent trace for every real $`p\geq1`;
* finite-exponent Banach trace quotients realizing the exact algebraic ranges;
* for $`1<p<\infty`, the half-space trace into the Gagliardo space
  $`W^{1-1/p,p}(\mathbb R^n)`, a bounded mollified lifting, and the
  identification of the trace quotient with that space, for scalar and
  Banach-valued functions;
* canonical operator, kernel, and quotient-space compatibility at $`p=2`;
* agreement with literal restriction on the ambient smooth core;
* the characterization of $`W^{1,p}_0` as the trace kernel on the half-space
  and on $`C^1` domains, for every finite $`p\geq1`, for scalar and
  Banach-valued functions;
* higher-order zero-boundary closures $`W^{k,2}_0`;
* first-order slices of lower derivative coordinates into $`H^1_0`.

In the Hilbert case, quotienting by the trace kernel gives an abstract boundary
Hilbert space.  Orthogonal projection onto the kernel complement supplies a
canonical norm-preserving minimal extension. On the half-space this
quotient is real $`H^{1/2}(\mathbb R^n)`. A Fourier estimate
constructs the trace and an explicit bounded lifting; agreement on smooth
functions and density show that its physical $`L^2` value is the existing
boundary trace. The two maps identify the quotient and fractional norms up
to proved bounds in both directions. On an operational $`C^1` domain the
same quotient is identified with boundary data whose localized chart
coordinates lie in $`H^{1/2}(\mathbb R^m)`, again with a bounded lifting and
two-sided norm bounds, and the chartwise spaces of two atlases are
equivalent.

The flat Fourier construction also works at every real order $`s>1/2`:
restriction to a hyperplane extends to a continuous map
$`H^s(\mathbb R^{n+1})\to H^{s-1/2}(\mathbb R^n)` with a bounded right inverse.
The half derivative is lost when we integrate out the normal frequency.
A weighted Cauchy–Schwarz estimate controls this integral, and its weight
gives an explicit lifting. Agreement with literal restriction on Schwartz
functions connects the Fourier operator to boundary values.

At finite exponent, quotienting by the trace kernel gives a canonical Banach
trace space. Its boundary-value map is continuous and injective, its image is
exactly the operator range, and the quotient is linearly equivalent to that
algebraic range. At $`p=2`, canonical exponent transport identifies this
operator, its kernel, and its quotient trace space with the Hilbert
construction, both on the half-space and on operational $`C^1` domains.
On the half-space and for $`1<p<\infty`, the trace satisfies the
Gagliardo condition of order $`1-1/p`: splitting a boundary difference
through points at height $`|x-y|` and applying Hardy's inequality in the
normal direction bounds its fractional energy. Mollifying the boundary data
at scale $`t` and cutting off in $`t` gives a bounded right inverse, so the
trace quotient is the Gagliardo space $`W^{1-1/p,p}(\mathbb R^n)` with
equivalent norms. Both arguments use only the norm of the target and hold
for Banach-valued functions. On operational $`C^1` domains and for
$`1<p<\infty` the range of the trace is characterized chartwise: a boundary
function is a trace exactly when each localized chart coordinate lies in the
Gagliardo space of order $`1-1/p`, and a bounded lifting recovers it from
those coordinates.

Weighted Hilbert graph spaces are defined by completing the weighted row
norm, which is complete for any nonnegative densities. Positivity of the
zeroth weight, lower bounds, and two-sided bounds give successively stronger
identifications with function spaces, and upper bounds give smooth density
on $`\mathbb R^n`. A weighted reflection bound and the Hölder step of
weighted interpolation are proved.

# Sobolev, Morrey, Poincaré, and Hardy

Sobolev embeddings depend on the exponent, derivative order, and domain geometry.

## Integrability

For $`1\leq p<n`, the first-order whole-space theorem reaches
$`p^*=np/(n-p)`.  Higher-order subcritical results iterate the first-order
step while $`kp<n`. On a bounded operational $`C^1` domain this gives a
bounded linear inclusion

$$`
W^{k+j,p}(\Omega)\longrightarrow W^{k,np/(n-jp)}(\Omega),
\qquad jp<n.
`

The map preserves every retained weak derivative. Its norm is bounded by
a product of first-order GNS constants, extension norms, and the finite
coordinate counts in the graph norm. Only first-order extension is used,
even when several derivatives are consumed.

At the critical exponent, a bounded operational $`C^1` domain admits the
bounded linear inclusion

$$`
W^{k+j,p}(\Omega)\longrightarrow W^{k,q}(\Omega),
\qquad jp=n,\quad j>0,\quad 1\leq q<\infty.
`

Every retained derivative agrees almost everywhere with the source. The
operator estimate combines the subcritical steps with a final critical
first-order estimate, and its constant depends on $`q`. This does not give
an $`L^\infty` embedding in dimensions greater than one.

## Pointwise regularity

For finite $`p>n`, Morrey gives a bounded linear map into the completed
$`C^{0,1-n/p}` space, globally and on operational domains.  Its output is a
specific bounded continuous representative with an almost-everywhere
agreement theorem.

Applying the first-order map to every admissible derivative slice produces a
completed Hölder jet. On an open domain, adjacent coordinates of the jet are
classical derivatives, and the selected base representative is `ContDiffOn`
of the expected order in the interior. On an operational $`C^1` domain, the
{bpref "sobolev.morrey_weak_to_classical_closure"}[boundary-relative theorem]
also gives `ContDiffOn` on $`\overline\Omega`, with derivatives taken within
the closed set.

The higher-order estimates also bound the full compatible Hölder
representative. For finite $`p` with $`n/p<K`, put
$`m=K-\lfloor n/p\rfloor-1`. If $`n/p` is not an integer, the target is
$`C^{m,\gamma}(\overline\Omega)` with
$`\gamma=\lfloor n/p\rfloor+1-n/p`; at an integer value, every
$`0<\gamma<1` is available. The bounds use the same extension, GNS, and
Morrey estimates as the first-order theory. A finite multi-index count
converts them to Evans's sum norm. For $`p=\infty`, finite-volume exponent
restriction gives the corresponding strict Hölder bounds. At this endpoint
there is also a bounded linear injection

$$`
W^{k+1,\infty}(\Omega)\longrightarrow C^{k,1}(\overline\Omega)
`

for every $`k\geq0` on a bounded open $`C^1` graph domain in positive
dimension. All retained derivatives agree almost everywhere with the source
weak derivatives. If $`E_{1,\infty}` is the first-order extension operator
of the chosen atlas, the graph-norm bound is
$`(n+1)\|E_{1,\infty}\|`. The Lipschitz estimate holds for every pair of
points in the closure, including points in different components.

The critical one-dimensional endpoint is separate:

$$`
W^{1,1}(\mathbb R)\longrightarrow C^0_b(\mathbb R)
`

is a continuous linear contraction, with a corresponding domain operator
obtained by extension and restriction.

## Coercivity and singular weights

On every bounded set in positive dimension, Poincaré controls the full
$`W^{1,p}_0` graph norm by the weak-gradient norm for every finite $`p\geq1`.
Here the zero-boundary space is the closure of the compactly supported smooth
core; no boundary regularity or extension operator is required. The $`p=2`
case supplies the coercivity estimate used by Dirichlet energy methods.

For every real $`p>1`, Hardy's classical constant
$`(p/(p-1))^p` is proved on finite intervals and on the smooth positive
half-line core.  Division by the boundary coordinate is completed as a
bounded operator on $`W^{1,p}_0` for the positive half-line and the flat
upper half-space. On a bounded operational $`C^1` domain, the same passage
from the smooth core constructs a bounded linear map
$`u\mapsto u/\operatorname{dist}(x,\partial\Omega)` on $`W^{1,p}_0`.
Its output agrees almost everywhere with the literal quotient. Combining
the chart estimate with Poincaré bounds its $`L^p` norm by the weak-gradient
norm; the resulting domain constant depends on the geometry.

The iterated quotient by $`r^j` is completed on
$`W^{j,2}_0(0,\infty)` with the exact odd-weight estimate.  This
higher-order branch is one-dimensional and Hilbertian.

# Difference quotients

For every finite exponent, the global forward theory is complete:

* the difference quotient is a bounded linear operator on the global
  $`L^p` model;
* Sobolev membership gives the standard quotient bound by the corresponding
  weak derivative;
* as the step tends to zero, difference quotients converge strongly to the
  weak derivative in $`L^p`;
* localization by a compactly supported cutoff transports the estimate to an
  interior region of a domain.

For $`1<p<\infty`, the converse recovers a weak gradient from uniformly
bounded local difference quotients, with the same bound. It holds on
arbitrary open domains. Reflexivity supplies a weakly convergent subsequence;
testing its limit against smooth compactly supported functions identifies
the derivative. The endpoint $`p=1` cannot be added to this statement:
bounded difference quotients can describe a function of bounded variation
with a jump.

# Rellich–Kondrachov compactness

On an operational bounded $`C^1` domain, the first-order embedding

$$`
W^{1,p}(\Omega)\longrightarrow L^q(\Omega)
`

is compact throughout the strict subcritical range formalized in the
compactness chapter, including the non-Hilbert endpoint
$`W^{1,1}(\Omega)\to L^1(\Omega)`.  The proof separates:

1. translation control from weak derivatives;
2. tightness from bounded support after extension and cutoff;
3. the Fréchet–Kolmogorov compactness criterion;
4. interpolation and finite-measure exponent changes;
5. restriction back to the original domain.

Compactness is proved in the strict range $`q<p^*`; at $`q=p^*` the embedding
is continuous but, classically, not compact.

The higher-order theory lowers derivative order coordinatewise and gives a
compact operator between graph spaces where the exponent and order
conditions are available.  Evolution compactness of Aubin–Lions type also
needs control of time derivatives and belongs to the parabolic theory.

# One-dimensional and coordinate-line calculus

Every global $`W^{1,1}(\mathbb R)` class has a selected representative that:

* is absolutely continuous on every compact interval;
* has classical derivative equal almost everywhere to the stored weak
  derivative;
* satisfies the literal fundamental theorem of calculus.

Absolute value, positive and negative parts, and interval truncation have the
expected almost-everywhere derivative formulas for this representative.  They
are also completed operations on $`W^{1,1}(\mathbb R)`, so later
proofs need not rebuild graph-space elements from raw representatives.

In higher dimensions, coordinate insertion and Fubini give absolutely
continuous representatives on almost every coordinate line.  The classical
line derivative agrees almost everywhere with the corresponding weak partial
derivative.  A two-way coordinate ACL characterization is available in the
finite-exponent setting used by the nonsmooth chain rule.

The line theorem is coordinatewise: absolute continuity holds on almost every
line parallel to a coordinate axis.

# Composition, truncation, and level sets

For every $`1\leq p\leq\infty`, a zero-preserving real Lipschitz map acts on
the global first-order Sobolev space with the expected weak chain rule.  The
proof treats the nonsmooth outer map through Rademacher differentiability,
the vanishing of weak gradients on level sets, and the ACL characterization.

The following are completed operations:

* absolute value;
* positive and negative parts;
* interval truncation containing zero on the whole space;
* arbitrary ordered interval truncation on bounded operational domains.

Their base coordinates and weak derivatives are identified almost everywhere.
In particular,

$$`
D(\min\{b,\max\{a,u\}\})
=\mathbf 1_{\{a<u<b\}}Du
`

almost everywhere. The
{bpref "sobolev.open_domain_lipschitz_chain_rule"}[local chain rule]
holds on every open domain for all $`1\leq p\leq\infty`, with no boundary
regularity assumption. A cutoff around each test function reduces it to
the whole-space calculation.

To obtain a global Sobolev element, the composed base function must also
belong to $`L^p`. A zero-preserving Lipschitz map always meets that condition.
On a finite-measure domain, every real Lipschitz map does, since its constant
offset is integrable.

Local Sobolev membership needs no such global integrability condition.
Every real Lipschitz map sends $`W^{1,p}_{\mathrm{loc}}(\Omega)` into itself,
including $`p=1` and $`p=\infty`. A compact neighborhood of each test
function supplies the finite measure needed for a nonzero constant offset.
The resulting weak chain rule holds on arbitrary open domains.

The nonsmooth composition theory is scalar-valued.

# Multipliers, slices, and coordinate changes

Derivative-word extraction is a bounded linear map from a higher-order graph
space to a lower-order slice.  This is the common interface used by
higher-order embeddings, traces of derivatives, regularity assembly, and
multiplier arguments.

The weak-calculus layer includes:

* smooth multiplication and Leibniz rules, including preservation of
  $`W^{k,p}_{\mathrm{loc}}` without global bounds on the smooth multiplier;
* $`W^{1,\infty}\times W^{1,2}` multiplication as a bounded bilinear map,
  with an explicit dimension-dependent operator-norm bound;
* $`W^{k,\infty}\times W^{k,2}` multiplication as a bounded bilinear map
  for every positive integer $`k`, with an explicit recursive
  dimension-and-order dependent bound;
* first-order pullback under controlled coordinate changes;
* higher-order pullback under bounded $`C^k` charts with $`C^1` inverses,
  for every positive integer $`k` and $`1\leq p\leq\infty`;
* rowwise norm estimates for transformed weak derivatives;
* assembly lemmas that recover a higher-order graph element from compatible
  derivative coordinates.

The first-order $`W^{1,\infty}` multiplier is both a fixed-coefficient
continuous linear endomorphism and a bounded bilinear map, with the constant
$`2\sqrt{\#\mathcal I_{n,1}}` for PDEAtlas's finite-product graph norms. At
every positive order $`k`, the $`W^{k,\infty}` multiplier is also a
fixed-coefficient
continuous linear endomorphism and a bounded bilinear map on $`W^{k,2}`.
Its recursive constant starts from the first-order bound and multiplies, at
each successor order, by
$`\sqrt{\#\mathcal I_{n,k+1}}(1+2n)`. This follows from contractive
derivative-word extraction, the two Leibniz summands in each coordinate, and
the quantitative successor-order assembly estimate.
The chosen product commutes with restriction to every positive lower
Sobolev order, agrees with the dedicated first-order multiplier at order
one, and exposes the expected first-derivative Leibniz coordinates almost
everywhere.
The second-order coordinate theorem retains explicit local estimates.
The higher-order construction instead proves boundedness through the closed
graph theorem after identifying the weak derivatives by induction.

# Fourier and fractional Sobolev theory

For every real $`s`, we use Mathlib's complex Hilbert space `H^{s}(ℝ^n)`
of tempered distributions. Three representatives are kept separate.

1. `toLp u` represents the Bessel potential
   $`(1-(2\pi)^{-2}\Delta)^{s/2}u`.
2. `𝓕 (toLp u)` is the Fourier transform of that $`L^2` representative.
3. For $`s\geq0`, `toL2Fun` is the physical $`L^2` representative of
   $`u` itself.

The third object need not exist at negative order.  This is why the carrier
remains a space of distributions rather than being forced into an $`L^2`
function model.

The whole-space theory contains:

* the exact norm identity through the weighted Fourier representative;
* the isometric equivalence between each $`H^s` and complex $`L^2`;
* scale inclusions $`H^t\to H^s` for $`s\leq t`;
* Bessel-potential shifts between arbitrary real orders;
* weak coordinate derivatives $`H^s\to H^{s-1}`;
* a single canonical real physical subspace `HsSpaceReal`, realized as a
  closed and complete kernel;
* Hermitian-symmetry characterizations of real-valuedness;
* a continuous real-linear equivalence
  $`H^k_{\mathbb R}\simeq W^{k,2}(\mathbb R^n)` for natural $`k`;
* explicit forward and reverse norm bounds for that integer bridge;
* for $`1\leq n` and $`0<s<1`, the whole-space Gagliardo seminorm identity
  with its named positive kernel constant, together with the corresponding
  Fourier-side finiteness criterion; and
* a continuous real-linear equivalence between the completed whole-space
  `GagliardoSpace` and $`H^s_{\mathbb R}`, preserving the physical
  $`L^2` function, with explicit norm bounds in both directions.

There is a single physical carrier. Characterization theorems relate
`HsSpaceReal` to `toL2Fun`, and the weak-derivative and integer-equivalence
results are all stated for this one space.

# Fractional spaces on domains

Three domain constructions describe different ways to control a function
near the boundary.

1. `HsRestrictionSpace` is the complete real Hilbert quotient of whole-space
   $`H^s` by the kernel of restriction into $`L^2(\Omega)`.  It is available
   at nonnegative order, carries the infimum-over-extensions quotient norm,
   and has a canonical least-norm whole-space extension.
   `hsRestrictionSubmodule` retains the corresponding raw-function membership
   interface.
2. `GagliardoSpace` is the complete real Hilbert graph space of the intrinsic
   difference quotient on $`\Omega\times\Omega`.
   `gagliardoSubmodule` retains the corresponding raw-function membership
   interface. Its intended Sobolev interpretation is $`0<s<1`.
3. `HsSupportedClosureSpace` is the closed complex subspace of whole-space
   $`H^s` generated by Schwartz functions supported in $`\Omega`.  It is
   complete for every real order, but its elements remain whole-space
   distributions.

For $`1\leq n` and $`0<s<1`, the completed whole-space Gagliardo model is
continuously linearly equivalent to $`H^s_{\mathbb R}`. The Fourier
seminorm identity supplies the norm comparison, and the equivalence preserves
the underlying $`L^2` function in both directions.

For any domain $`\Omega`, the same comparison identifies the quotient of
whole-space Gagliardo functions by the restriction kernel with
`HsRestrictionSpace`. Restricting a whole-space representative then gives a
bounded injective map into the intrinsic `GagliardoSpace` on $`\Omega`,
preserving the physical $`L^2` class. Its range is exactly the intrinsic
functions that admit a whole-space Gagliardo extension.

For a half-space, even reflection supplies the extension. It doubles the
squared $`L^2` norm and increases the squared fractional seminorm by at most
a factor of four, so its operator norm is at most $`2`. Combining reflection
with the whole-space Fourier comparison gives a continuous linear
equivalence between the intrinsic and restriction spaces, for every
$`n\geq 1` and $`0<s<1`. Both directions preserve the underlying
$`L^2` class.

On a domain with a $`C^1` extension atlas, in positive dimension and for
$`0<s<1`, the reflected chart extensions and the interior zero extension glue
into a bounded intrinsic extension operator. The same argument then makes
the canonical map from the restriction space to the intrinsic Gagliardo space
a continuous linear equivalence. Both
directions preserve the physical $`L^2(\Omega)` class, and the inverse norm
is bounded by the whole-space comparison factor times the norm of the atlas
extension.

# External-library boundary

The scalar theory uses Mathlib's `BesselPotentialSpace`, together with its
Fourier transform, Schwartz space, tempered distributions, $`L^p` spaces, and
continuous linear maps. Physlib's quantum-mechanical Sobolev submodule is
$`L^2`-based and narrower than the distribution-valued real-order scale used
here.

# Principal open interfaces

The main open directions are a Banach-space identification of the
finite-exponent trace quotient on curved boundaries with a chartwise
Gagliardo space, the identification of supported closures with an intrinsic
$`H^s_0(\Omega)`, and nonsmooth composition for Banach-valued Sobolev
functions.
