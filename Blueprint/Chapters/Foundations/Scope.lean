/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Foundations.BoundaryCalculus

/-!
# Foundations scope

Coverage of the foundational chapters: which topics are formalized,
inherited from Mathlib, or partial.
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
#doc (Manual) "Foundational Coverage and Open Problems" =>

# Coverage conventions

The entries distinguish three kinds of coverage. A topic
is *formalized* when PDEAtlas states and proves it, *inherited* when the
Blueprint cites the Mathlib declarations directly, without local restatements,
and *partial* when the reusable core is formalized in a stated range or
geometric setting; each partial entry names that range.

# Distribution theory

*Inherited:* test functions and distributions on open sets, regular
distributions, distributional derivatives, Schwartz space, tempered
distributions, the continuous Fourier equivalence and inversion laws, the
Fourier derivative rule, distributional support, closedness of support,
support monotonicity under differentiation, and the singleton support of Dirac
masses. Schwartz convolution, its continuity, and the Fourier convolution
theorem are inherited as well.

*Formalized:* the Heaviside identity $`D H=\delta_0`; continuous
constant-coefficient operators; and the generic fundamental-solution equation
$`P T=\delta_x` at an interior pole $`x\in\Omega`, with its test-function
characterization. For the ordinary regular distribution associated with
$`\Phi(x)=-|x|/2`, the exact equality $`-D^2T_\Phi=\delta_0` is proved.
Translation of tempered distributions is a continuous linear
equivalence with the expected action, composition, inverse, derivative, and
support-transport laws.
Convolution of a tempered distribution with a Schwartz function is a
continuous linear operation, has the expected Fourier characterization, and
agrees with ordinary convolution for regular Schwartz distributions.
Distributional differentiation commutes with this convolution. Pushforward
along continuous real-linear equivalences is functorial and obeys the expected
directional-derivative chain rule; it also maps distributional support to its
geometric image. Pushforward along continuous real-affine equivalences is
formalized as the composition of linear pushforward and translation, with
functoriality, inverse, directional-derivative, and exact support laws.
For ordinary distributions, every smooth proper map induces an LF-continuous
pullback of test functions and hence a continuous, functorial pushforward of
arbitrary real topological-module-valued distributions. Closed carriers
transport to closed image carriers under this pushforward, the resulting
distributional support lies in the image carrier, and compact carriers remain
compact. Every smooth scalar coefficient acts continuously on the LF
test-function space and, by compact-convergence transposition, on ordinary
distributions. The action formula, distributional Leibniz rule, support
monotonicity, and compact-carrier preservation are formalized. On a
finite-dimensional real normed source space, a compactly carried distribution
also admits pushforward along an arbitrary smooth map: a compact cutoff
localizes the test-function pullback, the resulting pushforward carries
support into the image carrier, and the final distribution is independent of
every cutoff equal to one near the carrier.
Finite real or complex linear combinations of iterated directional
derivatives are bundled as continuous constant-coefficient operators. On
ordinary and tempered distributions they preserve every vanishing region and
cannot enlarge support; on ordinary distributions they also preserve compact
carriers. Scalar test functions have external tensor products on product
spaces, with product-support control, continuous linear dependence on either
fixed factor in the LF topology, and the expected coordinate differentiation
laws. Product test functions restrict continuously and linearly to every fixed
coordinate fiber, with support controlled by the corresponding fiber of the
original support; coordinate differentiation commutes with slicing, and
slicing an external tensor product evaluates the fixed factor.
Every normed-space-valued distribution restricts continuously to each fixed
compact-support stage, where its norm is controlled by one finite-order
cumulative derivative seminorm. More generally, a continuous family whose
parameter derivative exists everywhere and is jointly continuous
differentiates over a compact fiber in the supremum-norm space of bounded
continuous functions, with the expected pointwise derivative. Applying a fixed
distribution to the moving fibers of a product test function on $`E\times F`,
with $`E` finite-dimensional, produces a smooth compactly supported test
function on $`E`, with support controlled by projection and coordinate
differentiation commuting with the construction. For fixed distribution,
this assignment is continuous linear between the canonical LF test-function
spaces. Transposing this map constructs scalar distribution tensor products
with finite-dimensional left coordinate space; for fixed right factor the
construction is continuous linear in the left distribution. The defining
action, factorization on elementary test-function tensors, tensor products of
Dirac masses, and both coordinate differentiation laws are formalized. Their
distributional support is contained in the product of the factor supports,
and products of compact carriers remain compact carriers. On every
finite-dimensional real normed space, two compactly carried scalar
distributions have a canonical convolution obtained by cutoff-localized
pushforward of their tensor product along addition. The construction is
independent of compact-carrier witnesses and normalized product-cutoff
choices, preserves compact carriers, has support in the corresponding
Minkowski sum, and sends
$`\delta_x*\delta_y` to $`\delta_{x+y}`; the Dirac mass at the origin is a
left identity. Arbitrary iterated directional derivatives and bundled finite
constant-coefficient differential operators commute with this convolution in
either factor. The algebraic identity $`P(G*T)=T` is proved for compactly
carried $`G` and $`T` with $`P G=\delta_0`.

# Vector calculus and domain geometry

*Formalized:* Euclidean gradient, divergence, and Laplacian; coordinate and
polar integration formulas; the general coordinate-box Gauss theorem; the
circulation (planar Stokes) and flux forms of Green's theorem on rectangles;
Green's first and second identities on coordinate boxes and
positive-radius Euclidean balls; and the sphere's outward normal derivative.
The boundary layer includes intrinsic codimension-one Hausdorff measure,
flat-boundary geometry, and chartwise surface-measure estimates for
operational $`C^1` domains. Every operational boundary chart supplies a
nonvanishing conormal and a chartwise outward unit normal with a proved
orientation law. On chart overlaps the conormals differ by a positive scalar,
so the normalized vectors define an intrinsic outward unit normal on the
entire boundary. The inverse charts restricted to the flat hyperplane give
injective $`C^1` parametrizations of the physical boundary pieces, with exact
image theorems and continuous, strictly positive tangential norm-determinant
Jacobians. Pushing their Jacobian-weighted parameter measures forward gives
physical chart measures, with a Banach-valued change-of-variables formula for
integrals. The transition maps between overlapping
boundary parametrizations are $`C^1` inverse bijections, their
Jacobian-weighted nonnegative integrals agree, and the resulting physical
chart measures coincide on overlaps. The $`C^1` area formula identifies each
chart measure with codimension-one Hausdorff measure on its chart, so the
assembled atlas measure is the intrinsic surface measure. On bounded open sets
with $`C^1` graph boundary, the divergence theorem and Green's first and second
identities hold for fields that are $`C^1` (respectively $`C^2`) up to the
boundary, with integrability of both sides as part of the conclusion.

*Partial:* the {bpref "sobolev.extension.atlas"}[extension atlas] supplies the
finite charts, cutoffs, flattening maps, and quantitative estimates required
by extension, trace, and compactness proofs. Concrete atlases exist for a
bounded interval and positive-dimensional Euclidean unit balls, and every
bounded open set with $`C^1` graph boundary carries one. Theorems on
Lipschitz domains take the atlas as a hypothesis.

# Sobolev foundations

*Formalized:* completed finite-exponent integer-order graph spaces,
mollification and density, first-order extension on operational $`C^1`
domains, finite-exponent trace operators, Hilbert quotient trace spaces and
their minimal-energy extensions on flat and operational $`C^1` domains,
canonical agreement of the finite-exponent and Hilbert trace theories at
$`p=2`, zero-boundary spaces, Poincaré, Hardy, Sobolev and Morrey inequalities, the
full strict subcritical Rellich–Kondrachov range, weak product and pullback
calculus, and the integer-order comparison with Fourier-defined Sobolev
spaces. On bounded operational $`C^1` domains, arbitrary-offset
one-Lipschitz $`C^1` scalar maps with derivative bounded by one define
completed finite-exponent Nemytskii operations and satisfy the weak chain
rule. Arbitrary ordered interval truncations are completed operations on
these bounded domains and satisfy the sharp open-interval derivative formula.
For every $`1\leq p\leq\infty`, every zero-preserving real Lipschitz map acts
on $`W^{1,p}(\mathbb R^n)` and satisfies the full almost-everywhere weak
chain rule with its classical derivative. On bounded operational $`C^1`
domains, every real Lipschitz scalar map acts on $`W^{1,p}(\Omega)` without
a zero-preserving hypothesis and satisfies the same chain rule.

Higher-order bounded extension is also formalized for every positive integer
$`k` on bounded open domains with $`C^k` graph boundary, for every
$`1\leq p\leq\infty`. The construction from only an operational $`C^1`
atlas remains first order. The global one-dimensional $`W^{1,1}` theory has
an absolutely continuous representative, almost-everywhere classical
derivative, and finite-kink calculus for absolute value, positive and negative
parts, and interval truncations. In every positive dimension, each global
$`W^{1,1}` class has an explicit absolutely continuous representative on
almost every line parallel to every coordinate axis, with the corresponding
weak derivative as its classical derivative almost everywhere.

# Compactness and the direct method

*Formalized:* relative weak compactness for bounded Hilbert-space families, weakly
closed sets cut out by arbitrary families of continuous linear constraints,
preservation of those constraints under weak limits, and their pointwise
lifting to almost-everywhere constraints on Bochner $`L^2` trajectories.
The lifted constraint spaces are weakly closed, survive weak $`L^2` limits,
and preserve weak compactness when imposed on bounded weakly closed families.
Continuous linear functionals that vanish on the kernel of a closed-range
operator factor continuously through its range and have a unique
range-valued Hilbert multiplier; this is the abstract pressure-recovery step
for a divergence operator.
Componentwise weak convergence in two Hilbert spaces also preserves every
common bound on a nonnegative weighted sum of squared norms, which is the
kinetic-plus-dissipation limit passage used in energy-class constructions.
The formalized layer also includes weak lower semicontinuity of convex
functionals, coercive direct-method theorems, Sobolev integral applications,
spatial Rellich–Kondrachov compactness, and the weak Bochner compactness and
Lions–Magenes machinery used by the Galerkin chapters.
For compact dense Gelfand inclusions of real Hilbert spaces on a fixed
finite interval $`a<b`, the abstract Aubin–Lions theorem is formalized for
Lions–Magenes trajectories: uniform $`L^2(a,b;V)` bounds and
$`L^2(a,b;V^*)` bounds on their weak time derivatives imply relative
compactness in $`L^2(a,b;H)`.
For Hölder-related exponents $`p,q,r\in[1,\infty]`, strong $`L^p` and
$`L^q` convergence passes continuous bilinear pointwise operations to strong
$`L^r` convergence. In particular, quadratic strong $`L^2` convergence yields strong
$`L^1` convergence. Weak dual trajectories can also be paired with strongly
convergent states inside the time integral. Continuous trilinear forms have
abstract skew-symmetry lemmas for cubic energy cancellation and quadratic
difference estimates, a bounded-set Lipschitz estimate for the induced
dual-valued quadratic map, and a strong–strong–weak limit theorem for
bounded weak test families. Quadratic Gelfand weak equations satisfy both
a state-tested energy identity and an exact difference equation. At
the Galerkin level, skew cancellation transfers the dimension-independent
pivot and integrated coercive estimates from the linear equation to the
quadratic equation. Finite-partition ODE solutions can be
continued inside a time-dependent family of invariant sets, including
moving energy envelopes. The quadratic mass-inverted Galerkin vector field
has explicit growth and bounded-set Lipschitz estimates. Combining its local
Picard theorem, finite-dimensional pivot norm equivalence, coercivity, and
skew cancellation gives global Galerkin existence on every finite interval.
The argument uses no Navier–Stokes structure. A sign-unrestricted differential Grönwall
theorem and its dissipative corollary provide a complementary scalar route:
if $`\alpha>0`, $`R\geq\beta/\alpha`, and $`e(a)\leq R`, then a
differentiable trajectory satisfying $`e' + \alpha e \leq \beta` on
$`[a,b]` satisfies $`e\leq R` throughout that interval.

*Partial:* Aubin–Lions compactness covers Hilbert Gelfand triples with
$`L^2` time integrability of both the trajectories and their weak time
derivatives. Around it the evolution layer has coordinated common-filter weak
limits, identification of weak time derivatives, and the basic nonlinear limit
passages that use its strong convergence.

# Cauchy problems

*Formalized:* for smooth quasilinear scalar equations of any order,
noncharacteristic Cauchy data determine every derivative of a solution on the
initial hypersurface. For first-order analytic systems in normal form, the
formal power-series solution exists and is unique over any commutative ring
containing $`\mathbb Q`, majorized systems have majorized solutions, an
explicit scalar majorant converges, and the resulting analytic solution with
zero initial data exists near the origin and is locally unique. The
{bpref "methods.power_series.analytic_evolution"}[analytic evolution theorem]
and its {bpref "methods.power_series.analytic_hypersurface"}[hypersurface form]
restore general analytic data.

# Geometric PDE

*Inherited:* Mathlib supplies smooth manifolds, vector bundles, tangent
bundles, Riemannian metrics with their path-length distance, and differential
forms on normed spaces with their exterior derivative. The analytic PDE
theorems of the book are stated on Euclidean space.

# Priority order

The open direction with the most consequences here is convolution of
distributions when only one factor has compact support: once $`P` has positive
order, a fundamental solution $`G` cannot have compact support, so the formula
$`P(G*T)=T` needs that convolution.
