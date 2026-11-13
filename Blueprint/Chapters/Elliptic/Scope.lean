/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.SolutionOperators

/-!
# Elliptic theory scope

The classical, variational, and regularity routes
through the elliptic development.
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
#doc (Manual) "Elliptic Coverage and Open Problems" =>

:::group "elliptic.chapter_guide"
Elliptic theory
:::

# Fundamental solutions and classical harmonic functions

## Fundamental solutions

The canonical Laplace kernel is locally integrable and is smooth and harmonic
away from its pole. For $`n\geq2`, its radial derivative has the normalized
unit flux across spheres centered at the pole. The off-pole statements hold
in every positive dimension; the distributional equation needs more than the
flux normalization and is proved by a separate argument in each of three cases.

* In dimension one, the scalar kernel $`\Phi(x)=-|x|/2` and its canonical
  $`\mathbb R^1` encoding are proved equal. The associated regular
  distribution satisfies $`-D^2T_\Phi=\delta_0`.
* In dimension two, the logarithmic kernel is regularized, its finite-order
  test-function identity is proved, and the ordinary distribution satisfies
  $`-\Delta T_{\Phi_2}=\delta_0`.
* For $`n\geq3`, the Newtonian kernel satisfies
  $`\int\Phi_n\Delta\varphi=-\varphi(0)` for compactly supported
  $`C^2` test functions. Spherical means, the ball divergence theorem, and
  coarea give the pole identity, including the limit at the origin.
  Its regular distribution therefore satisfies $`-\Delta T_{\Phi_n}=\delta_0`.

For every $`n\geq2`, convolution with a compactly supported $`C^2` datum
produces a classical $`C^2` solution of $`-\Delta(\Phi_n*f)=f`.
Differentiation under the integral transfers the Laplacian to the datum,
and the corresponding planar or Newtonian pole identity gives the equation.

## Mean values, derivative estimates, and rigidity

Sphere and ball averages are defined as normalized integrals, and the coarea
formula connects them. Harmonicity implies the sphere mean-value property,
which in turn yields the ball mean-value formula. In one dimension the
parallel result is proved directly: a $`C^2` function with zero second
derivative is affine on each relevant interval and obeys the interval
mean-value identity.

The first-derivative estimates are proved from the ball Poisson formula and
mean values. On an open set in positive dimension, classical harmonicity
implies interior smoothness and harmonicity of every fixed iterated
derivative evaluation. The arbitrary-order estimates therefore need only
harmonicity of $`u` and a bound on $`u` itself. For $`r>0`, they give
$`\|D^k u(x)\|\leq n^k M/r^k` when the closed ball of radius $`kr`
lies in the domain and $`|u|\leq M` there. Liouville's theorem holds in its
bounded form: a globally bounded harmonic function on $`\mathbb R^n` is
constant.

## Maximum principles and energy identities

The weak maximum and minimum principles, comparison, and Dirichlet uniqueness
are proved for Euclidean balls and functions continuous on the closed ball.
The strong maximum and minimum principles are proved for harmonic functions on
arbitrary open preconnected sets.

The variable-coefficient theory treats
$`Lu=-a^{ij}\partial_i\partial_j u+b\cdot Du+cu`. Its weak maximum
principle assumes an open domain with compact closure, nonnegative principal
quadratic forms, a uniform positive lower bound on one diagonal entry, an
upper bound on the corresponding drift component, and $`c\geq0`.
A boundary bound $`M` with $`cM\geq0` controls a classical subsolution
continuous on the closure.

The strong principle uses local uniform ellipticity and local upper bounds
on the trace, drift norm, and nonnegative potential. An attained maximum
$`M` with $`cM\geq0` forces constancy on an open preconnected domain.
Both matrix principles allow arbitrary real principal matrices: their
self-adjoint parts give the same operator on $`C^2` functions.
Coefficient continuity is not required.

The Hopf lemma for the same operators gives a strictly positive outer normal
derivative at a boundary maximum point with an interior ball condition. A
Harnack inequality is proved for nonnegative $`C^2` solutions of
$`Lu=0` with continuous bounded coefficients, symmetric uniformly elliptic
principal part, and a potential of either sign, through a contact-set measure
estimate and geometric decay of superlevel sets.
Radial symmetry of positive solutions of $`-\Delta u=f(u)` on the unit ball
with zero boundary values is proved by moving planes, for $`C^2` solutions
and globally Lipschitz $`f`.

Green's first and second identities are proved on coordinate boxes with their
boundary fluxes expanded face by face. The resulting classical Dirichlet
uniqueness theorem assumes pointwise $`C^2` data on a nondegenerate closed
box. This is separate from weak uniqueness in $`H^1_0`, where the boundary
condition and integration by parts are encoded variationally. On a bounded open
set with $`C^1` graph boundary and forcing continuous in $`\Omega`, the
{bpref "elliptic.energy.dirichlet_principle"}[classical Dirichlet principle]
identifies the solutions of $`-\Delta u=f` in the classical boundary class with
the minimizers of the Dirichlet energy over its finite-energy members.

## Explicit model-domain kernels

The ball Poisson extension is smooth and harmonic in the interior and
converges to its continuous boundary data. Uniqueness follows from the maximum
principle. In positive dimension, the Dirichlet problem on
a Euclidean ball with continuous data has exactly one classical solution
continuous up to the boundary.
The Kelvin-image Green-kernel boundary and off-pole harmonicity theorems
carry their own dimension restrictions.

On a bounded open set with $`C^1` boundary in dimension $`n\geq2`, the
harmonic corrector of the Green function is constructed and unique among
functions continuous on the closure, and the Green function is symmetric.
The representation formula is proved for correctors in
$`C^2(\overline\Omega)`, and such correctors are produced for $`C^{n+3}`
boundaries.

For upper half-spaces, the Green kernel, its reflection geometry, the Poisson
kernel, the pushed-forward boundary measure, and the coordinate integral
formula are dimension-generic. Exact normalization and boundary recovery
along every approach from the upper half-space are proved in every positive
dimension:

$$`
P_{\mathbb H}1=1,\qquad
\lim_{\substack{x\to(a,0)\\x\in\mathbb H}}(P_{\mathbb H}g)(x)=g(a,0)
`

The datum is measurable, uniformly bounded on the boundary hyperplane,
and its boundary restriction is continuous at the limiting point.
Horizontal displacement and height may tend to zero independently.
For continuous ambient data uniformly bounded on the boundary, the extension
is also proved $`C^2` and harmonic in the open half-space.

The method-of-images inversion theorem is planar. It treats an odd
compactly supported $`C^2` whole-space source, proves the necessary logarithmic
integrability, identifies the half-space Green potential with the whole-space
convolution, and concludes $`-\Delta u=f`.

# Weak boundary-value problems

## Poisson and principal divergence form

The abstract foundation is Lax–Milgram for a bounded coercive bilinear form on
a real Hilbert space. Its first concrete specialization uses the graph-space
model of $`H^1_0(\Omega)` and the Dirichlet form.

On a bounded measurable set in positive dimension, Poincaré gives coercivity
and produces a continuous linear solver

$$`
S:L^2(\Omega)\longrightarrow H^1_0(\Omega).
`

When the set is also open, density of compactly supported smooth tests proves
that the variational equation is equivalent to
$`-\Delta u=f` in $`\mathcal D'(\Omega)`. Existence, uniqueness, an a priori
bound, Lipschitz dependence on the forcing, the exact completion-of-the-square
identity, and uniqueness of the Dirichlet-energy minimizer are all proved.

For the principal equation

$$`
-D_i(a^{ij}D_j u)=f,
`

the form accepts a finite matrix of bounded operators on
$`L^2(\Omega)`. A measurable essentially bounded matrix field enters through
its multiplication operators. Almost-everywhere uniform ellipticity is proved
to imply the integrated coercivity inequality; symmetry is not required.
For an open, measurable, bounded domain in positive dimension and
$`f\in L^2`, this yields exactly one solution in $`H^1_0`.

Operator-valued coefficients are a functional-analytic generalization. The
displayed local differential equation is the multiplication-operator case.

## Positive mass and lower-order terms

The modified Helmholtz equation

$$`
-\Delta u+\lambda u=f,\qquad \lambda>0,
`

is solved on every open measurable domain, with no boundedness assumption.
The mass term directly controls the base $`L^2` coordinate, so coercivity does
not use Poincaré. The variational and distributional formulations are proved
equivalent, and existence and uniqueness hold for every $`L^2` forcing.

For full divergence-form operators, first- and zeroth-order terms are allowed
as bounded operators, with $`L^\infty` multiplication fields as the local
specialization. Every continuous graph-space load is represented in the
standard form

$$`
f_0-\sum_iD_i f^i,\qquad f_i\in L^2(\Omega),
`

and the chosen coordinates satisfy an exact squared-norm identity.

The full unshifted form need not be coercive. Let $`\alpha>0` be the
principal ellipticity constant, and let $`\beta,\gamma\geq0` bound the
first- and zeroth-order operator norms, respectively. For multiplication
fields, these bounds are supplied by the $`L^\infty` coefficient norms.
Gårding's estimate gives the threshold

$$`
\mu_0=\frac{n\beta^2}{2\alpha}+\gamma+\frac{\alpha}{2}.
`

Every $`\mu\geq\mu_0` makes the shifted form coercive with lower bound
$`\alpha/2`. On an open measurable domain, each standard $`H^{-1}` load then
has a unique shifted weak solution and an explicit graph-norm estimate. No
bounded-domain hypothesis is needed for this shifted theorem.

## Fredholm theory and weak spectrum

Removing the shift is a compact-perturbation problem. The abstract theory
proves compactness of Hilbert adjoints, equality of the kernel and adjoint
kernel dimensions for a compact perturbation of the identity, the adjoint
orthogonality criterion for solvability, and the exact exclusive Fredholm
alternative.

For the Sobolev problem, boundedness of the measurable domain supplies the
compact mass operator through Rellich–Kondrachov. If the full form becomes
coercive after adding a mass shift, exactly one of the following occurs:
there is a nonzero homogeneous weak solution, or every continuous dual load
has a unique weak solution.

The associated real weak spectrum has finite-dimensional eigenspaces, is
countable, has no finite accumulation point, and exactly characterizes failure
of unique solvability of the inhomogeneous pencil.

For a symmetric form coercive after a mass shift, a compact map with dense
range into the pivot Hilbert space gives a Hilbert basis of weak
eigenfunctions. The eigenvalues are greater than the negative shift.
For symmetric uniformly elliptic $`L^\infty` principal coefficients on a
nonempty bounded open subset of $`\mathbb R^n`, $`n>0`, the Dirichlet
eigenfunctions form an $`L^2` Hilbert basis indexed by $`\mathbb N`.
Their positive eigenvalues, counted with multiplicity, are nondecreasing
and tend to infinity.

The eigenvalue at index $`k` is the least uniform Rayleigh bound on a
$`(k+1)`-dimensional subspace of $`H^1_0`. This basis and min–max theorem
requires neither connectedness nor boundary smoothness. For the Laplacian on
a connected domain, the first Dirichlet eigenvalue is positive and simple,
with a positive eigenfunction. The variable-coefficient positivity theorem
also assumes the interior regularity hypotheses needed to construct a
classical representative. For the full operator with smooth coefficients and $`c\geq0` on
a smooth domain, the principal eigenvalue is real, has a positive
eigenfunction, is geometrically simple, and bounds from below the real part of
every other eigenvalue.

## Prescribed Sobolev boundary values

On a bounded set in positive dimension, every supplied
$`\varphi\in H^1(\Omega)` admits a solution in
$`\varphi+H^1_0(\Omega)` for a measurable monotone hemicontinuous
gradient flux with linear growth and a quadratic coercive lower bound,
together with a measurable continuous monotone reaction of linear growth.
The monotonicity and continuity assumptions hold almost everywhere in space.
Growth offsets belong to $`L^2`, the coercivity offset is integrable,
and the forcing is a continuous dual load on $`H^1_0`.

Strict monotonicity of the flux gives uniqueness in this boundary class.
The boundary condition is the Sobolev condition $`u-\varphi\in H^1_0`.

# Regularity and geometry

## Interior regularity

The one-dimensional Poisson theorem directly reconstructs a
$`W^{2,2}` representative and identifies its second weak derivative with
$`-f`.

There is also a raw distributional Poisson result in every dimension. If
$`u,f\in L^2_{\mathrm{loc}}(\Omega)` and $`\Delta u=f` against compactly supported
smooth tests, then for $`R>0` and $`\overline{B_{8R}(a)}\subset\Omega` it constructs
a $`W^{2,2}(B_R(a))` representative of $`u`. Each second derivative has
$`L^2` norm at most $`C(\|f\|_{L^2(B_{8R})}+R^{-2}\|u\|_{L^2(B_{8R})})`.
The constant depends only on dimension and the fixed smooth bump. No prior
$`H^1` membership or boundary trace is assumed.

In arbitrary positive dimension, the compact-set interior theorem starts from
an $`H^1` weak solution on an open set $`\Omega`; no zero trace is assumed.
The coefficient matrix on $`\Omega` must be the restriction of a globally
essentially bounded, almost-everywhere uniformly elliptic matrix on
$`\mathbb R^n` with globally Lipschitz representatives. With $`L^2` forcing,
this gives an $`H^2` representative on an open neighborhood of every compact
subset of $`\Omega`.

The higher-order local theorem has the same form. Coherent
$`W^{m+1,\infty}` coefficient data and $`W^{m,2}` forcing give a
$`W^{m+2,2}` representative near every compact subset, again without a
boundary condition. The same global boundedness, ellipticity, and Lipschitz
hypotheses remain part of this theorem. The higher-order coefficient bundles
agree almost everywhere with the restricted global field.

## Operational boundary geometry

Global Dirichlet regularity uses an operational atlas: finite interior and
boundary cutoffs, flattening charts, inverse charts, differentiability data,
bounded targets, and the identities needed to transport the equation. A
bounded open set whose boundary is locally a $`C^m` graph, $`m\geq2`, has
such an atlas with $`C^m` charts and inverse charts.

Two concrete atlases are built by hand. The interval $`(-1,1)` has affine
endpoint charts, and every positive-dimensional Euclidean unit ball has a
finite signed-cap cover, a subordinate partition of unity, globally smooth
height extensions, and complete graph-flattening charts. Both supply the charts required by global boundary regularity.

## Global Sobolev regularity

For homogeneous Dirichlet data and $`p=2`, the principal global theorem says

$$`
f\in L^2,\quad a^{ij}\in W^{1,\infty}
\quad\Longrightarrow\quad u\in H^2,
`

under the operational $`C^2` atlas, global $`C^1` coefficient
representatives, and pointwise uniform ellipticity. The assembled
representative agrees almost everywhere with the original weak solution.

Bounded first- and zeroth-order coefficients are then moved into an effective
$`L^2` forcing, giving full-operator $`H^2` regularity. At arbitrary order,
the proof combines principal regularity with the lower-order reduction and
derives the preceding Sobolev regularity by induction. The chart, coefficient,
and forcing hypotheses remain explicit.

For every $`k\in\mathbb N`, the arbitrary-order principal theorem proves

$$`
f\in W^{k,2},\quad a^{ij}\in W^{k+1,\infty}
\quad\Longrightarrow\quad u\in W^{k+2,2},
`

with forward charts of class $`C^{k+2}`, inverse charts of class
$`C^{k+1}`, coherent global $`C^{k+1}` coefficient representatives, and
uniform ellipticity. Under the same principal and atlas hypotheses,
first- and zeroth-order coefficients in $`W^{k,\infty}` give the full
shifted-operator result. It starts with the homogeneous-Dirichlet weak
solution in $`H^1_0` and constructs a $`W^{k+2,2}` representative.
Previous-order regularity and the principal regularity implication are
proved within the argument.

## Classical reconstruction and solution operators

Under coherent data at every Sobolev order and operationally smooth boundary
charts, the principal weak solution has one representative in
$`C^\infty(\overline\Omega)`. The proof raises each finite Sobolev order to a
supercritical $`W^{m+1,2n}` jet, reconstructs the classical derivatives
within the closure using boundary charts and derivative extension, and then
identifies the finite-order representatives by almost-everywhere agreement
and continuity. The interior $`C^\infty(\Omega)` theorem is the
corresponding restriction.

Uniqueness and the closed graph theorem turn the principal regularity
theorems into bounded linear maps

$$`
S_2:L^2(\Omega)\longrightarrow H^2(\Omega),\qquad
S_{m+2}:H^m(\Omega)\longrightarrow H^{m+2}(\Omega).
`

Their norm inequalities use the operator norm, so the constant is uniform in
the forcing datum but is not given explicitly in terms of the coefficients or
the domain. These maps come from the principal
divergence-form solver. For the full operator with first- and zeroth-order
terms, at any shift above the Gårding threshold, the same closed-graph argument
gives a bounded solution map $`H^m\to H^{m+2}` whose values solve the shifted
weak equation with zero Dirichlet trace.

# From the present theory to broader elliptic analysis

The main open extensions are:

* Green representation on domains with boundary regularity between $`C^1`
  and $`C^{n+3}`;
* operational atlases from geometric boundary hypotheses other than local
  $`C^m` graphs with $`m\geq2`, in particular $`C^1` boundaries;
* bounded $`H^k\to H^{k+2}` solution operators for full lower-order problems
  in their whole uniquely solvable range, below the Gårding shift;
* Neumann and mixed boundary-value theories, and nonhomogeneous Dirichlet
  regularity beyond the proved Poisson examples and supplied Sobolev boundary classes;
* general $`W^{k,p}` estimates and Schauder theory; and
* Weyl-type eigenvalue asymptotics and finer spectral estimates.
