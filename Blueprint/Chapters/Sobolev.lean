/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Sobolev.Scope
import Blueprint.Commands.Figures

/-!
# Sobolev chapter

Assembles the Sobolev subdocuments into one chapter. Each Blueprint node lives
in the module for its subject. The global dependency graph is emitted after
every chapter has been loaded.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Sobolev Spaces and Weak Derivatives" =>
%%%
htmlSplit := .never
shortTitle := "Sobolev Spaces"
%%%

A bound on the Dirichlet energy controls the gradient in $`L^2`, but does not
ensure classical differentiability or pointwise boundary values. In existence
proofs, weak derivatives let us retain derivative bounds under weak convergence.
Compactness and trace theorems then supply stronger convergence and boundary
values under additional hypotheses.

For locally integrable functions $`u` and $`v`, the weak-derivative identity is
$`\int_\Omega u\,\partial_i\varphi = -\int_\Omega v\,\varphi` for every smooth
compactly supported $`\varphi` in $`\Omega`. Requiring the function and its derivatives
through order $`k` to belong to $`L^p` gives $`W^{k,p}(\Omega)`, equipped with
a graph norm.

Two useful consequences are compactness and continuity. On a domain with the
bounded $`C^1` boundary atlas used by the extension theorem, the
{bpref "sobolev.rellich_full_subcritical"}[Rellich–Kondrachov theorem] makes
the embedding $`W^{1,p}(\Omega)\to L^q(\Omega)` compact for
$`1\le p<n` and $`1\le q<p^*`. Bounded sequences therefore have subsequences
converging strongly in those $`L^q` spaces; evolution arguments also need
control in time to obtain strong spacetime convergence.
The {bpref "sobolev.morrey_embedding_domain"}[Morrey embedding]
sends $`W^{1,p}(\Omega)` into Hölder-continuous functions for $`p>n`.
Applied to sufficiently many weak derivatives, it recovers classical regularity
from the elliptic Sobolev estimates.

# The analytic language of weak solutions

For a continuously differentiable $`u`, integration by parts shows that the
identity

$$`\int_\Omega u\,\partial_i\varphi = -\int_\Omega v\,\varphi`

forces $`v=\partial_i u` almost everywhere on the open domain. The same
identity defines weak derivatives for rougher functions. For example,
$`u(x)=|x|` on $`(-1,1)` has no classical derivative at the origin. Its weak
derivative is the sign function: integration by parts separately on $`(-1,0)`
and $`(0,1)` gives the defining identity, with the boundary terms at zero
vanishing. The Sobolev space $`W^{k,p}(\Omega)`
collects the $`L^p` functions whose weak derivatives up to order $`k` are again
in $`L^p`.

For this example the calculation is

$$`
\int_{-1}^1 |x|\varphi'(x)\,dx
=\int_{-1}^0\varphi(x)\,dx-\int_0^1\varphi(x)\,dx
=-\int_{-1}^1\operatorname{sign}(x)\varphi(x)\,dx.
`

The value assigned to the sign function at zero does not affect the
integral. This is why weak derivatives are determined *almost everywhere*:
changing a function on a set of Lebesgue measure zero leaves these tests
unchanged.

{leanpde_figure "weak-derivative"}

For $`1\leq p<\infty`, one standard graph norm is

$$`\|u\|_{W^{k,p}} = \Big(\sum_{|\alpha|\le k}\|D^\alpha u\|_{L^p}^p\Big)^{1/p},`

while the $`p=\infty` norm takes the maximum of the derivative norms. With the
graph norm $`W^{k,p}` is a Banach space, and for $`p=2` a Hilbert space.

For finite $`p`, the norm
$`\|f\|_{L^p}=(\int_\Omega|f|^p)^{1/p}` measures integrated size.
The $`L^\infty` norm is the least bound valid outside a null set, called
the *essential supremum*. In either case $`L^p` identifies functions that
agree almost everywhere. The graph norm measures the function together with
its weak derivatives; for $`H^1=W^{1,2}` it is
$`\|u\|_{H^1}^2=\int_\Omega(|u|^2+|\nabla u|^2)`.
Completeness means that a sequence Cauchy in this norm has a limit in the
same space, including compatible limits for its derivative coordinates.

A short estimate explains how derivative control can recover continuity.
For a $`C^1` function on $`[0,1]` and $`0\leq x<y\leq1`, the
fundamental theorem of calculus and Cauchy–Schwarz give

$$`
|u(y)-u(x)|
\leq\int_x^y|u'(t)|\,dt
\leq |y-x|^{1/2}\|u'\|_{L^2(0,1)}.
`

The exponent $`1/2` is the one-dimensional Morrey exponent at $`p=2`.
Smooth approximation carries this estimate to the continuous representative
of an $`H^1(0,1)` class. The
{bpref "sobolev.morrey_embedding_domain"}[domain embedding] supplies that
representative on domains with the stated boundary atlas; evaluating an
arbitrary almost-everywhere representative would not give this conclusion.

## The Dirichlet example with one fewer derivative

Return to $`-u''=f` on $`(0,1)` with zero endpoint values. Multiplying a
classical solution by $`\varphi\in C_c^\infty(0,1)` and integrating by parts
gives

$$`
\int_0^1u'\varphi'\,dx=\int_0^1f\varphi\,dx.
`

This equation only needs $`u\in H^1_0(0,1)` and $`f\in L^2(0,1)`.
Density and Cauchy–Schwarz extend the test identity to every
$`\varphi\in H^1_0(0,1)`. The boundary condition is carried by the space
$`H^1_0`, defined by closure of compactly supported smooth functions.
It would not follow from the interior test identity alone.

There is also an energy interpretation. For

$$`
\begin{aligned}
J(u)&=\frac12\int_0^1|u'|^2\,dx-\int_0^1fu\,dx,\\
\left.\frac{d}{dt}J(u+t\varphi)\right|_{t=0}
&=\int_0^1u'\varphi'\,dx-\int_0^1f\varphi\,dx.
\end{aligned}
`

the weak equation says that the first variation vanishes. Expanding the
square then gives $`J(u+v)-J(u)=\frac12\int_0^1|v'|^2\,dx` for every
$`v\in H^1_0(0,1)`, so a weak solution minimizes this energy.
For $`f=1`, the same arch $`u=x(1-x)/2` from Foundations satisfies both
formulations. For rougher data, the weak formulation still makes sense
before a classical second derivative has been established. A regularity
theorem is what permits the later return to a pointwise equation.

## Approximation and the scale of spaces

We follow Chapter 5 of
{Informal.citet "evans-2010"}[]. At finite exponent, mollification gives
smooth density. Smooth functions are not norm-dense in $`W^{k,\infty}`, so
the density theorems stop at finite exponent. On suitable domains, extension
operators carry functions out to all of $`\mathbb{R}^n` without losing the
derivatives covered by the operator, and the trace operator recovers boundary
values as a bounded linear map. Strong convergence from compactness passes
lower-order terms to a limit, while weak convergence of derivatives and lower
semicontinuity control the energy.

The exponents in the embedding theorems are dictated by scaling. Take
$`\lambda>0` and
$`u\in C_c^\infty(\mathbb R^n)`, and set $`u_\lambda(x)=u(\lambda x)`. Then

$$`\|u_\lambda\|_{L^q}=\lambda^{-n/q}\|u\|_{L^q},\qquad
\|\nabla u_\lambda\|_{L^p}
=\lambda^{1-n/p}\|\nabla u\|_{L^p}.`

So the homogeneous inequality $`\|u\|_{L^q}\le C\|\nabla u\|_{L^p}` has a
chance of holding with a scale-independent constant only if the two powers
match. Solving $`-n/q=1-n/p` gives the Sobolev conjugate
$`q=p^*=\frac{np}{n-p}` for $`p<n`, the only exponent dilation allows. The
Gagliardo–Nirenberg–Sobolev inequality shows that this exponent is attained.
Past the threshold, when $`p>n`, membership in $`W^{1,p}` buys a
Hölder-continuous representative on $`\mathbb R^n` and on domains with suitable
extension geometry. The full Sobolev norm is doing the work there:
gradient integrability by itself neither picks out a representative nor controls
an additive constant. The dimension $`n` is the dividing line between improved
integrability and outright continuity.

Evans's Chapter 5 is the PDE-oriented reference; {Informal.citet "adams-fournier-2003"}[] is
a detailed reference for Sobolev-space theory. The composition of Sobolev functions
with Lipschitz maps follows {Informal.citet "marcus-mizel-1972"}[].

## Spaces, exponents, and boundary data

The parameters that matter stay in the theorem statements: the open domain
$`\Omega`, the derivative order $`k`, the exponent $`p`, the ambient dimension,
and the measure. The completed graph-space model keeps derivative coordinates as
$`L^p` classes, which is what separates an almost-everywhere class from any
particular continuous or pointwise representative.

$`L^p` membership of every output does not by itself
give a bounded operator, and almost-everywhere agreement identifies a selected
representative with an $`L^p` class without turning the class into a
pointwise function. Trace values and singular quotients such as
$`u/\operatorname{dist}(x,\partial\Omega)` are defined on the completed space
by density and continuity, never by evaluating an arbitrary representative.

Boundary theorems use a finite collection of
{bpref "sobolev.extension.atlas"}[boundary charts with controlled derivatives].
Each chart flattens a piece of the boundary into a coordinate hyperplane;
cutoff functions localize the function to those pieces and assemble the local
extensions. Bounds on the charts and their inverses let us transfer Sobolev
estimates between the original domain and the flattened coordinates. We ask
for these maps and bounds explicitly because the extension, trace, and
compactness proofs use them quantitatively. A separate geometric theorem
constructs this data for a bounded open set with $`C^1` graph boundary. The
interval and the Euclidean unit ball are the concrete instances.

Zero boundary values come from closures of compactly supported smooth
functions: $`H^1_0` and the higher-order $`W^{k,2}_0` model. The embedding
theorems carry their own exponent inequalities, which is what decides whether
you are in the subcritical, critical, or Morrey regime.

# Weak Derivatives and Approximation

{include 2 Blueprint.Chapters.Sobolev.Core}
{include 2 Blueprint.Chapters.Sobolev.Approximation}

# Extension, Trace, and Embeddings

{include 2 Blueprint.Chapters.Sobolev.Extension}
{include 2 Blueprint.Chapters.Sobolev.Trace}
{include 2 Blueprint.Chapters.Sobolev.Holder}
{include 2 Blueprint.Chapters.Sobolev.Inequalities}

# Difference Quotients, Compactness, and Weak Calculus

{include 2 Blueprint.Chapters.Sobolev.DifferenceQuotients}
{include 2 Blueprint.Chapters.Sobolev.Compactness}
{include 2 Blueprint.Chapters.Sobolev.WeakCalculus}

# Fourier Sobolev Spaces

Fractional and negative regularity can be defined through the Fourier
transform. On the whole space the
Fourier transform converts differentiation into multiplication by $`2\pi i\xi`,
so one can ask that $`(1+\|\xi\|^2)^{s/2}\widehat u` be square integrable for
any real $`s`. This gives a Hilbert scale $`H^s(\mathbb R^n)` of tempered
distributions.

{include 2 Blueprint.Chapters.Sobolev.Fourier}

# Coverage and Open Problems

{include 2 Blueprint.Chapters.Sobolev.Scope}
