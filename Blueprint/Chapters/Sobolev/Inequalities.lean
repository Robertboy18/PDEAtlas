/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Inequalities.PoincareHardy
import Blueprint.Commands.Figures

/-!
# Sobolev inequalities

Assembles the Sobolev-embedding, Morrey-embedding, and Poincaré–Hardy
subdocuments. Each Blueprint node lives with its inequality family.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Sobolev, Morrey, Poincaré, and Hardy Inequalities" =>

A Sobolev graph norm stores a function and its weak derivatives, but most PDE
arguments need a different form of control.  They may need a stronger
integrability exponent, a continuous representative, coercivity of a gradient
energy, or an integrable singular quotient.  Four theorem families perform
these conversions:

1. Sobolev estimates spend weak derivatives to gain integrability.
2. Morrey estimates spend weak derivatives to gain pointwise regularity.
3. Poincaré estimates remove the constant mode by imposing zero boundary data.
4. Hardy estimates control approach to a distinguished boundary through a
   singular weight.

# The exponent trichotomy

For one weak derivative in dimension $`n`, the comparison between $`p` and
$`n` determines the conclusion.

{leanpde_figure "sobolev-ladder"}

Below the dimension threshold, one derivative improves integrability. At
$`p=n`, the finite-target estimates give no general supremum bound in
dimensions $`n\geq2`; the one-dimensional $`W^{1,1}` endpoint is stronger.
Above the threshold, Morrey's estimate gives a continuous representative
with a quantitative modulus of continuity. Extension carries the whole-space
estimates to domains with the stated geometry.

## The subcritical range 1 ≤ p < n

The Sobolev conjugate is

$$`
p^*=\frac{np}{n-p},
\qquad
\frac1{p^*}=\frac1p-\frac1n.
`

The global Gagliardo–Nirenberg–Sobolev estimate controls the
$`L^{p^*}` norm by the first derivative for compactly supported smooth
functions, and density carries it to the completed space. At order $`k`,
repeated first-order steps give

$$`
p_k=\frac{np}{n-kp}
`

as long as $`kp<n`.  Each step consumes one derivative and replaces the
current exponent by its first-order Sobolev conjugate.  The proof uses
derivative-word slices of the graph bundle, which record which weak
derivative becomes the base coordinate of the next first-order Sobolev
element.

On a domain there are two routes: a supplied order-$`k` extension operator
transfers the whole-space theorem, or an operational bounded $`C^1` atlas
performs the iteration directly through first-order slices. Both give bounded
operators.

## The critical range kp = n

The formula $`np/(n-kp)` has no finite value when $`kp=n`.  On a bounded
operational $`C^1` domain, PDEAtlas proves membership in every finite target:

$$`
W^{k,p}(\Omega)\subseteq L^q(\Omega)
\qquad
\text{for every }1\leq q<\infty.
`

The $`L^\infty` endpoint is excluded because it is false: already in the
first-order case $`W^{1,n}` need not embed into $`L^\infty` when $`n\geq2`.
Each finite-$`q` inclusion is a continuous linear map. For higher order, the
atlas route first reaches a $`W^{1,n}` representative with the same base
function almost everywhere and then applies the first-order finite-target
theorem. In dimension one the endpoint is better: $`W^{1,1}(\mathbb R)` maps
contractively into $`C^0_b(\mathbb R)`.

## The supercritical range p > n

Morrey's exponent is

$$`
\gamma=1-\frac np\in(0,1].
`

For finite $`p>n`, the global theorem is a bounded linear map

$$`
W^{1,p}(\mathbb R^n)
\longrightarrow C^{0,\gamma}_b(\mathbb R^n)
`

whose value agrees almost everywhere with the Sobolev base coordinate.
Composing extension, the global embedding, and restriction gives the domain
operator. Applied to every derivative slice of order at most $`k`, the
estimate produces a completed Hölder jet for $`u\in W^{k+1,p}`, whose
adjacent coordinates are one another's classical derivatives.

At $`p=\infty` the smooth estimate is a Lipschitz bound. Smooth functions are
not norm-dense in $`W^{1,\infty}`, so the completed $`p=\infty` statement
cannot come from this estimate by density; it is proved separately from a
Lipschitz representative.

# Coercivity

## Poincaré

On a bounded set in dimension $`n>0`, the completed Poincaré theorem holds
for every finite $`p\geq1` on the closure of compactly supported smooth
functions. In its Hilbert case, there is a finite constant
$`C_\Omega` such that

$$`
\|u\|_{L^2(\Omega)}
\leq C_\Omega\|\nabla u\|_{L^2(\Omega)}
`

for $`u` in the $`H^1_0` closure of compactly supported smooth functions.
Neither measurability nor a $`C^1` atlas is needed. The hypotheses that matter
are boundedness and the zero-boundary closure: without zero boundary data the
constant functions remain in the kernel of the gradient, and without a
finite geometric scale no domain constant can be expected in this form.

Together with the trivial estimate of the gradient coordinates by the graph
norm, Poincaré makes the gradient norm equivalent to the full $`H^1_0` norm.
That is the coercivity input used by the Dirichlet Lax–Milgram theory.
The finite-$`p` theorem also controls the full $`W^{1,p}_0` graph norm by
the $`L^p` norm of its vector-valued weak gradient.

To see what *coercivity* buys, write the Hilbert estimate as
$`\|u\|_2\leq C_\Omega\|\nabla u\|_2`. Then

$$`
\|u\|_{H^1}^2
=\|u\|_2^2+\|\nabla u\|_2^2
\leq(1+C_\Omega^2)\|\nabla u\|_2^2.
`

The quadratic energy therefore controls the whole solution norm:
$`\frac12\|\nabla u\|_2^2\geq
\|u\|_{H^1}^2/(2(1+C_\Omega^2))`. A sequence cannot have bounded
Dirichlet energy while its $`H^1_0` norm escapes to infinity.
For the forced energy $`J(u)=\frac12\|\nabla u\|_2^2-\int fu`,
Cauchy–Schwarz bounds the second term by
$`\|f\|_2\|u\|_{H^1}`; the positive quadratic term eventually dominates
this linear term. This is how the inequality supplies the bounded
minimizing sequences needed by the variational method.

## Hardy

For $`1<p<\infty`, Hardy's inequality bounds
$`u/\operatorname{dist}(x,\partial\Omega)` in $`L^p` by the derivative
of $`u` in the zero-boundary Sobolev space. Each
version is first proved for smooth compactly supported functions, where
division is literal, and the quotient is then extended by continuity to a
bounded operator on the zero-boundary closure. The model cases are the
positive half-line, with the classical constant $`(p/(p-1))^p`, and the upper
half-space, where the distance to the boundary is the normal coordinate.
Boundary charts carry the half-space estimate to an operational bounded
$`C^1` domain.

# Geometric hypotheses

The geometric assumptions differ by theorem family.

* Whole-space Sobolev and Morrey estimates require no boundary geometry.
* Domain Sobolev and Morrey estimates use either an explicit extension
  operator or the operational bounded $`C^1` atlas.
* In positive dimension, the completed Poincaré theorem needs only a bounded
  set, because its source is already the zero-boundary closure.
* Completed finite-$`p` Hardy quotients are available on the positive
  half-line and the flat upper half-space without further geometry, and on a
  general domain through the operational atlas.

{include 0 Blueprint.Chapters.Sobolev.Inequalities.SobolevEmbeddings}
{include 0 Blueprint.Chapters.Sobolev.Inequalities.MorreyEmbeddings}
{include 0 Blueprint.Chapters.Sobolev.Inequalities.PoincareHardy}
