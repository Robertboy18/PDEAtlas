/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Approximation
import Blueprint.Commands.Figures
import PDE.Spaces.Sobolev.Approximation.Density.ExtensionDomain
import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
import PDE.Spaces.Sobolev.Boundary.Atlas.Interval
import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic
import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.RepresentativeBridge
import PDE.Spaces.Sobolev.Extension.Representative.Basic

/-!
# Sobolev extension

Abstract Sobolev extension interfaces, the first-order extension operator on
an operational `C¹` domain, and smooth density on extension domains.
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
#doc (Manual) "Extension and Density on Regular Domains" =>

Whole-space approximation and embedding theorems become useful on a domain
$`\Omega` once a Sobolev function on $`\Omega` can be continued to all of
$`\mathbb R^n` without changing its almost-everywhere class on $`\Omega`.
There are two distinct reasons to ask for such a continuation, and they require
different kinds of control.

For approximation of one fixed function, it is enough to know that some global
Sobolev representative exists. No estimate for the chosen extension is used:
one extends, applies the whole-space density theorem, and restricts the
approximants. To transfer norm estimates, compactness, or nonlinear operations
uniformly from $`\mathbb R^n` to $`\Omega`, we use a bounded linear map
between the completed graph spaces.

We therefore distinguish three mathematical conclusions. A
{bpref "sobolev.representative_extension"}[representative extension] agrees
with the original function almost everywhere on the domain. A
{bpref "sobolev.extension_operator"}[bounded extension operator] makes this
choice linearly and controls the norm by one constant for every input. A
{bpref "sobolev.supported_extension_operator"}[supported extension operator]
also keeps the extensions inside a prescribed region, a property needed when
compactness arguments must prevent mass from escaping to infinity.
{bpref "sobolev.extension.atlas"}[Boundary charts and cutoffs] construct the
first-order operator with these controls.

The geometric hypothesis is operational. The extension construction assumes a
finite atlas
containing globally represented chart maps, inverse maps, and the
partition-of-unity cutoffs used by the proof. Every bounded open set with
$`C^1` graph boundary admits such an atlas.

The local construction is easiest to see on an interval. For
$`u\in W^{1,p}(0,a)` with $`a>0`, reflect across zero:

$$`
Eu(t)=u(|t|),\qquad
(Eu)'(t)=
\begin{cases}
u'(t),&t>0,\\
-u'(-t),&t<0.
\end{cases}
`

The two sides meet with the same value, so reflection creates no jump at
zero. For finite $`p`, each integral in the first-order graph norm doubles:
$`\|Eu\|_{W^{1,p}(-a,a)}=2^{1/p}\|u\|_{W^{1,p}(0,a)}`.
In particular, a constant reflects to a constant, whereas its zero extension
has a jump. A boundary chart performs this reflection after flattening the
boundary, and cutoffs combine the reflected pieces.

{leanpde_figure "sobolev-reflection-extension"}

The figure shows the two continuations side by side. The reflected
derivative jumps at zero, which costs nothing in $`L^p`; the jump of the zero
extension puts a point mass into its derivative, so the zero extension of a
function with nonzero boundary value is not in $`W^{1,p}(-a,a)`.

This first-order picture also explains an order restriction. Reflecting
$`u(t)=t` gives $`|t|`, whose second distributional derivative is
$`2\delta_0`. The same reflection therefore does not automatically extend
$`W^{2,p}`. Higher-order extension needs additional matching of derivatives
across the boundary.

:::group "sobolev.extension"
Sobolev extension
:::

# Abstract Extension Interfaces

The two basic extension interfaces live at the same two levels as the
representative and graph-space Sobolev models. Each contains only the data
that later theorems use.

:::definition "sobolev.representative_extension" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.Representative.HasExtension") (uses := "sobolev.representative_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For natural order $`k`, exponent $`p`, and domain
$`\Omega\subseteq\mathbb R^n`, the representative-level extension property is
the existence of a map

$$`
\mathcal E_{\mathrm{rep}}:
  W_{\mathrm{rep}}^{k,p}(\Omega)
  \longrightarrow
  W_{\mathrm{rep}}^{k,p}(\mathbb R^n)
`

such that

$$`
\mathcal E_{\mathrm{rep}}u=u
\qquad\text{almost everywhere on }\Omega
`

for every representative-level Sobolev function $`u`.

Only the existence of $`\mathcal E_{\mathrm{rep}}` and the almost-everywhere
agreement of base functions are required; the map need not be linear or
bounded, and its values outside $`\Omega` are unconstrained.

The chosen global object is a global Sobolev representative. When $`\Omega`
is open, its weak derivatives restrict to $`\Omega`, and almost-everywhere
agreement of the base functions and uniqueness of weak derivatives identify
them with the derivatives of $`u`. This is the information used by the
extension-and-restriction density theorems.
:::

The graph-space interface asks for the same almost-everywhere agreement on
$`\Omega`, realized by a continuous linear map between the completed spaces,
which is the form in which norm estimates and compactness travel from
$`\mathbb R^n` to $`\Omega`.

:::definition "sobolev.extension_operator" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.GraphSpace.Operator, SobolevSpace.Extension.GraphSpace.HasExtensionOperator") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A graph-space extension operator of order $`k` is a continuous linear map

$$`
E:W^{k,p}(\Omega)\longrightarrow W^{k,p}(\mathbb R^n)
`

whose base coordinate agrees almost everywhere with the base coordinate of the
input on $`\Omega`. The structure stores:

* `toContinuousLinearMap`, the bounded linear map between the completed graph
  spaces;
* `agree_ae`, the almost-everywhere agreement statement for the base
  coordinate with respect to Lebesgue measure restricted to $`\Omega`.

The proposition `HasExtensionOperator` is `Nonempty` applied to this structure:
it asserts existence without selecting a canonical operator in theorem
statements.

Agreement of the derivative coordinates is not stored separately. Both the
output and input graph bundles certify that their stored coordinates are weak
derivatives of their base coordinates, so restriction of the global
weak-derivative identities, followed by uniqueness on the open domain,
recovers derivative-coordinate agreement whenever it is required.
:::

Neither interface constrains the extension outside $`\Omega`. Support of the
extension in a prescribed neighborhood of $`\overline\Omega` is recorded as
separate data because it comes from
a separate step, multiplication by a cutoff, which is available at every
order.

:::definition "sobolev.supported_extension_operator" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.GraphSpace.SupportedOperator, SobolevSpace.Extension.GraphSpace.HasSupportedExtensionOperator, SobolevSpace.Extension.GraphSpace.Operator.withSupportIn") (uses := "sobolev.extension_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Prescribed support is data added to an extension operator. A supported
operator over a set $`V` consists of an extension
operator together with

$$`
\mathbf 1_V\, (Eu)=Eu
\qquad\text{almost everywhere on }\mathbb R^n
`

for the base coordinate of every input $`u`. This indicator identity is
independent of modifications on null sets and is equivalent to saying that the
chosen base representative vanishes almost everywhere outside $`V`.

At every Sobolev order $`k`, including $`k=0` and $`p=\infty`, any bounded
extension operator can be localized when
$`\Omega` is measurable, $`\overline\Omega` is compact, and
$`V` is an open neighborhood of $`\overline\Omega`. Choose a smooth compactly
supported cutoff $`\psi` in $`V` with $`\psi=1` on
$`\overline\Omega`, and define

$$`
E_Vu=\psi\,Eu.
`

Boundedness follows from boundedness of multiplication by $`\psi` on
$`W^{k,p}(\mathbb R^n)`, agreement is preserved because the cutoff equals one
on $`\Omega`, and the cutoff support gives the indicator identity
(`Operator.withSupportIn`).
:::

One implication between the interfaces is needed later. Almost-everywhere
agreement of base coordinates is all that survives the passage, and it is
all the density argument uses.

:::theorem "sobolev.extension_operator_bridge" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.GraphSpace.exists_representativeExtensionOperator") (uses := "sobolev.extension_operator, sobolev.representative_extension, sobolev.model_bridge")
Every bounded graph-space extension operator induces a representative-level
extension.

Given $`u` in the representative model, first store its weak derivatives in
graph space by `ofRepresentative`, apply the bounded graph-space operator, and then forget
the global derivative coordinates with `toRepresentative`. The operator's
base-coordinate agreement and the model bridge show that the resulting global
representative equals $`u` almost everywhere on $`\Omega`.

The converse would need linearity and norm control, which a
representative-level extension does not carry.
:::

:::proof "sobolev.extension_operator_bridge"
Send the input representative to the domain graph space. Apply the
continuous linear extension and convert the result back to a global
representative. Combine the extension operator's `agree_ae` field with the
almost-everywhere base-coordinate identity for `ofRepresentative`.
:::

# Density on an Abstract Extension Domain

These results need no boundary charts, only a representative-level extension
hypothesis, so every geometric construction of extensions yields density by
the same proof.

:::theorem "sobolev.extension_domain_approximation" (parent := "sobolev.extension") (lean := "SobolevSpace.Approximation.approximation_Wkp") (uses := "sobolev.global_approximation, sobolev.representative_extension, sobolev.mollifier")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be open, let $`k` be a natural number, and
let the extended nonnegative-real exponent satisfy

$$`1\leq p,\qquad p\neq\infty.`

Assume `Representative.HasExtension n k p Ω`. For every representative-level
$`u\in W^{k,p}(\Omega)`, there is a sequence
$`u_m:\mathbb R^n\to\mathbb R` such that:

* every $`u_m` is smooth to all finite orders;
* every $`u_m` has compact support in $`\mathbb R^n`;
* the base functions converge on $`\Omega` in `eLpNorm`;
* for every derivative word $`\alpha:\operatorname{List}(\operatorname{Fin}n)`
  with $`|\alpha|\leq k`, there is an $`L^p(\Omega)` function $`g_\alpha`
  which is the weak $`\alpha`-derivative of $`u`, and
  $`D^\alpha u_m\to g_\alpha` in `eLpNorm` on $`\Omega`.

The conclusion is coordinatewise and representative-level.

The proof uses no uniform estimate for the extension. For the fixed input
$`u`, choose its global extension $`U`, apply
{uses "sobolev.global_approximation"}[] to $`U`, and restrict every convergence
statement from Lebesgue measure on $`\mathbb R^n` to Lebesgue measure
restricted to $`\Omega`. The global weak derivatives restrict to weak
derivatives of $`u` because $`U=u` almost everywhere on $`\Omega`.

The approximants are smooth on all of $`\mathbb R^n`, which is why the
extension hypothesis is needed. The finite-exponent condition comes from the
whole-space compact-support approximation theorem.
:::

:::proof "sobolev.extension_domain_approximation"
Choose a global Sobolev extension $`U` of $`u`. Apply whole-space
compact-support approximation to $`U`. Monotonicity of `eLpNorm` under measure
restriction transfers convergence to $`\Omega`. Restrict each global weak
derivative identity to the open domain, then replace the base function $`U`
by $`u` using their almost-everywhere equality.
:::

:::theorem "sobolev.extension_domain_density" (parent := "sobolev.extension") (lean := "SobolevSpace.GraphSpace.approximation_WkpSpaceOn") (uses := "sobolev.graph_space, sobolev.model_bridge, sobolev.extension_domain_approximation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "263-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same openness, finite-exponent, and representative-extension
hypotheses, every

$$`U\in W^{k,p}(\Omega)`

in the completed graph-space model is the norm limit of restrictions to
$`\Omega` of globally smooth compactly supported functions.

More precisely, the theorem returns concrete functions $`f_m`, their
`ContDiff` and compact-support proofs, and convergence of
`mkWkpSpaceOnOfContDiff f_m` to $`U` in the ordinary real-valued graph-space
norm.

The graph space indexes derivatives by finite symmetric multi-indices, whereas
the representative theorem is stated for derivative words. For each graph
index, its canonical word has length at most $`k`. Weak-derivative uniqueness
identifies the representative theorem's limiting function with the derivative
coordinate already stored in $`U`. Coordinatewise convergence over the finite
index type is then assembled into convergence for the finite `PiLp` norm.

The approximating global functions need not have support contained in
$`\Omega`. Their restrictions are the standard smooth-up-to-the-boundary
approximants of an extension domain; density of $`C_c^\infty(\Omega)` itself
would impose a zero-boundary condition.
:::

:::proof "sobolev.extension_domain_density"
Convert $`U` to a representative, apply
{uses "sobolev.extension_domain_approximation"}[], and inspect one symmetric
derivative coordinate at a time. Uniqueness of weak derivatives replaces the
coordinatewise limiting representative by the coordinate stored in $`U`.
Finite-coordinate convergence then gives convergence in the graph norm.
:::

# Operational C¹ Geometry

Evans's first-order extension construction is carried out from explicit
finite boundary data.

The local idea is reflection. After flattening a boundary patch, reflect the
function across the coordinate hyperplane, then return to the original
coordinates. The chain rule and change of variables explain why derivative
bounds for both the chart and its inverse enter the norm estimate. Cutoffs
keep each reflected piece within its chart, and a finite partition of unity
joins the pieces to the unchanged interior part. Later boundary estimates
reuse the same localization, with stronger chart regularity when more
derivatives are required.

:::definition "sobolev.extension.atlas" (parent := "sobolev.extension") (lean := "SobolevSpace.Boundary.C1ExtensionAtlas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For positive dimension, an operational $`C^1` extension atlas on
$`\Omega\subseteq\mathbb R^n` contains:

* proofs that $`\Omega` is open and bounded;
* a finite number $`N` of boundary charts;
* for each $`i:\operatorname{Fin}N`, an open partial homeomorphism of
  $`\mathbb R^n`;
* globally defined $`C^1` representatives of the chart map and inverse map;
* the local equivalence
  $`x\in\Omega\Longleftrightarrow\Phi_i(x)\in\mathbb R^n_+` on the chart
  source;
* boundedness of each chart target;
* one smooth compactly supported interior cutoff supported in $`\Omega`;
* finitely many smooth compactly supported boundary cutoffs, each supported in
  its chart source;
* the pointwise partition identity

  $$`
  \chi_{\mathrm{int}}(x)+\sum_{i=1}^N\chi_i(x)=1
  \qquad(x\in\Omega).
  `

The partial homeomorphism is required to be invertible only between its open
source and target. The total functions used to represent it are globally
$`C^1` because the weak chain rule and pullback theorems are stated for
global maps.

The class contains the finite atlas and partition of unity that the proofs
use. Every bounded open set with $`C^1` graph boundary
admits these data.
:::

:::definition "sobolev.extension.concrete_interval" (parent := "sobolev.extension") (lean := "SobolevSpace.Boundary.Atlas.Interval.domain, SobolevSpace.Boundary.Atlas.Interval.c1ExtensionAtlas, SobolevSpace.Boundary.Atlas.Interval.domainC1ExtensionAtlas") (uses := "sobolev.extension.atlas")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The domain

$$`
\{x\in\mathbb R^1:-1<x_0<1\}
`

has a fully constructed operational atlas. The left chart is translation by
$`+1`; the right chart is reflection $`x\mapsto1-x`. On suitable bounded open
chart sources these maps flatten the two endpoints to the positive half-line.
A finite smooth partition of unity on the closure supplies one interior and
two boundary cutoffs.

The resulting `c1ExtensionAtlas` is installed as the typeclass instance
`domainC1ExtensionAtlas`. Thus all the extension, density, trace, and
compactness results formulated for an operational atlas can be instantiated on
this concrete nonempty interval without adding geometric axioms.
:::

# First-Order Extension on an Operational C¹ Domain

:::theorem "sobolev.c1_extension" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.C1.exists_extensionOperator_W1p, SobolevSpace.Extension.C1.extensionCLM, SobolevSpace.Extension.C1.operator") (uses := "sobolev.extension.atlas, sobolev.extension_operator, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0`, let $`1\leq p\leq\infty`, and suppose
$`\Omega\subseteq\mathbb R^n` carries a `Boundary.C1ExtensionAtlas`. Then there
is a bounded linear extension

$$`
E:W^{1,p}(\Omega)\longrightarrow W^{1,p}(\mathbb R^n)
`

whose base coordinate agrees almost everywhere with the input on $`\Omega`.
The construction has one interior contribution and finitely many boundary
contributions. An interior cutoff allows zero extension away from the
boundary. For each boundary piece, compose the localized function with the
inverse chart, extend across the half-space boundary by reflection, localize
in the chart target, and compose with the chart to return to physical
coordinates. The partition identity proves agreement on $`\Omega`;
boundedness of the component maps and their finite sum proves continuity.

The theorem is first order. Bounded extension in $`W^{k,p}` for $`k>1`
requires stronger chart regularity and higher-order composition estimates;
weighted reflection constructs such an extension on every bounded open set
with local $`C^k` graph boundary.

The linked Lean operator includes the endpoint $`p=\infty`, under the
operational atlas assumptions.
:::

:::proof "sobolev.c1_extension"
Construct a continuous linear interior piece and one continuous linear
boundary piece for each chart. Sum this finite family. Almost everywhere on
$`\Omega`, each piece has base coordinate equal to its partition cutoff times
the original base function. The cutoff sum is one, so the assembled base
coordinate agrees with the input.
:::

The assembled operator has no prescribed support. Because the atlas makes
$`\Omega` open and bounded, $`\overline\Omega` is compact, which is exactly
the hypothesis under which the support localization of the abstract section
applies.

:::theorem "sobolev.c1_extension.supported" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.C1.exists_supportedExtensionOperator_W1p, SobolevSpace.Extension.C1.supportedOperator") (uses := "sobolev.supported_extension_operator, sobolev.c1_extension")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "268-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`V\subseteq\mathbb R^n` be open and suppose
$`\overline\Omega\subseteq V`. The first-order bounded extension can be chosen
so that its base coordinate satisfies

$$`
\mathbf 1_V(E_Vu)=E_Vu
\qquad\text{almost everywhere on }\mathbb R^n
`

for every $`u\in W^{1,p}(\Omega)`.

This is the generic support localization of
{uses "sobolev.supported_extension_operator"}[] applied to
{uses "sobolev.c1_extension"}[].
:::

:::proof "sobolev.c1_extension.supported"
Choose a smooth compactly supported cutoff in $`V` that equals one on
$`\overline\Omega`, and postcompose the extension operator with multiplication
by this cutoff. Agreement on $`\Omega` is unchanged, while the cutoff support
gives the almost-everywhere indicator identity.
:::

The bounded operator exists for every $`1\leq p\leq\infty`; smooth
approximation follows in the range where whole-space approximation is
available.

:::theorem "sobolev.c1_density" (parent := "sobolev.extension") (lean := "SobolevSpace.Extension.C1.approximation_W1p, SobolevSpace.Extension.C1.approximation_W1pSpaceOn") (uses := "sobolev.c1_extension, sobolev.extension_operator_bridge, sobolev.extension_domain_approximation, sobolev.extension_domain_density")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "266-271"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n>0`, let $`1\leq p<\infty`, and suppose
$`\Omega` carries the operational bounded $`C^1` atlas. Then restrictions to
$`\Omega` of globally smooth compactly supported functions are dense in
$`W^{1,p}(\Omega)`.

The approximants converge in $`L^p` together with their first weak
derivatives, hence in the norm of the completed first-order graph space.

The conclusion excludes $`p=\infty`, even though the extension operator itself
exists there, because compactly supported smooth functions are not generally
dense in the $`L^\infty`-based Sobolev norm. Under the $`C^1` hypothesis the
density theorem is first order.

These approximants are restrictions of functions in
$`C_c^\infty(\mathbb R^n)` and may be nonzero on the boundary; the closure of
$`C_c^\infty(\Omega)` is the zero-trace space.
:::

:::proof "sobolev.c1_density"
Apply {uses "sobolev.extension_operator_bridge"}[] to the bounded first-order
operator from {uses "sobolev.c1_extension"}[]. Use the resulting
representative-level extension in the abstract extension-domain approximation
and graph-space density theorems.
:::
