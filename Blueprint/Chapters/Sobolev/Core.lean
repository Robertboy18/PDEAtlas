/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
import PDE.Spaces.Sobolev.Calculus.Composition.Truncation
import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions
import PDE.Spaces.Sobolev.GraphSpace.Norms
import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.GraphSpace.Operators.Restriction
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge
import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
import PDE.Spaces.Sobolev.Variational.Spaces.H1
import Verso
import VersoBlueprint
import VersoManual

/-!
# Weak derivatives and Sobolev spaces

Weak derivatives and the two Sobolev-space models.
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
#doc (Manual) "Weak Derivatives and Sobolev Spaces" =>

The Sobolev development rests on one analytic relation and two data models,
arranged in three layers:

1. `HasWeakDerivativeOn` is a proposition about concrete functions;
2. `SobolevSpaceOn` stores one concrete representative together with proofs
   that suitable derivative representatives exist;
3. `WkpSpaceOn` keeps the base function and all derivative coordinates as
   `Lp` classes and is the complete normed space used by operators.

Pointwise formulas naturally live at the first two layers, while bounded
linear maps, compactness, and variational arguments require the third. The
bridge between the latter two is canonical from graph space to a selected base
representative, but choosing all derivative representatives in the reverse
direction is noncomputable.

In the graph model, derivative *words* are reduced to symmetric
multi-indices, completeness holds for every $`1\leq p\leq\infty`, including
the endpoints $`p=1` and $`p=\infty`, and equality of `Lp` classes never
yields a pointwise equality.

For a two-dimensional function with two weak derivatives, the graph element
can be pictured as

$$`
(u,\partial_xu,\partial_yu,\partial_{xx}u,\partial_{xy}u,\partial_{yy}u)
\in (L^p(\Omega))^6.
`

These six entries are constrained by the test identities; they cannot be
chosen independently. The mixed derivative occurs once because the symmetric
index identifies the two orders of differentiation. This is the *graph* in
graph space: the compatible tuples of a function and its derivatives.

The reason this model is complete is visible already in one dimension.
If $`u_j\to u` and $`u_j'\to g` in $`L^p`, pairing with a fixed smooth
compactly supported test function passes to the limit:

$$`
\int u\varphi'
=\lim_j\int u_j\varphi'
=-\lim_j\int u_j'\varphi
=-\int g\varphi.
`

Hölder's inequality justifies both limits, including the endpoint pairing
with a bounded test function when $`p=1`. Thus the limiting derivative
coordinate is still the weak derivative of the limiting base coordinate.
The closedness proof for the graph space repeats this argument for every
stored derivative.

:::group "sobolev.weak"
Weak derivatives and Sobolev spaces
:::

:::definition "sobolev.weak_derivative" (parent := "sobolev.weak") (lean := "SobolevSpace.HasWeakDerivativeOn")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "255-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega \subseteq \mathbb R^n`, let $`\alpha` be a word of coordinate
indices, and let $`f,g : \mathbb R^n \to \mathbb R`.  The predicate
`HasWeakDerivativeOn Ω α f g` is defined for an arbitrary set $`\Omega`. It
requires both functions to be locally integrable on $`\Omega` with respect to
ambient Lebesgue measure and requires

$$`
\int_\Omega f\,D^\alpha\varphi
  = (-1)^{|\alpha|}\int_\Omega g\,\varphi
`

for every globally smooth compactly supported test function $`\varphi` whose
closed support `tsupport φ` is contained in $`\Omega`. Both integrals are
Bochner integrals against the restricted measure
`volume.restrict Ω`; compact support and local integrability make the pairings
integrable.

Thus the declaration is an arbitrary-set *restricted-test relation*. When
$`\Omega` is open, these are exactly the usual $`C_c^\infty(\Omega)` tests and
the definition has Evans's distributional meaning. On a nonopen set,
especially one with empty interior, the available tests can be too small to
determine $`g`. PDE-facing predicates such as weak Poisson and weak divergence
solutions therefore carry an explicit `IsOpen Ω` field. The relation says
nothing about pointwise differentiability of $`f`.

For open domains, weak derivatives are unique almost everywhere under only
the local-integrability hypotheses already present in the predicate.
:::

Uniqueness is what later allows a derivative to be stored as a single `Lp`
class rather than as a relation: two functions that both satisfy the identity
for the same word on an open set define the same class. The openness
hypothesis enters here for the first time, and it is inherited by every later
statement that identifies a stored coordinate with a distributional
derivative.

:::theorem "sobolev.weak_derivative_unique" (parent := "sobolev.weak") (lean := "SobolevSpace.HasWeakDerivativeOn.unique_ae") (uses := "sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "257"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
On an open domain, two proposed derivative representatives satisfying the
same weak-derivative identity for the same base function agree almost
everywhere with respect to `volume.restrict Ω`. Concretely, if

$$`
  \int_\Omega f\,D^\alpha\varphi
    =(-1)^{|\alpha|}\int_\Omega g_1\varphi
    =(-1)^{|\alpha|}\int_\Omega g_2\varphi
  \quad\text{for every }\varphi\in C_c^\infty(\Omega),
`

then $`g_1=g_2` almost everywhere on $`\Omega`. This is Evans's primitive
uniqueness result. No exponent and no global $`L^p` hypothesis occur in the
statement.
:::

:::proof "sobolev.weak_derivative_unique" (uses := "sobolev.weak_derivative")
Subtract the two distributional identities and apply the fundamental lemma
for locally integrable functions paired against all compactly supported
smooth test functions.
:::

Uniqueness compares two witnesses for one word. The second basic property of
the relation compares one witness across two words. On an open set the two
results combine, so witnesses for any two rearrangements of a word agree
almost everywhere.

:::theorem "sobolev.derivative_permutation" (parent := "sobolev.weak") (lean := "SobolevSpace.HasWeakDerivativeOn.perm") (uses := "sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "261-262"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If two coordinate words are permutations of one another, a weak derivative
witness for one word is also a witness for the other. This theorem does not
require $`\Omega` to be open: it follows because every smooth test function has
commuting classical mixed derivatives, and a permutation preserves the sign
$`(-1)^{|\alpha|}`.

This is the formal reason the completed graph model can use commutative
multi-indices rather than one coordinate for every ordered word. It does not
assume that $`f` itself has classical mixed derivatives.
:::

:::proof "sobolev.derivative_permutation"
The proof first proves equality of the corresponding iterated derivatives of a
smooth test function and then rewrites the integration-by-parts identity from
{uses "sobolev.weak_derivative"}[].
:::

With the relation and its two basic properties in hand, the first data model
can be stated. It adds to a base function exactly the global information that
the relation lacks: `HasWeakDerivativeOn` asks only for local integrability,
whereas a Sobolev function needs an $`L^p(\Omega)` bound on the base function
and on a witness for every word of length at most $`k`.

:::definition "sobolev.representative_space" (parent := "sobolev.weak") (lean := "SobolevSpace.SobolevSpaceOn") (uses := "sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
`SobolevSpaceOn n k p Ω` contains:

- a concrete function $`u : \mathbb R^n\to\mathbb R`;
- a proof that $`u\in L^p(\Omega)`;
- for every coordinate word $`\alpha` with $`|\alpha|\leq k`, a proof that
  some $`g_\alpha\in L^p(\Omega)` satisfies
  `HasWeakDerivativeOn Ω α u gα`.

The derivative clause is existential: it records that derivative
representatives exist but does not expose a canonical derivative-valued function.
That is why it is convenient for hypotheses and pointwise formulas but not
the primary normed-space model.

Equality of two `SobolevSpaceOn` values is literal equality of their `toFun`
fields, not almost-everywhere equality. The base `MemLp` field is stated
separately. On an open domain it can be recovered from the order-zero
weak-derivative clause and uniqueness, but on an arbitrary set that
uniqueness can fail. The type is meaningful for every extended nonnegative
`p`; its standard Sobolev interpretation uses an open domain and
$`1\leq p\leq\infty`.
:::

The representative model quantifies over ordered words, so $`D_1D_2u`
and $`D_2D_1u` are certified separately even though, by the permutation
theorem together with uniqueness, their witnesses agree almost everywhere on
an open set. A model that stores derivatives as coordinates should not carry
this redundancy, and a symmetric index type removes it.

:::definition "sobolev.symmetric_derivative_index" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.DerivIndex, SobolevSpace.GraphSpace.DerivIndex.toList, SobolevSpace.GraphSpace.derivIndexOfList") (uses := "sobolev.derivative_permutation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The graph model does not retain every ordering of a mixed derivative.
`DerivIndex n k` is the finite type

$$`
\coprod_{m=0}^{k}\operatorname{Sym}^m(\{1,\ldots,n\}),
`

implemented as a dependent pair of an order $`m\leq k` and a symmetric power
of `Fin n`. Thus $`D_1D_2u` and $`D_2D_1u` use the same coordinate.

`DerivIndex.toList` chooses an ordered representative only when a declaration
such as `HasWeakDerivativeOn` needs a list. Conversely,
`derivIndexOfList α hα` sends a word of length at most $`k` to its symmetric
index, and converting it back produces a permutation of $`\alpha`, not
necessarily the same list. The permutation theorem shows that this choice is
analytically harmless.
:::

Fixing the index type fixes the shape of a graph element: one $`L^p(\Omega)`
class for each symmetric index, the empty index standing for the base
function. The ambient bundle collects these coordinates with no relation
imposed between them. It is a finite product of `Lp` spaces, and it is where
the norm is defined.

:::definition "sobolev.graph_ambient" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.WkpAmbientOn, PiLp.norm_eq_sum, PiLp.norm_eq_ciSup") (uses := "sobolev.symmetric_derivative_index") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`1\leq p\leq\infty`, the ambient coordinate bundle is

$$`
\mathcal A^{k,p}(\Omega)
  = \prod_{\substack{|\alpha|\leq k\\\text{mod permutation}}}^{\ell^p}
      L^p(\Omega).
`

In Lean this is the finite `PiLp` product `WkpAmbientOn n k p Ω`. If
$`p<\infty`, its norm is exactly

$$`
\|U\|_{\mathcal A^{k,p}}
  = \left(\sum_a \|U_a\|_{L^p}^{\,p}\right)^{1/p}.
`

At $`p=\infty` it is the supremum, hence the maximum, of the finitely many
coordinate norms:

$$`
\|U\|_{\mathcal A^{k,\infty}}=\max_a\|U_a\|_{L^\infty}.
`

Some texts instead sum the finitely many $`L^\infty` coordinate norms. Those
norms are equivalent, but every quantitative PDEAtlas estimate uses the
`PiLp` maximum convention unless it explicitly states another norm.
:::

An ambient family is a Sobolev function only when each coordinate is in fact a
weak derivative of the base coordinate. The graph space is the subset of the
bundle cut out by these identities, one for every symmetric index; the ordered
word that `HasWeakDerivativeOn` requires is supplied by `DerivIndex.toList`.

:::definition "sobolev.graph_space" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.IsWkpOn, SobolevSpace.GraphSpace.wkpSubmoduleOn, SobolevSpace.GraphSpace.WkpSpaceOn") (uses := "sobolev.weak_derivative, sobolev.graph_ambient")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`0` denote the empty multi-index. The predicate `IsWkpOn U` imposed on
an ambient family $`U` is

$$`
\forall a,\qquad
\operatorname{HasWeakDerivativeOn}
  (\Omega,\operatorname{toList}(a),U_0,U_a).
`

`wkpSubmoduleOn` is the real submodule cut out by these identities, and
`WkpSpaceOn` is the same submodule used as a type, for every exponent. The assumption
`Fact (1 ≤ p)` is not part of the type; where it is available, it gives the finite
`PiLp` bundle its normed-space structure. Local integrability of every coordinate
is a field of the weak-derivative relation itself.

Each coordinate is a Mathlib `Lp` value, so equality is already
almost-everywhere equality. On an open domain, uniqueness identifies these
coordinates with the usual distributional derivatives of the base
coordinate. On an arbitrary set, the type still records the restricted-test
relation, and the available tests may be too few to determine the derivative
coordinates.
:::

Two structural operators act on the graph space, and both are contractions
because the bundle norm is a monotone function of the coordinate norms. The
first shrinks the domain while keeping every derivative coordinate.

:::theorem "sobolev.graph_space_restriction" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.restrictCLM_apply_ae, SobolevSpace.GraphSpace.norm_restrictCLM_apply_le, SobolevSpace.GraphSpace.norm_restrictCLM_le_one, SobolevSpace.GraphSpace.restrictCLM_self, SobolevSpace.GraphSpace.restrictCLM_comp, SobolevSpace.GraphSpace.restrictCLM, SobolevSpace.GraphSpace.norm_restrictAmbient_apply_le, SobolevSpace.GraphSpace.norm_restrictDerivLp_le, SobolevSpace.GraphSpace.restrictDerivLp_apply_ae, SobolevSpace.GraphSpace.restrictDerivLp_self, SobolevSpace.GraphSpace.restrictDerivLp_comp, SobolevSpace.GraphSpace.restrictDerivLp") (uses := "sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega_1\subseteq\Omega_2`, with $`\Omega_1` measurable. Coordinatewise
restriction of the stored weak derivatives defines a bounded linear map

$$`
\rho_{\Omega_2,\Omega_1}:
  W^{k,p}(\Omega_2)\longrightarrow W^{k,p}(\Omega_1).
`

Every restricted coordinate agrees almost everywhere on $`\Omega_1` with
the corresponding coordinate on $`\Omega_2`. The map is contractive:

$$`
\|\rho_{\Omega_2,\Omega_1}U\|_{W^{k,p}(\Omega_1)}
  \le \|U\|_{W^{k,p}(\Omega_2)},
\qquad
\|\rho_{\Omega_2,\Omega_1}\|\le 1.
`

Restriction to the same measurable domain is the identity. For
$`\Omega_1\subseteq\Omega_2\subseteq\Omega_3`, with both $`\Omega_1` and
$`\Omega_2` measurable,

$$`
\rho_{\Omega_2,\Omega_1}\circ\rho_{\Omega_3,\Omega_2}
  =\rho_{\Omega_3,\Omega_1}.
`
:::

:::proof "sobolev.graph_space_restriction"
Monotonicity of restricted Lebesgue measure gives the canonical contractive
map on each derivative-coordinate $`L^p` space. Restricting the test-function
identity that defines a weak derivative shows that the coordinate family
still satisfies `IsWkpOn` on the smaller domain. The coordinatewise map
therefore restricts to the graph submodule. Monotonicity of the finite
$`\ell^p` sum, or of the finite supremum when $`p=\infty`, gives contraction
of the graph norm. Identity and composition follow from the
corresponding laws for the coordinate $`L^p` restrictions.
:::

The second operator keeps the domain and forgets the derivative coordinates of
order above $`k`. The retained identities are unchanged, and omitting
coordinates can only decrease the $`\ell^p` sum or the maximum, so this map is
again contractive; it also commutes with restriction to a measurable
subdomain.

:::theorem "sobolev.graph_space_order_restriction" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.lowerOrderCLM_apply, SobolevSpace.GraphSpace.firstDerivIndex, SobolevSpace.GraphSpace.firstDerivIndex_toList, SobolevSpace.GraphSpace.DerivIndex.castOrder_firstDerivIndex, SobolevSpace.GraphSpace.DerivIndex.castOrder_singleDerivIndex, SobolevSpace.GraphSpace.norm_lowerOrderCLM_apply_le, SobolevSpace.GraphSpace.norm_lowerOrderCLM_le_one, SobolevSpace.GraphSpace.lowerOrderCLM_trans, SobolevSpace.GraphSpace.lowerOrderCLM_refl, SobolevSpace.GraphSpace.restrictCLM_lowerOrderCLM, SobolevSpace.GraphSpace.norm_lowerOrderAmbient_apply_le, SobolevSpace.GraphSpace.DerivIndex.castOrder_injective, SobolevSpace.GraphSpace.lowerOrderCLM") (uses := "sobolev.graph_space_restriction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`k\le m`, forgetting every represented derivative of order greater than
$`k` defines a continuous linear map

$$`
\pi_{m,k}:W^{m,p}(\Omega)\longrightarrow W^{k,p}(\Omega).
`

Every retained coordinate is literally the corresponding coordinate of the
original derivative bundle, and forgetting coordinates is contractive:

$$`
\|\pi_{m,k}U\|_{W^{k,p}(\Omega)}
  \le \|U\|_{W^{m,p}(\Omega)},
\qquad
\|\pi_{m,k}\|\le 1.
`

These maps satisfy
$`\pi_{k,r}\circ\pi_{m,k}=\pi_{m,r}` and $`\pi_{k,k}=\mathrm{id}`.
They also commute with restriction to measurable subdomains.
The canonical first-derivative coordinate $`\partial_i` is named uniformly
at every positive ambient order and is preserved by these order casts.
:::

:::proof "sobolev.graph_space_order_restriction"
Project the finite derivative bundle along the canonical inclusion of
multi-indices of order at most $`k` into those of order at most $`m`.
This inclusion is injective, so monotonicity of the finite $`\ell^p` sum, or
of the finite supremum when $`p=\infty`, gives contraction. The retained
weak-derivative identities are unchanged. Transitivity, reflexivity, and
commutation with domain restriction follow coordinatewise.
:::

Bounded operators between normed spaces are only half of what the variational
and compactness chapters need; they also need limits. Each graph identity is a
closed condition on the bundle, so completeness of the finite `Lp` product
passes to the graph space for every set $`\Omega` and every $`p\geq1`.

:::theorem "sobolev.graph_space_complete" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.isClosed_WkpSubmoduleOn, SobolevSpace.GraphSpace.completeSpace_WkpSpaceOn, SobolevSpace.GraphSpace.HkSpaceOn") (uses := "sobolev.graph_space") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every set $`\Omega` and every $`p\geq1`, `WkpSpaceOn n k p Ω` is complete.
Consequently it is a Banach space at both endpoints $`p=1` and
$`p=\infty` as well as in the reflexive range $`1<p<\infty`.

At $`p=2`, the ambient `PiLp` product has the coordinatewise sum inner product,
the graph submodule inherits that inner product, and completeness makes
`HkSpaceOn n k Ω = WkpSpaceOn n k 2 Ω` a Hilbert space. Openness is needed to
interpret the relation as the usual Sobolev space, not for the closed-subspace
argument itself.
:::

:::proof "sobolev.graph_space_complete"
For each symmetric derivative index $`a` and each test function supported in
$`\Omega`, subtract the two sides of the weak-derivative identity. The result
is a continuous linear functional on the finite `PiLp` bundle: its two terms
are the $`L^p`–$`L^q` pairings with $`D^a\varphi` and $`\varphi`, where
$`q` is the Hölder conjugate of $`p`. The graph submodule is the intersection
of the zero sets of all these functionals, hence is closed. A closed subspace
of the complete finite product of `Lp` spaces is complete.
:::

At $`p=2` the completeness theorem yields a Hilbert space, and the order-one
case is the one every variational chapter uses. It is given its own name,
together with the map sending a test function to its classical derivative
bundle.

:::definition "sobolev.h1_space" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.H1SpaceOn, SobolevSpace.GraphSpace.H1Space, SobolevSpace.GraphSpace.testFunctionToH1, SobolevSpace.GraphSpace.testFunctionToH1Linear") (uses := "sobolev.graph_space, sobolev.graph_space_complete")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`n` and every set $`\Omega\subseteq\mathbb R^n`, the Hilbert
Sobolev space used by the variational chapters is the order-one,
exponent-two graph space:

$$`
H^1(\Omega):=W^{1,2}(\Omega),
\qquad
\|u\|_{H^1(\Omega)}^2
  =\|u_0\|_{L^2(\Omega)}^2+\sum_{i=1}^n\|u_i\|_{L^2(\Omega)}^2 .
`

In Lean, `H1SpaceOn n Ω` is literally `WkpSpaceOn n 1 2 Ω`. An element is a
bundle $`(u_0,u_1,\ldots,u_n)` of $`L^2(\Omega)` classes in which $`u_i` is
a weak derivative of $`u_0` in direction $`i` on $`\Omega`, and the norm is
the $`\ell^2` sum of the coordinate norms. The space is
complete, hence a Hilbert space, and `H1Space n` is the whole-space case
$`\Omega=\mathbb R^n`.

A smooth compactly supported $`\varphi` whose support lies in $`\Omega`
determines the element $`(\varphi,\partial_1\varphi,\ldots,\partial_n\varphi)`
whose derivative coordinates are the classical derivatives;
`testFunctionToH1` is this map and `testFunctionToH1Linear` is its linear
form. When $`\Omega` is open this is Evans's $`H^1(\Omega)`. The definition
itself imposes no regularity on $`\Omega`; on a nonopen set it retains the
restricted-test meaning of the weak-derivative relation.
:::

The test-function map has range inside $`H^1(\Omega)`, and closing that range
in the complete space $`H^1(\Omega)` gives a closed, hence complete, subspace.
This closure is the formal replacement for the boundary condition $`u=0`
on $`\partial\Omega`; the trace chapter shows that on an operational $`C^1`
domain every element of it has zero trace.

:::definition "sobolev.h10_space" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.h10SubmoduleOn, SobolevSpace.GraphSpace.H10SpaceOn, SobolevSpace.GraphSpace.ccSmoothSubmoduleOn, SobolevSpace.GraphSpace.testFunctionToH10, SobolevSpace.GraphSpace.testFunctionToH10Linear, SobolevSpace.GraphSpace.testFunctionToH1_mem_H10, SobolevSpace.GraphSpace.mem_H10_of_tendsto_testFunctionToH1, SobolevSpace.GraphSpace.H10SpaceOn.mem_closure_CcSmooth, SobolevSpace.GraphSpace.H10SpaceOn.closed_property_of_CcSmooth, SobolevSpace.GraphSpace.denseRange_testFunctionToH10Linear") (uses := "sobolev.h1_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "259"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\iota:C_c^\infty(\Omega)\to H^1(\Omega)` be the test-function map of
{uses "sobolev.h1_space"}[], where $`C_c^\infty(\Omega)` denotes the smooth
compactly supported functions with support inside $`\Omega`. The zero-trace
space is the closure of its range:

$$`
H^1_0(\Omega)
  :=\overline{\iota\bigl(C_c^\infty(\Omega)\bigr)}^{\,H^1(\Omega)} .
`

`h10SubmoduleOn` is this closed submodule of `H1SpaceOn n Ω`, and
`H10SpaceOn n Ω` is the same submodule used as a normed type with the
restricted $`H^1` norm. It is the case $`k=1`, $`p=2` of the general
supported-core closure `wkp0SubmoduleOn`. The linked closure interface
records the defining facts used later:

- every test function lies in $`H^1_0(\Omega)`, and so does every
  $`H^1(\Omega)` limit of a sequence of test functions;
- every $`u\in H^1_0(\Omega)` lies in the closure of the test functions,
  and the canonical map $`C_c^\infty(\Omega)\to H^1_0(\Omega)` has dense
  range;
- if $`S\subseteq H^1(\Omega)` is closed and contains
  $`\iota(C_c^\infty(\Omega))`, then $`H^1_0(\Omega)\subseteq S`.

The last item is the closure principle behind every estimate that is proved
first on test functions and then extended to $`H^1_0`. For open $`\Omega`
this is Evans's $`H^1_0(\Omega)`. No boundary regularity enters the
definition.
:::

Boundary conditions on a cube should not require a smooth-boundary trace
theorem. The closure definition gives a useful criterion directly.

:::theorem "sobolev.continuous_zero_boundary" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.restrict_mem_H10_of_continuous_zero_outside, SobolevSpace.GraphSpace.tendsto_intervalTruncation_zero, SobolevSpace.GraphSpace.exists_H10_of_lipschitzWith_zero_outside, SobolevSpace.GraphSpace.mkW1pOfLipschitzCompactSupport") (uses := "sobolev.h10_space")
Let $`\Omega\subseteq\mathbb R^n` be open and let $`U\in H^1(\mathbb R^n)`
have a continuous, compactly supported representative $`f`. If
$`f(x)=0` for every $`x\notin\Omega`, then

$$`U|_\Omega\in H^1_0(\Omega).`

The boundary may have corners. The hypotheses concern a global Sobolev
function and its representative; continuity alone does not supply its weak
derivatives.

In particular, a globally Lipschitz, compactly supported function that vanishes
outside $`\Omega` gives an $`H^1_0(\Omega)` element directly. Its weak
coordinate derivatives agree almost everywhere with its classical partial
derivatives, even if the function has corners. More generally, compact
Lipschitz functions belong to every $`W^{1,p}(\mathbb R^n)` with
$`1\le p\le\infty`.
:::

:::proof "sobolev.continuous_zero_boundary"
For $`\varepsilon>0`, clamp the function to a small interval about zero:

$$`T_\varepsilon(t)=\min\{\varepsilon,\max\{-\varepsilon,t\}\}.`

Subtracting this clamp gives $`g_\varepsilon=f-T_\varepsilon\circ f`.
Its support lies in the compact superlevel set
$`\{x:|f(x)|\ge\varepsilon\}\subseteq\Omega`. Mollifying inside the
positive collar between this support and the complement of $`\Omega`
therefore puts $`g_\varepsilon|_\Omega` in $`H^1_0(\Omega)`.

As $`\varepsilon\to0`, the removed clamp converges to zero in $`L^2`.
Its weak derivative is the derivative of $`U` on
$`\{|f|<\varepsilon\}` and zero elsewhere. The derivative of $`U`
vanishes almost everywhere on $`\{f=0\}` by the level-set theorem, so
dominated convergence also sends the derivative error to zero. Thus
$`g_\varepsilon\to U` in $`H^1`, and the closedness of
$`H^1_0(\Omega)` finishes the proof.

For the Lipschitz case, Rademacher's theorem supplies differentiability almost
everywhere. The derivative is bounded by the Lipschitz constant and is
compactly supported, so every derivative row belongs to $`L^p`, including
$`L^\infty`. The weak derivative identity gives the global Sobolev element
to which the zero-exterior criterion applies.
:::

The representative model and the graph model describe the same functions with
different data, and the chapter needs to pass between them: pointwise formulas
are proved on representatives, while operators act on graph elements. In one
direction the passage is canonical; in the other it requires choosing
derivative representatives.

:::definition "sobolev.model_bridge" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.toRepresentative, SobolevSpace.GraphSpace.ofRepresentative") (uses := "sobolev.representative_space, sobolev.graph_space, sobolev.symmetric_derivative_index") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
`toRepresentative` reads the `Lp` representative of the base coordinate of a
graph-space element and uses the derivative coordinates to certify every
ordered derivative word. Each word is read through its symmetric index, and the
permutation theorem carries the stored identity back to the word.

`ofRepresentative` goes in the other direction, for exponents at least one. It keeps the given base
function, chooses one $`L^p` weak-derivative representative for every symmetric
index, and sends those functions to their `Lp` classes. This map is
noncomputable because `SobolevSpaceOn` asserts the existence of derivatives
rather than selecting canonical ones.
:::

How much survives a round trip is dictated by two facts. Reading the base
coordinate of an `Lp` class recovers a function only almost everywhere, and
the derivative representatives chosen by
`ofRepresentative` can be identified with the stored coordinates only through
uniqueness, hence only on an open domain.

:::theorem "sobolev.model_bridge_round_trip" (parent := "sobolev.weak") (lean := "SobolevSpace.GraphSpace.toRepresentative_ofRepresentative_toFun_ae, SobolevSpace.GraphSpace.ofRepresentative_toRepresentative") (uses := "sobolev.model_bridge, sobolev.weak_derivative_unique") (autoDeps := true)
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "258-263"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The two round trips have the exact strengths forced by the models.

For every set $`\Omega`, converting a `SobolevSpaceOn` value to graph space
and reading the base coordinate back recovers the original function almost
everywhere on $`\Omega`.

If $`\Omega` is open, converting a graph-space element to a representative
and back is exactly the original graph-space element. Openness is needed:
without it weak derivatives need not be unique, so different choices can
yield different derivative coordinates.
:::

:::proof "sobolev.model_bridge_round_trip"
The first statement is the defining almost-everywhere property of `MemLp.toLp`.
For the second, compare one symmetric coordinate at a time. The reconstructed
base coordinate agrees almost everywhere with the original one. Transport the
reconstructed weak-derivative identity across that equality, then use
open-domain uniqueness to identify the reconstructed derivative with the
original coordinate almost everywhere. Equality in `Lp`, followed by
extensionality of the finite product and the graph subtype, gives exact
equality.
:::
