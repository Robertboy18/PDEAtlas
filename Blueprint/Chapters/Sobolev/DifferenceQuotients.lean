/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Inequalities
import Blueprint.Commands.Figures
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.FiniteDifferences
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalConverse
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Difference quotients

Finite-difference estimates and weak-derivative characterizations.
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
#doc (Manual) "Difference Quotients" =>

Difference quotients recover differential information from translations.
For a function $`u` and a coordinate direction $`e_i`, the forward quotient

$$`
D_i^h u(x)=\frac{u(x+h e_i)-u(x)}{h}
`

is meaningful before a weak derivative of $`u` has been constructed. This is
why the method is so effective in weak PDE arguments: one first translates
the weak equation, derives an energy estimate for $`D_i^h u`, and only then
uses compactness to obtain $`\partial_i u`.

For a smooth formula, $`D^h(x^2)=2x+h` tends to the expected derivative.
A jump behaves very differently. Take $`u=\mathbf1_{(0,1)}` on the real
line and $`0<h<1`. The quotient is $`1/h` on $`(-h,0]` and $`-1/h`
on $`[1-h,1)`, and is zero elsewhere. Hence, for finite $`p\geq1`,

$$`
\|D^h u\|_{L^p(\mathbb R)}
=2^{1/p}h^{1/p-1}.
`

For $`p>1` this blows up as $`h\downarrow0`; a uniform quotient estimate
would rule out this jump. At $`p=1` the norm stays equal to two, although
the derivative is the measure $`\delta_0-\delta_1`, not an $`L^1`
function. This is the endpoint obstruction to a converse criterion at
$`p=1`.

{leanpde_figure "difference-quotient-limit"}

In the figure the corner of a tent costs only a ramp of width $`h`, and the
quotients converge to the weak derivative in $`L^2`. The jump produces two
spikes of height $`1/h`, whose $`L^2` norm grows while their $`L^1` norm
stays at two.

The pointwise quotient is a function-level expression; the analytic quotient
is a bounded linear operator on the global $`L^p` model. The forward theory
holds at every finite exponent $`p\geq1`: the quotient of a Sobolev function
is bounded by one weak-derivative coordinate with constant one and converges
strongly to it. The converse needs weak compactness. It is proved at $`p=2`
on the whole space, in a localized form for interior regularity, and with
the gradient bound for $`1<p<\infty` on open sets.

Elliptic regularity combines these quotient estimates with discrete
integration by parts and the translated-coefficient Leibniz rule. Lipschitz
coefficient bounds control the extra terms; the localized $`L^2` converse
then recovers the weak derivative from the resulting energy estimate.

:::group "sobolev.difference_quotients"
Difference quotients
:::

:::definition "sobolev.forward_difference" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.forwardDifference")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a coordinate $`i`, a real step $`h`, and a scalar-valued function $`f`,
the pointwise forward difference is

$$`
D_i^h f(x)=\frac{f(x+h e_i)-f(x)}{h}.
`

The coordinate step is $`h e_i`, with the sign convention fixed by the
translated value $`f(x+h e_i)`. This convention determines every later sign,
including the appearance of the backward quotient $`D_i^{-h}` in discrete
integration by parts.

The definition is total at $`h=0`; it then evaluates using Lean's total
inverse. Statements that divide by the geometric length of the step assume
$`h\ne0`.
:::

The pointwise formula depends on the representative: changing $`f` on a null
set changes $`D_i^hf` on the translate of that null set as well. On $`L^p`
classes the quotient is instead defined through the translation operator,
and the almost-everywhere agreement theorem shows that the two descriptions
coincide on the whole-space model.

:::definition "sobolev.difference_quotient_operator" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.differenceQuotientLp, SobolevSpace.GraphSpace.DifferenceQuotient.differenceQuotientLp_apply_ae") (uses := "sobolev.forward_difference, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`1\le p\le\infty`. On the global $`L^p(\mathbb R^n)` model, the
coordinate difference quotient is the continuous linear map

$$`
\mathcal D_{i,h}^{(p)}
  = h^{-1}\bigl(\tau_{h e_i}-I\bigr),
`

where $`\tau_a u(x)=u(x+a)`. For every $`L^p` class $`u`, its representative
satisfies

$$`
\bigl(\mathcal D_{i,h}^{(p)}u\bigr)(x)
  =h^{-1}\bigl(u(x+h e_i)-u(x)\bigr)
\quad\text{for almost every }x.
`

Thus the bundled operator agrees almost everywhere with the pointwise
formula, while remaining independent of the chosen representative. The
operator is defined only on the whole-space model in this chapter because
translation need not preserve a proper domain.

At $`h=0` the bundled map is also total, but no derivative meaning is assigned
to that value. The elementary operator bound behaves like $`2|h|^{-1}` and is
therefore useful only away from zero. The uniform estimate near zero comes
from Sobolev regularity, not from boundedness of translation alone.
:::

Because the bundled quotient is built from translations, its adjoint on
$`L^2` can be computed exactly: translation by $`he_i` is unitary, with
adjoint translation by $`-he_i`. The resulting identity is the discrete
replacement for integration by parts, and it is what the converse criteria
later pair against test functions.

:::theorem "sobolev.difference_quotient_discrete_ibp" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.inner_differenceQuotientL2_left") (uses := "sobolev.difference_quotient_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`u,v\in L^2(\mathbb R^n)` and $`h\ne0`,

$$`
\left\langle D_i^h u,v\right\rangle_{L^2}
  =-\left\langle u,D_i^{-h}v\right\rangle_{L^2}.
`

The adjoint of the forward quotient is therefore the negative backward
quotient. Using $`D_i^h` on both sides would be a sign-and-translation error.
The identity has no boundary term because it is proved on all of
$`\mathbb R^n`.
:::

:::proof "sobolev.difference_quotient_discrete_ibp"
Translation by $`a` is unitary on $`L^2`, and its adjoint is translation by
$`-a`:

$$`
\langle\tau_a u,v\rangle=\langle u,\tau_{-a}v\rangle.
`

Expand $`h^{-1}(\tau_{h e_i}-I)`, move the translation to the second slot,
and use $`(-h)e_i=-(h e_i)`. The scalar identity
$`(-h)^{-1}=-h^{-1}` gives the displayed minus sign.
:::

Elliptic regularity applies difference quotients to products $`au` with a
variable coefficient, so a product rule is needed. Since $`D_i^h` is built
from a translation rather than a derivative, the rule is exact but carries
the translated coefficient $`\tau_{he_i}a` on the principal term.

:::theorem "sobolev.difference_quotient_leibniz" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.differenceQuotientL2_lpSMul") (uses := "sobolev.difference_quotient_operator")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`a\in L^\infty(\mathbb R^n)` and $`u\in L^2(\mathbb R^n)`. For every
real step $`h`, the exact product rule in $`L^2` is

$$`
D_i^h(a u)
  =(\tau_{h e_i}a)\,D_i^h u+(D_i^h a)\,u.
`

The coefficient multiplying the principal difference is translated. Replacing
$`\tau_{h e_i}a` by $`a` would omit the commutator created by the forward
difference convention. The theorem is an equality of bundled $`L^2` classes
and is valid at $`h=0` because all operations are total.
:::

:::proof "sobolev.difference_quotient_leibniz"
At the representative level, insert and subtract
$`a(x+h e_i)u(x)`:

$$`
a(x+h e_i)u(x+h e_i)-a(x)u(x)
=a(x+h e_i)\bigl(u(x+h e_i)-u(x)\bigr)
 +\bigl(a(x+h e_i)-a(x)\bigr)u(x).
`

The formal proof transports this algebra through almost-everywhere
representatives of translation, subtraction, scalar multiplication, and the
$`L^\infty` action on $`L^2`.
:::

The commutator term $`(D_i^ha)\,u` in the product rule is harmless only if
$`D_i^ha` is bounded uniformly in $`h`. That is a Lipschitz property of the
coefficient, not a property of its $`L^\infty` class, and it holds with the
Lipschitz constant itself whenever $`a` has a Lipschitz representative.

:::theorem "sobolev.difference_quotient_lipschitz_coefficient" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.differenceQuotientLp_top_eq_coefficientDifferenceLInf, SobolevSpace.GraphSpace.DifferenceQuotient.norm_differenceQuotientLp_top_le") (uses := "sobolev.difference_quotient_operator, sobolev.difference_quotient_leibniz")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose an $`L^\infty` coefficient class $`a` has a representative
$`f:\mathbb R^n\to\mathbb R` which is Lipschitz with constant $`C`, and
$`a=f` almost everywhere. For every $`h\ne0`,

$$`
\|D_i^h a\|_{L^\infty}\le C.
`

More precisely, the abstract $`L^\infty` quotient is equal to the bundled
class built directly from the Lipschitz representative.

Together with the exact Leibniz rule, this gives uniform control of the
coefficient commutator term $`(D_i^h a)u` in $`L^2`.
:::

:::proof "sobolev.difference_quotient_lipschitz_coefficient"
Translation preserves null sets, so the almost-everywhere identity $`a=f`
remains valid after composition with $`x\mapsto x+h e_i`. Hence the abstract
quotient and the concrete quotient of $`f` agree almost everywhere.
Lipschitz continuity gives

$$`
|f(x+h e_i)-f(x)|\le C|h e_i|=C|h|,
`

and division by $`|h|` yields the $`L^\infty` bound.
:::

For an arbitrary $`L^p` class, the elementary quotient bound deteriorates
as $`h\to0`. Sobolev regularity gives uniform bounds for the field itself.
For $`u\in H^1_0(\Omega)`, the zero extension is a global $`H^1` function,
and its translation defect is controlled by the $`H^1_0` norm.

:::theorem "sobolev.zero_extension_difference_quotient" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.differenceQuotientL2.zeroExtend_base_norm_le") (uses := "sobolev.difference_quotient_operator, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega\subseteq\mathbb R^n` be measurable, let
$`u\in H_0^1(\Omega)`, and extend $`u` by zero to all of $`\mathbb R^n`.
For every coordinate $`i` and every $`h\ne0`,

$$`
\|D_i^h\widetilde u\|_{L^2(\mathbb R^n)}
  \le \|u\|_{H_0^1(\Omega)}.
`

The statement concerns the base coordinate of the global Sobolev zero
extension. It avoids extending an arbitrary $`H^1(\Omega)` function by zero:
without the zero-trace hypothesis such an extension may acquire a boundary
distribution and need not belong to $`H^1(\mathbb R^n)`.
:::

:::proof "sobolev.zero_extension_difference_quotient"
The zero-extension translation-defect estimate gives

$$`
\|\tau_a\widetilde u-\widetilde u\|_2
  \le |a|\,\|u\|_{H_0^1(\Omega)}.
`

Take $`a=h e_i`, use $`|h e_i|=|h|`, and divide by $`|h|`. The nonzero-step
hypothesis is used exactly in cancelling this factor.
:::

On the whole space the bound can be sharpened: a single weak-derivative
coordinate replaces the graph norm on the right.

:::theorem "sobolev.difference_quotient_forward_estimate" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.norm_differenceQuotientLp_base_le_deriv_of_ne_top") (uses := "sobolev.difference_quotient_operator, sobolev.weak_derivative, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`p\in[1,\infty]` be an extended-real exponent satisfying
$`p\ne\infty`, let $`U\in W^{1,p}(\mathbb R^n)`, and let $`h\ne0`.
For every coordinate $`i`,

$$`
\|D_i^h U_0\|_{L^p(\mathbb R^n)}
\le \|U_i\|_{L^p(\mathbb R^n)}.
`

Here $`U_0` is the bundled base coordinate and $`U_i` is its selected weak
derivative in direction $`i`. The constant is exactly one. In particular,
the theorem is stronger than the coarser estimate
$`\|D_i^hU_0\|_p\le\|U\|_{W^{1,p}}`.

The exponent is not restricted syntactically to the form
$`\operatorname{ofReal}(r)`. The theorem accepts any finite extended-real
exponent carrying the standard $`1\le p` instance.
:::

:::proof "sobolev.difference_quotient_forward_estimate" (uses := "sobolev.global_density")
For a compactly supported smooth function $`f`, the one-dimensional
fundamental theorem of calculus along the coordinate segment gives

$$`
D_i^h f(x)=\int_0^1\partial_i f(x+t h e_i)\,dt.
`

Convexity of $`|\cdot|^p`, Jensen's inequality in $`t`, Tonelli–Fubini, and
translation invariance of Lebesgue measure give

$$`
\|D_i^h f\|_p^p\le\|\partial_i f\|_p^p.
`

The endpoint $`p=1` is included; no reflexivity is used in the forward
argument. Global smooth density supplies a sequence of compactly supported
smooth graph-space elements converging to $`U`. The set

$$`
\{V:\|D_i^hV_0\|_p\le\|V_i\|_p\}
`

is closed because both coordinates are continuous. Passing to the limit
therefore preserves the sharp inequality without introducing a larger
constant.
:::

The constant-one estimate does more than bound the quotients: it makes the
family of quotient operators equicontinuous, uniformly in the step, which
upgrades convergence on a dense set to strong convergence for every $`U`.

:::theorem "sobolev.difference_quotient_forward_convergence" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.tendsto_differenceQuotientLp_base_of_ne_top") (uses := "sobolev.difference_quotient_forward_estimate")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same finite-exponent hypotheses, let $`h_m\to0` and assume every
$`h_m\ne0`. Then

$$`
D_i^{h_m}U_0\longrightarrow U_i
\quad\hbox{strongly in }L^p(\mathbb R^n).
`

This is convergence in the norm topology of the bundled $`L^p` space.
:::

:::proof "sobolev.difference_quotient_forward_convergence" (uses := "sobolev.global_density")
For compactly supported smooth functions, pointwise convergence follows from
the one-dimensional derivative along $`x+t e_i`. For all sufficiently small
steps, the quotients are dominated by a bounded function supported in a fixed
compact enlargement of the original support, so dominated $`L^p`
convergence applies.

For general Sobolev data, write

$$`
T_mU=D_i^{h_m}U_0,\qquad DU=U_i.
`

The sharp estimate implies $`\|T_m\|\le1` uniformly in $`m`; hence the family
$`(T_m)` is equicontinuous. The set of $`U` for which $`T_mU\to DU` is closed.
Since global smooth density places a dense subset in that closed set, it is
the whole space. This closed-set argument avoids choosing a density
approximation depending on $`m`.
:::

The converse direction asks whether bounded difference quotients force the
existence of a weak derivative. At $`p=2` the answer is yes, by weak
compactness of bounded sets in the Hilbert space $`L^2` together with the
discrete integration-by-parts identity.

:::theorem "sobolev.one_coordinate_difference_quotient_criterion" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm") (uses := "sobolev.difference_quotient_discrete_ibp, sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix a coordinate $`i`. Let $`u\in L^2(\mathbb R^n)`, let $`h_m\to0` with
$`h_m\ne0`, and suppose

$$`
\|D_i^{h_m}u\|_2\le C
\qquad\text{for every }m.
`

Then there exists $`g\in L^2(\mathbb R^n)` such that

$$`
\|g\|_2\le C
`

and $`g` is the weak derivative $`\partial_i u` on $`\mathbb R^n`. The norm
bound is part of the conclusion.
:::

:::proof "sobolev.one_coordinate_difference_quotient_criterion" (uses := "analysis.weak_compactness.norm_bound")
The bounded quotient sequence has a weakly convergent ultrafilter refining
the tail filter. Write $`g` for its weak limit. For a test function $`\varphi`,
discrete integration by parts gives

$$`
\langle D_i^{h_m}u,\varphi\rangle
  =-\langle u,D_i^{-h_m}\varphi\rangle.
`

The left side converges to $`\langle g,\varphi\rangle` by weak convergence.
The backward quotients of the smooth test function converge strongly in
$`L^2` to $`\partial_i\varphi`, so the right side converges to
$`-\langle u,\partial_i\varphi\rangle`. This is exactly the weak-derivative
identity. Weak lower semicontinuity of the norm yields $`\|g\|_2\le C`.

No subsequence is selected: the compactness theorem returns an ultrafilter
$`\mathcal U` with $`\mathcal U\le\operatorname{atTop}`. This is enough
because every ordinary limit along $`\operatorname{atTop}` also holds along
$`\mathcal U`.
:::

Applying the one-coordinate criterion in each direction produces $`n` weak
derivatives of the same class $`u`, which are exactly the data needed to
assemble a first-order graph-space element.

:::theorem "sobolev.difference_quotient_criterion" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.exists_H1_of_bounded_differenceQuotients") (uses := "sobolev.one_coordinate_difference_quotient_criterion, sobolev.graph_space")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`u\in L^2(\mathbb R^n)` and let $`h_m\to0` with every $`h_m\ne0`.
Assume that for each coordinate $`i` there is a constant $`C_i` such that

$$`
\|D_i^{h_m}u\|_2\le C_i
\qquad\text{for every }m.
`

Then there exists $`U\in H^1(\mathbb R^n)` whose bundled base coordinate is
equal almost everywhere to $`u`.

The constants may depend on the coordinate but not on $`m`. The conclusion
is existence of a bundled $`H^1` representative, with no bound on its full
$`H^1` norm; coordinatewise derivative bounds come from the one-coordinate
theorem.

This is the sequential global converse at $`p=2`. For $`1<p<\infty` the
{bpref "sobolev.local_difference_quotient_converse"}[local converse] also
keeps the gradient bound.
:::

:::proof "sobolev.difference_quotient_criterion"
Apply the one-coordinate criterion separately to each $`i` to obtain
$`g_i\in L^2` and the weak-derivative identity for $`\partial_i u`. Build the
order-one graph-space family by assigning $`u` to the empty derivative index
and $`g_i` to the singleton index $`[i]`. There are no higher-order indices at
order one. The base identity is inherited from the chosen $`L^2` class, and
the coordinate weak-derivative identities prove membership in the closed
Sobolev graph subspace.
:::

For $`1<p<\infty` the same conclusion holds on an open set, with the gradient
bound kept. Write $`D^hu=(D_1^hu,\ldots,D_n^hu)` for the vector of forward
quotients. At $`x\in V` it reads $`u(x+he_i)`, which may lie outside $`V`, so
$`u` is a function on all of $`\mathbb R^n`.

:::theorem "sobolev.local_difference_quotient_converse" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.exists_sobolev_of_bounded_vectorDifference, SobolevSpace.GraphSpace.DifferenceQuotient.exists_sobolev_of_vectorDifference_sequence") (uses := "sobolev.difference_quotient_criterion, sobolev.graph_space")
Let $`1<p<\infty`, let $`V\subseteq\mathbb R^n` be open, and let
$`u:\mathbb R^n\to\mathbb R` lie in $`L^p(V)`. Suppose there are
$`\delta>0` and $`C\ge0` with

$$`
\|D^hu\|_{L^p(V)}\le C
\qquad\text{for every }0<|h|<\delta.
`

Then there is $`U\in W^{1,p}(V)` whose base coordinate equals $`u` almost
everywhere on $`V` and whose full gradient satisfies
$`\|\nabla U\|_{L^p(V;\mathbb R^n)}\le C`.
The same holds when the bound is assumed only along one nonzero sequence
$`h_m\to0`.
:::

:::proof "sobolev.local_difference_quotient_converse"
Take $`h_m\to0` inside $`(0,\delta)`. Euclidean-valued $`L^p(V)` is
reflexive, so the bounded quotients have a weakly convergent refinement,
whose limit has norm at most $`C`. Pairing with compactly supported tests in
$`V` and moving the quotient onto the test identifies the coordinates of the
limit as the weak derivatives of $`u`.
:::

In interior regularity the quotient bound is available only after
multiplication by a cutoff, so the hypothesis becomes a bound on
$`q\,D_i^{h_m}u` rather than on $`D_i^{h_m}u` itself. The multiplier
hypothesis is stated exactly, as an identity action on test functions
supported in $`V`, rather than derived from a collar condition on a cutoff,
so the theorem holds for an arbitrary set $`V`.

:::theorem "sobolev.localized_difference_quotient_criterion" (parent := "sobolev.difference_quotients") (lean := "SobolevSpace.GraphSpace.DifferenceQuotient.exists_L2_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm") (uses := "sobolev.difference_quotient_discrete_ibp, sobolev.weak_derivative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "291-293"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Fix a coordinate $`i`, an arbitrary set $`V\subseteq\mathbb R^n`,
$`u\in L^2(\mathbb R^n)`, and a multiplier
$`q\in L^\infty(\mathbb R^n)`. Let $`h_m\to0`, with every $`h_m\ne0`.
Assume

$$`
\|q\,D_i^{h_m}u\|_2\le C
\qquad\text{for every }m,
`

and assume that for every smooth compactly supported test function
$`\varphi` with $`\operatorname{tsupp}\varphi\subseteq V`,

$$`
q\varphi=\varphi
\quad\text{as an }L^2\text{ class}.
`

Then there exists $`g\in L^2(\mathbb R^n)` with $`\|g\|_2\le C`
satisfying the integration-by-parts relation against every such test
function. For open $`V`, this says that $`g` is the usual weak derivative
$`\partial_i u`. On an arbitrary set, the test class can be trivial and
uniqueness need not hold.

The test relation is defined without a measurability or openness hypothesis
on $`V`. It uses integrals restricted to $`V`; compact support of the test
function and its derivative permits the global pairing identities to be
restricted to that set.

The multiplier hypothesis is semantic and exact. A smooth cutoff equal to one
pointwise on $`V` satisfies it, but the theorem also accepts any bounded
multiplier with the same action on supported test vectors. Conversely,
membership of $`q` in $`L^\infty` alone is not enough.
:::

:::proof "sobolev.localized_difference_quotient_criterion" (uses := "analysis.weak_compactness.norm_bound")
Apply Hilbert weak compactness to

$$`
s_m=q\,D_i^{h_m}u
`

and let $`g` be the weak ultrafilter limit. For a test function $`\varphi`
supported in $`V`, self-adjointness of real $`L^\infty` multiplication and
the identity action of $`q` give

$$`
\langle s_m,\varphi\rangle
 =\langle D_i^{h_m}u,q\varphi\rangle
 =\langle D_i^{h_m}u,\varphi\rangle.
`

Discrete integration by parts changes the last expression to
$`-\langle u,D_i^{-h_m}\varphi\rangle`. Strong convergence of the test-function
quotients identifies the limit with
$`-\langle u,\partial_i\varphi\rangle`. Weak lower semicontinuity gives the
norm bound.

Finally, both integrands vanish off $`V`: the support of $`\varphi` lies in
$`V`, and the support of $`\partial_i\varphi` lies in the topological support
of $`\varphi`. Therefore the whole-space integral identity is exactly the
weak-derivative identity over $`V`.
:::
