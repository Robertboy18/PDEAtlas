/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.Enclosures
import Blueprint.Commands.Figures
import CAS.Continuum.IntervalEval.Registry.Planner
import CAS.Continuum.ExprAdaptiveTaylor
import CAS.Continuum.ModelTreePayload
import CAS.Continuum.TaylorJet

/-!
## Taylor models

Taylor-model approximation and certified remainder enclosures.
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
#doc (Manual) "Taylor Models" =>

Taylor models combine a finite polynomial with a uniform remainder theorem on
an explicit interval. We keep three errors distinct: analytic
truncation, uncertainty in the polynomial coefficients, and any roundoff used
to evaluate the polynomial. A final certificate may add them, and each is
bounded by its own theorem.

{leanpde_figure "taylor-model"}

We return to the rational function used in the interval-enclosure figure.
Subdivision narrowed the input intervals; a retained polynomial keeps
algebraic dependence that a single interval would discard. The remainder
panel uses its own vertical scale, making the difference visible even where
the function and polynomial nearly coincide. A model needs a uniform bound
on that difference throughout the stated interval; agreement at sampled
points alone cannot supply it.

Uniform approximation of values does not by itself certify derivatives.
For $`\varepsilon>0` and $`k>0`, the smooth error
$`e(x)=\varepsilon\sin(kx)` obeys
$`|e(x)|\leq\varepsilon`, while $`|e'(0)|=\varepsilon k` can be as
large as we choose. Consequently, differentiating the polynomial in a model
does not automatically give an equally accurate model of the derivative.
For a PDE residual involving derivatives, we need certificates for those
derivatives or a direct residual certificate, with the analytic regularity
needed to interpret them. The derivative-bound and symbolic-calculus results
supply these alongside the value models.

*A concrete polynomial and remainder for the exponential.*

FloatLib's small-argument exponential theorem gives a direct example of
analytic truncation. For a rational $`q` with $`|q|\leq1`, choose a degree
$`d\in\mathbb N` and put $`n=d+1`. Its polynomial and radius are

$$`T_n(q)=\sum_{k<n}\frac{q^k}{k!},
\qquad
R_n(q)=\frac{|q|^n\,(n+1)}{n!\,n}.`

Both are exact rationals. As a hand specialization, $`d=2` gives $`n=3`,
$`T_3(q)=1+q+q^2/2`, and $`R_3(q)=2|q|^3/9\leq2/9`. The radius bounds the
truncation error at rational points with $`|q|\leq1`; the general Taylor-model
constructors supply uniform approximation certificates from derivative bounds
at arbitrary real inputs.

:::definition "symbolic.model_certificate" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate") (lean := "CAS.Certificate.ModelApproxCert")
A model-approximation certificate records an original function, a reference
function, model-order metadata, an error budget, and the proved uniform error
estimate. Writing its source as $`f`, its model as $`p`, its domain as $`S`,
and its error as $`\varepsilon`, the trusted field is

$$`\forall x\in S,\qquad \lVert f(x)-p(x)\rVert\leq\varepsilon.`

The stored order does not occur in this proposition; it is metadata. A
supplied model need not be a Taylor polynomial or have a finite-dimensional
representation, and such structure requires a separate construction.
:::

:::theorem "symbolic.taylor_example" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "FloatLib.Numerics.Enclosure.abs_exp_sub_expTaylor_le, FloatLib.Numerics.Enclosure.contains_expSmall")
For every rational $`q` with $`|q|\leq1` and every degree $`d`, FloatLib's
`expSmall q d` encloses $`\exp q`. With $`n=d+1`, the polynomial
$`T_n(q)` has absolute error at most $`R_n(q)`, so the real exponential lies
between the exact rational endpoints $`T_n(q)-R_n(q)` and $`T_n(q)+R_n(q)`.
:::

:::proof "symbolic.taylor_example"
FloatLib identifies its rational Taylor sum and error radius with their real
counterparts, then applies Mathlib's `Real.exp_bound` with $`d+1` terms.
The hypothesis $`|q|\leq1` gives the bound
$`|\exp q-T_n(q)|\leq R_n(q)`. Its `contains_expSmall` theorem expresses
that absolute-error estimate as interval containment. CEGA reuses the upstream
kernel through its exponential range adapter.
:::

:::theorem "symbolic.generated_taylor_certificate" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate") (lean := "CAS.Continuum.scalarTaylorPolynomialWithin_eval, CAS.Continuum.scalarTaylorPolynomialWithin_natDegree_le, CAS.Continuum.taylorApproxCert")
For an ordinary scalar function on an ordered closed interval, we build
the actual order-$`n` Taylor polynomial from within-derivatives, prove that its
evaluation is Mathlib's Taylor evaluation, and prove that its degree is at
most $`n`. Assuming $`C^{n+1}` regularity on that interval, a bound $`C` on
the norm of the $`(n+1)`-st within-derivative produces an
`ApproxCert` with uniform error
$`C(b-a)^{n+1}/n!`, the conservative remainder supplied by Mathlib's
mean-remainder theorem.
:::

:::proof "symbolic.generated_taylor_certificate"
The finite polynomial is the sum of the within-derivative coefficients through
order $`n`, so its evaluation agrees term by term with Mathlib's Taylor
evaluation and its degree is at most $`n`. Mathlib's mean-remainder theorem,
together with the supplied next-derivative bound, gives the uniform error,
which is the `sound` field of the approximation certificate.
:::

:::definition "symbolic.compositional_model_calculus" (parent := "symbolic.cega") (uses := "symbolic.model_certificate, symbolic.approx_certificate") (lean := "CAS.Certificate.ApproxCert.add, CAS.Certificate.ApproxCert.sub, CAS.Certificate.ApproxCert.neg, CAS.Certificate.ApproxCert.mulRealOfBoundCerts")
Finite-model approximations compose through the canonical `ApproxCert`
calculus after projecting a `ModelApproxCert` to its stored certificate. If
$`f` and $`g` are approximated on $`S` by $`p` and $`q` with errors
$`\varepsilon` and $`\delta`, respectively, then the additive rules prove

$$`\begin{aligned}
f+g&\sim_{\varepsilon+\delta}p+q,&
f-g&\sim_{\varepsilon+\delta}p-q,&
-f&\sim_{\varepsilon}-p.
\end{aligned}`

For real-valued functions, checked bounds $`|f(x)|\leq A` and
$`|q(x)|\leq B` give the nonlinear rule

$$`fg\sim_{A\delta+B\varepsilon}pq\qquad\text{on }S.`

Here $`u\sim_\eta v` abbreviates
$`\forall x\in S,\ \lVert u(x)-v(x)\rVert\leq\eta`. The rules act on the
underlying `ApproxCert`; model-order metadata can be reattached afterwards.
:::

*Finite Taylor jets.*

The jet uses the real coefficients $`c_0,\ldots,c_n` to define the finite
polynomial $`\sum_{k=0}^{n}c_k(x-a)^k`. The certificate accepts a real-valued
coefficient function; it does not require a rational or floating-point encoding.
We prove three separate statements: exact coefficients recover the mathematical
Taylor polynomial, coefficient intervals bound the perturbation of that
polynomial, and a bound on the next derivative controls the analytic remainder.
Only after those statements are available are their two error budgets added.

*Reading a `TaylorJetCert`.*

For order $`n=2` on $`[a,b]` with $`a\leq b`, a `TaylorJetCert` stores coefficients
$`c_0,c_1,c_2`, coefficient uncertainties
$`\delta_0,\delta_1,\delta_2`, and a bound $`C` for the third within-derivative.
Its model is

$$`q(x)=c_0+c_1(x-a)+c_2(x-a)^2.`

The certificate keeps the error calculation visible:

$$`\begin{aligned}
E_{\mathrm{coeff}}
  &=\delta_0+\delta_1(b-a)+\delta_2(b-a)^2,\\
E_{\mathrm{rem}}
  &=C\frac{(b-a)^3}{2!},\\
E_{\mathrm{jet}}
  &=E_{\mathrm{rem}}+E_{\mathrm{coeff}}.
\end{aligned}`

The coefficient inequalities prove that the exact Taylor polynomial is within
$`E_{\mathrm{coeff}}` of `q`. The derivative bound and `ContDiffOn`
hypothesis prove that the source function is within $`E_{\mathrm{rem}}` of
the exact Taylor polynomial. Adding the two error bounds gives

$$`\forall x\in[a,b],\qquad |f(x)-q(x)|\leq E_{\mathrm{jet}}.`

:::theorem "symbolic.taylor_jet_exact_semantics" (parent := "symbolic.cega") (uses := "symbolic.generated_taylor_certificate") (lean := "CAS.Continuum.taylorJetEval_exact")
Let
$`c_k=(k!)^{-1}D^k_{[a,b]}f(a)` be the exact within-derivative coefficient.
For every real $`x`, evaluating the finite power-basis jet gives exactly
Mathlib's scalar Taylor polynomial:

$$`\sum_{k=0}^{n}c_k(x-a)^k
   =T^{[a,b]}_{n,a}f(x).`

Thus the finite coefficient sum and the analytic object used by the remainder
theorem have the same real semantics.
:::

:::proof "symbolic.taylor_jet_exact_semantics"
Expand the finite real jet as its coefficient sum and substitute the definition
$`c_k=D^k_{[a,b]}f(a)/k!`. The resulting finite sum is exactly the definition
of Mathlib's scalar Taylor evaluation, so the two functions agree for every $`x`.
:::

:::definition "symbolic.compiled_taylor_derivative_family" (parent := "symbolic.cega") (uses := "symbolic.partial_derivative_bridge, symbolic.interval_bridge") (lean := "CAS.Continuum.CompiledTaylorJet.derivative, CAS.Continuum.RationalInterval.compileTaylorJet?")
The Taylor compiler constructs the derivatives of orders zero through
$`n+1` under one checked validity certificate. It fails when the panel crosses
an unsupported branch boundary or when rational canonicalization cannot prove
its generated side conditions. Each compiled derivative reuses its canonical
derivative object and adds only the panel orientation and analytic-validity
route. A successful result exposes every derivative through this same checked
interface.
:::

:::theorem "symbolic.taylor_coefficient_perturbation" (parent := "symbolic.cega") (uses := "symbolic.taylor_jet_exact_semantics") (lean := "CAS.Continuum.approxOn_taylorJetEval_of_coefficient_bounds, CAS.Continuum.TaylorJetCert.coefficients_approx")
Suppose the stored coefficient $`c_k` is within $`\delta_k\geq0` of the exact
Taylor coefficient $`c_k^\ast` for $`0\leq k\leq n`. For the stored jet
$`q_n(x)=\sum_{k=0}^{n}c_k(x-a)^k`, the coefficient bounds imply

$$`\forall x\in[a,b],\qquad
\left|T^{[a,b]}_{n,a}f(x)-q_n(x)\right|
\leq\sum_{k=0}^{n}\delta_k(b-a)^k.`

This estimate contains coefficient uncertainty only.
:::

:::proof "symbolic.taylor_coefficient_perturbation"
Subtract the two finite power series term by term and apply the triangle
inequality. Each coefficient difference is at most $`\delta_k`, while
$`|x-a|^k\leq(b-a)^k` on the ordered interval. Summing these bounds gives the
displayed perturbation estimate.
:::

:::theorem "symbolic.taylor_remainder_bound" (parent := "symbolic.cega") (uses := "symbolic.generated_taylor_certificate") (lean := "CAS.Continuum.TaylorJetCert.remainder_approx")
A uniform bound on the $`(n+1)`-st within derivative, together with the
certificate's $`C^{n+1}` regularity on the ordered interval, gives the analytic
remainder between the source function and its exact Taylor polynomial. This
term contains no coefficient uncertainty and no runtime roundoff.
:::

:::proof "symbolic.taylor_remainder_bound"
Apply the within-interval Taylor remainder theorem at the left endpoint.
The supplied uniform bound on the next derivative controls the remainder
factor, and $`|x-a|\leq b-a` makes the estimate uniform over the panel.
:::

:::theorem "symbolic.taylor_jet_certificate" (parent := "symbolic.cega") (uses := "symbolic.model_certificate, symbolic.interval_bridge, symbolic.taylor_coefficient_perturbation, symbolic.taylor_remainder_bound") (lean := "CAS.Continuum.TaylorJetCert.sound, CAS.Continuum.TaylorJetCert.ofDerivativeEnclosures, CAS.Continuum.TaylorJetCert.toModelApproxCert")
The combined certificate converts derivative enclosures into coefficient
centers $`c_k`, coefficient radii $`\delta_k`, and a bound $`C` on the
$`(n+1)`-st within derivative. For
$`q_n(x)=\sum_{k=0}^{n}c_k(x-a)^k`, its soundness theorem is

$$`\forall x\in[a,b],\qquad
|f(x)-q_n(x)|
\leq
C\frac{(b-a)^{n+1}}{n!}
+\sum_{k=0}^{n}\delta_k(b-a)^k.`

The same proposition is exported as an ordinary `ModelApproxCert`. Runtime
roundoff in evaluating $`q_n` is a separate error.
:::

:::proof "symbolic.taylor_jet_certificate"
Insert the exact Taylor polynomial between $`f` and the stored jet $`q_n`.
The Taylor remainder theorem bounds the first difference, and the coefficient
perturbation theorem bounds the second. The triangle inequality adds these two
independent budgets, producing the certificate's soundness field.
:::

*Informal sizing calculation for $`\sin(x)` on $`[0, \pi]`.*

Suppose we request a piecewise model approximating $`\sin x` to tolerance
$`\eta = 10^{-4}` on $`[0, \pi]`. The adaptive algorithm proceeds:

1. *Initial attempt.* At the root interval $`[0, \pi]` with order $`n = 4`,
   the remainder bound uses $`C = \max_{x \in [0,\pi]} |D^5\sin(x)| = 1`. The
   remainder is $`C(\pi-0)^5/4! \approx 12.7`, which exceeds $`\eta`.

2. *First bisection.* Split at $`\pi/2`. On each half-panel of width
   $`\pi/2 \approx 1.57`, the remainder is $`1 \cdot (1.57)^5/24 \approx 0.39`,
   still exceeding $`\eta`.

3. *Further bisection.* After 4 levels (panels of width
   $`\pi/16 \approx 0.196`), the remainder is
   $`(0.196)^5/24 \approx 1.2 \times 10^{-5} < \eta`. The analytic remainder
   fits the budget; leaf acceptance still needs the coefficient and validity
   certificates.

This calculation suggests 16 quartic panels. A `RationalModelTree`
certificate has rational endpoints, whereas $`\pi` is irrational. A checked
implementation must first choose a rational outer interval and provide the
derivative and coefficient certificates required by each leaf. The intended
global guarantee would then have the form

$$`\forall x \in [0, \pi], \qquad |\sin x - P_\tau(x)| \leq 10^{-4},`

where $`P_\tau` selects the appropriate leaf polynomial based on which
subinterval contains $`x`.

*The distinction from pure interval arithmetic.*

Classical interval arithmetic (Moore, 1966; Neumaier, 1990) replaces each real
number by an interval $`[\underline{x}, \overline{x}]` and propagates bounds
through every arithmetic operation. Repeated occurrences are treated
independently, which can overestimate the range. For example, evaluating
$`x - x` with $`x \in [0,1]` yields $`[-1, 1]` instead of $`\{0\}`. This is
the interval dependency problem; repeated enclosure of transformed sets also
gives rise to the related wrapping effect.

Taylor models (Berz and Makino, 1998) mitigate this loss of correlation by
retaining polynomial structure. Instead of an interval, each quantity is
represented as a polynomial plus a remainder interval. Subtraction of
correlated expressions can cancel matching polynomial parts exactly, leaving
the remainder enclosure to account for the unresolved error. This is useful
for PDE verification, where expressions such as
$`\nabla u \cdot \nabla u - |\nabla u|^2` should simplify before interval
evaluation.

PDEAtlas's Taylor certificates are approximation and composition theorems,
assembled into piecewise models, rather than a Taylor-model arithmetic with
the wrapping-control strategies of that literature.

The rational interval operations, such as `expRange`, `logRange` on strictly
positive panels, `RationalInterval.sin`, and `RationalInterval.cos`, enclose
the range of a function on a whole panel. A Taylor model instead retains a
polynomial approximation over the panel; the symbolic Taylor constructors use
interval analysis only to establish analytic-domain conditions and to bound
the remainder derivative, while coefficient enclosures can separately supply
the jet's coefficient-error budget.

*Order selection and error decomposition.*

The Taylor-jet certificate makes the three error sources explicit:

$$`\underbrace{C \frac{(b-a)^{n+1}}{n!}}_{\text{truncation}}
  + \underbrace{\sum_{k=0}^n \delta_k (b-a)^k}_{\text{coefficient uncertainty}}
  + \underbrace{r_{\text{eval}}}_{\text{runtime roundoff}}.`

The first term depends on the smoothness of the function and the panel width.
The second term vanishes when exact symbolic coefficients are used (all
$`\delta_k = 0`). The third term is added separately by the numerical backend
and is separate from the analytic approximation theorem.

The CEGA option `expOrder` (default `defaultExpTaylorOrder = 8`, so a reduced
Taylor sum with $`n=9` terms) is a different order: it is the degree of the
elementary exponential enclosure used by the interval evaluator, while a
Taylor jet has its own polynomial order and these three error budgets.

*Piecewise models.*

:::theorem "symbolic.model_tree_assembly" (parent := "symbolic.cega") (uses := "symbolic.model_certificate, symbolic.compositional_model_calculus") (lean := "CAS.Continuum.RationalModelTree.sound, CAS.Continuum.RationalModelTree.sound_of_adaptive")
`RationalModelTree` joins local approximation certificates along exact rational
split points; the leaf models need not be polynomials. If $`P_\tau` is the
piecewise model selected by a tree $`\tau` and $`E_\tau` is the maximum of
its leaf errors after replacing each by $`\max(0,E_\ell)`, structural induction
proves

$$`\forall x\in[a,b],\qquad
|f(x)-P_\tau(x)|\leq E_\tau.`

For an adaptive result with $`E_\tau\leq\eta`, the exported theorem replaces
$`E_\tau` by the requested tolerance $`\eta`.
:::

:::proof "symbolic.model_tree_assembly"
Induct on the model tree. A leaf uses its local model certificate. At a split,
membership in the root interval places the point in one child panel; apply the
corresponding inductive estimate and weaken its leaf error to the maximum of
the two child errors. The adaptive conclusion follows by transitivity with
$`E_\tau\leq\eta`.
:::

:::theorem "symbolic.model_tree_payload_selection" (parent := "symbolic.cega") (uses := "symbolic.model_tree_assembly") (lean := "CAS.Continuum.RationalModelTree.WithPayload.sound, CAS.Continuum.RationalModelTree.WithPayload.model_eq_selectedLeaf")
A payload tree may retain derivative enclosures, centers, or backend data at
each leaf while erasing to the underlying model tree. For
$`x\in[a,b]`, let $`\ell_x` be the selected leaf and $`p_{\ell_x}` its
certified local model. Selection satisfies the exact identity

$$`P_\tau(x)=p_{\ell_x}(x),`

while erasure supplies
$`|f(x)-P_\tau(x)|\leq E_\tau`. Payloads leave the approximation semantics
unchanged.
:::

:::proof "symbolic.model_tree_payload_selection"
Follow the same endpoint comparison used by the piecewise model evaluator to
select a leaf. Structural induction shows that erasing payloads does not
change this branch choice or the selected local model. The payload tree
therefore evaluates to the certified leaf model, while the erased tree
supplies its approximation bound.
:::

:::theorem "symbolic.validated_model_tree_selection" (parent := "symbolic.cega") (uses := "symbolic.model_tree_payload_selection") (lean := "CAS.Continuum.RationalModelTree.Validated.selectLeaf_relation, CAS.Continuum.RationalModelTree.Validated.sound_of_adaptive")
Let $`R(c,d)` be a declared relation between a leaf certificate and its
payload. If every leaf satisfies $`R`, then point selection proves

$$`\forall x\in[a,b],\qquad
R\!\left(c_{\ell_x},d_{\ell_x}\right).`

Validated adaptive search preserves this local relation together with the
global guarantee
$`\forall x\in[a,b],\ |f(x)-P_\tau(x)|\leq\eta` for the requested tolerance
$`\eta`.
:::

:::proof "symbolic.validated_model_tree_selection"
Induct along the branch selected by the point. At a leaf, the stored validation
field proves $`R(c,d)`. At a split $`m`, use the left child when $`x\leq m`
and the right child otherwise; root membership gives membership in that chosen
child, so its induction hypothesis applies. A queried split point uses the
left branch. The global approximation estimate is inherited from the erased
model tree.
:::

:::definition "symbolic.taylor_leaf_compilation" (parent := "symbolic.cega") (uses := "symbolic.compiled_taylor_derivative_family, symbolic.taylor_jet_certificate, symbolic.interval_evaluator_sound") (lean := "CAS.Continuum.taylorLeafCandidate, CAS.Continuum.RationalInterval.compileDerivative?, CAS.Continuum.CompiledDerivative.contDiffOn, CAS.Continuum.CanonicalDerivative.sound, CAS.Continuum.RationalInterval.EnclosureAttempt.memReal")
The leaf construction combines the checked symbolic derivative pipeline with
a noncomputable Taylor polynomial. Given rational $`a<b`, regularity through order
$`n+1`, and a proved nonnegative rational bound
$`\lVert D^{n+1}_{[a,b]}f(x)\rVert\leq C`, a successful leaf construction
returns the exact Taylor model $`T^{[a,b]}_{n,a}f` with

$$`\forall x\in[a,b],\qquad
\left|f(x)-T^{[a,b]}_{n,a}f(x)\right|
\leq C\frac{(b-a)^{n+1}}{n!}.`

The compiler records analytic branch conditions explicitly and verifies
rational cancellation and denominator conditions. Unsupported derivatives or
failed interval obligations return `none`, so this theorem is exposed only
after all required evidence has been constructed.
:::

:::definition "symbolic.sensitivity_guided_subdivision" (parent := "symbolic.cega") (uses := "symbolic.interval_evaluator_sound") (lean := "CAS.Continuum.RationalInterval.CertifiedEvalRegistry.variableSensitivities, CAS.Continuum.RationalInterval.CertifiedEvalRegistry.selectVariableSubdivisionChoice?")
For each splittable coordinate $`x_i`, the planner encloses the symbolic
partial derivative and assigns the exact rational score

$$`(b_i-a_i)\max\{|L_i|,|U_i|\},
\qquad
\operatorname{eval}(\operatorname{diff}_i e,X)\subseteq[L_i,U_i].`

This is an enclosure of the formal derivative expression. Its identification
with an analytic partial derivative requires the separate validity
hypotheses. The largest positive score selects the coordinate; if no score is positive, the
widest coordinate with an unenclosed derivative is chosen. The ranking is a heuristic, and
soundness comes from the checked interval enclosures used by the adaptive
search.
:::

:::theorem "symbolic.adaptive_taylor_model" (parent := "symbolic.cega") (uses := "symbolic.model_tree_assembly, symbolic.validated_model_tree_selection, symbolic.taylor_leaf_compilation, symbolic.sensitivity_guided_subdivision") (lean := "CAS.Continuum.ExprAdaptiveTaylor.adaptiveToTolerance?_sound, CAS.Continuum.ExprAdaptiveTaylor.panelOfRange")
`ExprAdaptiveTaylor.panelOfRange` is the analytic handoff from a proved
derivative enclosure to a real Taylor model with an exact-rational error
bound. Both it and the adaptive constructor `adaptiveToTolerance?` are
noncomputable. The latter constructs a leaf of the requested order on each
panel from the exact-rational enclosure of its remainder derivative. It retries
rejected leaves on half-panels until the model tree meets the requested
tolerance $`\eta` or the finite search budget is exhausted. If the optional
search returns a result with piecewise model $`P`, Lean proves

$$`\forall x\in[a,b],\qquad
\left|\operatorname{eval}(e,x)-P(x)\right|\leq\eta.`

Failure returns `none`, and success carries an ordinary `ApproxOn`
theorem.
:::

:::proof "symbolic.adaptive_taylor_model"
Every accepted leaf is produced from a derivative enclosure and the Taylor
remainder theorem, hence carries a local model certificate. Recursive
subdivision assembles these leaves with the model-tree soundness theorem.
The successful search result also stores that the maximum leaf error is at
most $`\eta`; composing the two facts proves the root-domain approximation.
:::
