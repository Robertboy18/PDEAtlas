/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.PDEExamples
import Blueprint.CodeExamples
import CAS
import CAS.Continuum.IntervalEval.WellFormed
import CAS.Expr.FloatLib
import CAS.Continuum.Interval.Inclusion.Elementary

/-!
## Certified enclosures

Approximation, residual, bound, and enclosure certificates.
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
#doc (Manual) "Certified Approximation and Enclosures" =>

:::group "symbolic.cega"
Certified continuous computation
:::

FloatLib supplies the interval arithmetic and elementary-function enclosures.
The rational backend uses `FloatLib.Numerics.Interval ℚ`; PDEAtlas's
`RationalInterval` extends it with just the endpoint-order proof `hle`.
Its endpoints remain exact rationals. FloatLib's generic expression evaluator
accepts CAS expressions through a proved semantic translation, and its
upstream backends choose the endpoint representation and rounding policy.
CEGA connects their containment proofs to real inequalities, so an analytic
theorem can use a different representation without changing its statement.

*The four basic certificate shapes.*

On a domain `s`, the records name their data as follows: `ApproxCert α E s`
has functions `lhs` and `rhs` and an error `eps`; `ResidualCert α E s` has a
`residual` and an `eps`; `BoundCert α s` has a real function `fn` and an
`upper` endpoint; `EnclosureCert α s` has `fn`, `lo`, and `hi`. Each `sound`
field proves the corresponding proposition on `s`. These general records may
contain noncomputable real data, while concrete rational enclosures provide
executable endpoints. For example, an enclosure
$`-0.01\le r(x)\le0.01` immediately gives a residual certificate with error
$`0.01`; an enclosure of $`f-g` inside $`[-\varepsilon,\varepsilon]` gives an
approximation certificate from $`f` to $`g`.

:::definition "symbolic.approx_certificate" (parent := "symbolic.cega") (lean := "CAS.Certificate.ApproxCert")
An approximation certificate stores two functions, an explicit domain and
uniform error budget, and a proof of the corresponding norm bound. Exact
equality is the zero-error special case. The budget is stored as a real number.

Its theorem-facing field is exactly

$$`\operatorname{ApproxOn}(f,g,s,\varepsilon)
  \;:\!\Longleftrightarrow\;
  \forall x\in s,\quad \lVert f(x)-g(x)\rVert\leq\varepsilon.`
:::

:::theorem "symbolic.certificate_budget_invariant" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate") (lean := "CAS.Certificate.ApproxCert.eps_nonneg_or_eq_empty, CAS.Certificate.ResidualCert.eps_nonneg_or_eq_empty")
An approximation or residual certificate has a nonnegative error budget unless
its certified domain is empty. Equivalently, a negative budget can never be
used to establish a nonvacuous estimate.

For either certificate family,

$$`0\leq c.\mathrm{eps}\quad\lor\quad s=\varnothing.`
:::

:::proof "symbolic.certificate_budget_invariant"
If the domain is nonempty, choose one point in it. Soundness bounds a norm,
which is nonnegative, by the stored budget; hence the budget is nonnegative by
transitivity. If no point exists, the alternative $`s=\varnothing` holds.
:::

:::definition "symbolic.approx_composition" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate") (lean := "CAS.Certificate.ApproxCert.trans, CAS.Certificate.ApproxCert.mapLipschitz, CAS.Certificate.ApproxCert.eqOn_of_eps_eq_zero")
Approximation certificates compose by adding error budgets, pass through
Lipschitz maps, and recover exact equality when the final budget is zero.

The three principal rules are

$$`\begin{aligned}
\operatorname{ApproxOn}(f,g,s,\varepsilon_1)
\land\operatorname{ApproxOn}(g,h,s,\varepsilon_2)
&\Longrightarrow
\operatorname{ApproxOn}(f,h,s,\varepsilon_1+\varepsilon_2),\\
\operatorname{ApproxOn}(f,g,s,\varepsilon)
\land L\geq0
\land\left(\forall u,v,\ \lVert\phi(u)-\phi(v)\rVert\leq L\lVert u-v\rVert\right)
&\Longrightarrow
\operatorname{ApproxOn}(\phi\circ f,\phi\circ g,s,L\varepsilon),\\
\operatorname{ApproxOn}(f,g,s,0)
&\Longrightarrow f= g\quad\text{on }s.
\end{aligned}`
:::

:::definition "symbolic.interval_backend" (parent := "symbolic.cega") (lean := "CAS.Continuum.RealIntervalBackend")
A real interval implementation supplies lower and upper endpoints, a
membership predicate, and proofs that membership implies the corresponding
real inequalities. Exact rational intervals are the registered instance; a
verified finite-precision representation with the same two proofs feeds the
same enclosure theorems.

Every backend instance must establish

$$`x\in_{\!B} I
  \quad\Longrightarrow\quad
  \operatorname{lo}(I)\leq x\leq\operatorname{hi}(I).`

The representation of $`I` and the implementation of membership are otherwise
abstract. For the rational backend, CEGA's endpoint inequalities are
equivalent to FloatLib's real containment predicate.
Attaching `hle` preserves that predicate and gives refinement and quadrature
an ordered interval with a nonnegative radius.
:::

:::definition "symbolic.expression_well_formed" (parent := "symbolic.cega") (lean := "CAS.Verified.Expr.isWellFormed") (uses := "symbolic.expression")
Before interval compilation, an intrinsic syntax check rejects malformed
rational literals whose denominator is zero. Division, logarithm, and square
root remain ordinary real expressions with pointwise analytic validity
conditions; this check handles only malformed syntax, so it cannot be bypassed
by evaluating over an empty domain.

The nontrivial recursive clauses are

$$`\begin{aligned}
\operatorname{WF}(\operatorname{rat}(m,d))&\Longleftrightarrow d\neq0,\\
\operatorname{WF}(e_1\mathbin\circ e_2)
  &\Longleftrightarrow\operatorname{WF}(e_1)\land\operatorname{WF}(e_2),\\
\operatorname{WF}(\operatorname{op}(e))
  &\Longleftrightarrow\operatorname{WF}(e).
\end{aligned}`

Here $`\circ` ranges over binary syntax constructors and
$`\operatorname{op}` over unary constructors; branch-domain proofs are
deliberately separate.
:::

:::theorem "symbolic.interval_evaluator_sound" (parent := "symbolic.cega") (uses := "symbolic.expression, symbolic.expression_well_formed, symbolic.interval_backend") (lean := "CAS.Verified.Expr.eval_toFloatLib, FloatLib.Numerics.Interval.Expr.containsReal_eval?, CAS.Continuum.RationalInterval.evalWithLookups_sound")
Successful evaluation by a sound FloatLib backend encloses every real value
of the expression on the input panel. The semantic translation identifies
that value with the original CAS expression when the coordinate environments
agree and every real-power base is positive.

For an environment enclosure
$`\rho(i)\in_{\!B}\operatorname{env}(i)`, successful evaluation satisfies

$$`\operatorname{evalInterval}(\operatorname{env},e)
  =\operatorname{some}(J)
  \quad\Longrightarrow\quad
  \operatorname{eval}(e,\rho)\in_{\!B}J.`

The admissible numerical domains depend on the provider. FloatLib's generic
backends require positive logarithm panels and nonnegative square-root
panels. CEGA's rational callback route also treats strictly negative logarithm
panels through $`\log(-x)=\log x`, the singleton zero through
$`\log0=0`, and negative square-root inputs through $`\sqrt x=0`.
A nontrivial panel touching zero has no finite logarithm range. Division
requires exclusion of zero; unsupported or failed operations return `none`.

The rational callback evaluator has the same enclosure conclusion once its
division and unary-range callbacks prove their semantic contracts. A checked
denominator entry stores a positive rational lower bound $`\delta`, its direct
theorem $`\delta\leq|\operatorname{eval}(d,\rho)|` on the chart, and route
provenance.
:::

:::proof "symbolic.interval_evaluator_sound"
FloatLib proves containment by induction on its expression tree: leaves use
the environment and constant contracts, and each operation uses the backend's
soundness theorem on the inductive enclosures. Compose this result with the
CAS translation's real-denotation equality. The rational callback route
uses the same inductive argument with its checked denominator and unary
facts. Failed operations propagate `none`, so every successful branch retains
its containment proof.
:::

:::theorem "symbolic.interval_bridge" (parent := "symbolic.cega") (uses := "symbolic.interval_backend, symbolic.approx_certificate") (lean := "CAS.Continuum.RealIntervalBackend.enclosedOn_of_memReal, CAS.Continuum.RealIntervalBackend.residualBound_of_memReal_le")
Backend membership yields ordinary real enclosures. If the interval lies
inside $`[-\varepsilon,\varepsilon]`, the same bridge yields a certified
residual bound.
:::

:::proof "symbolic.interval_bridge"
Apply the backend membership theorem pointwise to obtain the real lower and
upper inequalities. If those endpoints lie in
$`[-\varepsilon,\varepsilon]`, transitivity gives
$`-\varepsilon\leq f(x)\leq\varepsilon`, which is equivalent to the required
absolute residual bound.
:::

*How FloatLib encloses elementary functions.*

An interval for $`f(I)` must contain $`f(x)` for every real $`x\in I`,
including irrational inputs. FloatLib's `ContainsReal` theorems make exactly
this claim. PDEAtlas's elementary-function adapters call the upstream routines,
express their results in CEGA's ordered interval interface, and connect the
routines' domains to Mathlib's total real functions. The numerical
series, remainder estimates, period reduction, and integer square root live
in FloatLib.

*Exponential enclosure.* `expRangeWith I order` calls FloatLib's `expBounds`
with degree $`d=\max(\mathrm{order},1)`. For an endpoint $`q`, FloatLib
chooses a binary scale $`s` so that $`r=q/2^s` has $`|r|<1`. With
$`n=d+1`, its exact rational Taylor sum and error bound are

$$`T_n(r)=\sum_{k=0}^{n-1}\frac{r^k}{k!},\qquad
R_n(r)=\frac{|r|^n(n+1)}{n!\,n}.`

The proved estimate puts $`\exp r` in $`[T_n(r)-R_n(r),T_n(r)+R_n(r)]`.
Repeated interval squaring then uses
$`\exp q=(\exp r)^{2^s}` to restore the original scale. Monotonicity
combines the lower endpoint enclosure at $`I.lo` with the upper endpoint
enclosure at $`I.hi`, and `expBounds` clamps the lower bound to zero.

*Logarithm enclosure.* `logRangeWith` takes a proof that the input panel is
strictly positive and calls FloatLib's `logBounds?`. For a positive endpoint
$`q\geq1`, binary reduction writes $`q=2^k r` with $`1\leq r<2`;
for $`0<q<1`, FloatLib first encloses $`\log(q^{-1})` and negates the
result. The transformed series argument
$`t=(r-1)/(r+1)` lies in $`[0,1/3)`, while the separate enclosure of
$`\log2` uses $`t=1/3`. Writing $`P_d(t)=\sum_{j=1}^{d}t^j/j`, the
identity $`\log r=\log(1+t)-\log(1-t)` gives the rational estimate

$$`\left|\log r-\bigl(P_d(t)-P_d(-t)\bigr)\right|
  \leq\frac{2|t|^{d+1}}{1-|t|}.`

FloatLib restores $`k\log2` by interval arithmetic. There is no reduction
fuel limit: the binary scale comes from the rational argument. CEGA maps a
requested `logTerms` value to $`d=2\max(\mathrm{logTerms},1)` for this
geometric remainder bound.

*Square root enclosure.* For $`q=n/d\geq0` in lowest terms, CEGA calls
FloatLib's `sqrtPointBounds` on $`q d^2=nd` and divides the resulting
endpoints by $`d`. With $`S=2^s`, the upstream integer square root
$`r=\lfloor\sqrt{ndS^2}\rfloor` gives

$$`\sqrt q\in\left[\frac{r}{dS},\frac{r+1}{dS}\right].`

*Trigonometric enclosures.* The base calls are FloatLib's `sinBounds` and
`cosBounds`, each with degree $`32`. They enclose the panel midpoint and
inflate that enclosure by the panel radius using
$`|f(x)-f(m)|\leq|x-m|` for $`f=\sin,\cos`. Intersecting with
$`[-1,1]` retains the global range, including when the panel crosses an
extremum. For a midpoint of magnitude above $`4`, FloatLib reduces by
approximate full periods derived from its certified enclosure of $`\pi/4`.
The error includes both the Taylor remainder and the accumulated period
uncertainty. That uncertainty grows with the number of removed periods, so
a narrow input panel alone does not guarantee a sharp range at large arguments.

CEGA refines these FloatLib bounds with endpoint monotonicity and sign facts
when rational branch tests justify them. For example, on a panel crossing
zero inside $`[-\pi,\pi]`, cosine's lower bound comes from the two endpoint
enclosures and its upper bound is $`1`. Those endpoint enclosures also come
from FloatLib. Subdivision can sharpen a range but need not improve it strictly.

*Arctangent enclosure.* `atanRange` calls FloatLib's `atanBounds` with
parameter $`16`. Oddness reduces negative inputs to nonnegative ones;
reciprocation reduces inputs above one to $`[0,1]`. On $`(1/2,1]`, the
identity

$$`\arctan q=\frac{\pi}{4}+\arctan\frac{q-1}{q+1}`

leaves a series argument of magnitude at most $`1/2`. FloatLib bounds the
arctangent series by a geometric tail and encloses $`\pi/4` using Machin's
identity $`\pi/4=4\arctan(1/5)-\arctan(1/239)`. Monotonicity combines
the endpoint enclosures into a range for the full panel.

*Inverse trigonometric and hyperbolic functions.* Arcsine and arccosine use
FloatLib's `asinBounds?` and `acosBounds?`. CEGA clamps endpoint arguments
to $`[-1,1]`, proves agreement with Mathlib's total functions, and uses their
monotonicity to lift point bounds to panels. If an optional point enclosure
fails, a proved global range supplies the fallback. Hyperbolic ranges call
FloatLib's `sinhBounds`, `coshBounds`, and `tanhBounds` with the requested
positive exponential degree; their containment theorems pass through the
same real-membership bridge.

*Example: enclosing $`\exp(\cos x)` on $`[-1/10, 1/10]`.*

A conservative hand calculation shows how enclosures compose; its Taylor order
is chosen by hand.

1. *Variable range.* The input panel gives $`x \in [-1/10, 1/10]`.

2. *Cosine enclosure.* At center $`0`, $`\cos 0 = 1`. The one-Lipschitz
   inflation gives $`\cos x \in [1 - 1/10, 1 + 1/10] = [9/10, 11/10]`.
   Intersecting with $`[-1, 1]` gives $`\cos x \in [9/10, 1]`.

3. *Exponential enclosure.* At each endpoint $`q\in\{9/10,1\}`, use
   $`T_8(q)=\sum_{k<8}q^k/k!` and
   $`R_8(q)=q^8\,9/(8!\,8)`.
   The proved Taylor estimate gives
   $`\exp(q)\in[T_8(q)-R_8(q),T_8(q)+R_8(q)]`.
   Monotonicity therefore encloses the composition in the exact rational interval
   $`[T_8(9/10)-R_8(9/10),T_8(1)+R_8(1)]`.

4. *Result.* These rational endpoints and the uniform enclosure proof give
   the data needed for an `EnclosureCert`. The evaluator can instead compose
   FloatLib's cosine and exponential bounds through the same containment rule.

The evaluator handles composed transcendental expressions without
special-case code for $`\exp \circ \cos`. Each function's enclosure feeds into
the next through the generic interval backend interface. The exact range is
$`[\exp(\cos(1/10)),\exp(1)]`; the conservative cosine step accounts for much
of the excess width.

*The interval evaluator's compositional structure.*

`Expr.toFloatLib` translates CAS syntax into
`FloatLib.Numerics.Interval.Expr`. FloatLib's `Expr.eval?` traverses this
expression using an upstream backend:

- Rational literals are enclosed by the backend's constant operation.
- Variables take their intervals from the supplied coordinate environment.
- Arithmetic and elementary nodes use FloatLib's operations and containment
  theorems.
- The translation represents $`\pi` by $`4\arctan1` and $`\mathrm e`
  by $`\exp1`. These identities preserve the exact real values.
- Inverse sine and cosine clamp their arguments to $`[-1,1]`, preserving
  Mathlib's total functions. Real powers use
  $`a^b=\exp(\log(a)b)` under the explicit condition $`a>0`.

The translation proves agreement of real values; numerical evaluation and
its soundness theorem live upstream. Ordinary multiplication followed by
addition remains two expression nodes. An application requiring fused
multiply-add uses FloatLib's explicit FMA node.

The rational CEGA route `RationalInterval.evalWithLookups` additionally
accepts expression-specific analytic facts. Division uses either a denominator
interval excluding zero or a certified positive
lower bound for the actual denominator's absolute value. Unary providers
supply exponential, logarithm, square-root and inverse-trigonometric ranges;
real powers require a strictly positive base interval. A failed subevaluation
propagates `none`. Its $`\pi` and $`\mathrm e` literals use fixed rational
brackets of widths $`10^{-20}` and $`2\cdot10^{-20}`; kernel-checked rational
inequalities place FloatLib's degree-$`24` Machin and exponential enclosures
inside them.

*Direct FloatLib execution.*

FloatLib provides `Backend.rational` for rational endpoints,
`Backend.binaryGrid` for integer endpoints on a specified binary grid, and
`Backend.ofRounding` for a supplied outward rounder. The latter computes
rational elementary bounds and rounds them into the chosen endpoint
representation. Decoding failures, rejected domains, and unrepresentable
bounds propagate as `none`. These are upstream types and operations.

The `binaryGrid` representation uses scaled integers on a binary grid; it is
not an IEEE format. FloatLib's certified IEEE binary32 operations form a
separate facility, and the concrete CEGA backend used by the command and
tactic is rational. The generic expression translation and rounding interface
can connect another backend once its operations and containment proofs are
supplied.

For quadrature or a Taylor model, the numerical enclosure must refer to the
same exact-real rule or polynomial as the analytic certificate. Its radius
then bounds replacement by the interval midpoint, including any outward
rounding. Adding that radius to the analytic remainder gives the total error.
An enclosure alone supplies neither differentiability nor a quadrature
remainder; CEGA's analytic theorems retain those hypotheses.

*A certified enclosure.*

The command asks for a uniform cosine enclosure on a rational panel:

```Blueprint.leanExample (name := enclosuresCosineExample)
-- Prove one interval enclosure uniformly
-- over the whole input panel.
set_option linter.hashCommand false in
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)
```

If the query succeeds with rational endpoints $`a,b`, its mathematical
meaning is

$$`\forall x\in[-1/10,1/10],\qquad a\leq\cos x\leq b.`

:::theorem "symbolic.interval_product" (parent := "symbolic.cega") (uses := "symbolic.interval_backend") (lean := "CAS.Continuum.RationalInterval.mul_sound")
FloatLib computes interval multiplication as the exact four-corner product.
For rational panels
$`I=[a,b]` and $`J=[c,d]` the product panel has endpoints
$`\min(ac,ad,bc,bd)` and $`\max(ac,ad,bc,bd)`, which is sharp for
independent factors in every sign configuration; on $`x\in[-1,2]`,
$`y\in[2,3]` it gives $`[-3,6]` where a symmetric magnitude bound gives
$`[-6,6]`.

$$`x\in I\ \land\ y\in J
  \quad\Longrightarrow\quad
  xy\in I\cdot J.`
:::

:::proof "symbolic.interval_product"
The interval product bound follows from FloatLib's multiplication theorem.
To see why the four corners suffice, fix the sign of $`y`. Multiplication
by $`y` is then monotone or antitone, so
$`xy` lies between $`ay` and $`by`. Each of these is a fixed factor times a
value between $`c` and $`d`, hence lies between the two corner products with
that factor. Both bounds are therefore between the minimum and the maximum of
the four corners.
:::

:::theorem "symbolic.exp_taylor_range" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "CAS.Continuum.RationalInterval.expRange_sound, CAS.Continuum.RationalInterval.expRangeWith_sound")
For every rational panel $`I` and every requested order, `expRangeWith`
contains $`\exp x` whenever $`x\in I`. The implementation passes
$`\max(\mathrm{order},1)` to FloatLib's `expBounds`, and the automatic
`expRange` uses degree $`8`. Positive, negative, and zero-crossing input
panels all satisfy the same theorem.
:::

:::proof "symbolic.exp_taylor_range"
FloatLib's pointwise exponential bound encloses the exponential of the reduced argument;
repeated squaring transports that bound through
$`\exp q=(\exp(q/2^s))^{2^s}`, and monotonicity covers the panel.
Attaching the order proof and translating containment back to `MemReal`
preserves the resulting inequalities.
:::

:::theorem "symbolic.log_rational_range" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "CAS.Continuum.RationalInterval.logRange_sound, CAS.Continuum.RationalInterval.logRangeWith_sound, CAS.Continuum.RationalInterval.logPointIntervalWith_sound")
For every rational panel $`I=[\ell,h]` with $`0<\ell`, `logRangeWith`
contains $`\log x` whenever $`x\in I`. It calls FloatLib's `logBounds?`
with degree $`2\max(\mathrm{terms},1)`. The positivity proof ensures that
the upstream optional routine succeeds. The default request is $`10`, hence
FloatLib degree $`20`.
:::

:::proof "symbolic.log_rational_range"
The positive lower endpoint establishes the domain condition. The two
logarithm series and their geometric tails
bound $`\log(1+t)-\log(1-t)`; binary scaling and, for inputs below one,
reciprocation restore the original argument. Monotonicity lifts the point
bounds to the whole positive panel.
:::

:::theorem "symbolic.sqrt_rational_range" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "CAS.Continuum.RationalInterval.sqrtNonnegativePointInterval_sound, CAS.Continuum.RationalInterval.sqrtNonnegativePointInterval_width_le, CAS.Continuum.RationalInterval.sqrtRangeInterval_sound, CAS.Continuum.RationalInterval.sqrtRange_sound")
For every rational panel and every binary precision $`s`, `sqrtRangeInterval`
contains Mathlib's total real square root throughout the panel. At a
nonnegative endpoint $`q=n/d` in lowest terms, the point enclosure has width
at most $`1/(d2^s)` and is exact when its lower endpoint squares to $`q`.
Negative endpoints map to zero. The default precision is $`12` binary digits.
:::

:::proof "symbolic.sqrt_rational_range"
FloatLib proves both containment and the width bound for its integer-root
enclosure. Since $`d>0`, division by $`d` preserves the endpoint order, and
$`\sqrt{qd^2}=d\sqrt q` gives the desired point enclosure. For negative
arguments, Mathlib's square root is zero. Apply monotonicity of this total
function to the two endpoint certificates to enclose the full panel.
:::

:::theorem "symbolic.atan_rational_range" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "CAS.Continuum.RationalInterval.atanRange_sound")
For every rational panel, `atanRange` contains the real arctangent throughout
that panel. It uses FloatLib's `atanBounds` with parameter $`16`, and no
sign restriction on the input panel is needed.
:::

:::proof "symbolic.atan_rational_range"
FloatLib's pointwise arctangent bound transports the
small-argument series bounds through the arctangent identities, using a
certified Machin enclosure for $`\pi/4`. Monotonicity then combines the lower
bound at the left endpoint with the upper bound at the right endpoint.
:::

:::theorem "symbolic.local_trig_range" (parent := "symbolic.cega") (uses := "symbolic.interval_bridge") (lean := "CAS.Continuum.RationalInterval.sinBase_sound, CAS.Continuum.RationalInterval.cosBase_sound, CAS.Continuum.RationalInterval.sin_sound, CAS.Continuum.RationalInterval.cos_sound")
For every rational panel, the sine and cosine ranges contain all real
function values on it. The base ranges are FloatLib's degree-$`32` bounds;
CEGA intersects them with endpoint or sign bounds when the panel satisfies a
proved principal-branch condition.
:::

:::proof "symbolic.local_trig_range"
FloatLib's sine and cosine bounds include the error introduced by period
reduction. If $`m` is the
midpoint, $`r` the panel radius, and $`[a,b]` contains $`f(m)`, the
one-Lipschitz estimate gives $`f(x)\in[a-r,b+r]` for every panel member.
For each accepted branch test, monotonicity and symmetry justify endpoint
bounds from the same FloatLib point enclosures; a proved sign permits clamping
at zero. Each intersection contains the exact function value, so the final
interval retains the containment theorem.
:::

:::theorem "symbolic.centered_form" (parent := "symbolic.cega") (uses := "symbolic.interval_evaluator_sound, symbolic.interval_bridge") (lean := "CAS.Continuum.RationalInterval.CertifiedEvalRegistry.exists_eq_add_deriv_mul_sub, CAS.Continuum.RationalInterval.CertifiedEvalRegistry.centeredFormEnclosureAttempt?")
For a rational box $`B=I_1\times\cdots\times I_n` with midpoint $`m` and a
function differentiable on the box, the mean value theorem in centered form
gives

$$`f(x)=f(m)+\sum_{i=1}^{n}\partial_i f(c)\,(x_i-m_i)
\qquad\text{for some }c\text{ on the segment from }m\text{ to }x,`

so that $`f(B)\subseteq f(m)+\sum_i \partial_i f(B)\,(I_i-m_i)`; a coordinate
whose panel is a single point contributes nothing. For a symbolic expression,
the checked route first certifies analytic validity throughout the box. It
encloses the midpoint value and the symbolic partial derivatives, then adds
the interval products with $`I_i-m_i`. In one dimension, if $`J_0` encloses
$`f(m)` and $`D` encloses $`f'` on $`I`, the result is
$`J_0+D(I-m)`, with width
$`\mathrm{width}(J_0)+2\,\mathrm{radius}(I)\max(|\inf D|,|\sup D|)`.
This can improve the natural extension without a fixed derivative sign;
the midpoint error and derivative magnitude determine the gain.
The companion monotonicity route works coordinatewise on the same boxes: when
a partial derivative $`\partial_i f` keeps one sign on $`B`, every value of
$`f` lies in the hull of the enclosures of $`f` on the two faces
$`x_i=\min I_i` and $`x_i=\max I_i`, and one planner level nests up to $`n`
such face reductions. On $`[1,2]^2`, direct interval substitution in $`xy-x`
gives $`[1,4]-[1,2]=[-1,3]`. As a hand calculation, the factorization
$`x(y-1)` makes the exact range $`[0,2]` visible; likewise,
$`xyz-xy=xy(z-1)` has exact range $`[0,4]` on $`[1,2]^3`.
Previews rank candidate routes by width, endpoint magnitude, and route length,
after any correlated hyperbolic enclosure; the selected route must still
construct its certificate, with fallback on failure.
:::

:::proof "symbolic.centered_form"
The box is convex, so the segment from the midpoint $`m` to $`x` stays in it;
apply the mean value theorem to $`t\mapsto f(m+t(x-m))` on $`[0,1]`, whose
derivative is the Fréchet derivative of $`f` applied to $`x-m`, that is the sum
of the partial derivatives weighted by the coordinate offsets, to obtain the
intermediate point $`c`. Interval soundness of the midpoint evaluation, of each
partial-derivative enclosure at $`c`, and of the products with $`I_i-m_i` then
places $`f(x)` in the assembled box. For the face reduction, a one-signed
partial derivative makes $`t\mapsto f(x+t e_i)` monotone on the segment across
the box, so $`f(x)` lies between the values at the two faces, hence in the hull
of their enclosures.
:::

:::definition "symbolic.precision_policy" (parent := "symbolic.cega") (uses := "symbolic.exp_taylor_range, symbolic.log_rational_range, symbolic.sqrt_rational_range") (lean := "CAS.Continuum.RationalInterval.Precision, CAS.Continuum.RationalInterval.Precision.withPrec, CAS.Continuum.RationalInterval.Precision.withDepth")
A `Precision` value bundles three requests for FloatLib-backed elementary
ranges and a depth for checked box refinement:

$$`(\mathrm{expOrder},\ \mathrm{sqrtDigits},\ \mathrm{logTerms},\ \mathrm{depth})
  \quad\text{with defaults}\quad(8,\ 12,\ 10,\ 2).`

`expOrder` supplies FloatLib's exponential degree after promotion of zero to
one. `sqrtDigits` sets the binary grid for the denominator-scaled square-root
bounds. `logTerms` maps to FloatLib degree $`2\max(\mathrm{logTerms},1)`.
The sine, cosine, and arctangent adapters use their own fixed parameters.
The configuration group `(prec := n)` sets the first three fields to $`n`;
`(depth := n)` sets the subdivision depth. An omitted policy uses the defaults.

The policy is planner data. Every range theorem holds for all parameter
values, so changing the policy preserves soundness while affecting cost and
potential sharpness. The final width also depends on input variation,
dependence between subexpressions, and period uncertainty, any of which can
dominate the error.
:::

:::theorem "symbolic.dyadic_inclusion" (parent := "symbolic.cega") (uses := "symbolic.exp_taylor_range, symbolic.log_rational_range, symbolic.sqrt_rational_range, symbolic.atan_rational_range, symbolic.local_trig_range, symbolic.precision_policy") (lean := "CAS.Continuum.CEGAInclusion.mem_liftUnary, CAS.Continuum.CEGAInclusion.div_mem, CAS.Continuum.CEGAInclusion.exp_mem, CAS.Continuum.CEGAInclusion.log_mem, CAS.Continuum.CEGAInclusion.sqrt_mem, CAS.Continuum.CEGAInclusion.sin_mem, CAS.Continuum.CEGAInclusion.cos_mem")
Mathlib's `dyadic_interval` tactic evaluates a real proposition over intervals
with dyadic endpoints and checks the outcome in the kernel. The `cega_real`
family adds CEGA's ranges to it: quotients, natural powers, $`\pi`, the
exponential, the logarithm, the square root, the trigonometric and inverse
trigonometric functions, and the hyperbolic functions. A bounded dyadic
interval $`I` has rational endpoints, so it passes unchanged to a CEGA range
$`F`, and the rational interval $`F(I)` is rounded outward to the grid
$`2^{-p}`, where $`p` is the tactic's `prec` parameter. If $`x\in I`, then
$`f(x)` lies in the rounded interval. An unbounded argument, and a reciprocal
or logarithm whose argument interval contains zero, give a range that holds
for every real input: $`[-1,1]` for sine and cosine, $`[0,\infty)` for the
exponential and the square root, and the whole line otherwise. The Taylor
order of the exponential family and the series length of the logarithm are
at least $`p/2`, and the square root keeps at least $`p+4` binary digits.
The $`\pi` bracket and the trigonometric and inverse-trigonometric series use
fixed parameters; increasing $`p` refines their outward rounding but does not
refine those underlying rational ranges.

Bare `cega` runs this evaluation with $`p=32` on a goal without free
variables that its carrier and box routes do not prove, such as a
conjunction, a disjunction, a negation, an interval membership or an
equality of real constants.
:::

:::proof "symbolic.dyadic_inclusion"
The rational interval with the endpoints of $`I` contains $`x`, so the CEGA
soundness theorem places $`f(x)` in $`F(I)`, and outward rounding only
enlarges $`F(I)`. The global ranges follow from $`-1\le\sin x\le 1`,
$`0<e^x`, $`0\le\sqrt x`, $`\lvert\arctan x\rvert<\pi/2\le 2` and the
corresponding bounds for $`\arcsin`, $`\arccos`, $`\cosh` and $`\tanh`.
Mathlib's `inclusion` tactic composes these one-step facts along the
expression tree.
:::
