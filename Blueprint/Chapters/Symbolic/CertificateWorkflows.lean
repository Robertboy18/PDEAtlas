/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Symbolic.DerivativeBounds
import Blueprint.CodeExamples
import CAS.Numerics.Finite
import CAS.CEGA.Query
import CAS.Certificate.Atlas.Residual
import CAS.Certificate.Enclosure
import CAS.Tactic.Certificate
import CAS.Continuum.ODETrajectory

/-!
## Certificate workflows

The semantic contracts exposed by CEGA certificates and
the finite-dimensional numerical forms of the unified `#cas` command.
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
#doc (Manual) "Certificate Workflows" =>

Checked numerical certificates enter an ordinary Lean proof through the
`cega` tactic, which can project a supplied certificate or construct one
through a checked rational-box query. For an ordinary inequality goal, bare
`cega` can read the box off rational literal bounds among the hypotheses;
explicit box syntax supplies the query directly. In either route, a checked
soundness proof must establish the target, including any domain or error
weakening.

:::theorem "symbolic.quadrature_roundoff" (parent := "symbolic.cega") (uses := "symbolic.quadrature_certificate") (lean := "CAS.Continuum.QuadratureCert.replaceValue_sound")
An independently certified numerical value may replace the exact-real
quadrature value. Its roundoff bound is added to the analytic quadrature error
by the triangle inequality. The theorem is the common interface for a
verified exact, interval, or floating-point implementation: a backend must
prove the displayed norm bound before its computed value enters the
quadrature certificate.

Concretely, if $`Q` is the value stored in a certificate with error $`E` and
$`\widehat Q` is a computed replacement satisfying
$`\lVert Q-\widehat Q\rVert\leq\delta`, then

$$`\left\lVert\int_a^b f(x)\,dx-\widehat Q\right\rVert
  \leq E+\delta.`
:::

:::proof "symbolic.quadrature_roundoff"
Insert and subtract the exact certificate value $`Q`. The triangle inequality
bounds the new integral error by the original quadrature error plus
$`\lVert Q-\widehat Q\rVert`; applying the two stored bounds yields
$`E+\delta`.
:::

:::theorem "symbolic.certificate_domain_restriction" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate") (lean := "CAS.Certificate.ApproxCert.sound_restrict, CAS.Certificate.ResidualCert.sound_restrict, CAS.Certificate.BoundCert.sound_restrict, CAS.Certificate.EnclosureCert.sound_restrict, CAS.Certificate.ModelApproxCert.restrict, CAS.Certificate.ModelApproxCert.sound")
Approximation, residual, upper-bound, enclosure, and model-approximation
certificates may be restricted from a domain `s` to any subset `t ⊆ s`.
The resulting theorem is the original `sound` field composed with the subset
proof; no backend computation is repeated.

For every semantic predicate $`P`, the restriction step is simply

$$`t\subseteq s,\qquad
  \bigl(\forall x\in s,\ P(x)\bigr)
  \quad\Longrightarrow\quad
  \forall x\in t,\ P(x).`
:::

:::proof "symbolic.certificate_domain_restriction"
At a point of the smaller domain, the subset hypothesis places that point in
the original domain, where the stored semantic theorem already applies.
Every certificate family uses this same set-theoretic argument.
:::

:::definition "symbolic.local_certificate_projection" (parent := "symbolic.cega") (uses := "symbolic.certificate_domain_restriction, symbolic.quadrature_certificate, symbolic.quadrature_roundoff") (lean := "CAS.Tactic.Certificate.closeFromLocalCertificates")
The certificate-projection route of `cega` searches the local context and
target for a recognized checked certificate. It first tries the certificate's
semantic theorem exactly, then permits a proved domain restriction, a larger
error budget, or a wider enclosure when those changes match the goal. Any new
real inequalities are discharged separately by ordinary arithmetic. The tactic
succeeds only after Lean confirms that the constructed proof has the user's target type.

For an approximation certificate, the representative projection is

$$`t\subseteq s,\quad c.\mathrm{eps}\leq\varepsilon
  \quad\Longrightarrow\quad
  \forall x\in t,\qquad
  \lVert c.\mathrm{lhs}(x)-c.\mathrm{rhs}(x)\rVert\leq\varepsilon.`

Residual, bound, enclosure, model, and quadrature goals use the analogous
typed projection; `cega` never changes the proposition being proved.
:::

*Certificate example: cosine near the origin.*

`PDE/Examples/Numerics/CosineEnclosure.lean` compiles a complete enclosure of
`Real.cos` on

$$`D=\left[-\frac1{10},\frac1{10}\right].`

CEGA certifies $`[199/200,1]` on $`D`. The interval and its proof are stored as
`CAS.Examples.Numerics.CosineEnclosure.cosineEnclosure`, an `EnclosureCert ℝ D`
whose fields have the following meaning:

* `fn` is `Real.cos`;
* `lo` is `199 / 200`;
* `hi` is `1`;
* `sound` proves $`199/200\leq\cos x\leq1` for every $`x\in D`.

The theorem-facing use is short:

```Blueprint.leanExample
-- Import the backend-independent certificate propositions.
open CAS.Certificate

-- CEGA projects the certificate's soundness
-- theorem into the target.
example
    (domain : Set ℝ)
    (cosineEnclosure : EnclosureCert ℝ domain) :
    EnclosedOn cosineEnclosure.fn domain
      cosineEnclosure.lo cosineEnclosure.hi := by
  cega using cosineEnclosure
```

The tactic projects the stored theorem; cosine is not evaluated again.

The same object can support a smaller domain. Given
$`D'\subseteq D`, `cosineEnclosure.restrict D' hsub` stores the same
function and endpoints with soundness restricted along `hsub`. It can also
support a coarser conclusion: `EnclosureCert.weaken` turns $`[199/200,1]` into
any proved wider interval, for example $`[-1,1]`. These operations are set
inclusion and transitivity proofs.

The generic proof pattern is therefore:

```Blueprint.leanExample
-- A certificate on s proves the same
-- enclosure on a subset t.
example
    {s t : Set ℝ}
    (c : EnclosureCert ℝ s)
    (hsub : t ⊆ s) :
    EnclosedOn c.fn t c.lo c.hi := by
  cega using c
```

Here `cega` finds the domain restriction needed to match the target.

:::theorem "symbolic.ode_trajectory_validation" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate, symbolic.local_certificate_projection") (lean := "CAS.Continuum.ODETrajectoryCert.dist_velocity_vectorField_le, CAS.Continuum.ODETrajectoryCert.dist_le_gronwall, CAS.Continuum.ODETrajectoryCert.comparison_sound")
An `ODETrajectoryCert` stores an ordinary Lean curve, its proposed velocity,
continuity on $`[a,b]`, a proof that the velocity is its right derivative on
$`[a,b)`, membership in the state region, and one backend-independent residual
bound for
$`u'(t)-F(t,u(t))`. Mathlib's approximate-trajectory Grönwall theorem compares
two such trajectories. The pointwise estimate is converted to a uniform
`ApproxCert` by evaluating the monotone Grönwall bound at the right endpoint.
No ordering hypothesis is needed: if the left endpoint is below the right one, residual
soundness there makes both budgets nonnegative, and otherwise the claim is immediate.

As an example, the affine Euler curve $`1+t` is compared with the exact
trajectory $`\exp t` for $`u'=u` on $`[0,1]`. Its residual is $`-t`, hence has
norm at most one, and the generated uniform error is $`\exp(1)-1`. An exact
CAS proof or a FloatLib enclosure may supply the residual bound. The ODE
stability theorem consumes that real bound and gives the same final
`ApproxOn` statement.
:::

:::proof "symbolic.ode_trajectory_validation"
The residual certificate bounds the defect between the proposed velocity and
the vector field. Apply the approximate-trajectory Grönwall estimate to this
defect and the initial discrepancy, then use monotonicity of the exponential
bound to replace its time-dependent right-hand side by its value at the final
time. This produces the uniform approximation certificate.
:::

The stability estimate explains how the residual enters the trajectory
error. If the vector field is $`L`-Lipschitz in the state variable,
the initial discrepancy is $`e_0`, and the sum of the two residual budgets
is $`\delta`, Grönwall gives, for $`L>0`,

$$`
\|u(t)-v(t)\|
\leq e^{L(t-a)}e_0+
      \delta\,\frac{e^{L(t-a)}-1}{L}.
`

For $`L=0`, the corresponding bound is $`e_0+\delta(t-a)`. In the
$`1+t` versus $`e^t` example, $`e_0=0`, $`L=1`, and $`\delta=1`,
giving the stated $`e-1` budget at time one. The actual maximum error is
$`e-2`: the certificate is conservative because it replaces the varying
defect $`t` by the uniform bound one. Both curves are hypotheses of the
comparison theorem.

:::theorem "symbolic.total_tolerance_quadrature" (parent := "symbolic.cega") (uses := "symbolic.tolerance_planning, symbolic.quadrature_roundoff") (lean := "CAS.Continuum.QuadratureCert.trapezoidalToTotalToleranceOfInterval_sound_le")
Under the trapezoidal regularity and second-derivative-bound hypotheses, one
user-supplied tolerance can control analytic truncation and verified numerical
error. Let $`I` have radius $`r<\mathrm{tolerance}`. The enclosure proof must
refer to the exact-real trapezoidal value on the mesh planned with the budget
$`\mathrm{tolerance}-r`. Replacing that exact rule value by the interval
midpoint then has total certified error at most the original tolerance.
:::

:::proof "symbolic.total_tolerance_quadrature"
Reserve the interval radius $`r` for replacement error and invoke the
trapezoidal planner with the positive remaining budget $`\tau-r`. The
roundoff-replacement theorem adds the two contributions, and
$`(\tau-r)+r=\tau` gives the requested total bound.
:::

:::theorem "symbolic.patchwise_assembly" (parent := "symbolic.cega") (uses := "symbolic.approx_certificate, symbolic.interval_bridge") (lean := "CAS.Domain.PatchCover.lift, CAS.Certificate.ApproxAtlasCert.sound, CAS.Certificate.ResidualAtlasCert.sound")
Patch covers assemble local approximation or residual proofs into a global
theorem on the covered domain. The atlas layer, used near singularities or
across piecewise regimes, rests on this theorem.

The shared logical contract is

$$`\left(\forall x\in s,\ \exists i,\ x\in s_i\right)
  \land
  \left(\forall i,\ \forall x\in s_i,\ P(x)\right)
  \quad\Longrightarrow\quad
  \forall x\in s,\ P(x).`

For approximation and residual atlases, $`P(x)` is the corresponding stored
norm bound.
:::

:::proof "symbolic.patchwise_assembly"
Fix a point in the global domain and use the cover property to choose a patch
containing it. The local certificate on that patch proves the desired
predicate at the point. Since the argument is independent of the selected
patch, it assembles the local soundness fields into the global theorem.
:::

*External data and analytic proofs.*

A numerical solver can propose rational coefficients, interval endpoints, or
binary64 words in JSON. The exact-data importer embeds integer columns as Lean
data, rejecting incorrect lengths and invalid word ranges. Decimal strings
preserve large integers even when the producer's JSON tools use floating point.
The data file is a Lake dependency, so changing it invalidates the build trace.
Importing those values proves no numerical or analytic property.

:::theorem "symbolic.finite_certificate_coverage" (parent := "symbolic.cega") (lean := "CAS.Numerics.forall_of_batchAll, CAS.Numerics.claim_of_batch_checks")
For any positive batch size, consecutive truncated batches cover every index
of a finite domain. A sound checker therefore supplies all finite hypotheses
of an analytic theorem, independently of the chosen batch size.
:::

:::proof "symbolic.finite_certificate_coverage"
For index $`i` and batch size $`b>0`, Euclidean division writes
$`i=b\lfloor i/b\rfloor+(i\bmod b)`. The remainder lies in its batch,
including the shorter final batch. Apply that batch's check and then the
analytic soundness theorem. The empty domain needs no checks.
:::

The tactic forms `cega [batch := 128]` and `cega [fast, batch := 128]`
generate these internal proof steps without numbered source modules. The
fast form follows the configured native/kernel checking profile. Native
checking additionally trusts Lean's compiler and runtime; kernel checking
computes the same proposition and can take longer.

The analytic bridge remains essential. Bounds at sampled points alone do not
control the function between them: an interval cover, interpolation estimate,
derivative remainder, or stability theorem must supply that argument. In the
De Gregorio spline construction, verified smoothing replay identifies the
candidate values, exact row checks bound the linear-system residual, and
diagonal dominance converts that budget to an error bound against the exact
slope vector.

*Finite-dimensional numerical commands.*

:::theorem "symbolic.finite_box_queries" (parent := "symbolic.cega") (uses := "symbolic.interval_evaluator_sound, symbolic.approx_certificate") (lean := "CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq, CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq, CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq, CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq")
The public query layer accepts an arbitrary finite rational box and reports
failure unless it can produce a proof. One successful enclosure supplies four
theorems: the two-sided range, an ordinary upper bound, a bound for the
magnitude, and uniform approximation by the rational center with the rational
radius as error. Each theorem connects the executable query result to an
ordinary semantic proposition. Route steps remain diagnostic metadata.

Writing $`B=\prod_i[a_i,b_i]` and $`[\ell,h]` for the certified interval of a
successful enclosure of $`e` on $`B`, the four contracts are

$$`\begin{aligned}
&\forall x\in B,\quad \ell\leq e(x)\leq h,\\
&\forall x\in B,\quad e(x)\leq h,\\
&\forall x\in B,\quad |e(x)|\leq\max(|\ell|,|h|),\\
&\forall x\in B,\quad \left|e(x)-\tfrac{\ell+h}{2}\right|\leq\tfrac{h-\ell}{2}.
\end{aligned}`
:::

:::proof "symbolic.finite_box_queries"
Successful interval evaluation first supplies a two-sided enclosure for every
point of the input box. The enclosure query returns it directly; the
upper-bound and absolute-bound queries project elementary consequences of its
endpoints; and the midpoint query rewrites membership in the interval as a
distance bound from its center. Each projection preserves the evaluator's
quantification over the whole domain.
:::

*How the certificate layer fits together.*

Exact symbolic proofs are the zero-error case. Approximation certificates add
a uniform error, enclosure certificates retain a function and scalar
endpoints, and quadrature certificates combine an exact-real rule with an
analytic remainder. Patch covers glue pointwise identities, enclosures, and
uniform error bounds on a covered domain. Quadrature certificates on adjacent
oriented intervals compose using interval integrability and integral
additivity, with their error budgets added.

For PDE applications, the patch theorem's pointwise conclusion should be
kept explicit. A piecewise constant function can have classical derivative
zero on both sides of an interface while its distributional derivative
contains a jump term at that interface. Covering those open pieces and
checking their residuals does not settle the interface equation. A weak
solution assembled from local pieces also needs the appropriate matching
or flux conditions, as well as integrability.
