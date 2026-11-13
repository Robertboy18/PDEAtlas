/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Symbolic.ValidatedNonlinearAlgebra
import Blueprint.CodeExamples
import Blueprint.Commands.CardIndex
import Blueprint.Commands.CertifiedPlots
import Blueprint.Commands.Figures
import Blueprint.Commands.TextbookMap
import PDE.Analysis.Scalar.ConvexIntegral
import CAS

/-!
# Verified symbolic and continuous computation chapter

The exact CAS, its analytic bridges, the PDE examples, and the CEGA
(Certified Enclosures, Guarantees, and Approximations) certificate
subdocuments, followed by the generated textbook coverage map and the
certified plots. Mathematical nodes stay in the subsystem files.
The global dependency graph is emitted after every chapter has been loaded.
The SymLean manual documents the full command and tactic syntax.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanPDE.Ledger (casCount)

-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- The re-elaborated proofs below keep the layout of their source files; the
-- sixty-column limit is Verso's default for short calculator snippets.
set_option verso.code.warnLineLength 100

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Verified Symbolic and Continuous Computation" =>
%%%
htmlSplit := .never
shortTitle := "CAS and Certified Bounds"
tag := "verified-computation"
%%%

PDE proofs contain calculations that are easy to state and tedious to repeat:
expand a residual, differentiate a composed function, find an antiderivative,
or bound a coefficient on a box. We want those calculations to produce facts
that the rest of a Lean proof can use. A formula returned by a calculator does
not, by itself, prove an equality of real functions or a bound on an interval.
The calculation must retain its domain and justify each transformation.

This matters even for familiar rules. Cancelling a factor requires it to be
nonzero. Differentiating a real power can require a positive base. An interval
bound must cover every point in the stated box. Our CAS records these conditions
and proves the resulting identity; CEGA carries numerical bounds into the same
analytic language. The surrounding PDE argument supplies boundary data,
regularity, existence, and stability.

# Earlier approaches

There are two established ways to obtain this guarantee. An external algebra
system can propose an answer that a proof assistant checks. Lewis and Wu's
Lean–Mathematica interface follows this approach: it translates expressions
between the systems and reconstructs proofs for selected returned computations
{Informal.citet "lewis-wu-2021"}[]. The search can be powerful without making
the external calculator part of the proof's trusted basis.

Alternatively, an algorithm can be defined inside the proof assistant and
proved correct once. Computational reflection evaluates that algorithm on an
expression tree and applies its correctness theorem; Boutin developed this
approach for certified decision procedures in Coq
{Informal.citet "boutin-1997"}[]. PDEAtlas uses this pattern for its supported
symbolic transformations and interval evaluators. The
{ref "related-work"}[Related Work] chapter compares the surrounding projects.

# Algorithms and their guarantees

The frontend translates ordinary Lean expressions into a finite syntax tree.
The exact normalizer recursively rewrites that tree using proved algebraic
rules and explicit side conditions. Differentiation applies the sum, product,
quotient, and chain rules, then simplifies the derivative. Integration searches
a bounded collection of rules and candidates; a candidate is accepted only
when checked differentiation recovers the integrand on the required domain.
These are the procedures behind `cas`.

CEGA's numerical routes evaluate exact rational intervals through the same
expression structure. Elementary-function bounds use proved approximations
and remainder estimates. Subdivision bisects a box and combines the bounds
from its children; Taylor models retain polynomial information with a bounded
remainder. Quadrature, root, and matrix certificates add their own soundness
theorems. Each method gives a specified conclusion, such as an enclosure or
error bound, rather than a general PDE existence theorem.

# A heat-equation residual

Return to the separated heat profile from the parabolic chapter:
$$`
u(t,x)=e^{-t}\sin x.
`
It keeps its sine shape while its amplitude decays. Differentiating once in
time and twice in space gives the same expression,
$$`
\partial_t u=-e^{-t}\sin x=\partial_{xx}u,
`
so the heat-equation residual is zero. On a rod with endpoints at $`0` and
$`\pi`, the profile also vanishes at both ends. At time zero it is the sine
profile. We have checked the differential identity, the boundary values, and
the initial value separately. A uniqueness argument would tell us whether
another solution with the same data is possible in the chosen solution class.

The initial-value check is essential even when the residual is exactly zero.
For any constant $`\delta`, the profile
$`\widetilde u(t,x)=(1+\delta)e^{-t}\sin x` has the same zero residual
and homogeneous boundary values, but its initial value differs from the
prescribed sine by $`\delta\sin x`. We use this simple example to keep track
of what a calculation has established: an equation, its data, and a
uniqueness or stability theorem each answer a different part of the PDE
problem.

We have already used this kind of calculation for harmonic polynomials,
transport, and the rotation and shear flows. The same
calculator supports those proofs. For this profile we can follow the
derivatives by eye. Longer formulas involve the same rules, with more terms
and more conditions to track. The `cas` tactics
prove supported exact identities, derivatives, and antiderivatives; `cega`
proves numerical bounds from exact rational interval computations or applies
an existing certificate, such as a Taylor or quadrature certificate with its
analytic hypotheses.

The {bpref "methods.semilinear.contraction"}[fixed-point chapter] gives one
quantitative connection. For a contraction $`T` with constant $`q<1`
and fixed point $`u`, a candidate $`v` satisfies
$`\|u-v\|\leq\|T(v)-v\|/(1-q)`. A certified defect becomes a solution-error
bound through this stability estimate. For a PDE, the norm, boundary
conditions, and inverse-operator estimate in that argument come from the
analysis of the problem, not from the residual computation.

For a real residual $`R`, the certificate relation `ResidualBound R Ω ε`
means $`|R(p)|\le\varepsilon` for every $`p\in\Omega`. At
$`\varepsilon=0` it gives the exact equation $`R=0` on that domain.
At positive tolerance it gives uniform control of the residual.

We justify the exact transformations with the
{bpref "symbolic.normalization_sound"}[soundness of normalization] theorem and
the numerical bounds with the
{bpref "symbolic.interval_evaluator_sound"}[soundness of interval evaluation] theorem.

# Proof-producing computation

In the opening heat calculation, the useful conclusion is an equality between
derivatives of an ordinary real function. Computing a syntax tree for the
answer is an intermediate step. A soundness theorem connects that tree to the
function and gives us an equality we can use in a proof.

{leanpde_figure "cega-pipeline"}

An expression, interval, or polynomial becomes usable in a proof only after
it is connected to the original function by a soundness theorem. The domain
conditions travel with that theorem: a cancellation involving a denominator,
for instance, still needs the denominator to be nonzero at the points in
question.

## From input to theorem

After importing `CAS.CAS`, calculations are written in ordinary
real-scalar notation. The frontend reifies that notation internally, so users
do not have to construct a `Verified.Expr` by hand.

Closed finite certificates have a simpler route. After its semantic routes refuse
a goal, bare `cega` can evaluate a closed decidable proposition in the kernel,
such as a bound on every entry of a finite integer table. `cega [fast]` first
tries compiled evaluation of that proposition, then a computable polynomial
interval enclosure. It restores the proof state and environment on refusal
before falling back to kernel CEGA. Compiled successes additionally trust Lean's
compiler and native evaluation; their generated axioms reach downstream results.
The kernel build profile disables these native paths without changing the statements.
Exponential, logarithmic, and other proof-bearing analytic planner routes stay
kernel checked. A closed finite certificate can still contain rational enclosures
for these functions: checking that finite data and proving its analytic meaning
are separate steps.

The semantic theorem determines how we can use the answer. A derivative
identity lets us replace a term in a PDE operator. An enclosure
$`\ell\le f(x)\le h` for every $`x` in a box can bound an error on that
box; it says nothing about points outside it. An antiderivative identity
supplies the derivative step of the fundamental theorem of calculus, whose
interval hypotheses must also hold.

The `#cas` command displays expressions and checked evidence together with
any outstanding conditions or diagnostics. The theorem-facing tactics use
that evidence in ordinary Lean goals. If a closing tactic cannot justify
the requested conclusion, it fails and preserves the goal.
The SymLean manual gives the full command and tactic syntax,
coordinate-selection rules, side-condition contract, and limitations.

## The Expression Representation

To differentiate a formula, the algorithm needs to see how it is assembled:
which operation is outermost, which subexpressions it acts on, and where
variables occur. We store that structure as a finite expression tree, called
`Verified.Expr ι`, rather than only its value as a real function. Its
constructors include integer and rational constants, variables, the four
arithmetic operations, negation, natural powers, real powers `a ^ b` with an
arbitrary real exponent (Mathlib's `Real.rpow`), `sin`, `cos`, `atan`,
`asin`, `acos`, `exp`, `log`, and `sqrt`, together with `pi` and `e`. An
environment
$`\rho:\iota\to\mathbb R`
assigns a real value to every variable, and `Expr.eval ρ e` interprets the
syntax tree as a real number.

This is called a *deep embedding*. A *shallow* representation by Lean functions
$`\mathbb R\to\mathbb R` is convenient for stating analytic theorems, but an
opaque function does not expose its constituent operations to a symbolic
algorithm. The expression tree does: differentiation, normalization, and
interval evaluation recurse over those operations. We use it because these
three computations can then share one representation. The price is a proof
that each computation has the intended meaning when the tree is evaluated.
The bridge theorems provide that proof and return statements about ordinary
real functions, such as the derivatives used in the earlier PDE chapters.

The index type carries arity, not a new scalar type. For example,
`Verified.Expr (Fin 2)` is a scalar expression in two ordered real
coordinates. The expression $`\sin(xy)` therefore denotes a map
$`\mathbb R^2\to\mathbb R`. A vector-valued expression is represented by a finite family of
scalar expressions, one for each output coordinate.

The `#cas` command and theorem tactics recognize supported ordinary Lean
notation and build the tree internally; a real power is recognized whether it
is written `x ^ (r : ℝ)` or `Real.rpow x r`, while a literal natural exponent
keeps the natural-power constructor.

## Domains, Types, and Side Conditions

The calculator frontend has fixed real semantics. Writing
`(x : ℝ)` documents that semantics; it does not select a different backend.
A complex annotation is rejected.

Inside ordinary theorem goals, coefficients can come from many Lean types as
long as the resulting expression is real-valued. Natural, integer, rational,
and nonnegative-real casts, structure fields, and arbitrary real-valued
parameters may remain opaque coefficients. Differentiated coordinates
themselves are real.

Evaluation is total because Lean's real division, logarithm, square root, and
real power are total functions. Classical calculus rules are not
unconditional. The predicate `Expr.ValidAt ρ e` records the facts needed at a
point: denominators and logarithm arguments are nonzero, square-root arguments
and the bases of real powers are strictly positive, and the argument of an
inverse sine or cosine differs from $`\pm1`. The analytic logarithm
derivative bridge therefore needs $`x\ne0` (or a stronger hypothesis such as
$`0<x`), and the power rule for $`x^{3/2}` needs $`0<x`. This is distinct
from identities and enclosures about the total value, which need not assume
analytic validity.

For example,
$`(x^2-1)/(x-1)=x+1` holds when $`x\ne1`. At $`x=1`, Lean's
totalized division makes the left side zero, whereas the right side is two.
The side condition protects the equality itself. For an interval calculation,
a bound such as $`|x-1|\geq\delta>0` also controls division quantitatively:
the reciprocal has magnitude at most $`1/\delta`. Domain information
therefore affects both the validity of an exact simplification and the width
of a numerical certificate.

Every checked frontend, whether it normalizes, differentiates, integrates, or
lowers a PDE residual, generates the same small family of obligations:
nonvanishing denominators and logarithm arguments, positive square-root
arguments and power bases, and finite lists of such facts collected as
`ValidAt`, `ValidityRequirements.Holds`, or `Alg.SideHolds`. One tactic,
`symbolic_assumptions`, discharges all of them. It first reduces the
requirement container to a conjunction of atomic real facts without rewriting
the atoms, so a generated condition keeps the shape a user hint refers to, and
then closes each atom by exactly one of `assumption`, `positivity`,
`norm_num`, or `nlinarith`, also in their `≠ 0` forms; a disequality
hypothesis $`a\ne b` closes $`a-b\ne0`, and a positive hypothesis
$`0<e` also discharges a nonvanishing condition $`e\ne0`. Evidence given through a
`using` clause is simply added to the local context first. On failure the
tactic names the atoms it could not prove and leaves the goal unchanged; no
assumption is ever inserted.

These obligations explain why a plausible simplification can stop short of a
proof. Cancelling a denominator requires evidence that it is nonzero; if we
cannot establish that condition, we still have work to do. The question of
how a calculator should expose such conditions also appears in a 2020 Lean
Zulip wishlist of computer-algebra features
([Effectiveness as a computer algebra system?](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Effectiveness.20as.20a.20computer.20algebra.20system.3F.html))
and again in 2023
([Is there a field\_simp variant that generates hypotheses?](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Is.20there.20a.20field_simp.20variant.20that.20generates.20hypotheses.3F.html)).
Here the obligations travel with the result. The tactic must prove them from
the available context, including any supplied hints, before it can use the
calculation to close the goal.

# Using Verified Computation

We can first inspect a calculation, then use a tactic to prove a statement
about it. `#cas` prints the input, computed result, available checked evidence,
and planner metadata in the InfoView. It adds auxiliary theorems to check the
displayed proof evidence in Lean's kernel; it does not close a user's theorem
goal. Representative commands use the same syntax throughout:

```Blueprint.leanExample
-- Exact algebra and calculus.
#cas [derive x] (2 * x)
#cas [simplify] ((x + 0) * 1)
#cas [derive] (sin x)
#cas [derive x] (sin (x * y))
#cas [derive x] (x ^ (3 / 2 : ℝ))
#cas [grad x, y] (sin (x * y))
#cas [laplacian x, y] (x ^ 2 + y ^ 2)
#cas [integrate] (sin x)
#cas [integrate x] (y * exp x)

-- Certified ranges, with the upper, absolute and midpoint bounds read off them.
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)
#cas [enclose x in [0, 1]] (x - 2)

-- Refine an enclosure with a higher approximation degree or subdivision.
#cas (prec := 40) [enclose x in [0, 1]] (exp x)
#cas (depth := 3) [enclose x in [0, 2]] (sin x * cos x)
```

The partial derivative names its coordinate; `grad` and `laplacian` name an
ordered list. The real-power calculation records the base-positivity condition.
`enclose` reports both endpoints of a certified interval and reads three bounds
off it: an upper bound, a magnitude bound, and a midpoint with its radius.
Precision and subdivision settings are explained with the enclosure algorithms
below.

Bare `derive` and bare `integrate` use a function's binder when given a unary lambda,
or the sole free variable of a bare expression. Thus
`#cas [derive] (fun x : ℝ ↦ 2 * x)` returns `2`, and
`#cas [derive] (fun x ↦ a * x + b)` returns `a` with `a` and `b` as parameters.
The binder also allows constant bodies: `#cas [integrate] (fun x ↦ 2)` returns `2*x`.
A named coordinate must agree with the binder. Multiplication uses `*`, and these
commands need no prior variable declarations or `#eval`.

Exact differentiation is finite-dimensional and supports any finite list of
coordinates. The numerical `enclose` command accepts any finite list of named
coordinates with exact rational interval endpoints. Every free variable must
have a box binding. An optional configuration group before the mode bracket,
`(prec := n)` or `(depth := n)`, selects the precision policy described in the
enclosure section; the command and the `cega` tactic accept it alike.

## Choosing an Interface

Most users should stay in ordinary Lean notation and choose an interface by
what they are trying to do:

* Use `#cas [...] expression` while exploring. It calculates and prints the
  inferred domain and result, registering auxiliary theorems for its proof
  evidence.
* Use bare `cas`, or `cas using h` with a domain hypothesis, when an ordinary
  theorem goal should be closed by algebraic reasoning, checked
  differentiation, or a supported integral rule.
* Use `cas_nf` to transform a supported real expression inside a larger goal
  or hypothesis, or inside a selected `conv` occurrence. The reflected
  `Verified.Expr.eval` interface remains available.
* Use `cega using certificate` when a proof already has an enclosure, error,
  quadrature, or residual certificate and needs its `sound` theorem. Bare
  `cega` projects a matching checked certificate or infers a rational box from
  local hypotheses.
* Use `cega [enclose x in [a, b]] e` when an `EnclosedOn`, `BoundOn`, or
  `ApproxOn` goal over an exact rational box, or an ordinary inequality in the
  box variables, should be closed by a fresh interval certificate; the goal
  selects the projection. Prefix `(prec := n)` or `(depth := n)` when the
  default policy is too coarse.
* Use `cas?` or `cega?` when the same proof search should also explain the
  selected route in the InfoView.
* Use bare `cega` for a numerical bound on an interval integral with a closed real
  integrand and rational limits. It accounts for the quadrature error as well as sample
  uncertainty.
* Use the lower-level `Verified.Expr` and certificate constructors only when
  extending the engine or building a reusable verified algorithm.

## Simplification

The simplifier reifies the supported expression, computes an algebraic normal
form, and accepts that form only through the normalization soundness theorem.
For example,

```Blueprint.leanExample (name := symbolicSimplify)
-- Normalize only through the simplifier's
-- soundness theorem.
#cas [simplify] ((x + 0) * 1)
```

prints the compact calculation

```InlineLean.leanOutput symbolicSimplify +summarize
#cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x + 0) * 1)
Output (scalar ℝ): x

[CAS.Command.details] More details
```

The algorithm recursively normalizes subexpressions and applies the exact
algebraic route appropriate to the reflected fragment. Division, logarithms,
and square roots carry side conditions; normalization does not cancel a
denominator or cross a branch condition without evidence.

The normal form knows the algebra of real powers and of the exponential,
which it treats as a power of $`\mathrm e`: inside a product or quotient all
powers of one base collect into a single power, nested powers flatten, powers
of products distribute, exponents are normalized, and a literal exponent is
read back as a natural power, a reciprocal, or a square root. Each rewrite
that Mathlib states for a positive base records that positivity as a
condition:

```Blueprint.leanExample (name := symbolicRealPowerIdentity)
-- Powers of one base collect; the base must be positive.
#cas [simplify]
  (a ^ (s / 2) * a ^ ((t - s) / 2) - a ^ (t / 2))
```

```InlineLean.leanOutput symbolicRealPowerIdentity +summarize
#cas [simplify]
Domain: (a, s, t) ∈ ℝ^3
Input (scalar ℝ): (a ^ (s / 2) * a ^ ((t - s) / 2) - a ^ (t / 2))
Output (scalar ℝ): 0
Conditions: a > 0

[CAS.Command.details] More details
```

Identities that hold for Mathlib's total `Real.rpow`, such as
$`x^{(2:\mathbb R)}=x^2`, and the exponential identities
$`\exp a\,\exp b=\exp(a+b)` and $`(\exp u)^2=\exp(2u)`, record no
condition at all.

## Differentiation, Gradients, and Laplacians

Consider the scalar function $`f(x,y)=\sin(xy)`. To differentiate only in
the first coordinate, write:

```Blueprint.leanExample (name := symbolicPartialDerivative)
-- Differentiate in x; y remains a parameter.
#cas [derive x] (sin (x * y))
```

The compact report says:

```InlineLean.leanOutput symbolicPartialDerivative +summarize
#cas [derive x]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (scalar ℝ): cos(x*y)*y

[CAS.Command.details] More details
```

The domain line identifies the ordered real coordinate space inferred from
the free variables. The input and output lines identify scalar-valued
expressions; the output is the partial derivative $`\partial_x f`, not the
full derivative of a one-variable function. With `set_option cas.verbose true`,
`More details` also shows the sine chain rule, the product rule for $`xy`, the raw expression
$`\cos(xy)(1\cdot y+x\cdot0)`, and the checked normalization to
$`\cos(xy)y`.

For the full gradient, name its coordinates and their order:

```Blueprint.leanExample (name := symbolicGradient)
-- The written variable order fixes the
-- output coordinate order.
#cas [grad x, y] (sin (x * y))
```

The result is

```InlineLean.leanOutput symbolicGradient +summarize
#cas [grad x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x * y))
Output (vector ℝ^2; order x, y): (cos(x*y)*y, cos(x*y)*x)

[CAS.Command.details] More details
```

Thus `grad x, y` means
$`(\partial_x f,\partial_y f)`. Writing `grad y, x` requests the same two
partials in the opposite output order. This explicit convention avoids
guessing whether a multivariable `derive` request meant one coordinate or an
entire gradient.

The Laplacian computes each diagonal second partial and sums the results:

```Blueprint.leanExample (name := symbolicLaplacian)
-- Sum the diagonal second derivatives in x and y.
#cas [laplacian x, y] (x ^ 2 + y ^ 2)
```

```InlineLean.leanOutput symbolicLaplacian +summarize
#cas [laplacian x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x ^ 2 + y ^ 2)
Output (scalar ℝ): 4

[CAS.Command.details] More details
```

The final bridge theorem identifies the assembled reflected expression with
Mathlib's analytic gradient or the analytic Laplacian defined in the
foundations chapter.

A real power is differentiated by the rule behind Mathlib's
`HasDerivAt.rpow`, and the report records the positivity of the base:

```Blueprint.leanExample (name := symbolicRealPowerDerivative)
-- A real exponent; the base must be positive.
#cas [derive x] (x ^ (3 / 2 : ℝ))
```

```InlineLean.leanOutput symbolicRealPowerDerivative +summarize
#cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ (3 / 2 : ℝ))
Output (scalar ℝ): 3/2*sqrt(x)
Conditions: x > 0

[CAS.Command.details] More details
```

The raw derivative is $`\tfrac32\,x^{3/2-1}`; the normal form reads the
literal exponent $`1/2` back as a square root. A symbolic exponent stays a
real power, so `#cas [derive x] (x ^ y)` reports $`y\,x^{y-1}` under the
same condition.

The theorem tactic can also differentiate functions outside the calculator's real-expression
grammar. Mathlib supplies the arithmetic and chain rules; derivative families in the local
context supply the function-specific step:

```Blueprint.leanExample (name := symbolicDerivativeFamily)
example (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    deriv (fun t ↦ f (t ^ 2) + f t) x = f' (x ^ 2) * (2 * x) + f' x := by
  cas
```

A theorem tagged `@[cas_deriv]` makes its derivative rule available to subsequent calls.
The rule's premises still have to be proved. This route also handles complex scalar calculus:

```Blueprint.leanExample (name := symbolicComplexDerivative)
example (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ Complex.exp (w ^ 2)) (2 * z * Complex.exp (z ^ 2)) z := by
  cas
```

## Checked Antiderivatives

The integration command searches for a primitive and then verifies it:

```Blueprint.leanExample (name := symbolicAntiderivative)
-- Search for a primitive, then verify it
-- by differentiation.
#cas [integrate] (sin x)
```

Its compact report is:

```InlineLean.leanOutput symbolicAntiderivative +summarize
#cas [integrate]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x)
Output (scalar ℝ; antiderivative): -cos(x)

[CAS.Command.details] More details
```

The detailed calculation has four mathematical stages:

1. differentiate the proposed primitive using the indexed symbolic rules;
2. subtract the original integrand to form a residual;
3. prove that the residual normalizes to zero;
4. retain every nonzero or positivity requirement needed by the analytic
   derivative theorem.

For this example there are no side conditions. An accepted antiderivative
certificate supplies both a pointwise derivative identity and its
coordinate-line fundamental theorem of calculus consequence. The ordinary
tactic chooses how to prove the stated goal. The elementary `HasDerivAt`
branch checks the function already in the goal. An interval-integral
equality can provide a primitive through its endpoint expression, or leave
the bounded planner to find one. These are separate tactic calls:

```Blueprint.leanExample
-- Check the stated function's derivative.
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ -Real.cos t)
      (Real.sin x) x := by
  cas

-- Search for a primitive and apply the fundamental theorem of calculus.
example (a b : ℝ) :
    (∫ t in a..b, Real.sin t) =
      Real.cos a - Real.cos b := by
  cas
```

Substitution can reuse the integration methods rather than guess another formula. For
$`f(x)=\log(x)/x`, choose $`u=\log x`. Dividing by $`u'=1/x` leaves $`u`, whose integral is
$`u^2/2`. Substituting back gives $`(\log x)^2/2`; differentiation certifies the result wherever
$`x\ne0`. The same step works for a rational function of an exponential:

```Blueprint.leanExample
#cas [integrate] (fun x ↦ log x / x)
#cas [integrate] (fun x ↦ exp x / (1 + (exp x) ^ 2))
```

For the second expression, $`u=\exp x` gives $`1/(1+u^2)`, so the primitive is
$`\arctan(\exp x)`. Other variables remain coefficients. The rational calculation
$`(a x+b)/(1+x^2)` has primitive $`a\log(1+x^2)/2+b\arctan x`, without assigning values to
$`a` and $`b`. Mixed sine–cosine powers first use $`\sin^2 x+\cos^2 x=1`. Rational expressions
in a common affine trigonometric phase can use the tangent half-angle substitution; its
primitive may require a restricted interval to avoid a branch singularity.

The search runs in compiled code, and the kernel checks the proposed primitive against the
original integrand. A division introduced during discovery does not, by itself, become a
hypothesis: for $`2x\cos(x^2)`, the primitive $`\sin(x^2)` is valid at $`x=0` as well.

Suppose the requested endpoint difference is `F b - F a`. When its two terms
exhibit a common function, the tactic can try that function as a primitive.
It differentiates the candidate and checks the residual against the original
integrand. An unsuccessful automatic candidate leaves bounded search
available. A function supplied with `cas [integrate primitive := F]` is a
different contract: that candidate must pass, including the interval
requirements and the final endpoint equality.

For example, `Real.log t ^ 2 / 2` is a useful proposed primitive for
`Real.log t / t`. Its use requires that every point of `Set.uIcc a b` avoid
zero. The interval includes both endpoints and works in either orientation.
Adding a constant to the primitive leaves its endpoint difference unchanged;
adding a constant to the requested integral value changes the proposition
that must be proved. Candidate selection cannot excuse that mismatch.

The integration engine is deliberately incomplete. It searches a bounded
collection of polynomial, rational, substitution, integration-by-parts,
exponential, trigonometric, logarithmic, and quadratic-terminal patterns.
Finding a candidate is not enough: failure of the residual check or any
required side condition makes the tactic fail without changing the goal.

## Numerical Integration

An exact primitive is often unnecessary for a numerical estimate. The Gaussian integral
$`\int_0^1 e^{-x^2}\,dx`, for example, can be bounded directly:

```Blueprint.leanExample (name := symbolicGaussianIntegral)
example :
    |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - 746824 / 1000000| ≤ 1 / 1000000 := by
  cega
```

On a panel $`[a,b]`, Simpson's approximation is

$$`S=\frac{b-a}{6}\left(f(a)+4f\left(\frac{a+b}{2}\right)+f(b)\right).`

If $`f` is four times continuously differentiable there and $`|f^{(4)}|\leq M`, then
$`|\int_a^b f-S|\leq M(b-a)^5/2880`. CEGA bounds the fourth derivative and each of the
three sample values. It adds the sample uncertainty and the analytic remainder to obtain
an interval containing the integral, then adds the intervals from adjacent panels.
Compiled code doubles the number of panels from one until the stated bound holds and then
chooses the leanest working precision for the elementary function enclosures;
`(panels := n)` fixes the panel count and `(digits := d)` the precision. Both errors are
included in the proved bound.

At a corner or a nonsmooth endpoint, Simpson's hypotheses may fail even though the integral
exists. If continuity can be proved, the tactic can instead bound the range on each panel:
$`l\leq f\leq u` implies $`(b-a)l\leq\int_a^b f\leq(b-a)u`. This route applies to
$`\sqrt{x}` at zero and to $`|x|` across zero, though its bounds can require more subdivision.
The automatic frontend requires a closed real expression and rational limits.
Failure to prove the requested accuracy is not a claim that the integral does not exist.

## Certified Numerical Enclosures

The numerical command

```Blueprint.leanExample (name := symbolicEnclosure)
-- Enclose every value on the interval,
-- rather than sampling points.
set_option linter.hashCommand false in
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)
```

returns

```InlineLean.leanOutput symbolicEnclosure +summarize
#cas [enclose x in [-1 / 10, 1 / 10]]
Domain: x ∈ [-1/10, 1/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (cos x)
Output (certified interval in ℝ): [0.995004, 1]
Upper bound: 1
Absolute bound: 1
Center and radius: ≈0.997502 ± 0.002498

[CAS.Command.details] More details
```

The output bounds every value of cosine throughout the input interval. The
decimal preview rounds outward; the certificate retains exact rational
endpoints. It also implies the coarser bound

$$`\frac{716402999}{720000000}\leq\cos x\leq 1
\qquad\text{for every }x\in\left[-\frac1{10},\frac1{10}\right].`

{leanpde_figure "interval-enclosure"}

The figure uses a rational function to show why a valid enclosure can still
be loose. Interval arithmetic treats repeated occurrences of the variable
independently, losing the relation between numerator and denominator.
Subdivision restricts that loss on each smaller panel. The cosine query
has the same obligation: its bounds must contain every value between
the endpoints, however the evaluator finds them. The figure illustrates the
mechanism; the displayed theorem is the guarantee for the cosine calculation.

For a concrete example of that dependence loss, consider
$`f(x)=x^2/(1+x^2)` on $`[-1,1]`. Write $`z=x^2`, so $`0\leq z\leq1`.
Bounding numerator and denominator separately gives $`[0,1]/[1,2]=[0,1]`.
To obtain the sharper upper bound, retain their common $`z`. Since
$`1+z>0`,

$$`\frac{z}{1+z}\leq\frac12
\quad\Longleftrightarrow\quad 2z\leq1+z
\quad\Longleftrightarrow\quad z\leq1.`

Together with nonnegativity this proves $`f(x)\in[0,1/2]`, with equality
at $`x=\pm1`. A valid interval can be wider than the actual range; a
failed request for a tighter interval need not mean that the requested bound
is false. It may require a different representation or subdivision.

Returning to cosine, the coarser enclosure can be stated as an ordinary theorem
about the one-dimensional Euclidean space and closed by `cega`:

```Blueprint.leanExample
open CAS.Certificate in
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.cos (p 0))
      {p | -1/10 ≤ p 0 ∧ p 0 ≤ 1/10} (716402999/720000000) 1 := by
  cega [enclose x in [-1/10, 1/10]] (Real.cos x)
```

The rational interval computation supplies the candidate endpoints. The
theorem-facing finite-box API exposes the same guarantee through
`CAS.CEGA.encloseBox?` and the returned attempt's
`EnclosureAttempt.sound`; the more general `encloseOn?` API accepts
an arbitrary semantic domain with a proved interval environment. A theorem can
later consume the resulting certificate without knowing which interval
algorithm produced it.

```Blueprint.leanExample
-- Import the certificate vocabulary used
-- by the theorem statement.
open CAS.Certificate

-- CEGA exposes the certificate's stored soundness theorem.
example
    (domain : Set ℝ)
    (certificate : EnclosureCert ℝ domain) :
    EnclosedOn certificate.fn domain
      certificate.lo certificate.hi := by
  cega using certificate
```

Those endpoints are exact rationals. The proposition bounds a real-valued
function, while the endpoint arithmetic uses rational numbers. The certificate
connects that arithmetic to the function. Endpoint representations and
checking costs are discussed in the Zulip threads
[Interval arithmetic -- what approach?](https://leanprover-community.github.io/archive/stream/239415-metaprogramming-/-tactics/topic/Interval.20arithmetic.20--.20what.20approach.3F.html)
and
[LeanCert](https://leanprover-community.github.io/archive/stream/113488-general/topic/LeanCert.20-.20Verified.20Computation.20.26.20Interval.20Arithmetic.html).
Here subdivision and an explicit precision option control how much work the
enclosure calculation performs.

The same box computation also proves the other numerical claims. Below the
certified interval the report gives an upper bound, a bound on the magnitude,
and the midpoint of the interval with its radius as a uniform error:

```Blueprint.leanExample (name := symbolicProjections)
-- One certified interval and the bounds
-- read off it.
set_option linter.hashCommand false in
#cas [enclose x in [0, 1]] (x - 2)
```

```InlineLean.leanOutput symbolicProjections +summarize
#cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x - 2)
Output (certified interval in ℝ): [-2, -1]
Upper bound: -1
Absolute bound: 2
Center and radius: -3/2 ± 1/2

[CAS.Command.details] More details
```

## Sharper Enclosures and the Precision Option

Four mechanisms help sharpen a certified range. Products and argument
reduction improve interval evaluation; derivative enclosures and precision
choices provide further ways to tighten it. The planner compares available
routes, and every accepted enclosure carries its own soundness proof.

*Products.* Interval multiplication is the exact four-corner product: for
$`x\in[a,b]` and $`y\in[c,d]` the product lies in the hull of $`ac`, $`ad`,
$`bc`, and $`bd`. For $`xy` on
$`[-1,2]\times[2,3]` a symmetric magnitude bound would give $`[-6,6]`; the four
corners give the sharp range.

```Blueprint.leanExample (name := symbolicFourCornerProduct)
-- Two coordinates, one exact product.
set_option linter.hashCommand false in
#cas [enclose x in [-1, 2], y in [2, 3]] (x * y)
```

```InlineLean.leanOutput symbolicFourCornerProduct +summarize
#cas [enclose x in [-1, 2], y in [2, 3]]
Domain: x ∈ [-1, 2], y ∈ [2, 3] ⊆ ℝ^2
Input (scalar map ℝ^2 → ℝ): (x * y)
Output (certified interval in ℝ): [-3, 6]
Upper bound: 6
Absolute bound: 6
Center and radius: 3/2 ± 9/2

[CAS.Command.details] More details
```

*Argument reduction.* FloatLib supplies sine and cosine enclosures with
certified period reduction and midpoint bounds. The local adapter uses degree
$`32` and refines those bounds using proved monotonicity and derivative-sign
conditions. A narrow panel far from the origin can receive a tighter enclosure
than the global range $`[-1,1]`:

```Blueprint.leanExample (name := symbolicSineFarFromOrigin)
-- A narrow panel around x = 10.
set_option linter.hashCommand false in
#cas [enclose x in [10, 1001 / 100]] (sin x)
```

```InlineLean.leanOutput symbolicSineFarFromOrigin +summarize
#cas [enclose x in [10, 1001 / 100]]
Domain: x ∈ [10, 1001/100] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x)
Output (certified interval in ℝ): [-0.552385, -0.544021]
Upper bound: -0.544021
Absolute bound: 0.552385
Center and radius: ≈-0.548203 ± 0.004182

[CAS.Command.details] More details
```

The exact range on this panel is $`[\sin(10.01),\sin(10)]`, approximately
$`[-0.55238449,-0.54402111]`. On $`[100,100.001]` a certified cosine enclosure
is $`[0.862318,0.862856]`, and on $`[-7,-6.9]` a certified sine enclosure is
$`[-0.657006,-0.577702]`; on $`[1,2]` the sine enclosure is $`[0.841470,1]`.
When exact endpoints are long, the headline shows a six-place decimal preview
that rounds lower endpoints down and upper endpoints up; the kernel-checked
proposition keeps the exact rationals.

*The centered form.* When an expression repeats a coordinate, the natural
interval extension overestimates. If a partial derivative keeps one sign on
the box, the monotonicity route replaces the box by its two faces in that
coordinate and takes the hull of their enclosures. Each face reruns the
planner, so reductions can continue while fuel and fixed-sign derivative
certificates remain available. The centered form also competes for selection
and allows derivative enclosures of either sign. The mean value theorem in
centered form, $`f(x)=f(m)+\sum_i\partial_i f(c)(x_i-m_i)` with $`c` on the
segment from the midpoint $`m` to $`x`, encloses $`f` by
$`f(m)+\sum_i\partial_i f(B)\,(I_i-m_i)`; both routes work on boxes of any
literal dimension. For example, $`xy-x` on $`[1,2]^2` is certified to its exact
range $`[0,2]`, and
$`xy\,\mathrm e^{-xy}` on $`[0.9,1.1]^2` to $`[0.303083,0.432632]`. In one
variable the centered form is $`f(m)+f'(I)\,(I-m)`. For $`x\,\mathrm e^{-x}` on $`[0.9,1.1]`
the derivative $`\mathrm e^{-x}(1-x)` changes sign; the natural extension
gives $`[0.2996,0.4473]` and the centered form gives

```Blueprint.leanExample (name := symbolicCenteredForm)
-- The derivative changes sign, so the
-- centered form replaces monotonicity.
set_option linter.hashCommand false in
#cas [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))
```

```InlineLean.leanOutput symbolicCenteredForm +summarize
#cas [enclose x in [9 / 10, 11 / 10]]
Domain: x ∈ [9/10, 11/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x * exp (-x))
Output (certified interval in ℝ): [0.356443, 0.379316]
Upper bound: 0.379316
Absolute bound: 0.379316
Center and radius: ≈0.367879 ± 0.011437

[CAS.Command.details] More details
```

against the true range, approximately $`[0.3659,0.3679]`. The planner previews
the natural, monotonicity, and centered routes without proofs, then attempts
certificate construction in order of previewed sharpness until a route
succeeds. The preview determines which route to try; the returned certificate
justifies the enclosure.

*Precision.* The elementary-function ranges are parameterized: a FloatLib degree
for the exponential, a series-term request for the logarithm, a number of
binary digits for square-root brackets, and a bisection depth for checked
subdivision. A `Precision` value bundles them, with defaults $`8`,
$`10`, $`12`, and $`2`. The configuration group `(prec := n)` sets the first
three to $`n` and `(depth := n)` sets the depth; every range theorem is proved
for all parameter values, so the policy affects sharpness and cost but never
soundness. With the default order,

```Blueprint.leanExample (name := symbolicExpDefaultPrecision)
-- FloatLib degree eight.
set_option linter.hashCommand false in
#cas [enclose x in [0, 1]] (exp x)
```

```InlineLean.leanOutput symbolicExpDefaultPrecision +summarize
#cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (exp x)
Output (certified interval in ℝ): [1, 2.718282]
Upper bound: 2.718282
Absolute bound: 2.718282
Center and radius: ≈1.859140 ± 0.859142

[CAS.Command.details] More details
```

also certifies the coarser bound
$`\mathrm e\le876809/322560\approx2.71828187`, while

```Blueprint.leanExample (name := symbolicExpHighPrecision)
-- FloatLib degree forty.
set_option linter.hashCommand false in
#cas (prec := 40) [enclose x in [0, 1]] (exp x)
```

```InlineLean.leanOutput symbolicExpHighPrecision +summarize
#cas (prec := 40) [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (exp x)
Output (certified interval in ℝ): [1, 2.718282]
Upper bound: 2.718282
Absolute bound: 2.718282
Center and radius: ≈1.859140 ± 0.859142

[CAS.Command.details] More details
```

certifies an upper bound with twenty-four decimal places behind the six-place
preview: the theorem-facing form
`cega (prec := 40) [enclose x in [0, 1]] (exp x)` closes an `EnclosedOn` goal
with requested upper bound $`2.718281828459045235360288`. Subdivision depth
works the same way. For $`\sin x\cos x` on $`[0,2]`, `(depth := 2)`
certifies an upper bound of $`53190539/83886080\approx0.634`; a third level
gives

```Blueprint.leanExample (name := symbolicSubdivisionDepth)
-- Three checked bisection levels.
set_option linter.hashCommand false in
#cas (depth := 3)
  [enclose x in [0, 2]] (sin x * cos x)
```

```InlineLean.leanOutput symbolicSubdivisionDepth +summarize
#cas (depth := 3) [enclose x in [0, 2]]
Domain: x ∈ [0, 2] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x * cos x)
Output (certified interval in ℝ): [-0.378402, 0.544012]
Upper bound: 0.544012
Absolute bound: 0.544012
Center and radius: ≈0.082805 ± 0.461207

[CAS.Command.details] More details
```

against the true range, approximately $`[-0.3784,0.5]`. The trigonometric Taylor
degrees are fixed and are not affected by the option. Repeated identical
queries in one file reuse the kernel evaluation of the closed query term; the
certificate theorem is checked again in every declaration that uses it.

## Reading the InfoView

Every `#cas` mode uses the same compact layout. The heading repeats the
command as typed; `Domain` states the real coordinate space or closed interval;
`Input` and `Output` state both shape and scalar type; further results read off
the output, such as the bounds of an enclosure, follow it; and `Conditions`,
when present, records branch or denominator assumptions.

The proof-evidence section lists the propositions and theorem names
that Lean typechecked. Route metadata is separate and depends on the mode.
For integration, the displayed normalization passes explain the accepted
candidate's residual check; they do not record rejected primitive candidates.
The strategy list in a planner refusal names available methods; it does not
record which methods ran.

For theorem goals, `cas?` and `cega?` display the suggested proof and a short
footer naming the selected route. Set `cas.verbose` to `true` locally
to inspect the full evidence tree, with its checked propositions and separate
planner metadata; the same option adds the derivation trees to `#cas` reports.

The integration route returns that explanation with its completed proof.
A primitive report identifies explicit verification, verification of a
goal-derived primitive, or bounded search. When the ordinary `HasDerivAt`
fallback certifies the function already in the statement, its label is
`checked primitive differentiation`, since the function came from the
statement and was not found by search. A direct Mathlib calculus step names the theorem used and
retains its analytic premises. The reporting layer checks those premise
proofs separately from the proof of the original goal.

The suggested replay retains an explicit or goal-derived primitive when the
route has recorded the ordinary function. Replaying it checks the residual
and domain requirements again. Direct Mathlib steps can replay the completed
proof with `exact`. A search result without a recorded ordinary function
replays the integration tactic; its suggestion does not freeze an unrecorded
search decision.

## From a Calculation to a Theorem

Lowercase `cas` is a proof tactic. It works against the ordinary proposition
already written by the user. For example, a theorem with conclusion
$`\frac d{dx}\sin x=\cos x` can be closed by `cas`. A logarithm
example with a hypothesis $`h_x:0<x` uses `cas using hx`.

The derivative route accepts the ordinary Mathlib shapes in which such
statements are written. For an explicit function of one real variable these
are `deriv f x₀ = rhs`, `HasDerivAt f f' x₀`, `HasDerivWithinAt f f' s x₀`,
and nested derivatives `deriv (fun x ↦ deriv g x) x₀`, with the inner
derivative applied or not. The inner rewrite uses a proved function equality,
including for the exponential representations of `sinh` and `cosh`, and
requires its analytic conditions to hold at every real point.
For an explicit function on `ℝ^n` with a literal
dimension `n` they are `partialDeriv i f p = rhs`, repeated `partialDeriv`,
`laplacian f p = rhs`, and `fderiv ℝ f p (EuclideanSpace.single i 1) = rhs`.
The same reflection certifies regularity: `DifferentiableAt ℝ f x₀`,
`Differentiable ℝ f`, `ContDiffAt ℝ n f x₀`, `ContDiffOn ℝ n f s`, and
`ContDiff ℝ n f`, on `ℝ` or on `ℝ^k` with literal `k`, for every smoothness
order `n`, whether a natural literal, `⊤`, a variable, or the analytic order,
because the Mathlib lemmas for the elementary functions hold for every order.
The domain conditions are those of the derivative rules, at the point for the
`At` forms and at every point of the set or the space for the others. Bare
`cas` dispatches on all of these shapes, and on interval integrals when the
integration frontend is imported; `cas?` closes the goal the same way and
suggests the explicit form.

```Blueprint.leanExample
open PDE (partialDeriv laplacian)

-- A HasDerivAt statement about an
-- exponential decay mode.
example (lambda t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-lambda * s))
      (-lambda * Real.exp (-lambda * t)) t := by
  cas

-- A coordinate partial derivative on ℝ^2.
example (p : ℝ^2) :
    partialDeriv 1 (fun q : ℝ^2 ↦ q 0 * Real.cos (q 1)) p =
      -p 0 * Real.sin (p 1) := by
  cas

-- The coordinate Laplacian of a harmonic function.
example (p : ℝ^2) :
    laplacian
        (fun q : ℝ^2 ↦ Real.exp (q 0) * Real.sin (q 1)) p =
      0 := by
  cas

-- A nested derivative is eliminated inner-first.
example (a x : ℝ) :
    deriv (fun x ↦ deriv (fun y ↦ Real.sin (a * y)) x) x =
      -(a ^ 2) * Real.sin (a * x) := by
  cas

-- The power rule with a real exponent needs
-- the positivity of the base.
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ (3 / 2 : ℝ)) x =
      (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  cas using hx

-- A regularity statement on ℝ^2; the quotient's
-- condition is read from the context.
example (p : ℝ^2) (hp : p 0 ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 1 / y 0) p := by
  cas

-- Smoothness of every order on a half-line.
example :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ 1 / t)
      (Set.Ioi 0) := by
  cas
```

Definitions of the current module that depend on the differentiated variable
are unfolded automatically; an imported definition is opened with an explicit
`unfold` so that the reader sees which definition is used, and a hypothesis
stated through such a definition must be unfolded by hand before the analytic
conditions can be matched against it. A false derivative value, a nested
logarithm that is not valid everywhere, or a differentiability claim whose
analytic condition is missing is refused without changing the proof state,
and the error names the unproved condition. Outside the route are abstract
functions, symbolic dimension (refused with a message asking for a literal
one), norms and inner products, sums, piecewise definitions, improper
integrals outside the supported half-line families, and vector-valued
derivatives; those keep their Mathlib proofs.

An equality containing integrals or derivatives may need only algebra on
their values. Bare `cas` first tries that algebra with the integral and
derivative terms left as atoms. Moving an integral past another summand uses
commutativity of addition, even for an abstract integrand taking values in a
normed real vector space. Likewise, associating a sum containing `deriv f a`
does not require a formula for the derivative.

For equalities, disequalities, and order relations that need explicit
derivative values, the derivative-rewriting route rewrites every maximal
derivative subterm of an explicit elementary function (`deriv`,
nested `deriv`, `partialDeriv`, repeated `partialDeriv`, `laplacian`, the
coordinate `fderiv`) to its checked closed form, all or nothing, so that a
residual with several derivative terms becomes an ordinary identity. It then
prepares the goal with theorem-backed steps only: a hypothesis $`ab\ne0`
yields both factor conditions, absolute values of sign-known arguments are
evaluated, powers are distributed over products, the identities
$`(\sqrt u)^2=u` and $`\sqrt u\,\sqrt u=u` join the context wherever
$`0\le u` is provable, and constants such as $`\pi` and $`\exp a` count as
positive. Next come the checked simplifier with the local context and one
Mathlib arithmetic procedure, with the real-valued definitions of the current
module unfolded on a retry. If that fails on a real identity, it reflects both
sides over atoms, runs the side-conditioned normalizer in the kernel,
certifies the zero difference with `decide +kernel`, and discharges the
recorded conditions from the context or from `using` evidence. This is how
residual identities and the real-power and exponential identities close:

```Blueprint.leanExample
-- The wave residual of sin (x - t): both
-- derivatives are rewritten first.
example (t x : ℝ) :
    deriv (deriv (fun s : ℝ ↦ Real.sin (x - s))) t
        - deriv (deriv (fun y : ℝ ↦ Real.sin (y - t))) x
      = 0 := by
  cas

-- π is a positive constant.
example : 4 * Real.pi * (1 / (4 * Real.pi)) = 1 := by
  cas

-- Powers of one base collect under 0 < a.
example (a s t : ℝ) (ha : 0 < a) :
    a ^ (s / 2) * a ^ ((t - s) / 2) = a ^ (t / 2) := by
  cas

-- Exponentials recombine with no hypothesis.
example (u : ℝ) :
    Real.exp u ^ 2 * Real.exp (-2 * u) = 1 := by
  cas
```

Equations in the context can also supply the algebraic relations used by
`cas`. The explicit form `cas using [h₁, h₂]` adds separate equation proofs;
each entry can be an applied theorem, such as `h₁ 0`. Over any commutative
ring, the equations `a * d = b * c` and `c * f = e * d` imply
`c * (a * f - b * e) = 0`. The factor `c` matters: the equations alone do
not justify cancelling it.

For integrals, `cas` can also apply a direct theorem without
selecting a primitive. Splitting the integral of a sum uses interval
integrability of both summands, for the actual measure and codomain.
Differentiating an integral with a varying endpoint uses the continuity,
measurability and integrability premises of the corresponding fundamental
theorem; the left endpoint contributes a minus sign. These rules retain
abstract functions and an abstract normed codomain in the statement.
Supported real expressions with Lebesgue measure go through the scalar
certificate route.

`cas_nf` constructs a checked equality for the expression it transforms and
uses congruence to replace it in its surrounding context. An opaque predicate
can therefore retain its role in the statement while an algebraic argument
is normalized. For example, suppose `h` asserts
$`P((x^4-y^4)/(x^2-y^2))` and `hden` proves $`x^2-y^2\ne0`.
The factorization $`x^4-y^4=(x^2-y^2)(x^2+y^2)` permits cancellation,
so `cas_nf using hden at h` changes the hypothesis to $`P(x^2+y^2)`.
The calculation needs no information about $`P`. If this is the desired
conclusion, `exact h` completes the proof.

By default the tactic works in the goal; locations select hypotheses, and
`conv` selects an occurrence inside a larger expression. A second copy can
remain unchanged when only the first is needed for the next proof step.
Domain requirements still belong to each transformed expression. In
particular, total division at zero does not justify cancelling a denominator,
and $`\sqrt{x^2}` becomes $`|x|` without a sign assumption.

The ordinary interface reflects real arithmetic over opaque atoms and
transports its checked equality back into the statement. Existing
`Verified.Expr.eval` occurrences keep their evaluator and original index type.
Both interfaces use the established normalization pipeline; the resulting
form need not be the shortest equivalent expression.

## Where the Calculator Is Used

For algebra and ordinary real derivatives, import `CAS.ExactTactic`.
Add `PDE.Symbolic.PDEDerivatives` when the calculation involves coordinate
derivatives, a Laplacian, or coordinate applications of `fderiv`. Either import
order works. For interval integrals, `CAS.IntegrationTactic` adds the
integration route of `cas`, with primitive search and integration by parts.
Numerical enclosures use `CAS.CEGA`.
These choices let an algebra calculation use the calculator without importing
the PDE operators.

The Blueprint build scans the library for every `cas`, `cega`, and `#cas`
call and records its module, line, enclosing declaration, tactic form, and the
statement the declaration proves. The scan finds
{casCount "production"}[] production call sites in
{casCount "production-modules"}[] modules of the `PDE` library,
with a further {casCount "examples"}[] sites in
the instructional modules under `PDE/Examples/`. Among these,
{casCount "tactic:cas"}[] use bare `cas` to close a residual, a derivative, or
an algebraic identity, and {casCount "tactic:cas using"}[] use `cas using h`
with domain evidence. The ledger also records integration, side-conditioned calculations,
enclosures, and closed finite certificate checks. A call site records a calculation inside a proof; it does not
mean that the calculator proves the entire enclosing theorem.

The sites cluster where the mathematics is explicit. In the hyperbolic modules
the calculator differentiates the Burgers profiles and Riemann solutions, the
simple waves and Riemann invariants of the p-system, and the Hopf–Lax and
characteristic formulas; in the fluid modules it checks axisymmetric
coordinate identities and the exact rotation and
shear flows; in the parabolic modules it differentiates the heat kernel and the
heat-ball geometry; in the elliptic modules it verifies fundamental solutions,
harmonic polynomials, and radial integrands; in the analysis modules it
evaluates Fourier-mode integrals and Laplace transforms. Four representative
uses show the pattern.

*The heat kernel's time derivative.* For $`t>0`, differentiating
$`\Phi(t,x)=(4\pi t)^{-n/2}\exp(-\|x\|^2/(4t))` gives

$$`\partial_t\Phi=\left(\frac{\|x\|^2}{4t^2}-\frac n{2t}\right)\Phi.`

The positive-time formula agrees with the heat kernel on a neighborhood of
$`t`, and $`4\pi t>0` justifies differentiating its real power.
`cas using hgt_pos` checks this calculation. Together with the
spatial derivatives, it proves the
{bpref "parabolic.heat_kernel_equation"}[heat kernel equation].

*Heat-ball geometry.* The squared slice radius is
$`r_{\mathrm{slice}}^2=2n\tau\log(r^2/(4\pi\tau))`. For $`r\ne0` and
$`\tau\ne0`, its derivative is
$`2n(\log(r^2/(4\pi\tau))-1)`. Differentiating its square root also
requires $`r_{\mathrm{slice}}^2>0`. These domain conditions enter the
{bpref "parabolic.heat_ball_mean_value"}[heat-ball mean value formula].

*The affine Burgers solution.* For $`u(t,x)=(ax+c)/(1+at)` on
$`1+at\ne0`, the derivative tactic proves
$`u_x=a/(1+at)` and $`u_t=-a(ax+c)/(1+at)^2`. Their sum
$`u_t+u\,u_x` cancels to zero, proving the
{bpref "hyperbolic.burgers.affine_solution"}[affine solution of Burgers' initial value problem].

*The endpoint chord.* Integrating the chord of $`f` between $`a` and $`b` gives:

$$`\int_a^b\Bigl(\frac{b-x}{b-a}\,f(a)+\frac{x-a}{b-a}\,f(b)\Bigr)\,dx
  =\frac{(b-a)\,(f(a)+f(b))}2.`

The proof is `cas using hne` with $`b-a\ne0`. The lemma is the
computational half of the strict upper Hermite–Hadamard inequality used by the
p-system shock theory.

```Blueprint.leanExample
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) =
      (b - a) * (f a + f b) / 2 := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  cas using hne
```

# Exact Symbolic Calculus

{include 2 Blueprint.Chapters.Symbolic.Exact}
{include 2 Blueprint.Chapters.Symbolic.Calculus}
{include 2 Blueprint.Chapters.Symbolic.AutomaticDifferentiation}
{include 2 Blueprint.Chapters.Symbolic.PDEExamples}

# Certified Bounds and Models

{leanpde_figure "certificate-budget"}

The exponential in the figure returns us to the heat profile that opened the
chapter. Here the question is quantitative: how far can a polynomial lie from
the function anywhere on the stated interval? Increasing the degree can
reduce that error, but the final zero-width band replaces the polynomial by
the exponential itself: the same inequality with the exponential as its own
model and error zero. The plotted coordinates illustrate the estimate; the
certificates supply proofs.

The shared semantic vocabulary is intentionally small:

* `ApproxOn f g s ε` means
  $`\lVert f(x)-g(x)\rVert\leq\varepsilon` for every $`x\in s`;
* `BoundOn f s c` means $`f(x)\leq c` throughout $`s`;
* `EnclosedOn f s lo hi` means
  $`\mathrm{lo}\leq f(x)\leq\mathrm{hi}` throughout $`s`;
* `ResidualBound r s ε` means $`\lVert r(x)\rVert\leq\varepsilon`
  throughout $`s`.

These are ordinary propositions in the language of approximation theory. The
certificate records `ApproxCert`, `ResidualCert`, `BoundCert`, and
`EnclosureCert` store the functions, domain, and numerical data of one of them
together with a `sound` field proving it; a `QuadratureCert` does the same for
the error of an interval integral. Checked certificates compose through
ordinary Lean theorems.

## One Calculation, End to End

The derivative request

```Blueprint.leanExample (name := symbolicLogDerivative)
-- Retain the nonzero-domain condition
-- for log in the report.
#cas [derive x] (log x)
```

```InlineLean.leanOutput symbolicLogDerivative +summarize
#cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (log x)
Output (scalar ℝ): 1/x
Conditions: x ≠ 0

[CAS.Command.details] More details
```

illustrates the complete exact path. The parser first turns the ordinary
notation into an expression tree. Inspecting the logarithm records a nonzero
condition on its argument. The differentiator constructs the candidate $`1/x`,
and the analytic differentiation theorem justifies the ordinary statement
that the derivative of $`\log` at $`x` is $`1/x`, provided $`x\ne0`.

The condition printed by the inspection command is part of the answer.
To use the derivative at a particular point, a theorem-facing tactic must
prove that condition from the hypotheses. This is the same obligation that
appeared in the affine Burgers denominator and in the logarithmic
fundamental solution away from its pole. Polynomial examples need no such
exclusion, but they pass through the same proof interface.

A CEGA query follows the same architecture but ends in a quantitative
certificate. For

```Blueprint.leanExample (name := symbolicEnclosurePipeline)
-- Exercise the full parser-to-certificate
-- pipeline.
set_option linter.hashCommand false in
#cas [enclose x in [-1 / 10, 1 / 10]] (cos x)
```

```InlineLean.leanOutput symbolicEnclosurePipeline +summarize
#cas [enclose x in [-1 / 10, 1 / 10]]
Domain: x ∈ [-1/10, 1/10] ⊆ ℝ
Input (scalar map ℝ → ℝ): (cos x)
Output (certified interval in ℝ): [0.995004, 1]
Upper bound: 1
Absolute bound: 1
Center and radius: ≈0.997502 ± 0.002498

[CAS.Command.details] More details
```

the parser again produces an expression tree, and a rational interval
evaluator constructs candidate endpoints. A successful computation returns
those endpoints together with a proof that every value on the input interval
lies between them.

Taylor models use enclosures to bound their remainders while retaining
polynomial structure. Derivative bounds also help determine a sufficient
subdivision for quadrature.

{include 2 Blueprint.Chapters.Symbolic.Enclosures}
{include 2 Blueprint.Chapters.Symbolic.TaylorModels}
{include 2 Blueprint.Chapters.Symbolic.DerivativeBounds}

# Certified Integration

{include 2 Blueprint.Chapters.Symbolic.Quadrature}

# Validated Solvers and Certificate Workflows

{include 2 Blueprint.Chapters.Symbolic.ValidatedNonlinearAlgebra}
{include 2 Blueprint.Chapters.Symbolic.CertificateWorkflows}

# Scope, Trust, and Notes

Once an analytic proof has reduced a problem to a supported exact identity,
derivative, integral, enclosure, or residual bound, we can compute that object
and return a theorem that the kernel checks. The surrounding analysis, such as
a weak formulation, trace regularity, a Galerkin limit, or an existence
theorem, is proved in the usual way.

## Relationship to Mathlib Tactics

The architecture is familiar from Mathlib's reflected tactics.
`ring` reifies polynomial expressions and proves equality through a normal
form; `norm_num` proves supported numerical propositions; `positivity`
constructs sign information. PDEAtlas adds a separate reflected language and
soundness layer for the continuous operations documented here. It reuses
Mathlib's analytic definitions and theorem statements rather than replacing
them.

The symbolic frontend supports a finite grammar and bounded searches.
For goals already handled by `ring`, `norm_num`, or `positivity`, use those tactics directly.

Mathlib's `inclusion` engine is another close comparison
{Informal.citet "mathlib-inclusion-2026"}[]. It combines registered enclosure
representations, expression handlers, hypotheses, and subdivision. Its default
and `+kernel` modes check the final computation in the kernel; its optional
`+native` mode additionally trusts compiled evaluation. Its pinned
`dyadic_interval` family and CEGA's FloatLib route are compared in the
{ref "related-work"}[related work chapter], together with the proposed Mathlib
computable-polynomial types and PDEAtlas's rational sparse lists.

## The Trust Boundary

A certificate includes the mathematical claim and its proof. A `QuadratureCert`
includes its `sound` field, an `AntiderivativeCert` includes a checked residual,
and an `EnclosureCert` includes the real inequalities connecting its interval
to the function. Search heuristics, fuel, and subdivision choose which
certificate to try; they do not replace these proof obligations.

CAS and bare `cega` check their computations in Lean's kernel. Their trusted
foundation includes the kernel, its type theory, and the axioms used by the
imported proofs, including propositional extensionality, quotients, and
classical choice.

With native certificates enabled, `cega [fast]` can instead establish a closed
finite computation by compiled evaluation. Its semantic transport remains a
Lean proof, but the generated computation axiom additionally trusts Lean's
compiler and runtime. A theorem using that certificate inherits this trust,
including through later lemmas. The kernel profile disables that native route
and checks the same finite propositions in the kernel. Certificate types
organize the mathematical guarantees; they do not erase the distinction
between these two ways of checking the computation.

## Historical notes and references

Proof-producing computation belongs to a longer line of work. Conventional
computer algebra systems optimize for breadth and speed; proof assistants ask
for an additional object, a proposition checked by the kernel, before a result
can be reused as a theorem. Interval arithmetic, polynomial approximation,
exact real arithmetic, root counting, and certified quadrature have been
formalized in proof assistants such as HOL Light, Coq, and Isabelle.

*Symbolic integration.* {Informal.citet "risch-1969"}[] and
{Informal.citet "bronstein-2005"}[] describe the theory of elementary
integration, including the Risch decision procedure and the Rothstein–Trager
algorithm. The checked search here covers bounded families of primitives and
verifies every candidate by differentiation.

*Taylor models and validated numerics.* {Informal.citet "berz-makino-1998"}[] and
{Informal.citet "makino-berz-2003"}[] provide background on Taylor models and
their use in validated computation, including Taylor-model arithmetic with
wrapping control. The Taylor-model certificates here are approximation and
composition theorems for a finite polynomial with a uniform remainder.

*Interval arithmetic.* {Informal.citet "moore-1966"}[] and
{Informal.citet "neumaier-1990"}[] provide general
background on interval methods. We use exact rational intervals and
proved enclosure theorems for the supported arithmetic and transcendental
operations.

*Modern computer arithmetic.* {Informal.citet "brent-zimmermann-2010"}[] is a general
reference for exact and multiple-precision arithmetic. Here the trusted
statements are the Lean theorems attached to the concrete arithmetic
operations.

*Sturm's theorem and root isolation.* Starting from the real-root count of
{Informal.citet "sturm-1835"}[], the polynomial layer contains checked Sturm
recurrences, root counts, and root-isolation certificates, including the global
isolator of the exact section.
{Informal.citet "cohen-2012"}[] and {Informal.citet "eberl-2015"}[] are useful
comparisons for formal real-algebraic reasoning.

*Formal verification of arithmetic.* {Informal.citet "boutin-1997"}[],
{Informal.citet "gregoire-mahboubi-2005"}[], {Informal.citet "harrison-2007"}[],
and {Informal.citet "melquiond-2008"}[] provide background on reflection
and proved numerical bounds in proof assistants. We follow the same
checked-computation pattern for the expression and
certificate types.

*Lean and Mathlib.* {Informal.citet "de-moura-ullrich-2021"}[] describes the
proof assistant, and {Informal.citet "mathlib-2020"}[] its mathematical library.
They supply the type theory, analytic definitions, and reusable proofs used
throughout this development.

# Textbook Coverage
%%%
tag := "textbook-coverage"
%%%

Cards with source annotations record a document and a cited location. The
tables group those cards by the table of contents of Evans's *Partial
Differential Equations* (second edition), chapter by chapter, followed by
briefer per-location tables for the other documents. Evans references use the
AMS second edition (2010). The map's section starts follow its table of
contents; page references for selected passages are recorded in
`Blueprint/Sources/Evans.md`.

A `CAS` chip marks a card with a declaration that contains a production call
site of the calculator in the computation ledger. It records use of the
calculator inside a declaration, without measuring how much of the proof that
calculation supplies.

The counts are counts of citing cards. A card may specialize or support the
result it cites, and its statement gives the precise hypotheses and
conclusion. *No mapped card* means that no card cites that section. Problem
and reference sections are listed for completeness.

Each card is placed by the first page it cites, so a card citing pages 47 to
51 counts once, in the section containing page 47. Section boundaries come
from the verified contents recorded in the generator. We regenerate the tables
from the card citations whenever we build the Blueprint. Each card name links
to its statement.

{leanpde_textbook_map "evans-pde"}

The remaining source documents are cited far less densely, so for them the map
lists the cited locations as the cards give them: a chapter, a page range, a
section, or an equation number.

{leanpde_textbook_map "others"}

{leanpde_card_index}

# Certified Plots
%%%
tag := "certified-plots"
%%%

The Gaussian kernel, traveling sine, and Burgers profile have already served
as examples of PDE identities. We return to them here to ask a different
question: which values can each function take throughout a small spatial
interval? The enclosure machinery answers that question with a theorem for
each panel. The horizontal axis is cut into forty
rational panels, and a theorem places each function between two rational
endpoints throughout every panel. The theorem is proved by
the `cega` tactic from an interval certificate and checked by Lean's kernel
when the site is built. What is drawn is exactly the union of those certified
boxes: three explicit solutions from the parabolic and hyperbolic chapters, as
the calculator certified them.

How to read a plot. Each colour is one value of the time parameter $`t`. Each
shaded panel is one theorem: its horizontal extent is the panel $`[a, b]` of
the $`x`-axis and its vertical extent is the certified range $`[\ell, h]`, so
the true curve runs inside the shaded strip. Each strip covers the function's
variation over the panel and may also include overestimation from the enclosure
calculation. Its endpoints are rounded outward to six decimal places so that
the statements stay readable.

Selecting a panel opens its row in the theorem listing under the plot. Each
row gives the panel, the certified range, and the full Lean statement, of the
form

```
EnclosedOn (fun p : ℝ^1 ↦ Real.sin (p 0 - 1))
  {p | 0 ≤ p 0 ∧ p 0 ≤ 3/20} (-841519/1000000) (-375639/500000)
```

read "for every point $`p` of the one-dimensional Euclidean space with
$`0 \le p_0 \le 3/20`, the value $`\sin(p_0 - 1)` lies between the two
rationals". The theorem name links to its line in the generated module, which
the Blueprint build compiles. The generator asks the calculator for every
certified range before writing the theorems, and it checks that the drawing
and the theorems list the same panels and bounds.

The first plot is the one-dimensional heat kernel
$$`\Phi(x, t) = \frac{1}{\sqrt{4\pi t}}\, e^{-x^2/(4t)}`
at $`t = 1/4`, $`1/2` and $`1` on $`x \in [-3, 3]`. Its total mass is one at
every time, so the curve spreads and flattens as $`t` grows. The panels are
narrow strips near the tails, where the kernel is nearly flat, and taller
around the flanks of the peak. The certificates handle the real power
$`(4\pi t)^{-1/2}`, the exponential and the constant $`\pi` together; the
Gaussian-kernel section of the parabolic chapter proves the kernel's
properties as theorems and the {ref "textbook-coverage"}[textbook coverage map]
locates them in Evans's §2.3.

{leanpde_certified_plot "heat"}

The second plot is d'Alembert's traveling sine wave $`u(x, t) = \sin(x - t)`
at $`t = 1/2`, $`1` and $`3/2` on $`x \in [-3, 3]`. The wave moves to the
right with unit speed, so the three curves are translates of one another by
one half. The function is the one whose wave-equation residual is checked in
the
{ref "symbolic-sine-example"}[wave and transport example].

{leanpde_certified_plot "wave"}

The third plot is the self-similar Burgers profile $`u(x, t) = x / t` at
$`t = 1/2`, $`1` and $`2` on $`x \in [-1, 1]`. This is the formula used
inside a rarefaction fan. The
{bpref "hyperbolic.burgers.riemann_solution"}[full Riemann solution] restricts
it to the region between the rays determined by the two states and joins it
to constant values outside. The plot encloses only the fan formula, on a
fixed window, without the outer states. The
profile is increasing and linear in $`x` on every panel, so its exact range is
determined by its endpoint values. The strips show how the fan opens with
time: the same window of $`x` covers a smaller range of velocities at later
times.

{leanpde_certified_plot "rarefaction"}
