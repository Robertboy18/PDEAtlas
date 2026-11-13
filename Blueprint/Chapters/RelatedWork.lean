/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Mathlib.Tactic.Linter.EmptyLine
import Mathlib.Tactic.Linter.HashCommandLinter
import Verso
import VersoBlueprint

/-!
# Related work

Primary-source comparisons with PDE formalization, verified computer algebra,
and validated numerics.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- Blank lines delimit paragraphs within the Verso document.
set_option linter.style.emptyLine false

set_option linter.hashCommand false in
#doc (Manual) "Related Work" =>
%%%
htmlSplit := .never
tag := "related-work"
shortTitle := "Related Work"
%%%

Computing a PDE residual, bounding an approximation error, and constructing a
solution are different mathematical tasks. A symbolic identity can verify a
candidate formula; a numerical enclosure can certify an estimate; an existence
proof must supply the analytic argument connecting its hypotheses to a solution.

# Shared analysis

Mathlib supplies a common mathematical language as well as individual theorems.
Its account of a unified, community-maintained library emphasizes the hierarchy
of structures and the organization that makes results reusable
{Informal.citet "mathlib-2020"}[]. For PDE work, using the same integrals,
derivatives, function spaces, and continuous linear maps lets an estimate connect
to existing analysis. PDEAtlas builds on those definitions. Compatibility also
requires decisions about domains, boundary conditions, and solution concepts:
two theorems called “Sobolev embedding” need not have interchangeable hypotheses.

Terence Tao's Lean companion to _Analysis I_ makes this transition explicit
{Informal.citet "tao-analysis-2026"}[]. Its commentary refers readers to the book
and documents changes required for Mathlib compatibility. Chapter 2 develops a
separate natural-number type; an epilogue introduces its correspondence with
Mathlib's natural numbers before later chapters use the shared library.
Exercises deliberately retain `sorry` placeholders, including some of those
correspondence proofs. PDE libraries need analogous identifications: for a
Dirichlet problem, identifying the closure of
compactly supported smooth functions in a Sobolev norm with the space of
functions having zero boundary trace lets an estimate stated in one formulation
apply in the other.

The July 2024 Zulip discussion that helped start PDEAtlas
{Informal.citet "george-pde-zulip-2024"}[] pointed to substantial analysis already
in Mathlib. Turning those foundations into PDE proofs required further work.

Tau Ceti explores another way to extend that shared library. Its human-written
roadmaps direct AI contributors, with adversarial review aimed at reusable
mathematics; the project explicitly defers to Mathlib's design decisions
{Informal.citet "tauceti-2026"}[]. Its PDE roadmap organizes the analysis needed for elliptic and parabolic
research into six dependency lanes {Informal.citet "tauceti-pde-roadmap-2026"}[].
A ✓ marks implemented coverage of the named area, under the hypotheses of
PDEAtlas's theorems. It is not a claim that every milestone or every domain
regularity in that lane is covered. “Compare” marks a lane whose full scope
still needs a statement-level comparison.

:::table +header (align := left) (tag := "pde-coverage")
*
  * Area
  * PDEAtlas coverage
  * Corresponding PDEAtlas development
*
  * A: domain function spaces
  * ✓
  * Weak-derivative Sobolev spaces, density, embeddings, traces, extension and compactness in
    `PDE/Spaces/Sobolev/`.
*
  * B: harmonic-analysis estimates
  * Compare
  * `PDE/Analysis/` contains reusable estimate infrastructure; the full proposed
    singular-integral and interpolation program needs a separate statement-level comparison.
*
  * C: maximum principles and potential theory
  * ✓
  * Classical harmonic analysis and ball/half-space kernels in `PDE/Elliptic/Classical/` and
    `PotentialTheory/`.
*
  * D: linear elliptic existence
  * ✓
  * Weak Dirichlet problems, Fredholm alternatives and spectral constructions in
    `PDE/Elliptic/Variational/`.
*
  * E: elliptic regularity
  * ✓
  * Interior, boundary and higher-order results in `PDE/Elliptic/Regularity/`, with coefficient
    and boundary hypotheses in each theorem.
*
  * F: parabolic evolution
  * ✓
  * Weak evolution, heat constructions, energy estimates and Dirichlet semigroups in
    `PDE/Analysis/Evolution/` and `PDE/Parabolic/`.
*
  * Symbolic calculus and certified numerics
  * ✓
  * The {ref "verified-computation"}[CAS and CEGA chapter]: normalization,
    differentiation, supported integration, interval bounds and certificate APIs.
*
  * Hyperbolic equations and fluid mechanics
  * ✓
  * Wave and transport theory in `PDE/Hyperbolic/`, and Euler, Navier–Stokes
    and Stokes constructions in `PDE/Fluid/`.
:::

The closest overlap is the domain Sobolev and energy-method infrastructure.
A whole-space Fourier Sobolev space and a domain weak-derivative space
require an agreement theorem in the appropriate exponent range. Likewise, a trace theorem on a smooth graph domain
must not be presented as the roadmap's full Lipschitz-domain theorem.
PDEAtlas's hyperbolic equations, fluid constructions and CAS add further uses
for this shared analysis. We aim to contribute suitable general results to
Mathlib and coordinate contributions with Tau Ceti's maintainers and roadmap.

# Other PDE libraries and geometric flow

Soto Franco and Marshall-Stevens's
[EllipticPDE](https://github.com/alejandro-soto-franco/EllipticPDE)
formalizes linear divergence-form Dirichlet theory
[with a companion paper](https://arxiv.org/abs/2609.32561).
Its named results cover weak solvability, Gårding's inequality, Fredholm theory,
spectral compactness, and interior regularity. This overlaps directly with
PDEAtlas's variational and regularity layers. Their work concentrates on linear
elliptic solvability, while PDEAtlas follows a wider textbook progression and
connects that analysis to evolution equations and certified calculations.
The useful compatibility questions concern their Sobolev-space definitions,
coefficient assumptions, and the passage from a weak solution to a regular
representative. A Hölder conclusion obtained from smooth-coefficient Sobolev
regularity has different hypotheses from De Giorgi–Nash–Moser theory.

Qin, Liao, Khaitan and Chow's
[Poincaré formalization](https://github.com/frenzymath/PoincareConjecture)
follows Hamilton–Perelman geometric analysis:
[their paper](https://arxiv.org/abs/2609.33842) describes Ricci flow with surgery
and finite-time extinction leading to the smooth and topological Poincaré
conjectures. This is PDE formalization in a geometric setting, with evolving
metrics and curvature. PDEAtlas's present exposition concerns Euclidean-domain
analysis. Sharing estimates, compactness or evolution arguments would require
connecting our Euclidean objects to the geometric objects and hypotheses of
that project.

# Regularity, random media, and fluid flow

Scott Armstrong and Julia Kempe's formalization of De Giorgi–Nash–Moser theory
proves regularity from a weak formulation
{Informal.citet "armstrong-kempe-2026"}[]. For uniformly elliptic divergence-form
equations with bounded measurable coefficients, their development in dimensions
at least three establishes local boundedness, weak Harnack and Harnack
inequalities, and interior Hölder regularity. The mathematical gain is the passage
from a weak formulation to pointwise regularity without assuming smooth
coefficients. Their supporting Sobolev and weak-solution infrastructure overlaps
with the foundations needed throughout PDE formalization.

Armstrong and Kuusi's CoarseGraining development extends this direction to
quantitative stochastic homogenization
{Informal.citet "armstrong-kuusi-coarsegraining-2026"}[]. Its public comparison
theorem is stated for uniformly elliptic, isotropic coefficient laws. Their
Superdiffusion formalization treats results from work with Bou-Rabee on random
incompressible flows {Informal.citet "armstrong-kuusi-superdiffusion-2026"}[],
for a model with specified properties.

For Navier–Stokes, Tomoki Uda's Leray–Hopf project reports global weak-existence
theorems for the unforced equation on the three-dimensional torus and on
$`\mathbb R^3`, together with energy inequalities
{Informal.citet "uda-leray-hopf-2026"}[]. Its public weak formulation uses
separated tests $`\psi(t)w(x)`, and its existence theorems are for weak
solutions.

# Computation with a mathematical conclusion

Verified computer algebra has its own history in Lean. Lewis and Wu's
Lean–Mathematica interface exchanges expressions in both directions and
reconstructs Lean proofs for selected computations returned by Mathematica
{Informal.citet "lewis-wu-2021"}[]. The external algebra system acts as an
untrusted source of candidates. This distinction also matters for an
antiderivative: finding a formula and proving that its derivative equals the
integrand, on the required domain, are separate steps.

Hex provides a more recent comparison inside Lean itself. Its released libraries
cover verified computational algebra, including polynomial algorithms, lattice
basis reduction, and algebraic numbers, with separate Mathlib correspondence
layers where available {Informal.citet "hex-2026"}[]. This exact algebra supports
computations with finite mathematical objects. PDEAtlas connects symbolic
differentiation, supported antiderivatives, and certified enclosures to analytic
functions and PDE residuals. Its procedures return theorems over the analytic
definitions used by the surrounding proofs, with domain and regularity
conditions retained in the statements. A residual calculation can then become
a proved identity inside an analytic argument.

Validated numerics contributes a complementary guarantee. Boldo, Clément,
Filliâtre, Mayero, Melquiond, and Weis verified a C implementation of a
one-dimensional acoustic wave scheme, accounting for both discretization and
floating-point roundoff errors
{Informal.citet "boldo-et-al-wave-2013"}[]. Their analysis connects the program,
the discrete scheme, and the continuous equation. The distinction explains why
certifying arithmetic alone cannot establish the accuracy of a PDE solver:
stability and approximation estimates must connect those levels.

The Rocq Interval library automates bounds on real expressions and integrals
{Informal.citet "rocq-interval-2026"}[]. In Lean, LeanCert turns interval,
root, and integral certificates into mathematical conclusions
{Informal.citet "leancert-2026"}[]. Its interval and quadrature tools overlap
closely with CEGA: a finite calculation produces a bound that an analytic proof
can use. In PDEAtlas, CEGA keeps the function and its domain attached to that
bound, so an estimate for a residual on one box can feed into a larger PDE
argument. LeanCert offers kernel reduction and a default native evaluation
route; the latter additionally relies on Lean's compiler and runtime.

# Mathlib's enclosure and polynomial computation

David Ledvinka's `inclusion` engine is already present in PDEAtlas's pinned
Mathlib revision {Informal.citet "mathlib-inclusion-2026"}[]. It connects
computable enclosure representations to sets through `ToSet`, then combines
registered expression handlers, hypotheses, and subdivision to prove a
membership statement. The `dyadic_interval` wrapper selects its real dyadic
interval family. Both its default mode and `+kernel` check the final
computation in the kernel; `+kernel` skips the preliminary fast evaluation.
The optional `+native` mode additionally trusts compiled evaluation.

In PDEAtlas's pinned Mathlib, the dyadic family handles rational constants,
addition, negation, subtraction, multiplication, comparisons, and subdivision;
general reciprocals and the exponential, logarithmic, and trigonometric
functions have no registered handlers there, although the engine itself is
extensible. CEGA's rational route obtains field operations and
elementary-function enclosures from FloatLib, with the required domain
conditions and local refinements. Both routes prove arithmetic bounds such as
`x * y ≤ 21` on a box, while bounds on `1 / (1 + x)`, `exp x`, `log x`, and
`sin x` need CEGA's ranges, which
[SymLean](https://github.com/Robertboy18/SymLean) also registers as the
`cega_real` family of `dyadic_interval`.

Computable polynomial representations are another point of contact.
Michail Karatarakis's proposed `SparsePoly` and `MvSparsePoly` types
{Informal.citet "mathlib-sparsepoly-2026"}[]
{Informal.citet "mathlib-mvsparsepoly-2026"}[]
carry ordered, nonzero-term invariants over generic coefficient rings and
provide semantics in Mathlib's polynomial types. PDEAtlas uses raw lists of
rational coefficients and exponent vectors. Its executable normalization and
arithmetic preserve evaluation, and its noncomputable Mathlib bridges
identify the resulting polynomial semantics. Since different lists can denote
the same polynomial, these theorems concern evaluation rather than a
canonical form. The companion
`poly_dvd_cert` proposal searches for quotient evidence in compiled metacode
and checks the resulting identity with `ring`
{Informal.citet "mathlib-poly-dvd-cert-2026"}[]: proposing algebraic evidence
and verifying its consequence are separate steps here too.

# FloatLib, exact algebra, and CEGA

FloatLib is our library for connecting executable floating-point arithmetic to
exact specifications and theorems about decoded real values
{Informal.citet "floatlib-2026"}[]. Its
[official guide](https://lean-dojo.github.io/FloatLib/#/chapter/using-the-library)
develops this connection through arithmetic and interval examples. TorchLean
also uses FloatLib {Informal.citet "torchlean-2026"}[], applying the arithmetic
library in a different mathematical development.

In PDEAtlas, exact symbolic computation supplies identities, derivatives, and
analytic side conditions. CEGA's ordinary interval queries use rational
endpoints and exact rational calculations to certify bounds on real functions.
FloatLib supplies their interval arithmetic, elementary-function enclosures,
and outward rounding. PDEAtlas's rational interval adds an endpoint-order proof
to `FloatLib.Numerics.Interval ℚ`. For generic expression evaluation, a
semantic translation maps CAS syntax into FloatLib's own expression language;
upstream backends supply the endpoint representation and numerical operations.
Their containment theorems cover arbitrary real members of the input intervals.
Failed decoding, unsupported domains, or unrepresentable output bounds return
no enclosure.

FloatLib also provides certified IEEE binary32 operations; CEGA's concrete
backend is rational and does not dispatch to them.

The connection to the CAS is explicit in the derivative-enclosure bridge.
PDEAtlas's `CompiledDerivative` certificate supplies the derivative expression
and its analytic justification on the chosen panel. The numerical evaluator
must enclose that same expression, with an input interval covering the whole
panel. Its soundness theorem then gives a bound on the requested derivative.
More generally, the shared real-interval interface allows a proved enclosure
to produce CEGA enclosure and residual certificates. The bridge requires a
proof that the original real function lies in the interval throughout the
stated domain.

FloatLib proves an exponential enclosure using argument reduction and a Taylor remainder,
then rounds its bounds outward when the chosen representation requires it.
PDEAtlas connects that containment theorem to the original symbolic expression
and its domain. Derivative and quadrature certificates add the analytic
regularity and remainder estimates needed for the surrounding PDE argument.

The numerical APIs also contain scalar and piecewise Taylor approximation
certificates, whose general constructors take real Taylor coefficients and so
are noncomputable; the derivative enclosures and rational error calculations
that feed them are executable. The polynomial subsystem includes a global root
isolator built from checked square-free reduction, a generated Cauchy bound,
and Sturm subdivision. When its finite search succeeds, the resulting atlas
covers every distinct real root.

Armstrong and collaborators describe extensive model assistance under human
supervision {Informal.citet "armstrong-kempe-2026"}[]; Tau Ceti organizes assisted
formalization around a shared library {Informal.citet "tauceti-2026"}[].
PDEAtlas aims to make its Sobolev, weak-solution, and certified-estimate
infrastructure reusable by other Mathlib-based PDE projects, and to prepare
suitable components for review in Mathlib and Tau Ceti.
