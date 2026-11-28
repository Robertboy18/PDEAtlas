<h1 align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset=".github/assets/readme-heading-dark.png">
    <img src=".github/assets/readme-heading.png" alt="PDEAtlas: Partial Differential Equations in Lean" width="772">
  </picture>
</h1>

PDEAtlas is a library of partial differential equations in Lean 4 and Mathlib. It follows Lawrence C.
Evans's *Partial Differential Equations*, second edition, and formalizes selected results from every
section of chapters 2 to 12 of the book: the four linear equations, first-order equations, Sobolev
spaces, elliptic and evolution equations, the calculus of variations, Hamilton–Jacobi equations,
conservation laws and nonlinear waves. Beyond the book it covers incompressible fluid mechanics. It
has about 1.17 million lines of Lean and 39,900 theorems.

* [Blueprint](https://lean-dojo.github.io/PDEAtlas/): the book that goes with the library, with
  statements, proof ideas, worked examples and figures linked to the Lean declarations, and a map of
  which sections of Evans each statement formalizes. The site is rendered on Lean 4.36, with
  VersoBlueprint at the commit of its open Lean 4.36 port
  ([leanprover/verso-blueprint#504](https://github.com/leanprover/verso-blueprint/pull/504)). We'll
  move the pin to the release branch when the port lands
  ([build notes](Blueprint/README.md#published-site)).
* [BlowupZoo](https://github.com/lean-dojo/BlowupZoo): finite-time blowup and nonuniqueness
  theorems for fluid equations, built on PDEAtlas
* [SymLean](https://github.com/lean-dojo/SymLean): the computer algebra system PDEAtlas computes with

I wanted to open Evans and be able to use the theorems from a graduate PDE course in a Lean proof,
with all their hypotheses in view. PDEAtlas is also an exposition: the Blueprint explains each
result with its proof idea and worked examples, next to its Lean statement. Lawrence C. Evans gave
us his full support in following his book.

## Three examples from Evans

- Smooth functions are dense in every Sobolev space $W^{k,p}(U)$, $1 \le p < \infty$, on every open set $U$.
  Evans §5.3.2, Theorem 2, proves the result for bounded $U$.
  [`OpenDomain.lean`](PDE/Spaces/Sobolev/Approximation/Density/OpenDomain.lean)
- Weak solutions of second-order parabolic equations exist and are unique under the assumptions
  of §7.1.2, Theorems 3 and 4, with the symmetry assumption $a^{ij} = a^{ji}$ dropped.
  [`MeasurableExistence.lean`](PDE/Parabolic/Heat/Variational/MeasurableExistence.lean)
- Kaplan's lifespan bound for $u_t - \Delta u = u^2$ (§9.4.1, Theorem 1) holds on a bounded open set
  whose boundary has no assumed regularity, for solutions that are only continuous up to the
  boundary. The theorem takes a Dirichlet eigenfunction $w \ge 0$ with eigenvalue $\lambda > 0$ and
  $\int w = 1$ that is $C^2$ inside and continuous up to the boundary, and nonnegative initial data $g$
  with $\eta_0 = \int w g > \lambda$; the solution then lives at most $\lambda^{-1} \log(\eta_0 / (\eta_0 - \lambda))$.
  [`DirichletBlowup.lean`](PDE/Parabolic/Heat/Nonlinear/DirichletBlowup.lean)

The regularity theory of Chapter 8 goes one step past the book. A local minimizer of $\int F(\nabla u)$
in $W^{1,2}_{\mathrm{loc}}$ has a real-analytic representative when $F$ is real-analytic on $\mathbb{R}^n$ with
$\theta|\xi|^2 \le D^2F(p)(\xi, \xi) \le \Lambda|\xi|^2$ for some $\theta > 0$, in every dimension and on every open
set. For smooth $F$ the representative is smooth, and for $F \in C^2$ it is $C^1$ with a locally Hölder
continuous gradient.
[`Analytic.lean`](PDE/CalculusOfVariations/LocalMinimizer/Analytic.lean)

We coordinate work on general PDE lemmas with the
[Tau Ceti PDE roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/PDE/README.md).

## Example

```lean
import PDE

#cas [pdesolve u t x, u 0 x = sin x + 3 * sin (2 * x), u t 0 = 0, u t pi = 0] (u_t = 2 * u_xx)
-- u(t, x) = Real.exp (-(2 * t)) * Real.sin x + 3 * Real.exp (-(8 * t)) * Real.sin (2 * x)
```

This is the heat equation $u_t = 2 u_{xx}$ on $[0, \pi]$, with $u = 0$ at both ends and
$u = \sin x + 3 \sin 2x$ at time $0$. Under "More details" the report shows the checked theorem that the formula solves the
problem and that every solution that is $C^2$ on the whole plane equals it on $[0, \pi]$ for $t \ge 0$. The
uniqueness proof uses the energy method. This heat solver takes initial data given as a finite
sum of sine modes. It refuses `sin (sin x)` on $[0, \pi]$ even though the datum satisfies both
boundary values. The command also has routes for transport and wave equations, and PDEAtlas
extends SymLean's `cas` and `cega` to PDE operators.

In a proof, the `cas` tactic does the same calculations:

```lean
example (p : ℝ^3) (hp : 0 < p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) :
    PDE.laplacian (fun q : ℝ^3 ↦ 1 / Real.sqrt (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2)) p = 0 := by
  cas
```

## What is in it

| Evans | Topics | Where |
| --- | --- | --- |
| Ch. 2 | Transport, Laplace's, heat and wave equations | [`Hyperbolic/Transport`](PDE/Hyperbolic/Transport), [`Elliptic/PotentialTheory`](PDE/Elliptic/PotentialTheory), [`Parabolic/Heat`](PDE/Parabolic/Heat), [`Hyperbolic/Classical`](PDE/Hyperbolic/Classical) |
| Ch. 3 | Complete integrals, characteristics, Hamilton–Jacobi equations, conservation laws | [`Hyperbolic/FirstOrder`](PDE/Hyperbolic/FirstOrder), [`Hyperbolic/HamiltonJacobi`](PDE/Hyperbolic/HamiltonJacobi), [`Hyperbolic/ConservationLaw`](PDE/Hyperbolic/ConservationLaw) |
| Ch. 4 | Separation of variables, similarity solutions, transforms, asymptotics, power series and Cauchy–Kovalevskaya | [`Representations`](PDE/Representations), [`Cauchy`](PDE/Cauchy) |
| Ch. 5 | Hölder and Sobolev spaces, approximation, extension, traces, Sobolev inequalities, compactness | [`Spaces`](PDE/Spaces) |
| Ch. 6 | Weak solutions, regularity, maximum principles, eigenvalues | [`Elliptic`](PDE/Elliptic) |
| Ch. 7 | Parabolic and hyperbolic equations, first-order hyperbolic systems, semigroups | [`Parabolic`](PDE/Parabolic), [`Hyperbolic`](PDE/Hyperbolic), [`Analysis/Evolution`](PDE/Analysis/Evolution) |
| Ch. 8 | Minimizers, regularity, constraints, critical points, Noether's theorem | [`CalculusOfVariations`](PDE/CalculusOfVariations) |
| Ch. 9 | Monotonicity, fixed points, sub- and supersolutions, nonexistence, gradient flows | [`Elliptic/Monotone`](PDE/Elliptic/Monotone), [`Elliptic/Semilinear`](PDE/Elliptic/Semilinear), [`Analysis/Evolution/GradientFlow`](PDE/Analysis/Evolution/GradientFlow) |
| Ch. 10 | Viscosity solutions, uniqueness, optimal control | [`Hyperbolic/HamiltonJacobi`](PDE/Hyperbolic/HamiltonJacobi) |
| Ch. 11 | Riemann's problem, systems of two conservation laws, entropy criteria | [`Hyperbolic/ConservationLaw`](PDE/Hyperbolic/ConservationLaw) |
| Ch. 12 | Energy, semilinear and critical-power waves, nonexistence | [`Hyperbolic/NonlinearWave`](PDE/Hyperbolic/NonlinearWave) |
| Beyond | Stokes, Euler, Navier–Stokes, Boussinesq, axisymmetric Euler, the De Gregorio model, transport systems in the half-plane with a general velocity law | [`Fluid`](PDE/Fluid) |

Each module doc says where its statements differ from the book. [`PDE/Examples`](PDE/Examples)
holds compiled examples, which no library module imports. The general analysis that the equations
share is under [`Analysis`](PDE/Analysis).

Hilbert's problems on the calculus of variations have a folder of their own,
[`PDE/HilbertProblems`](PDE/HilbertProblems). Each file quotes the problem as Hilbert asked it in
1900 and proves an answer for a stated class from the general theory.

- Problem 19, for one unknown function and integrands $F(\nabla u)$ whose second derivative is uniformly
  positive definite and bounded: when $F$ is real-analytic, a local minimizer in $W^{1,2}_{\mathrm{loc}}$ has a
  real-analytic representative, and a solution of the Euler–Lagrange equation with two continuous
  derivatives is real-analytic. Joined with Problem 20: on a bounded open set a minimizer with any
  boundary datum $g \in W^{1,2}$ ($u - g \in W^{1,2}_0$) exists and has a representative that is analytic
  inside.
  [`Nineteenth.lean`](PDE/HilbertProblems/Nineteenth.lean)
- Problem 20, for convex integrands of growth $p$: on a bounded set, the integral $\int F(x, u, Du)\thinspace dx$
  of any number of unknown functions has a minimizer with given boundary values in $W^{1,p}$,
  $1 < p < \infty$, when $F$ is measurable, continuous in $u$, convex in $Du$, at least $c|Du|^p - b(x)$
  and at most $a(x) + D|(u, Du)|^p$. If $F$ also has a derivative of growth $p - 1$, every minimizer is a
  weak solution of the Euler–Lagrange system. Dirichlet's principle is the case $F = |Du|^2$.
  [`Twentieth.lean`](PDE/HilbertProblems/Twentieth.lean)
- Problem 23, for the simple integral and curves along which the integrands are integrable: if
  the slope function $p$ solves Hilbert's first-order equation (1*) on a convex open region, the
  integral $J^\ast$ does not depend on the path. Weierstrass's formula $J(y) - J(\bar y) = \int E(y_x, p)\thinspace dx$
  follows, and $E \ge 0$ makes the curve $\bar y$ of the field a minimum.
  For a multiple integral, with a field that is given by a one-parameter family $Z_t$ of extremal
  surfaces: $J^\ast$ has the same value on two parameter graphs $z = Z_{\theta(x)}(x)$ whose parameters $\theta$
  agree on the boundary, and so on two parameter graphs through one boundary curve when the surfaces of
  the family do not meet over the boundary. For $\theta = 0$ on the boundary this value is $J(Z_0)$, and
  $J(z) - J(Z_0) = \int E\thinspace d\omega$, Hilbert's formula (IV). Slope functions of the point are not used.
  [`TwentyThird.lean`](PDE/HilbertProblems/TwentyThird.lean)

## Standards

- Lean's kernel checks every proof. No proof uses `sorry`, and every declaration of the library
  and of its examples rests only on Lean's three standard axioms, `propext`, `Classical.choice`
  and `Quot.sound`.
- The library builds with Mathlib's standard set of linters, and warnings are errors; the forty-two
  modules of [NOTICE](NOTICE) turn off the linter of the file header.
- Every theorem states all of its hypotheses, regularity included. This matters in Lean, where
  `fderiv` is zero at points where a function is not differentiable, so an equation written with
  derivatives is the classical PDE only together with the regularity hypotheses our solution
  classes carry.
- Every module starts with a doc that says what it proves and where its statements differ from
  their source, and every public theorem, definition, instance, type and field of a structure
  that is written in a source file of the library has a docstring.
- No two theorems of the library have the same statement as kernel terms, and none has the
  statement of a theorem of Lean, Mathlib, SymLean or FloatLib that the library imports.
- By default the kernel also checks the numerical certificates, instead of trusting compiled code.

[TRUST.md](TRUST.md) says what a theorem of the library trusts, how to repeat these checks and what
they cannot see.

## Using PDEAtlas

PDEAtlas builds with Lean v4.36.0 and Mathlib v4.36.0. Add it to your `lakefile.lean`:

```lean
require LeanPDE from git "https://github.com/lean-dojo/PDEAtlas.git" @ "main"
```

The Lake package is `LeanPDE` and its modules live under `PDE`. Run `lake update LeanPDE` and
`lake exe cache get`; SymLean and FloatLib come along. Then start a file with `import PDE`, or
import a single module for a smaller load. Mathlib comes from its cache, and Lake compiles
SymLean, FloatLib and the 6,598 library modules of PDEAtlas.

## Related projects

The Blueprint's [Related Work chapter](https://lean-dojo.github.io/PDEAtlas/Related-Work/) compares
PDEAtlas with Soto Franco and Marshall-Stevens's
[EllipticPDE](https://github.com/alejandro-soto-franco/EllipticPDE), Armstrong and Kempe's
De Giorgi–Nash–Moser theory in Lean ([arXiv:2604.05984](https://arxiv.org/abs/2604.05984)), Tomoki
Uda's [leray-hopf](https://github.com/uda-lab/leray-hopf), and work on computer algebra and
verified numerics.

## Citation, license and acknowledgements

```bibtex
@misc{pdeatlas,
  author       = {Robert Joseph George and Changhe Yang and Peicong Song and Thomas Y. Hou and Anima Anandkumar},
  title        = {{PDEAtlas}: Partial differential equations in {Lean}},
  year         = {2026},
  howpublished = {\url{https://github.com/lean-dojo/PDEAtlas}},
  note         = {Lean v4.36.0}
}
```

Our textbook reference is Lawrence C. Evans, *Partial Differential Equations*, second edition,
Graduate Studies in Mathematics **19**, American Mathematical Society, 2010, ISBN 978-0-8218-4974-3
([AMS record](https://www.ams.org/bookpages/gsm-19-r)). The release metadata is in
[formalization.yaml](formalization.yaml), and [CONTRIBUTING.md](CONTRIBUTING.md) says how to contribute.

PDEAtlas is written at Caltech by Robert Joseph George, Changhe Yang, Peicong Song, Thomas Y. Hou
and Anima Anandkumar. It is released under the [Apache License 2.0](LICENSE), except
forty-two modules of general lemmas under `PDE/Analysis` that carry proofs of Levent Alpöge and
Tristan Buckmaster, included with their permission, from the Lean package of their paper on the
Navier–Stokes equations; [NOTICE](NOTICE) lists them and explains their provenance. No other module
imports them, apart from the root `PDE.lean`, so the rest of the library can be used without them.

Everything here starts from [Mathlib](https://github.com/leanprover-community/mathlib4). The
Blueprint is written with [Verso](https://github.com/leanprover/verso),
[VersoBlueprint](https://github.com/leanprover/verso-blueprint) and
[SubVerso](https://github.com/leanprover/subverso).
