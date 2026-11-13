# Nonuniqueness for the unforced three-dimensional Navier–Stokes equation

Thomas Hou, Yixuan Wang, and Changhe Yang,
*Nonuniqueness of Leray–Hopf solutions to the unforced incompressible
3D Navier–Stokes Equation*, arXiv:2509.25116v2 (19 March 2026).

Primary source: https://arxiv.org/abs/2509.25116v2

Sections 3.1–3.2 develop validation around a numerical candidate: a finite-rank
correction makes the approximate linear solve coercive, and a weak-topology
fixed-point argument produces an exact solution when the residual budget closes.
LeanPDE proves the correction identity for bounded operators and coordinate maps,
retaining both interpolation and solve residuals. Its quadratic Dirichlet theorem
constructs a weak solution near a supplied candidate under explicit reconstruction,
coercivity, embedding, and error hypotheses. The interval and unit-cube examples
are Poisson validation examples that verify all their own hypotheses.

Section 4.1 separates the stationary similarity operator into a compensated
principal part and a compact perturbation. LeanPDE proves the principal energy
identity first for smooth compact test fields, then constructs its weak bilinear
form on bounded open domains. A weakly divergence-free bounded Sobolev background
and a bounded matrix field satisfying the stated compensation inequality give
coercivity. Restriction to the closed divergence kernel gives a unique principal
linear variational solve.

The convection form accepts an independent `L⁴` coefficient and zero-boundary
Sobolev unknown and test fields, using a supplied faithful scalar `H¹₀ → L⁴`
realization. Energy cancellation follows from the coefficient's `L²` values and
diagonal weak derivatives and zero weak divergence. In particular, a solenoidal
`H¹` coefficient can have nonzero trace on the artificial ball boundary.
The quantitative bound uses the full gradient norm with constant one in the
Lebesgue coordinate norms. Adding this transport to the compensated principal
form preserves coercivity and gives a unique bounded-domain solenoidal linear
solve without a smallness assumption on the advecting field.

A general transport-validation theorem formalizes the modified fixed-point
argument of Section 4.3, equation (4.24): transport stays in the linear solve,
and only the remaining nonlinear load enters the radius budget. Compactness
gives the fixed point without a contraction assumption. This theorem keeps the
coercivity, compact embedding, residual, and remainder budgets as hypotheses.

The fluid correction theorem combines these arguments with the actual
Lebesgue convection pairing. Supplied linear maps realize the coefficient and
correction-gradient matrix in the weaker `L⁴` topology. Their boundedness proves
continuity of the quadratic remainder on the energy set, so it is not a separate
nonlinear hypothesis. The finite-rank specialization in
`PDE/Fluid/NavierStokes/FiniteRankCorrection.lean` derives the sharp nonlinear
mass bound from a Gram quadratic-form bound, bounded derivative matrices, and
pairwise basis interaction bounds. It proves the coefficient-space estimate and
identifies the resulting `L²` pairing with the actual `L⁴` convection pairing
through almost-everywhere equality of their representatives. The coefficient is
`sqrt(g) A + g B`, with separate Gram, derivative-operator, and interaction budgets.
These numerical estimates and the identification of the reconstruction maps are
hypotheses. Both theorems also hold in a closed subspace of the
solenoidal space, with every hypothesis required only there and the equation tested by
its fields; for the paper's candidate the subspace is the even axisymmetric sector.

The split-energy variant retains separate `L²` and gradient radii from (4.27).
It proves invariant-set bounds from
`ε + M r₀² ≤ a r₀` and `a r₀² ≤ 4 b r₁²`, then uses compactness of that
closed convex set in the weaker topology. The advecting-field space is separate
from the zero-boundary solution space. The general Lebesgue transport pairing
also takes the derivative matrix separately, allowing the finite-rank correction
to have a nonzero trace on the artificial ball boundary.

Section 4.5.1 of the paper evaluates these two scalar budgets for its numerical
profile.

LeanPDE constructs distinct suitable Leray–Hopf solutions from any unstable profile
(`NavierStokes.Nonuniqueness.of_unstableProfile`). The certificates for the paper's numerical
profile and unstable eigenpair, and with them the nonuniqueness theorem `NavierStokes.nonuniqueness`,
are formalized in the companion repository [BlowupZoo](https://github.com/Robertboy18/BlowupZoo), at its level 8.

The cited preprint is distributed under CC BY 4.0, as linked from its arXiv record:
https://creativecommons.org/licenses/by/4.0/
This does not establish a reuse license for the accompanying numerical code or data.
