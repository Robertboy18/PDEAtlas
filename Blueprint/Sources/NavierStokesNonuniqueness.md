# Nonuniqueness for the unforced three-dimensional Navier–Stokes equation

Thomas Hou, Yixuan Wang, and Changhe Yang,
*Nonuniqueness of Leray–Hopf solutions to the unforced incompressible
3D Navier–Stokes Equation*, arXiv:2509.25116v2 (19 March 2026).

Primary source: https://arxiv.org/abs/2509.25116v2

Sections 3.1–3.2 develop validation around a numerical candidate: a finite-rank
correction makes the approximate linear solve coercive, and a weak-topology
fixed-point argument produces an exact solution when the residual budget closes.
PDEAtlas proves the correction identity for bounded operators and coordinate maps,
retaining both interpolation and solve residuals. Its quadratic Dirichlet theorem
constructs a weak solution near a supplied candidate under explicit reconstruction,
coercivity, embedding, and error hypotheses. The interval and unit-cube examples
are Poisson validation examples that verify all their own hypotheses.

Section 4.1 separates the stationary similarity operator into a compensated
principal part and a compact perturbation. PDEAtlas proves the principal energy
identity first for smooth compact test fields, then constructs its weak bilinear
form on bounded open domains. A weakly divergence-free bounded Sobolev background
and a bounded matrix field satisfying the stated compensation inequality give
coercivity. Restriction to the closed divergence kernel gives a unique principal
linear variational solve.

PDEAtlas constructs distinct suitable Leray–Hopf solutions from any unstable profile
(`NavierStokes.Nonuniqueness.of_unstableProfile`). The certificates for the paper's numerical
profile and unstable eigenpair, and with them the nonuniqueness theorem `NavierStokes.nonuniqueness`,
are formalized in the companion repository [BlowupZoo](https://github.com/lean-dojo/BlowupZoo), at its level 8.

The cited preprint is distributed under CC BY 4.0, as linked from its arXiv record:
https://creativecommons.org/licenses/by/4.0/
This does not establish a reuse license for the accompanying numerical code or data.
