# Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler equations

Jiajie Chen and Thomas Y. Hou, *Stable nearly self-similar blowup of the 2D
Boussinesq and 3D Euler equations with smooth data I: Analysis*,
arXiv:2210.07191v4 (16 August 2026).

Primary source: https://arxiv.org/abs/2210.07191v4

Section 2 writes the inviscid two-dimensional Boussinesq system in vorticity,
transport, and streamfunction form in equations (2.3a)–(2.3c), and gives the
dynamic rescaling in equations (2.4)–(2.7). The paper's theorem is about a
nearly self-similar solution remaining close to an approximate steady profile.

LeanPDE records two deliberately separate formulations. The default primitive
velocity–pressure model uses upward vertical buoyancy on the whole plane. The
vorticity–streamfunction model follows equations (2.3a)–(2.3c), including the
paper's clockwise scalar-vorticity sign, upper-half-plane equations, and zero
streamfunction boundary trace. A checked sign-parametrized curl calculation
shows that primitive force `κ θ e₂` gives clockwise-vorticity source
`-κ ∂₁θ`; hence the paper's positive source is the downward choice `κ = -1`.
Given a streamfunction representation, LeanPDE constructs the corresponding
upper-half-plane vorticity–stream solution. It also proves that the zero trace
gives no normal flow and proves the exact change of variables (2.4)–(2.7) at
the equation level. Finally, it checks the two origin-trace ODEs following
(2.10), proves that normalization (2.9) makes both derivatives vanish, and
deduces (2.10) on an open connected time domain.

For any normally odd source whose whole-space logarithmic potential is
integrable at every field point, LeanPDE proves that the method-of-images
potential is integrable, has zero boundary trace, and equals whole-space
convolution with the planar fundamental solution. For compactly supported
`C²` sources it additionally proves the pointwise Poisson equation. The
library also proves a separate noncompact sufficient condition for existence
of the potential: continuity, `f ∈ L¹`, and
`log(1+‖x‖) f ∈ L¹`.

For continuous compact sources, the Green potential is integrable without
requiring a smooth odd extension. At every interior point where the source is
`C²`, the potential is `C²` and satisfies `-Δφ = f`. This distinction matters
for the near-field profile: its vorticity need not vanish on the horizontal
boundary, so reflecting it oddly can introduce a jump there. A local cutoff
isolates the smooth source near the evaluation point; the remaining compact
source is separated from the point and contributes a harmonic potential.
The argument uses a general local planar Poisson inversion theorem for
compact, locally integrable sources, which may have jumps elsewhere.

Sections 7.2.1–7.2.2 of the paper, equations (7.6)–(7.10), split the approximate
vorticity into a semi-analytic far-field component and a faster-decaying
numerical remainder. The former has the form
`χ(r) r^{ᾱ₁} g₁(β)`, with `ᾱ₁ ≈ -1/3`, and is therefore not
integrable on the plane. Its streamfunction is constructed from
`χ(r) r^{2+ᾱ₁} f(β)`, where `f` solves the angular Dirichlet problem
`(-∂²β - (2+ᾱ₁)²)f = g₁`. For this inverse step LeanPDE proves the
homogeneous polar identity, the exact cutoff commutator, and the general
Cartesian-to-polar Laplacian bridge for `C²` pullbacks. Variation of constants
also constructs the angular Dirichlet solution from a continuous forcing.
For `-2 < α < 0`, nonresonance on `[0, π/2]` follows from `0 < 2+α < 2`.
The solution is `C²` and has explicit value and derivative bounds in terms of a
forcing bound and the sine resonance factor. For a homogeneous streamfunction
`r^{2+α} f(β)`, LeanPDE also proves the Cartesian gradient formula and its norm
identity. Uniform bounds on `f` and `f'` give an explicit velocity-size bound;
when `α < 0`, the gradient divided by `r` tends uniformly to zero on any angular
sector where those bounds hold. These estimates concern the homogeneous
component before the radial cutoff.

The library also proves that an odd streamfunction has the velocity parity and
boundary cancellation used by normalization, and that uniqueness in any
reflection-stable admissible Dirichlet class transfers tangential vorticity
parity to the streamfunction.

Section 2.8.1, equations (2.39)–(2.41), retains the initial mismatch and the
convolved evolution residual of an approximate response. LeanPDE proves the
general response identity, exact reconstruction after error cancellation, and
the resulting time-dependent norm bound. Section 2.8.2 corrects derivative
traces through an exact coefficient ODE; LeanPDE proves this construction for a
general continuous linear trace map and its right inverse. A general Neumann
correction also constructs that right inverse from a proposed reconstruction
whose coordinate residual has operator norm below one. The reconstruction,
its difference from the proposal, and its image under the spatial generator
have bounds with the residual margin in the denominator. Only the coefficient
space must be complete; no exact inverse matrix is required as input. Numerical
certificates must use the same coefficient norm as the trace map.
Data on a closed time interval suffice, with derivatives taken within the interval at both endpoints.
The trace-cancellation algebra also applies to other exact solutions of the
coefficient ODE. The correction fields
need not be eigenfunctions, and their remaining spatial evolution error is kept.
The same exact coefficients satisfy a quantitative integral estimate from supplied
propagator and extracted-residual envelopes. A projection estimate bounds the
remaining residual, including the generator acting on the spatial correction fields.
Evaluation of derivative extensions in the bounded higher-order Hölder space gives
a continuous linear trace map of norm at most one, even at boundary points.
Ordinary field formulas with compatible derivative identities, continuity on
the closure, uniform bounds, and top-order Hölder bounds can be bundled into
this space directly. The graph norm is bounded by a maximum budget, and
`evansNorm` by the sum of the individual budgets. A uniform value
bound and a Lipschitz estimate also give a quantitative Hölder constant through
interpolation, without requiring a bounded domain.
On an open convex domain, these continuous derivative fields are also derivatives
within the closure, including at boundary points. Their finite coordinate sums
give gradients and Hessians, and the Hessian norm equals the Euclidean operator
norm of its coordinate matrix. This identifies the matrix norm required of a
numerical bound; an entrywise or row-sum norm is a different quantity.
A local third derivative bound and a zero second-order jet give the cubic
singular-weight estimate described in Section 2.8.4. A general variant needs only
first and second derivative fields within the segment and a linear Hessian envelope;
it does not require differentiating the Hessian or extending across the boundary.
The same estimates apply directly to any coordinate derivative of a bounded
higher-order Hölder field with two further derivatives available. The value and
first-derivative traces must vanish exactly, and the Hessian envelope remains
an explicit input.
