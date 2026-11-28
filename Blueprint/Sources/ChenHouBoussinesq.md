# Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler equations

Jiajie Chen and Thomas Y. Hou, *Stable nearly self-similar blowup of the 2D
Boussinesq and 3D Euler equations with smooth data I: Analysis*,
arXiv:2210.07191v4 (16 August 2026).

Primary source: https://arxiv.org/abs/2210.07191v4

Section 2 writes the inviscid two-dimensional Boussinesq system in vorticity,
transport, and streamfunction form in equations (2.3a)–(2.3c), and gives the
dynamic rescaling in equations (2.4)–(2.7). The paper's theorem is about a
nearly self-similar solution remaining close to an approximate steady profile.

PDEAtlas records two deliberately separate formulations. The default primitive
velocity–pressure model uses upward vertical buoyancy on the whole plane. The
vorticity–streamfunction model follows equations (2.3a)–(2.3c), including the
paper's clockwise scalar-vorticity sign, upper-half-plane equations, and zero
streamfunction boundary trace. A checked sign-parametrized curl calculation
shows that primitive force `κ θ e₂` gives clockwise-vorticity source
`-κ ∂₁θ`; hence the paper's positive source is the downward choice `κ = -1`.
Given a streamfunction representation, PDEAtlas constructs the corresponding
upper-half-plane vorticity–stream solution. It also proves that the zero trace
gives no normal flow and proves the exact change of variables (2.4)–(2.7) at
the equation level. Finally, it checks the two origin-trace ODEs following
(2.10), proves that normalization (2.9) makes both derivatives vanish, and
deduces (2.10) on an open connected time domain.
