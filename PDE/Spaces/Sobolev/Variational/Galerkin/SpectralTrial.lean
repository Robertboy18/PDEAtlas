/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Spectral
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.VectorZeroBoundary

/-!
# Spectral trial spaces for the Sobolev Gelfand triple

Stable Galerkin trial systems for the inclusions `H¹₀(Ω) ↪ L²(Ω)` and
`H¹₀(Ω; ℝ^m) ↪ L²(Ω; ℝ^m)`, built from the eigenspaces of the compact Gram
operator without choosing a basis.

Evans builds the Galerkin approximations from functions `w_k` forming an orthogonal basis of
`H¹₀(U)` and an orthonormal basis of `L²(U)`, for instance eigenfunctions of `-Δ` (§7.1.2,
(12)-(13)). Our trial spaces are those of `PDE.Analysis.Evolution.gramSpectralGalerkinSystem`: sums
of whole eigenspaces of the compact symmetric operator `J†J`, where `J` is the inclusion
`H¹₀(Ω) ↪ L²(Ω)`, compact for bounded open `Ω` (`h10L2GelfandTriple_inclusion_isCompactOperator`).
Their union is dense by Mathlib's spectral theorem for compact symmetric operators,
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` (Evans App. D.6, Theorem 7).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, (12)-(13), p. 375; and App. D.6, Theorem 7, p. 728.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The canonical stable Galerkin trial system for `H¹₀(Ω) ↪ L²(Ω)` on a
bounded open set.

The `m`th space is the sum of all eigenspaces of `J†J` whose eigenvalues have
absolute value at least `1 / (m + 1)`. Taking whole eigenspaces avoids basis
choices and handles repeated eigenvalues correctly. -/
noncomputable def h10L2SpectralTrialSystem
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) :
    StableTrialSystem (h10L2GelfandTriple hΩopen) :=
  gramSpectralGalerkinSystem (h10L2GelfandTriple hΩopen)
    (h10L2GelfandTriple_inclusion_isCompactOperator hΩopen hΩbounded)

namespace ZeroBoundaryVectorSpace

/-- The stable Galerkin trial system for `H¹₀(Ω; ℝ^m) ↪ L²(Ω; ℝ^m)` on a bounded
open set, obtained from the eigenspaces of the compact Gram operator. -/
def spectralTrialSystem (m : ℕ)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) :
    StableTrialSystem (gelfandTriple (m := m) hΩopen) :=
  gramSpectralGalerkinSystem (gelfandTriple (m := m) hΩopen)
    (isCompactOperator_inclusion hΩopen hΩbounded)

end ZeroBoundaryVectorSpace

end SobolevSpace.GraphSpace
