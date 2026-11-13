/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.Modes
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Zeros

/-!
# The boundary functions in terms of `j_l` and `j_{l+1}`

For the root analysis of the Neumann-type Stokes modes the boundary functions are written with
the spherical Bessel functions themselves. With `γ² = l (l - 1) (l + 2)`,

* `meridionalBoundaryJ l α = ((l - 1)(2l + 1) - α²) α j_l(α) + (α² - γ²) j_{l+1}(α)`,
  which is `α^{l+1}` times the meridional boundary function;
* `azimuthalBoundaryJ l α = l j_l(α) - α j_{l+1}(α) = α j_l'(α)`, which is `α^l` times the
  azimuthal boundary function.

For `α > 0` both have the same zeros and signs as the boundary functions. The cubic
`meridionalRootPolynomial l s = s³ - 4 l² s² + l (l - 1)(6l² + 11l + 7) s
- 3 l (l - 1)² (l + 1)² (l + 2)` is the `Q_l` of Hou, Wang and Yang (Lemma 5): at a zero of the
meridional function the derivative times `α² - γ²` is `j_l(α) Q_l(α²)`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 6.2, Lemma 5, p. 52, and
  Appendix E, proof of Lemma 5, pp. 65-67.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open PDE.Analysis.SpecialFunctions

namespace PDE.Fluid.Stokes.Ball

/-- `α^{l+1}` times the meridional boundary function, in terms of `j_l` and `j_{l+1}`. -/
def meridionalBoundaryJ (l : ℕ) (α : ℝ) : ℝ :=
  (((l : ℝ) - 1) * (2 * l + 1) - α ^ 2) * α * sphericalBesselJ l α +
    (α ^ 2 - l * (l - 1) * (l + 2)) * sphericalBesselJ (l + 1) α

/-- `α^l` times the azimuthal boundary function: `l j_l(α) - α j_{l+1}(α) = α j_l'(α)`. -/
def azimuthalBoundaryJ (l : ℕ) (α : ℝ) : ℝ :=
  l * sphericalBesselJ l α - α * sphericalBesselJ (l + 1) α

/-- The cubic `Q_l(s)` of Lemma 5 of Hou, Wang and Yang. -/
def meridionalRootPolynomial (l : ℕ) (s : ℝ) : ℝ :=
  s ^ 3 - 4 * (l : ℝ) ^ 2 * s ^ 2 + l * (l - 1) * (6 * l ^ 2 + 11 * l + 7) * s -
    3 * l * ((l : ℝ) - 1) ^ 2 * (l + 1) ^ 2 * (l + 2)

/-- `α^{l+1}` times the meridional boundary function is `meridionalBoundaryJ l α`. -/
theorem pow_mul_boundaryFunction_meridional_eq (l : ℕ) (α : ℝ) :
    α ^ (l + 1) * boundaryFunction .meridional l α = meridionalBoundaryJ l α := by
  rw [pow_mul_boundaryFunction_meridional, meridionalBoundaryJ]

/-- `α^l` times the azimuthal boundary function is `azimuthalBoundaryJ l α`. -/
theorem pow_mul_boundaryFunction_azimuthal_eq (l : ℕ) (α : ℝ) :
    α ^ l * boundaryFunction .azimuthal l α = azimuthalBoundaryJ l α := by
  rw [pow_mul_boundaryFunction_azimuthal, azimuthalBoundaryJ]

/-- For `α > 0` the meridional boundary function vanishes exactly when
`meridionalBoundaryJ l α` does. -/
theorem boundaryFunction_meridional_eq_zero_iff {l : ℕ} {α : ℝ} (hα : 0 < α) :
    boundaryFunction .meridional l α = 0 ↔ meridionalBoundaryJ l α = 0 := by
  rw [← pow_mul_boundaryFunction_meridional_eq, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ hα.ne'

/-- For `α > 0` the azimuthal boundary function vanishes exactly when
`azimuthalBoundaryJ l α` does. -/
theorem boundaryFunction_azimuthal_eq_zero_iff {l : ℕ} {α : ℝ} (hα : 0 < α) :
    boundaryFunction .azimuthal l α = 0 ↔ azimuthalBoundaryJ l α = 0 := by
  rw [← pow_mul_boundaryFunction_azimuthal_eq, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ hα.ne'

/-- `meridionalBoundaryJ l` is differentiable. -/
theorem differentiable_meridionalBoundaryJ (l : ℕ) :
    Differentiable ℝ (meridionalBoundaryJ l) := by
  unfold meridionalBoundaryJ
  have h₁ := differentiable_sphericalBesselJ l
  have h₂ := differentiable_sphericalBesselJ (l + 1)
  fun_prop

/-- `azimuthalBoundaryJ l` is differentiable. -/
theorem differentiable_azimuthalBoundaryJ (l : ℕ) :
    Differentiable ℝ (azimuthalBoundaryJ l) := by
  unfold azimuthalBoundaryJ
  have h₁ := differentiable_sphericalBesselJ l
  have h₂ := differentiable_sphericalBesselJ (l + 1)
  fun_prop

end PDE.Fluid.Stokes.Ball
