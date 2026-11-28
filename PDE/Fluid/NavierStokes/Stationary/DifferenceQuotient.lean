/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Representative
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Difference quotients of `H¹` velocity fields

To show that a weak solution `u ∈ H¹(ℝⁿ)ⁿ` lies in `H²`, one bounds the difference quotients
`D_h u = h⁻¹ (u(· + h eₗ) - u)` in `H¹`, uniformly in `h`. This module defines `D_h u` for a
velocity field and proves the facts that this argument uses: `D_h u` is in `H¹`, and divergence
free when `u` is; its components are the forward differences of those of `u`;
`‖(D_h u)ᵢ‖₂ ≤ ‖∂ₗuᵢ‖₂`; and its gradient is the difference quotient of the gradient of `u`.

## Main results

* `NavierStokes.Stationary.differenceQuotient`: the difference quotient of a field in
  `H¹(ℝⁿ)ⁿ`, component by component, as a bounded operator.
* `divergenceCLM_differenceQuotient` (all divergence-free fields): `D_h u` is divergence free.
* `representative_differenceQuotient_ae` (all fields): the components of `D_h u` are the forward
  differences of the components of `u`, almost everywhere.
* `integral_sq_representative_differenceQuotient_le` (all fields, all `h ≠ 0`):
  `∫ (D_h u)ᵢ² ≤ ‖∂ₗuᵢ‖₂²`.
* `gradientCLM_differenceQuotient`, `massCLM_differenceQuotient` (all fields): the gradient and
  the mass coordinates of `D_h u` are the `L²` difference quotients of those of `u`.

## How it works

The scalar difference quotient `differenceQuotientH1` acts on each component. It commutes with
the coordinates of the `H¹` graph (`differenceQuotientH1_coordinate`), so the divergence of
`D_h u` is the difference quotient of the divergence of `u`, which is zero. The bound by the
derivative is `norm_differenceQuotientLp_base_le_deriv_of_ne_top`, and the forward differences
come from `differenceQuotientLp_apply_ae`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2(a), Theorem 3 (Difference quotients and weak
  derivatives), pp. 292-293. <https://doi.org/10.1090/gsm/019>
* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, proof of
  Proposition 3: the difference quotients `V = D_h u` of the regularity argument.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- **The difference quotient of an `H¹` velocity field**, `D_h u = h⁻¹ (u(· + h eₗ) - u)`,
component by component. -/
def differenceQuotient (l : Fin n) (h : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ differenceQuotientH1 l h

/-- The components of the difference quotient. -/
theorem differenceQuotient_apply (l : Fin n) (h : ℝ) (w : H) (i : Fin n) :
    differenceQuotient l h w i = differenceQuotientH1 l h (w i) :=
  rfl

/-- The gradient of `D_h u` is the `L²` difference quotient of the gradient of `u`. -/
theorem gradientCLM_differenceQuotient (l : Fin n) (h : ℝ) (w : H) (i j : Fin n) :
    gradientCLM (differenceQuotient l h w) i j = differenceQuotientLp 2 l h (gradientCLM w i j) :=
  differenceQuotientH1_coordinate l h (w i) (singleDerivIndex n j)

/-- The mass coordinates of `D_h u` are the `L²` difference quotients of those of `u`. -/
theorem massCLM_differenceQuotient (l : Fin n) (h : ℝ) (w : H) (i : Fin n) :
    massCLM (differenceQuotient l h w) i = differenceQuotientLp 2 l h (massCLM w i) :=
  differenceQuotientH1_coordinate l h (w i) (baseIndex n 1)

/-- The difference quotient of a divergence-free `H¹` field is divergence free: its divergence is
the difference quotient of the divergence. -/
theorem divergenceCLM_differenceQuotient (l : Fin n) (h : ℝ) {w : H}
    (hw : divergenceCLM w = 0) : divergenceCLM (differenceQuotient l h w) = 0 := by
  have h1 : divergenceCLM (differenceQuotient l h w) =
      differenceQuotientLp 2 l h (divergenceCLM w) := by
    simp only [divergenceCLM, sum_apply, ContinuousLinearMap.comp_apply,
      map_sum]
    exact Finset.sum_congr rfl fun j _ ↦
      differenceQuotientH1_coordinate l h (w j) (singleDerivIndex n j)
  rw [h1, hw, map_zero]

/-- The components of `D_h u` are the forward differences of the components of `u`, almost
everywhere. -/
theorem representative_differenceQuotient_ae (l : Fin n) (h : ℝ) (w : H) (i : Fin n) :
    (fun y ↦ representative (differenceQuotient l h w) y i) =ᵐ[volume]
      forwardDifference l h fun y ↦ representative w y i := by
  have h1 := differenceQuotientLp_apply_ae 2 l h (massCLM w i)
  rw [← massCLM_differenceQuotient] at h1
  exact h1

/-- The difference quotient is bounded by the derivative in `L²`: for `h ≠ 0` and each component,
`∫ (D_h u)ᵢ² ≤ ‖∂ₗuᵢ‖₂²`. -/
theorem integral_sq_representative_differenceQuotient_le (l : Fin n) {h : ℝ} (hh : h ≠ 0)
    (w : H) (i : Fin n) :
    ∫ y, representative (differenceQuotient l h w) y i ^ 2 ≤ ‖gradientCLM w i l‖ ^ 2 := by
  have h1 := Lp.norm_sq_eq_integral_sq (massCLM (differenceQuotient l h w) i)
  simp only [domainMeasure, Measure.restrict_univ] at h1
  have h2 := norm_differenceQuotientLp_base_le_deriv_of_ne_top 2 (by simp) l hh (w i)
  calc ∫ y, representative (differenceQuotient l h w) y i ^ 2
      = ‖massCLM (differenceQuotient l h w) i‖ ^ 2 := h1.symm
    _ = ‖differenceQuotientLp 2 l h (massCLM w i)‖ ^ 2 := by rw [massCLM_differenceQuotient]
    _ ≤ ‖gradientCLM w i l‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2

end NavierStokes.Stationary
