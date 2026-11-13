/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.DerivativeBounds
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Differentiated mollifiers for vector fields

Applying the scalar estimate in each component gives the same bound in the
finite Hilbert product. The constant depends on the fixed kernel, with no
additional factor for the number of components.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory GraphSpace
open scoped ENNReal Sobolev Laplacian

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The viscous Laplacian of a mollified vector field is uniformly controlled
by its H¹ norm, with the same kernel constant as in the scalar estimate. -/
theorem mul_norm_piLp_laplacian_mollifierSmoothingCLM_le
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : PiLp 2 (fun _ : ι ↦ H¹(ℝ^n))) :
    ε * ‖WithLp.toLp 2 (fun i ↦
      Δ (mollifierSmoothingCLM 2 μ hε (wkpBaseCoordinateCLM (U i))))‖ ≤
      (∑ j : Fin n, ∫ x, ‖fderiv ℝ μ.ρ x (EuclideanSpace.single j 1)‖) * ‖U‖ := by
  let v : PiLp 2 (fun _ : ι ↦ DerivLp n 2 Set.univ) :=
    WithLp.toLp 2 (fun i ↦
      Δ (mollifierSmoothingCLM 2 μ hε (wkpBaseCoordinateCLM (U i))))
  have h := PiLp.norm_le_mul_of_norm_apply_le (ε • v) U
    (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun x ↦ norm_nonneg _)
    (fun i ↦ by
      simpa only [PiLp.smul_apply, norm_smul, Real.norm_of_nonneg hε.le,
        v, PiLp.toLp_apply] using
        mul_norm_laplacian_mollifierSmoothingCLM_le μ hε (U i))
  simpa only [norm_smul, Real.norm_of_nonneg hε.le, v] using h

/-- Smoothing to any higher order gives the same vector Laplacian after
restriction to H². This includes the H³ data used for strong viscous solutions. -/
theorem mul_norm_piLp_laplacian_lowerOrder_mollifierSmoothingCLM_le
    {r : ℕ} (hr : 2 ≤ r) (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : PiLp 2 (fun _ : ι ↦ H¹(ℝ^n))) :
    ε * ‖WithLp.toLp 2 (fun i ↦
      Δ (lowerOrderCLM hr
        (mollifierSmoothingCLM r μ hε (wkpBaseCoordinateCLM (U i)))))‖ ≤
      (∑ j : Fin n, ∫ x, ‖fderiv ℝ μ.ρ x (EuclideanSpace.single j 1)‖) * ‖U‖ := by
  simpa only [lowerOrderCLM_mollifierSmoothingCLM] using
    mul_norm_piLp_laplacian_mollifierSmoothingCLM_le μ hε U

end SobolevSpace.Approximation
