/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder

/-!
# Matrix coordinates of the vector weak gradient

Unflattening the Euclidean gradient gives its rectangular
Jacobian matrix. The map is continuous and linear, and every entry agrees
almost everywhere with the corresponding original weak coordinate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μΩ" => domainMeasure n Ω

/-- The weak derivative matrix, obtained from the flattened
Euclidean gradient. The matrix uses its equivalent finite-product norm. -/
def vectorWkpJacobianCLM :
    (Fin m → W^{1,p}(Ω)) →L[ℝ] Lp (Matrix (Fin m) (Fin n) ℝ) p μΩ :=
  (Matrix.euclideanEquiv.symm.toContinuousLinearMap.compLpL p μΩ).comp
    vectorWkpGradientCLM

/-- Simultaneous identification with every original weak partial derivative. -/
theorem vectorWkpJacobianCLM_apply_ae (u : Fin m → W^{1,p}(Ω)) :
    ∀ᵐ x ∂μΩ, ∀ i j, vectorWkpJacobianCLM u x i j =
      wkpCoordinateCLM (singleDerivIndex n j) (u i) x := by
  have hcoords :
      ∀ᵐ x ∂μΩ, ∀ i, ∀ j, ∇ (u i) x j =
        wkpCoordinateCLM (singleDerivIndex n j) (u i) x :=
    ae_all_iff.mpr fun i ↦ wkpGradientCLM_apply_ae (u i)
  filter_upwards [Matrix.euclideanEquiv.symm.toContinuousLinearMap.coeFn_compLpL
      (∇ u),
    vectorWkpGradientCLM_apply_ae u, hcoords] with x hx hg hd
  intro i j
  change (Matrix.euclideanEquiv.symm.toContinuousLinearMap.compLpL p μΩ
    (∇ u)) x i j = _
  rw [hx]
  exact (hg i j).trans (hd i j)

end SobolevSpace.GraphSpace
