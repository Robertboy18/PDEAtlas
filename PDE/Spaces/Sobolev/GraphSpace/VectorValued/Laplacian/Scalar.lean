/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Laplacian
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.ZeroOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian

/-!
# Agreement with the scalar weak Laplacian

For real-valued functions of order two, the Sobolev-valued Laplacian
and the scalar `Lᵖ` Laplacian agree through the isometries.
Thus a scalar PDE can use either presentation without changing its residual.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped ENNReal Sobolev Laplacian

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}

/-- Reading the `Lᵖ` value of the Banach-valued Laplacian at real codomain gives
the scalar weak Laplacian. -/
theorem lpEquivZeroOrder_symm_laplacian (u : W^{2,p}(Ω; ℝ)) :
    lpEquivZeroOrder.symm (Δ u) = (Δ (scalarEquiv u) : DerivLp n p Ω) := by
  rw [lpEquivZeroOrder_symm_apply, laplacian_coordinate,
    GraphSpace.laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply]
  simp only [derivativeWordIndex_baseIndex, scalarEquiv_coordinate,
    pairDerivIndex, secondDerivIndex]

/-- Vanishing of the Laplacian is independent of the two scalar Sobolev presentations. -/
theorem laplacian_eq_zero_iff_scalar (u : W^{2,p}(Ω; ℝ)) :
    Δ u = 0 ↔ (Δ (scalarEquiv u) : DerivLp n p Ω) = 0 := by
  rw [← lpEquivZeroOrder_symm_laplacian]
  exact (lpEquivZeroOrder.symm.map_eq_zero_iff).symm

end SobolevSpace.VectorValued
