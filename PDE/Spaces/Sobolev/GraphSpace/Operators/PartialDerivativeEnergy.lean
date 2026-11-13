/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# Norms of first weak partial derivatives

For `u ∈ W^{1,p}(Ω)`, the weak derivative `∂[i] u` belongs to `W^{0,p}(Ω)`.
Its sole coordinate is the corresponding `L^p` weak derivative of `u`, and the
order-zero graph norm is exactly that coordinate's norm. The isometry
`lpEquivZeroOrder` gives the same identity for extended norms, including `p = ∞`.
No openness or boundary regularity of `Ω` is required.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- The base coordinate of a first weak partial derivative is its original `L^p` coordinate. -/
theorem wkpBaseCoordinateCLM_partialDeriv (i : Fin n) (u : W^{1,p}(Ω)) :
    wkpBaseCoordinateCLM (∂[i] u) = wkpCoordinateCLM (singleDerivIndex n i) u := by
  change wkpBaseCoordinateCLM (partialDerivCLM i u) = _
  rw [wkpBaseCoordinateCLM_apply, partialDerivCLM, derivativeWordCLM_apply,
    derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply]
  rfl

/-- The order-zero Sobolev norm of a weak partial derivative equals its `L^p` norm. -/
theorem norm_partialDeriv_eq_wkpCoordinateCLM (i : Fin n) (u : W^{1,p}(Ω)) :
    ‖∂[i] u‖ = ‖wkpCoordinateCLM (singleDerivIndex n i) u‖ := by
  calc
    ‖∂[i] u‖ = ‖wkpBaseCoordinateCLM (∂[i] u)‖ :=
      (lpEquivZeroOrder.symm.norm_map (∂[i] u)).symm
    _ = _ := congrArg norm (wkpBaseCoordinateCLM_partialDeriv i u)

/-- Extended norms of first weak partial derivatives agree in the graph and `L^p` models. -/
theorem enorm_partialDeriv_eq_wkpCoordinateCLM (i : Fin n) (u : W^{1,p}(Ω)) :
    ‖∂[i] u‖ₑ = ‖wkpCoordinateCLM (singleDerivIndex n i) u‖ₑ := by
  calc
    ‖∂[i] u‖ₑ = ‖wkpBaseCoordinateCLM (∂[i] u)‖ₑ :=
      (lpEquivZeroOrder.symm.enorm_map (∂[i] u)).symm
    _ = _ := congrArg enorm (wkpBaseCoordinateCLM_partialDeriv i u)

end SobolevSpace.GraphSpace
