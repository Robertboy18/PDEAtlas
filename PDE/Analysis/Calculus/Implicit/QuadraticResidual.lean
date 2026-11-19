/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Differentiating an equation with a quadratic residual

A quadratic remainder in a linearized equation determines the derivative
whenever its left-hand linear operator is invertible. For a perturbation of the
identity with norm less than one, the equivalence is the actual geometric-series
inverse from Mathlib.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

namespace PDE

/-- A quadratic residual after an invertible linear transformation gives the
Fréchet derivative of the original function. -/
theorem hasFDerivAt_of_quadratic_linear_residual
    (f : X → Y) (x : X) (e : Y ≃L[𝕜] Y) (B : X →L[𝕜] Y) (C : ℝ)
    (h : ∀ y, ‖e (f y - f x) - B (y - x)‖ ≤ C * ‖y - x‖ ^ 2) :
    HasFDerivAt f (e.symm.toContinuousLinearMap.comp B) x := by
  have hbig : (fun y ↦ e (f y - f x) - B (y - x)) =O[𝓝 x]
      (fun y ↦ ‖y - x‖ ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨C, Filter.Eventually.of_forall fun y ↦ ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖)] using h y
  have hsmall := hbig.trans_isLittleO (isLittleO_pow_sub_sub x (by norm_num : 1 < 2))
  have hmap := e.symm.toContinuousLinearMap.isBigO_comp
    (fun y ↦ e (f y - f x) - B (y - x)) (𝓝 x)
  apply hasFDerivAt_iff_isLittleO.mpr
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, map_sub,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_comp]
    using hmap.trans_isLittleO hsmall

variable [CompleteSpace Y]

/-- A linearized contraction equation has the derivative supplied by Mathlib's
actual inverse of `1 - A`; invertibility is derived from the norm bound. -/
theorem hasFDerivAt_of_quadratic_contraction_residual
    (f : X → Y) (x : X) (A : Y →L[𝕜] Y) (hA : ‖A‖ < 1)
    (B : X →L[𝕜] Y) (C : ℝ)
    (h : ∀ y, ‖f y - f x - A (f y - f x) - B (y - x)‖ ≤ C * ‖y - x‖ ^ 2) :
    HasFDerivAt f
      ((ContinuousLinearEquiv.ofUnit (Units.oneSub A hA)).symm.toContinuousLinearMap.comp B) x := by
  apply hasFDerivAt_of_quadratic_linear_residual f x
    (ContinuousLinearEquiv.ofUnit (Units.oneSub A hA)) B C
  exact h

end PDE
