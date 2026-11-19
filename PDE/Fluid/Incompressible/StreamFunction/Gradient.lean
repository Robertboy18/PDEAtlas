/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.StreamFunction
public import PDE.FDeriv.PartialDeriv.Energy
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The gradient of a planar stream velocity

The derivative of the velocity `(-∂₂ψ, ∂₁ψ)` of a stream function is bounded by the sum of
the absolute values of the second partial derivatives of `ψ`. No regularity is assumed: where the
velocity is not differentiable its derivative is `0`.

## Main results

* `norm_fderiv_planarStreamVelocity_le`: the derivative of the velocity of a stream is at most
  the sum of the absolute values of the second partial derivatives of the stream.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

/-- The gradient of a planar stream velocity is bounded by the second partial derivatives of the
stream function. -/
theorem norm_fderiv_planarStreamVelocity_le {ψ : ℝ^2 → ℝ} (x : ℝ^2) :
    ‖fderiv ℝ (planarStreamVelocity ψ) x‖ ≤
      ∑ i : Fin 2, ∑ k : Fin 2, |(∂[i] (fun y ↦ (∂[k] ψ) y)) x| := by
  by_cases hF : DifferentiableAt ℝ (planarStreamVelocity ψ) x
  swap
  · rw [fderiv_zero_of_not_differentiableAt hF, norm_zero]
    positivity
  refine (PDE.norm_fderiv_le_sum_norm_partialDeriv _ x).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  have hcoord : ∀ k : Fin 2, ((∂[i] (planarStreamVelocity ψ)) x) k =
      (∂[i] (fun y ↦ planarStreamVelocity ψ y k)) x := by
    intro k
    have h := ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
    change (fderiv ℝ (planarStreamVelocity ψ) x (EuclideanSpace.single i 1)) k =
      fderiv ℝ ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ) ∘ planarStreamVelocity ψ) x
        (EuclideanSpace.single i 1)
    rw [h]
    rfl
  refine (EuclideanSpace.norm_le_sum_abs _).trans ?_
  simp only [Fin.sum_univ_two]
  rw [hcoord 0, hcoord 1]
  have e0 : (fun y ↦ planarStreamVelocity ψ y 0) = -(∂[(1 : Fin 2)] ψ) := by
    funext y; simp [planarStreamVelocity_apply_zero]
  have e1 : (fun y ↦ planarStreamVelocity ψ y 1) = ∂[(0 : Fin 2)] ψ := by
    funext y; simp [planarStreamVelocity_apply_one]
  rw [e0, e1, PDE.partialDeriv_neg, abs_neg]
  change |(∂[i] (fun y ↦ (∂[1] ψ) y)) x| + |(∂[i] (fun y ↦ (∂[0] ψ) y)) x| ≤ _
  linarith

end IncompressibleFlow
