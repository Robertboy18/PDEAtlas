/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded continuous maps into a finite product

Taking coordinates identifies a bounded continuous map into a finite product
with a finite family of bounded continuous maps. This identification preserves
the supremum norm, including when either index type is empty.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

variable {α ι : Type*} [TopologicalSpace α] [Fintype ι]
  {𝕜 : Type*} [NormedField 𝕜] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- Coordinate rearrangement for bounded continuous functions is a linear
isometry for the finite-product supremum norm. -/
def piLinearIsometryEquiv :
    (α →ᵇ (∀ i, E i)) ≃ₗᵢ[𝕜] (∀ i, α →ᵇ E i) := by
  let toPi (f : α →ᵇ (∀ i, E i)) (i : ι) : α →ᵇ E i :=
    ofNormedAddCommGroup (fun x ↦ f x i)
      ((continuous_apply i).comp f.continuous) ‖f‖ fun x ↦
        (norm_le_pi_norm (f x) i).trans (f.norm_coe_le_norm x)
  let fromPi (f : ∀ i, α →ᵇ E i) : α →ᵇ (∀ i, E i) :=
    ofNormedAddCommGroup (fun x i ↦ f i x)
      (continuous_pi fun i ↦ (f i).continuous) ‖f‖ fun x ↦
        (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun i ↦
          ((f i).norm_coe_le_norm x).trans (norm_le_pi_norm f i)
  let e : (α →ᵇ (∀ i, E i)) ≃ₗ[𝕜] (∀ i, α →ᵇ E i) :=
    { toFun := toPi
      invFun := fromPi
      left_inv f := by ext x i; rfl
      right_inv f := by funext i; ext x; rfl
      map_add' f g := by funext i; ext x; rfl
      map_smul' c f := by funext i; ext x; rfl }
  refine LinearIsometryEquiv.ofBounds e (fun f ↦ ?_) (fun f ↦ ?_)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
    intro i
    apply (norm_le (norm_nonneg f)).mpr
    intro x
    exact (norm_le_pi_norm (f x) i).trans (f.norm_coe_le_norm x)
  · exact norm_ofNormedAddCommGroup_le _ (norm_nonneg f) fun x ↦
      (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun i ↦
        ((f i).norm_coe_le_norm x).trans (norm_le_pi_norm f i)

/-- Evaluation of the coordinate rearrangement. -/
@[simp] theorem piLinearIsometryEquiv_apply (f : α →ᵇ (∀ i, E i)) (i : ι) (x : α) :
    piLinearIsometryEquiv (𝕜 := 𝕜) f i x = f x i := rfl

/-- Evaluation of the inverse coordinate rearrangement. -/
@[simp] theorem piLinearIsometryEquiv_symm_apply (f : ∀ i, α →ᵇ E i) (x : α) (i : ι) :
    (piLinearIsometryEquiv (𝕜 := 𝕜)).symm f x i = f i x := rfl

end BoundedContinuousFunction
