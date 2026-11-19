/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Pointwise bounded bilinear maps

A continuous bilinear map acts pointwise on bounded continuous functions with
no increase in its operator norm. This is the bilinear analogue of Mathlib's
pointwise action of a continuous linear map on bounded continuous functions, for
which the same norm bound is recorded here.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Apply a continuous bilinear map pointwise to two bounded continuous
functions, as a continuous bilinear map. -/
def compLeftContinuousBounded₂ (B : E →L[𝕜] F →L[𝕜] G)
    (α : Type*) [TopologicalSpace α] : (α →ᵇ E) →L[𝕜] (α →ᵇ F) →L[𝕜] (α →ᵇ G) := by
  let b (u : α →ᵇ E) (v : α →ᵇ F) : α →ᵇ G :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun t ↦ B (u t) (v t))
      (B.continuous₂.comp (u.continuous.prodMk v.continuous))
      (‖B‖ * ‖u‖ * ‖v‖) fun t ↦
        B.le_of_opNorm₂_le_of_le le_rfl (u.norm_coe_le_norm t) (v.norm_coe_le_norm t)
  refine (LinearMap.mk₂ 𝕜 b ?_ ?_ ?_ ?_).mkContinuous₂ ‖B‖ ?_
  · intro u v w
    ext t
    change B (u t + v t) (w t) = B (u t) (w t) + B (v t) (w t)
    rw [map_add, _root_.add_apply]
  · intro c u v
    ext t
    change B (c • u t) (v t) = c • B (u t) (v t)
    rw [map_smul, _root_.smul_apply]
  · intro u v w
    ext t
    exact (B (u t)).map_add (v t) (w t)
  · intro c u v
    ext t
    exact (B (u t)).map_smul c (v t)
  · intro u v
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg u)) (norm_nonneg v))).mpr
    intro t
    exact B.le_of_opNorm₂_le_of_le le_rfl (u.norm_coe_le_norm t) (v.norm_coe_le_norm t)

/-- Evaluation of the pointwise bilinear operator is literal pointwise evaluation. -/
@[simp] theorem compLeftContinuousBounded₂_apply (B : E →L[𝕜] F →L[𝕜] G)
    {α : Type*} [TopologicalSpace α] (u : α →ᵇ E) (v : α →ᵇ F) (t : α) :
    B.compLeftContinuousBounded₂ α u v t = B (u t) (v t) := rfl

/-- Passing to bounded functions does not enlarge the bilinear operator norm. -/
theorem norm_compLeftContinuousBounded₂_le (B : E →L[𝕜] F →L[𝕜] G)
    (α : Type*) [TopologicalSpace α] :
    ‖B.compLeftContinuousBounded₂ α‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg B) (norm_nonneg u))
  intro v
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg u)) (norm_nonneg v))).mpr
  intro t
  exact B.le_of_opNorm₂_le_of_le le_rfl (u.norm_coe_le_norm t) (v.norm_coe_le_norm t)

/-- Passing to bounded functions does not enlarge the operator norm of a linear map. -/
theorem norm_compLeftContinuousBounded_le (g : E →L[𝕜] F) (α : Type*) [TopologicalSpace α] :
    ‖g.compLeftContinuousBounded α‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro u
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg g) (norm_nonneg u))).mpr
  intro t
  rw [compLeftContinuousBounded_apply]
  exact g.le_opNorm_of_le (u.norm_coe_le_norm t)

end ContinuousLinearMap
