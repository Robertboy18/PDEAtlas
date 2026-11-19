/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Constant bounded continuous functions as a linear map

The constant function construction is a continuous linear map of norm
at most one. No point of the domain is required, so the empty domain is allowed.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

variable (α 𝕜 E : Type*) [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The constant bounded function, as a continuous linear map. -/
def constCLM : E →L[𝕜] (α →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := const α
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
    1 (fun x ↦ by
      change ‖const α x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_const_le (α := α) x)

/-- The linear construction is exactly the constant function. -/
@[simp] theorem constCLM_apply (x : E) : constCLM α 𝕜 E x = const α x := rfl

/-- Constant functions have norm no larger than their value, including an
empty domain. -/
theorem norm_constCLM_le : ‖constCLM α 𝕜 E‖ ≤ 1 := by
  unfold constCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

end BoundedContinuousFunction
