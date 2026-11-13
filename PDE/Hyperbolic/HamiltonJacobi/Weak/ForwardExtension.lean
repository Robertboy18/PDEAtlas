/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Extending a forward Lipschitz solution across the initial time

Holding the initial value fixed at negative times gives a global Lipschitz
extension with the same constant. Spacetime mollification can therefore be
defined without assuming a separately supplied continuous extension.
-/

@[expose] public section

namespace HamiltonJacobi.Weak

variable {E : Type*}

/-- Extend a forward function by holding its initial value fixed at negative times. -/
def forwardExtension (u : E × ℝ → ℝ) (z : E × ℝ) : ℝ :=
  u (z.1, max z.2 0)

/-- The extension agrees with the original function at every nonnegative time. -/
theorem forwardExtension_eq {u : E × ℝ → ℝ} {z : E × ℝ} (hz : 0 ≤ z.2) :
    forwardExtension u z = u z := by
  simp only [forwardExtension, max_eq_left hz, Prod.mk.eta]

variable [PseudoMetricSpace E]

/-- Clamping time to the forward half-line preserves the Lipschitz constant. -/
theorem lipschitzWith_forwardExtension
    {u : E × ℝ → ℝ} {K : NNReal} (hu : LipschitzOnWith K u {z | 0 ≤ z.2}) :
    LipschitzWith K (forwardExtension u) := by
  have hc : LipschitzWith 1 (fun z : E × ℝ ↦ (z.1, max z.2 0)) := by
    simpa using LipschitzWith.prod_fst.prodMk (LipschitzWith.prod_snd.max_const 0)
  refine LipschitzWith.of_dist_le_mul fun z w ↦ ?_
  apply (hu.dist_le_mul (z.1, max z.2 0) (show 0 ≤ max z.2 0 from le_max_right _ _)
    (w.1, max w.2 0) (show 0 ≤ max w.2 0 from le_max_right _ _)).trans
  exact mul_le_mul_of_nonneg_left (by simpa using hc.dist_le_mul z w) K.coe_nonneg

end HamiltonJacobi.Weak
