/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.SmoothBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Lipschitz

/-!
# The completed cubic estimate

Smooth compact density transfers the H¹ estimate to the constructed high
Sobolev reaction. Its coefficient depends only on the lower H¹ norm.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- The cubic reaction at every classical Sobolev order has an H¹ bound
linear in the H² norm and quadratic in the H¹ norm. -/
theorem exists_lower_cubic_h1_bound {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h2 : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W^{k,2}(ℝ^3),
      ‖lowerOrderCLM (by omega : 1 ≤ k)
        (higherComposition hk (contDiff_id.pow 3) (by simp) u)‖ ≤
      C * ‖lowerOrderCLM (by omega : 1 ≤ k) u‖ ^ 2 * ‖lowerOrderCLM h2 u‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_smooth_cubic_h1_bound
  refine ⟨C, hC, fun u ↦ ?_⟩
  obtain ⟨v, hv, hc, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier 3) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) k u
  let V (j : ℕ) : W^{k,2}(ℝ^3) := mkWkpSpaceOnOfContDiff (v j) (hv j) (hc j)
  let L₁ := lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by omega : 1 ≤ k)
  let L₂ := lowerOrderCLM (n := 3) (p := 2) (Ω := univ) h2
  have hV : Tendsto V atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  have hcomp := (locallyLipschitz_higherComposition hk
    (contDiff_id.pow 3) (by simp)).continuous
  apply le_of_tendsto_of_tendsto ((L₁.continuous.comp hcomp).tendsto u |>.comp hV).norm
    ((((L₁.continuous.tendsto u |>.comp hV).norm.pow 2).const_mul C).mul
      (L₂.continuous.tendsto u |>.comp hV).norm)
  exact Eventually.of_forall fun j ↦ by
    dsimp only [L₁, L₂, V, Function.comp_apply]
    rw [higherComposition_smoothGraph]
    simp only [lowerOrderCLM_mkWkpSpaceOnOfContDiff]
    exact hbound _ _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
