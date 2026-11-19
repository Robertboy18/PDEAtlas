/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.SmoothBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Lipschitz
public import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# Affine H³ bounds for the higher composition in dimension five

Smooth compact density transfers the interpolated chain estimate to the
higher Sobolev composition. The H² radius and an affine H³ factor suffice.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- A globally bounded second reaction derivative gives an affine H³ bound
for the H² composition on every H² ball in dimension five. -/
theorem exists_norm_lower_higherComposition_affine_h3_bound_five {k : ℕ}
    (hk : (5 : ℝ) < 2 * ((k : ℝ) - 1)) (h2 : 2 ≤ k) (h3 : 3 ≤ k) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hl : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : W^{k,2}(ℝ^5), ‖lowerOrderCLM h2 u‖ ≤ R →
        ‖lowerOrderCLM h2 (higherComposition hk hf hf0 u)‖ ≤ C * (1 + ‖lowerOrderCLM h3 u‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_smooth_h2_composition_affine_h3_bound_five hf hl hf0 hD hsecond
    (by linarith : 0 ≤ R + 1)
  refine ⟨C, hC, fun u hur ↦ ?_⟩
  obtain ⟨v, hv, hc, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier 5) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) k u
  let V (j : ℕ) : W^{k,2}(ℝ^5) := mkWkpSpaceOnOfContDiff (v j) (hv j) (hc j)
  let L := lowerOrderCLM (n := 5) (p := 2) (Ω := univ) h2
  have hV : Tendsto V atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  have hevent : ∀ᶠ j in atTop, ‖L (V j)‖ ≤ R + 1 := by
    have hlt : ‖L u‖ < R + 1 := by dsimp only [L]; linarith
    filter_upwards [(L.continuous.tendsto u |>.comp hV).norm.eventually (gt_mem_nhds hlt)] with j hj
    exact hj.le
  have hcomp := (locallyLipschitz_higherComposition hk hf hf0).continuous
  let L₃ := lowerOrderCLM (n := 5) (p := 2) (Ω := univ) h3
  apply le_of_tendsto_of_tendsto ((L.continuous.comp hcomp).tendsto u |>.comp hV).norm
    (tendsto_const_nhds.mul (tendsto_const_nhds.add ((L₃.continuous.tendsto u |>.comp hV).norm)))
  filter_upwards [hevent] with j hj
  dsimp only [L, L₃, V, Function.comp_apply] at hj ⊢
  rw [higherComposition_smoothGraph, lowerOrderCLM_mkWkpSpaceOnOfContDiff,
    lowerOrderCLM_mkWkpSpaceOnOfContDiff]
  rw [lowerOrderCLM_mkWkpSpaceOnOfContDiff] at hj
  exact hbound _ _ _ hj

end PDE.Hyperbolic.NonlinearWave.Cauchy
