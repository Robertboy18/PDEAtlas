/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Lipschitz
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.SmoothData

/-!
# Amplitude-controlled Sobolev composition

Smooth density and the already proved composition continuity transfer the
tame estimate to every Sobolev input. The constant depends on a bound for
the values of the input, without a bound on its Sobolev norm.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- A bounded amplitude gives an affine bound for the full Sobolev reaction
norm. The constant is derived from scalar derivatives on a bounded interval. -/
theorem exists_tame_higherComposition_bound (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : W^{k,2}(ℝ^n), (∀ x, ‖classicalRepresentativeCLM hk u x‖ ≤ B) →
        ‖higherComposition hk hf hf0 u‖ ≤ C * (1 + ‖u‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_tame_smooth_composition_bound (n := n) (k := k)
    hf hf0 (by linarith : 0 ≤ B + 1)
  refine ⟨C, hC, fun u hub ↦ ?_⟩
  obtain ⟨v, hv, hc, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier n) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) k u
  let V (j : ℕ) : W^{k,2}(ℝ^n) := mkWkpSpaceOnOfContDiff (v j) (hv j) (hc j)
  let A := classicalRepresentativeCLM hk
  have hV : Tendsto V atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  have hA : Tendsto (fun j ↦ ‖A (V j) - A u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((A.continuous.tendsto u).comp hV)
  have hamp : ∀ᶠ j in atTop, ∀ x, ‖v j x‖ ≤ B + 1 := by
    filter_upwards [hA.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
    intro x
    have he := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hk (hv j) (hc j)) x
    have hd := (A (V j) - A u).norm_coe_le_norm x
    change ‖A (V j) x - A u x‖ ≤ _ at hd
    rw [← he]
    exact (norm_le_norm_sub_add (A (V j) x) (A u x)).trans (by linarith [hub x])
  have hcomp := ((locallyLipschitz_higherComposition hk hf hf0).continuous.tendsto u).comp hV
  apply le_of_tendsto_of_tendsto hcomp.norm
    (tendsto_const_nhds.mul (tendsto_const_nhds.add hV.norm))
  filter_upwards [hamp] with j hj
  dsimp only [Function.comp_apply, V]
  rw [higherComposition_smoothGraph]
  exact hbound (v j) (hv j) (hc j) hj

end PDE.Hyperbolic.NonlinearWave.Cauchy
