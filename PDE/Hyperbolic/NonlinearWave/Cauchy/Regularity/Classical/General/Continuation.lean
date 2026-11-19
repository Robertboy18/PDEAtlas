/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.LocalEvolution

/-!
# Higher Sobolev continuation for general smooth reactions

The proved composition estimates supply Lipschitz constants on state norm
balls. A bounded higher Sobolev trajectory therefore extends past a finite
endpoint, and a finite maximal higher lifespan forces norm divergence.
These are higher Sobolev statements; scalar global Lipschitzness alone is not
used to assert an a priori bound for this stronger norm.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- The higher vector field has a Lipschitz constant on every state
norm ball, derived from the general composition estimate. -/
theorem exists_lipschitzOn_higherSmoothMap (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (R : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (higherSmoothMap hk hs hf0) (Metric.closedBall 0 R) := by
  let Q : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n) :=
    (lowerOrderCLM (Nat.le_succ k)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hmaps : MapsTo Q (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro z hz
    have hzn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ((norm_lowerOrderCLM_apply_le (Nat.le_succ k) z.1).trans (norm_fst_le z)).trans hzn
  obtain ⟨L, hL⟩ := exists_lipschitzOn_higherComposition (R := R) hk hs hf0
  have hN := hL.comp Q.lipschitzWith.lipschitzOnWith hmaps
  have hD := Q.lipschitzWith.lipschitzOnWith.sub hN
  exact ⟨_, (LipschitzWith.const (0 : W^{k + 1,2}(ℝ^n))).lipschitzOnWith.prodMk hD⟩

/-- A finite higher Sobolev trajectory with a bounded state norm extends.
The conclusion agrees with the entire earlier trajectory. -/
theorem exists_higherSmooth_extension_of_bounded (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {b : ℝ}
    {u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)}
    (hu : (higherLinearSemigroup n k).IsMildSolutionBefore (higherSmoothMap hk hs hf0) x b u)
    (hb : 0 < b) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ t ∈ Ico 0 b, ‖u t‖ ≤ R) :
    ∃ ρ : ℝ≥0, b < (ρ : ℝ) ∧ ∃ v : C(Icc (0 : ℝ) (ρ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hs hf0) x ρ v ∧
      EqOn (IccExtend ρ.coe_nonneg v) u (Ico 0 b) :=
  hu.exists_extension_of_bounded (fun R _ ↦ exists_lipschitzOn_higherSmoothMap hk hs hf0 R) hb hR
    hbound

/-- At a finite maximal higher lifespan the Sobolev state norm eventually
exceeds every threshold. No unproved composition or source bound is an input. -/
theorem higherSmooth_maximal_norm_eventually_gt (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    (hb : (higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x ≠ ∞) :
    ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ico 0 ((higherLinearSemigroup n k).mildLifespan
        (higherSmoothMap hk hs hf0) x).toReal,
        ((higherLinearSemigroup n k).mildLifespan
          (higherSmoothMap hk hs hf0) x).toReal - t < ε →
          R < ‖(higherLinearSemigroup n k).maximalMildSolution
            (F := higherSmoothMap hk hs hf0)
            (locallyLipschitz_higherSmoothSource hk hs hf0) x t‖ :=
  (higherLinearSemigroup n k).maximalMildSolution_norm_eventually_gt_of_lifespan_ne_top
    (fun R _ ↦ exists_lipschitzOn_higherSmoothMap hk hs hf0 R) x hb

end PDE.Hyperbolic.NonlinearWave.Cauchy
