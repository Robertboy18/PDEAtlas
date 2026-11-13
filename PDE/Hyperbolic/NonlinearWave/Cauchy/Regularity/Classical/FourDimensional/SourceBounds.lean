/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FourDimensional.Composition
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FourDimensional.Restriction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.LocalEvolution

/-!
# The lower source bound for four-dimensional classical waves

The mass-canceling source is bounded in H³ × H² whenever displacement is
bounded in H². The bound is independent of the higher energy norm.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- A bounded second reaction derivative yields a lower source bound from
H² displacement alone in dimension four. -/
theorem exists_norm_higherWaveRestriction_source_bound {k : ℕ} (hk : (4 : ℝ) < 2 * ((k : ℝ) - 1))
    (h2 : 2 ≤ k) {f : ℝ → ℝ} {K : ℝ≥0} (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f)
    (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D) (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : W^{k + 1,2}(ℝ^4) × W^{k,2}(ℝ^4), ‖lowerOrderCLM (h2.trans (Nat.le_succ k)) z.1‖ ≤ R →
        ‖higherWaveRestrictionCLM 4 h2 (higherSmoothMap hk hs hf0 z)‖ ≤ C := by
  obtain ⟨C, hC, hcomp⟩ :=
    exists_norm_lower_higherComposition_h2_bound hk h2 hs hf hf0 hD hsecond hR
  refine ⟨R + C, add_nonneg hR hC, fun z hz ↦ ?_⟩
  change ‖(lowerOrderCLM _ (0 : W^{k + 1,2}(ℝ^4)),
    lowerOrderCLM h2 (lowerOrderCLM (Nat.le_succ k) z.1 -
      higherComposition hk hs hf0 (lowerOrderCLM (Nat.le_succ k) z.1)))‖ ≤ R + C
  rw [map_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), map_sub,
    lowerOrderCLM_trans_apply]
  exact (norm_sub_le _ _).trans (add_le_add hz
    (hcomp _ (by rwa [lowerOrderCLM_trans_apply])))

end PDE.Hyperbolic.NonlinearWave.Cauchy
