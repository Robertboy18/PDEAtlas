/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.Composition
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.Restriction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.LocalEvolution

/-!
# The affine lower source bound in dimension five

On a fixed H² displacement ball, interpolation makes the mass-canceling source
affine in the H³ × H² restriction of the state.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- A bounded second reaction derivative gives an affine bound for the
restricted wave source on every H² displacement ball in dimension five. -/
theorem exists_norm_higherWaveRestriction_source_affine_bound_five {k : ℕ}
    (hk : (5 : ℝ) < 2 * ((k : ℝ) - 1)) (h2 : 2 ≤ k) {f : ℝ → ℝ} {K : ℝ≥0}
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5), ‖lowerOrderCLM
      (h2.trans (Nat.le_succ k)) z.1‖ ≤ R → ‖higherWaveRestrictionCLM 5 h2
      (higherSmoothMap hk hs hf0 z)‖ ≤ C * (1 + ‖higherWaveRestrictionCLM 5 h2 z‖) := by
  have h3 : 3 ≤ k := by
    have : (2 : ℝ) < k := by linarith
    have : 2 < k := by exact_mod_cast this
    omega
  obtain ⟨C, hC, hcomp⟩ :=
    exists_norm_lower_higherComposition_affine_h3_bound_five hk h2 h3 hs hf hf0 hD hsecond hR
  refine ⟨R + C, add_nonneg hR hC, fun z hz ↦ ?_⟩
  have hb := hcomp (lowerOrderCLM (Nat.le_succ k) z.1)
    (by rwa [lowerOrderCLM_trans_apply])
  rw [lowerOrderCLM_trans_apply] at hb
  have hq : ‖lowerOrderCLM (h3.trans (Nat.le_succ k)) z.1‖ ≤
      ‖higherWaveRestrictionCLM 5 h2 z‖ := norm_fst_le (higherWaveRestrictionCLM 5 h2 z)
  have hc := hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hq) hC)
  change ‖(lowerOrderCLM _ (0 : W^{k + 1,2}(ℝ^5)),
    lowerOrderCLM h2 (lowerOrderCLM (Nat.le_succ k) z.1 -
      higherComposition hk hs hf0 (lowerOrderCLM (Nat.le_succ k) z.1)))‖ ≤
      (R + C) * (1 + ‖higherWaveRestrictionCLM 5 h2 z‖)
  rw [map_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), map_sub,
    lowerOrderCLM_trans_apply]
  exact ((norm_sub_le _ _).trans (add_le_add hz hc)).trans (by
    nlinarith [mul_nonneg hR (norm_nonneg (higherWaveRestrictionCLM 5 h2 z))])

end PDE.Hyperbolic.NonlinearWave.Cauchy
