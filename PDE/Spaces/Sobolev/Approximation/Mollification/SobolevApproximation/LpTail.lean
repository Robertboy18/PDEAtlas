/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convolution -- shake: keep
import Mathlib.Tactic.Positivity.Finset
/-!
# Vanishing `Lᵖ` tails

The part of an `Lᵖ` function outside an expanding sequence of balls
converges to zero in `Lᵖ` when the exponent is finite.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Convolution Pointwise Topology

namespace Approximation

variable {n : ℕ}

/-- The `Lᵖ` norm outside closed balls of integer radius tends to zero for finite `p`. -/
theorem tendsto_eLpNorm_indicator_compl_closedBall
    {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ^n → ℝ} (hf : MemLp f p (volume : Measure (ℝ^n))) :
    Filter.Tendsto
      (fun m : ℕ ↦
        eLpNorm ((Metric.closedBall (0 : ℝ^n) (m : ℝ))ᶜ.indicator f) p
          (volume : Measure (ℝ^n)))
      Filter.atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  let s : ℕ → Set (ℝ^n) := fun m ↦ (Metric.closedBall (0 : ℝ^n) (m : ℝ))ᶜ
  have hsf (m : ℕ) : AEStronglyMeasurable ((s m).indicator f) volume :=
    hf.aestronglyMeasurable.indicator measurableSet_closedBall.compl
  let F : ℕ → ℝ^n → ℝ≥0∞ := fun m x ↦ ‖(s m).indicator f x‖ₑ ^ p.toReal
  -- dominated convergence for `∫⁻ ‖1_{s m} f‖ₑ ^ p`, dominated by `‖f‖ₑ ^ p`
  have hlin : Filter.Tendsto (fun m ↦ ∫⁻ x, F m x) Filter.atTop (𝓝 0) := by
    simpa using tendsto_lintegral_filter_of_dominated_convergence' (F := F) (f := fun _ ↦ 0)
      (fun x ↦ ‖f x‖ₑ ^ p.toReal)
      (.of_forall fun m ↦ ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hsf m).enorm)
      (.of_forall fun m ↦ .of_forall fun x ↦
        ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self _ _) hp_pos.le)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.eLpNorm_lt_top).ne
      (ae_of_all _ fun x ↦ tendsto_const_nhds.congr' <| by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ‖x‖]
          with m hm
        simp [F, s, hm, ENNReal.zero_rpow_of_pos hp_pos])
  have hnorm (m : ℕ) : eLpNorm ((s m).indicator f) p volume = (∫⁻ x, F m x) ^ p.toReal⁻¹ := by
    simpa only [F, one_div] using eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hsf m)
  change Filter.Tendsto (fun m ↦ eLpNorm ((s m).indicator f) p volume) Filter.atTop (𝓝 0)
  simp_rw [hnorm]
  simpa only [ENNReal.zero_rpow_of_pos (inv_pos.2 hp_pos)] using
    hlin.ennrpow_const p.toReal⁻¹

end Approximation

end SobolevSpace
