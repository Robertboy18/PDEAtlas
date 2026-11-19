/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean.SpaceTime
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Analysis.Integration.Cone.Continuity
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Continuity of moving-ball L6 norms

Local continuity on an open time band gives continuity of the L6 norm on
compact interior time intervals. A local representative reduces the claim to
continuous ball integration, with no regularity at the cone vertex.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace PDE.Analysis

/-- On a compact interior time interval the actual moving-ball L6 norm is continuous.
The field need only be continuous on the open time band; no value at the apex is used. -/
theorem continuousOn_lpNorm_six_shrinking_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ^4 → E} {s₀ s τ T : ℝ}
    (hv : ContinuousOn v {p | s₀ < p 0 ∧ p 0 < T})
    (hs : s₀ < s) (hτ : τ < T) (c : ℝ^3) :
    ContinuousOn (fun t ↦ lpNorm (fun x ↦ v (timeSpaceCons t x)) 6
      (volume.restrict (Metric.ball c (T - t)))) (Icc s τ) := by
  have hv' : ContDiffOn ℝ 0 v {p | s₀ < p 0 ∧ p 0 < T} :=
    contDiffOn_zero.mpr hv
  obtain ⟨g, hg, heq⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 0) (f := v) (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ)
    (by simpa using hv') hs hτ
  simp only [EuclideanSpace.coe_proj] at heq
  have hc := (continuousOn_ballIntegral_shrinking
    (hg.continuous.norm.pow 6) c T).mono (show Icc s τ ⊆ Iic T from fun _ ht ↦ ht.2.trans hτ.le)
  have hr := hc.rpow_const
    (fun _ _ ↦ Or.inr (by norm_num : (0 : ℝ) ≤ (6 : ℝ)⁻¹))
  apply hr.congr
  intro t ht
  dsimp only
  have hsection : Continuous (fun x : ℝ^3 ↦ g (timeSpaceCons t x)) :=
    hg.continuous.comp ((timeSpaceContinuousLinearEquiv 3).symm.continuous.comp
      (continuous_const.prodMk continuous_id))
  have hm := hsection.continuousOn.memLp_of_subset_isCompact
    (μ := volume) (p := (6 : ℝ≥0∞)) (isCompact_closedBall c (T - t))
    measurableSet_ball Metric.ball_subset_closedBall
  have he : (fun x ↦ v (timeSpaceCons t x)) = fun x ↦ g (timeSpaceCons t x) := by
    funext x
    exact (heq (timeSpaceCons t x) (by simpa using ht)).eq_of_nhds
  rw [he, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hm.aestronglyMeasurable]
  simp only [ballIntegral, ENNReal.toReal_ofNat, Real.rpow_ofNat, Pi.pow_apply]

end PDE.Analysis
