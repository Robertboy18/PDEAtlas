/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Integration.Cone.Truncated
public import PDE.Analysis.Integration.UniformLimit

/-!
# Limits of integrals over finite cones

A truncated cone is compact, so uniform convergence controls both its volume integral and
its lateral flux. The lateral surface has finite Hausdorff measure: it is the Lipschitz image
of a bounded annulus. For the volume integral, Fubini identifies the cone with its shrinking
spatial sections.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE.Common WaveEquation
open scoped Topology ENNReal

namespace PDE.Analysis

/-- A finite truncated lateral cone has finite surface measure, even though this
surface measure is not locally finite in the ambient spacetime. -/
theorem measure_truncatedConeLateralSurface_lt_top {n : ℕ}
    (c : ℝ^n) (T s τ : ℝ) :
    Measure.euclideanHausdorffMeasure n (truncatedConeLateralSurface c T s τ) < ∞ := by
  rw [truncatedConeLateralSurface_eq_image]
  obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
  have hb := hK.lipschitzOnWith.euclideanHausdorffMeasure_image_le
    (s := Metric.closedBall c (T - s) \ Metric.ball c (T - τ)) n
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hb
  refine hb.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top
  · exact (measure_mono sdiff_subset).trans_lt (isCompact_closedBall c (T - s)).measure_lt_top

/-- Locally uniform convergence near a truncated lateral cone passes through
its surface integral. No assertion about behavior at spatial infinity is needed. -/
theorem tendsto_integral_truncatedConeLateralSurface {n : ℕ} {ι : Type*}
    {F : ι → ℝ^(n + 1) → ℝ} {f : ℝ^(n + 1) → ℝ}
    {l : Filter ι} [l.IsCountablyGenerated] {S : Set (ℝ^(n + 1))}
    (hlim : TendstoLocallyUniformlyOn F f l S)
    (hF : ∀ᶠ i in l, ContinuousOn (F i) S)
    (c : ℝ^n) (T s τ : ℝ) (hsub : truncatedConeLateralSurface c T s τ ⊆ S) :
    Tendsto (fun i ↦ ∫ p in truncatedConeLateralSurface c T s τ,
      F i p ∂Measure.euclideanHausdorffMeasure n) l
      (𝓝 (∫ p in truncatedConeLateralSurface c T s τ,
        f p ∂Measure.euclideanHausdorffMeasure n)) := by
  have hK := isCompact_truncatedConeLateralSurface c T s τ
  have hU := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.mono hsub)
  exact hU.tendsto_setIntegral_of_continuousOn (hF.mono fun i hi ↦ hi.mono hsub)
    hK hK.measurableSet Subset.rfl (measure_truncatedConeLateralSurface_lt_top c T s τ).ne

/-- Uniform convergence on a compact spacetime rectangle passes through the
volume integral of a truncated cone. The varying balls are handled by Fubini. -/
theorem tendsto_integral_ballIntegral_shrinking {n : ℕ} {ι : Type*}
    {F : ι → ℝ × ℝ^n → ℝ} {f : ℝ × ℝ^n → ℝ}
    {l : Filter ι} [l.IsCountablyGenerated] (c : ℝ^n) {s τ T : ℝ} (hsτ : s ≤ τ)
    (hlim : TendstoUniformlyOn F f l (Icc s τ ×ˢ Metric.closedBall c (T - s)))
    (hF : ∀ i, ContinuousOn (F i) (Icc s τ ×ˢ Metric.closedBall c (T - s)))
    (hf : ContinuousOn f (Icc s τ ×ˢ Metric.closedBall c (T - s))) :
    Tendsto (fun i ↦ ∫ t in s..τ, ballIntegral n (fun x ↦ F i (t, x)) c (T - t)) l
      (𝓝 (∫ t in s..τ, ballIntegral n (fun x ↦ f (t, x)) c (T - t))) := by
  let K := Icc s τ ×ˢ Metric.closedBall c (T - s)
  let D : Set (ℝ × ℝ^n) := {p | p.1 ∈ Ioc s τ ∧ p.2 ∈ Metric.ball c (T - p.1)}
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall c (T - s))
  have hD : MeasurableSet D :=
    (measurableSet_Ioc.preimage measurable_fst).inter
      (isOpen_lt (continuous_snd.dist continuous_const)
        (continuous_const.sub continuous_fst)).measurableSet
  have hDK : D ⊆ K := by
    intro p hp
    refine ⟨⟨hp.1.1.le, hp.1.2⟩, ?_⟩
    have hx : dist p.2 c < T - p.1 := hp.2
    exact (Metric.mem_closedBall).mpr (hx.le.trans (sub_le_sub_left hp.1.1.le T))
  have hfinite : (volume.prod volume) D ≠ ∞ :=
    ((measure_mono hDK).trans_lt hK.measure_lt_top).ne
  have hlimD := hlim.tendsto_setIntegral_of_continuousOn
    (Eventually.of_forall hF) hK hD hDK hfinite
  have hFubini (H : ℝ × ℝ^n → ℝ) (hH : ContinuousOn H K) :
      (∫ p in D, H p ∂volume.prod volume) =
        ∫ t in s..τ, ballIntegral n (fun x ↦ H (t, x)) c (T - t) := by
    have hi := (hH.integrableOn_of_subset_isCompact hK hD hDK hfinite).integrable_indicator hD
    rw [← integral_indicator hD, integral_prod _ hi, intervalIntegral.integral_of_le hsτ]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Ioc s τ
    · rw [indicator_of_mem ht]
      change (∫ x, D.indicator H (t, x)) = ∫ x in Metric.ball c (T - t), H (t, x)
      rw [← integral_indicator measurableSet_ball]
      congr 1
      funext x
      by_cases hx : x ∈ Metric.ball c (T - t)
      · rw [indicator_of_mem (show (t, x) ∈ D from ⟨ht, hx⟩), indicator_of_mem hx]
      · rw [indicator_of_notMem (show (t, x) ∉ D from fun h ↦ hx h.2),
          indicator_of_notMem hx]
    · rw [indicator_of_notMem ht]
      apply integral_eq_zero_of_ae
      filter_upwards [] with x
      exact indicator_of_notMem (show (t, x) ∉ D from fun h ↦ ht h.1) H
  simpa only [hFubini _ hf, hFubini _ (hF _)] using hlimD

end PDE.Analysis
