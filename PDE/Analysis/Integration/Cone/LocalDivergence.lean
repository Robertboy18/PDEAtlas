/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Divergence
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Analysis.Calculus.Divergence.Locality
import PDE.FDeriv.SpaceTime

/-!
# Cone divergence before a possibly singular vertex

The current need only be C¹ on an open time band containing the truncated cone.
For s₀ < s ≤ τ < T, temporal cutoffs supply global representatives agreeing
locally from s through τ. The truncated divergence identity therefore retains both
cap integrals, with no continuity or extension assumed at T.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped RealInnerProductSpace

namespace PDE.Analysis

variable {n : ℕ}

/-- Divergence on a truncated cone for a current smooth only on an open time band.
Both cap terms remain; no regularity or limiting value at the vertex is assumed. -/
theorem integral_divergence_truncatedCone_of_contDiffOn_band [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} {Q : ℝ^(n + 1) → ℝ^n} {s₀ s τ T : ℝ}
    (hP : ContDiffOn ℝ 1 P {p | s₀ < p 0 ∧ p 0 < T})
    (hQ : ContDiffOn ℝ 1 Q {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n)
    (hs : s₀ < s) (hsτ : s ≤ τ) (hτ : τ < T) :
    (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x) =
      (∫ x in Metric.ball c (T - τ), P (timeSpaceCons τ x)) -
        (∫ x in Metric.ball c (T - s), P (timeSpaceCons s x)) +
          (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
            (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
              ∂Measure.euclideanHausdorffMeasure n) := by
  obtain ⟨P', hP', heP⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 1) (f := P) (EuclideanSpace.proj 0 : ℝ^(n + 1) →L[ℝ] ℝ)
    (by simpa using hP) hs hτ
  obtain ⟨Q', hQ', heQ⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 1) (f := Q) (EuclideanSpace.proj 0 : ℝ^(n + 1) →L[ℝ] ℝ)
    (by simpa using hQ) hs hτ
  simp only [EuclideanSpace.coe_proj] at heP heQ
  have hvolume :
      (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
        (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x) =
      (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
        (∂[0] P') (timeSpaceCons t x) - ∇· (fun y ↦ Q' (timeSpaceCons t y)) x) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hsτ] at ht
    apply setIntegral_congr_fun measurableSet_ball
    intro x _
    have hp := heP (timeSpaceCons t x) (by simpa only [timeSpaceCons_zero] using ht)
    have hq := heQ (timeSpaceCons t x) (by simpa only [timeSpaceCons_zero] using ht)
    dsimp only
    rw [partialDeriv_congr_nhds 0 hp]
    congr 1
    simpa only [Function.comp_def] using (hq.comp_tendsto
      (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt).divergence_eq
  have hcap (t : ℝ) (ht : t ∈ Icc s τ) :
      (∫ x in Metric.ball c (T - t), P (timeSpaceCons t x)) =
        ∫ x in Metric.ball c (T - t), P' (timeSpaceCons t x) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x _
    exact (heP (timeSpaceCons t x) (by simpa only [timeSpaceCons_zero] using ht)).eq_of_nhds
  have hsurface :
      (∫ p in truncatedConeLateralSurface c T s τ,
        (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
          ∂Measure.euclideanHausdorffMeasure n) =
      (∫ p in truncatedConeLateralSurface c T s τ,
        (P' p - ⟪Q' p, NormedSpace.normalize (spatialPart p - c)⟫)
          ∂Measure.euclideanHausdorffMeasure n) := by
    apply setIntegral_congr_fun (isCompact_truncatedConeLateralSurface c T s τ).measurableSet
    intro p hp
    dsimp only
    rw [(heP p ⟨hp.1, hp.2.1⟩).eq_of_nhds, (heQ p ⟨hp.1, hp.2.1⟩).eq_of_nhds]
  rw [hvolume, hcap τ ⟨hsτ, le_rfl⟩, hcap s ⟨le_rfl, hsτ⟩, hsurface]
  exact integral_divergence_truncatedCone hP' hQ' c hsτ hτ.le

/-- Divergence on a truncated cone for a current smooth only before the vertex time.
Both cap terms remain; no regularity or limiting value at the vertex is assumed. -/
theorem integral_divergence_truncatedCone_of_contDiffOn [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} {Q : ℝ^(n + 1) → ℝ^n} {s τ T : ℝ}
    (hP : ContDiffOn ℝ 1 P {p | p 0 < T})
    (hQ : ContDiffOn ℝ 1 Q {p | p 0 < T}) (c : ℝ^n)
    (hsτ : s ≤ τ) (hτ : τ < T) :
    (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x) =
      (∫ x in Metric.ball c (T - τ), P (timeSpaceCons τ x)) -
        (∫ x in Metric.ball c (T - s), P (timeSpaceCons s x)) +
          (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
            (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
              ∂Measure.euclideanHausdorffMeasure n) := by
  exact integral_divergence_truncatedCone_of_contDiffOn_band
    (s₀ := s - 1) (hP.mono fun _ hp ↦ hp.2) (hQ.mono fun _ hp ↦ hp.2) c
    (sub_lt_self s zero_lt_one) hsτ hτ

end PDE.Analysis
