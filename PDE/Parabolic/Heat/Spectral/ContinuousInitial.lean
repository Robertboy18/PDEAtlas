/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.Stability

/-!
# Uniform initial attainment for continuous Dirichlet data

The same sine-coefficient heat series used for the `L²` evolution attains continuous
zero-boundary interval data uniformly as positive time decreases to zero.
Polynomial approximation and the supremum contraction reduce the assertion to
the `C²` initial-attainment theorem.
-/

@[expose] public section

namespace HeatEquation

open Set Filter PDE.Analysis.Fourier.SineSeries
open scoped Topology

/-- Continuous zero-boundary data are attained uniformly on the closed unit interval
by the convergent positive-time heat series. -/
theorem tendstoUniformlyOn_intervalHeatSeries_initial_of_continuousOn {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0) :
    TendstoUniformlyOn (intervalHeatSeries (intervalCoefficient g)) g
      (𝓝[>] (0 : ℝ)) (Icc 0 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨q, hq, hq0, hq1, hnear⟩ :=
    exists_contDiffOn_zero_boundary_near hg hzero hone (show 0 < ε / 3 by positivity)
  have ha := summable_norm_intervalCoefficient hq hq0 hq1
  have hi : EqOn (intervalHeatSeries (intervalCoefficient q) 0) q (Icc 0 1) := by
    intro x hx
    simpa only [intervalHeatSeries, intervalHeatMode_initial_trace] using
      (hasSum_intervalCoefficient_sineMode hq hq0 hq1 hx).tsum_eq
  have htrace := (tendstoUniformly_intervalHeatSeries_initial ha).tendstoUniformlyOn.congr_right hi
  have hevent := (Metric.tendstoUniformlyOn_iff.mp htrace (ε / 3) (by positivity)).filter_mono
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  filter_upwards [hevent, self_mem_nhdsWithin] with t ht htpos
  intro x hx
  have hstab := norm_intervalHeatSeries_sub_le hg hq.continuousOn hzero hone hq0 hq1
    (fun y hy ↦ by simpa only [norm_sub_rev] using (hnear y hy).le) htpos hx
  have h₁ : dist (g x) (q x) < ε / 3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hnear x hx
  have h₂ := ht x hx
  have h₃ : dist (intervalHeatSeries (intervalCoefficient q) t x)
      (intervalHeatSeries (intervalCoefficient g) t x) ≤ ε / 3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hstab
  have htriangle := dist_triangle (g x) (q x) (intervalHeatSeries (intervalCoefficient g) t x)
  have htriangle' := dist_triangle (q x) (intervalHeatSeries (intervalCoefficient q) t x)
    (intervalHeatSeries (intervalCoefficient g) t x)
  linarith

end HeatEquation
