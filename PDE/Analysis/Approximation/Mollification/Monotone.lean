/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Mollification.Real

/-!
# Smooth approximation of continuous monotone functions

Positive convolution preserves order, without boundedness or compact support of the
input. Normalized bumps with radii tending to zero converge locally uniformly.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set ContinuousLinearMap
open scoped Topology Convolution

namespace PDE.Analysis.Calculus

/-- Positive mollification preserves monotonicity of a continuous real function. -/
theorem monotone_realMollify (φ : ContDiffBump (0 : ℝ)) {f : ℝ → ℝ}
    (hf : Continuous f) (hmono : Monotone f) : Monotone (realMollify φ f) := by
  have hint := φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) (φ.integrable_normed (μ := volume)).locallyIntegrable hf
  intro x y hxy
  exact integral_mono (hint x) (hint y) fun t ↦
    mul_le_mul_of_nonneg_left (hmono (sub_le_sub_right hxy t)) (φ.nonneg_normed t)

/-- Normalized positive bumps approximate a continuous function locally uniformly. -/
theorem realMollify_tendstoLocallyUniformly {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    {f : ℝ → ℝ} (hf : Continuous f) :
    TendstoLocallyUniformly (fun i ↦ realMollify (φ i) f) f l := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have hmoll : Tendsto (fun p : ι × ℝ ↦ realMollify (φ p.1) f p.2)
      (l ×ˢ 𝓝 x) (𝓝 (f x)) :=
    ContDiffBump.convolution_tendsto_right (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ ↦ hf.aestronglyMeasurable)
      ((hf.tendsto x).comp tendsto_snd) tendsto_snd
  exact (((hf.tendsto x).comp tendsto_snd).prodMk_nhds hmoll).mono_right
    (nhds_le_uniformity _)

end PDE.Analysis.Calculus
