/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.ParameterApproximation
public import PDE.Analysis.Topology.UniformConvergence

/-!
# Continuous nonlinearities and spatial smoothing

The nonlinear commutator tends locally uniformly to zero. Its proof uses
Mathlib's normalized bump functions and the continuity of the limiting field.
-/

public section

open Filter Set MeasureTheory
open scoped Topology Convolution

namespace ContDiffBump

/-- Applying a continuous nonlinearity before or after spatial smoothing gives
the same locally uniform limit. This is the error term in a regularized
nonlinear equation. -/
theorem tendstoLocallyUniformlyOn_comp_convolution_sub_convolution_comp
    {P G E F ι : Type*} [TopologicalSpace P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    {u : P × G → E} {S : Set P} {g : E → F}
    (hu : ContinuousOn u (S ×ˢ univ)) (hg : Continuous g)
    {φ : ι → ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun i p ↦ g (((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
          (fun y ↦ u (p.1, y))) p.2) -
        ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
          (fun y ↦ g (u (p.1, y)))) p.2)
      (fun _ ↦ 0) l (S ×ˢ univ) := by
  have hfirst := hg.comp_tendstoLocallyUniformlyOn
    (tendstoLocallyUniformlyOn_convolution_parameter (μ := μ) hu hφ) hu
  have hsecond := tendstoLocallyUniformlyOn_convolution_parameter (μ := μ)
    (hg.comp_continuousOn hu) hφ
  simpa only [Function.comp_def, Pi.sub_def, sub_self, Pi.zero_def] using hfirst.sub hsecond

end ContDiffBump
