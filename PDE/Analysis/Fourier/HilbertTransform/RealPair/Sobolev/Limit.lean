/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Limit
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative

/-!
# Hilbert-transform convergence from the real L² base

The base coordinate of the real H¹ graph is its vorticity L² class.
Its continuous representative defines the same class. Continuity of the
spectral Hilbert transform therefore supplies the velocity derivative
limit from strong convergence of the base alone. Convergence in the graph
norm is a sufficient special case; the first derivative may instead converge weakly.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace PDE.Analysis

/-- Strong convergence of the real base constructs the limiting Hilbert
pair and gives strong L² convergence of its output. -/
theorem exists_hilbertPair_limit_of_tendsto_realLineCoordinate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → W^{1,2}(ℝ^1)} {F : W^{1,2}(ℝ^1)}
    {g : ι → ℝ → ℝ}
    (hf : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (f i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    (hpair : ∀ i, IsHilbertPair (realLineRepresentative (f i)) (g i)) :
    ∃ G : Lp ℝ 2 (volume : Measure ℝ),
      IsHilbertPair (realLineRepresentative F) G ∧
        Tendsto (fun i ↦ (hpair i).memLp_right.toLp (g i)) l (𝓝 G) := by
  apply exists_hilbertPair_limit_of_tendsto_Lp
    (fun i ↦ memLp_realLineRepresentative (f i)) (memLp_realLineRepresentative F) hpair
  simpa only [toLp_realLineRepresentative] using hf


/-- H¹ convergence constructs the limiting Hilbert pair and gives L²
convergence of the supplied output representatives. -/
theorem exists_hilbertPair_limit_of_tendsto_H1
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → W^{1,2}(ℝ^1)} {F : W^{1,2}(ℝ^1)}
    {g : ι → ℝ → ℝ}
    (hf : Tendsto f l (𝓝 F))
    (hpair : ∀ i, IsHilbertPair (realLineRepresentative (f i)) (g i)) :
    ∃ G : Lp ℝ 2 (volume : Measure ℝ),
      IsHilbertPair (realLineRepresentative F) G ∧
        Tendsto (fun i ↦ (hpair i).memLp_right.toLp (g i)) l (𝓝 G) := by
  exact exists_hilbertPair_limit_of_tendsto_realLineCoordinate
    (((realLineCoordinateCLM (baseIndex 1 1)).continuous.tendsto F).comp hf) hpair

end PDE.Analysis
