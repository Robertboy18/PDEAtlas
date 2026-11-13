/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.LocallyFinite
public import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.Partition
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Summing interior approximations

An absolutely summable series in the Sobolev graph has the expected almost everywhere sum
of base representatives. Separately, a locally finite sum of smooth functions on an open
domain is smooth there. These two facts identify the Sobolev limit with its smooth local
representative without requiring local finiteness at boundary points.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Manifold Topology Sobolev

namespace SobolevSpace.Approximation.OpenDomain

open GraphSpace

/-- Absolute convergence in the Sobolev graph gives the pointwise series almost everywhere
for the base representative. -/
theorem baseRepresentative_tsum_ae {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Set (ℝ^n)} (E : ℕ → W^{k,p}(Ω))
    (hE : Summable (fun i ↦ ‖E i‖)) :
    baseRepresentative (∑' i, E i) =ᵐ[domainMeasure n Ω]
      fun x ↦ ∑' i, baseRepresentative (E i) x := by
  let B := wkpBaseCoordinateCLM (n := n) (m := k) (p := p) (Ω := Ω)
  have hB : Summable (fun i ↦ ‖B (E i)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun i ↦ wkpBaseCoordinateCLM_norm_le (E i)) hE
  have he : (∑' i, ‖B (E i)‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hB
  change (fun x ↦ B (∑' i, E i) x) =ᵐ[domainMeasure n Ω] _
  rw [B.map_tsum hE.of_norm]
  exact Lp.coeFn_tsum he

end SobolevSpace.Approximation.OpenDomain
