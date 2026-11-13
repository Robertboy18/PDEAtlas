/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform completion from a quadratic comparison

A squared-distance bound by the sum of two vanishing errors makes a family uniformly
Cauchy. Neither the parameter set nor the value space needs a linear structure.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Metric

/-- A uniform squared-distance comparison with a vanishing additive error gives a
uniformly Cauchy sequence. The comparison itself forces all necessary nonnegativity. -/
theorem uniformCauchySeqOn_of_dist_sq_le_add
    {α E : Type*} [PseudoMetricSpace E] {f : ℕ → α → E} {s : Set α}
    {error : ℕ → ℝ} (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ i j x, x ∈ s → dist (f i x) (f j x) ^ 2 ≤ error i + error j) :
    UniformCauchySeqOn f atTop s := by
  apply uniformCauchySeqOn_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (herror.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2 / 2)))
  refine ⟨N, fun i hi j hj x hx ↦ ?_⟩
  have h := hbound i j x hx
  have hi' := hN i hi
  have hj' := hN j hj
  nlinarith [dist_nonneg (x := f i x) (y := f j x)]

end Metric
