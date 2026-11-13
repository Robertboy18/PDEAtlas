/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2

/-!
# Integrability of a weighted L² pairing

If `q √w` and `r √w` are in `L²` and `w ≥ 0` almost everywhere, then `q r w` is
integrable, by Hölder's inequality for the two square-integrable factors.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- The product of two weighted L² factors is integrable in the original weight. -/
theorem integrable_weighted_pair_of_memLp
    {μ : Measure ℝ} {q r w : ℝ → ℝ}
    (hq : MemLp (fun x ↦ q x * √(w x)) 2 μ)
    (hr : MemLp (fun x ↦ r x * √(w x)) 2 μ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) : Integrable (fun x ↦ q x * r x * w x) μ := by
  apply (hq.integrable_mul hr).congr
  filter_upwards [hw] with x hx
  simp only [Pi.mul_apply]
  calc
    _ = q x * r x * (√(w x)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hx]

end MeasureTheory
