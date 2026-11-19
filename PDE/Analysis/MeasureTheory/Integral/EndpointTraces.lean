/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Order.ExtendFrom
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrability from finite endpoint traces

A continuous function on a bounded open interval with finite limits at both
endpoints extends continuously to the closed interval, so it is integrable.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- Finite endpoint limits make a continuous function integrable on an open interval. -/
theorem integrableOn_Ioo_of_finite_traces
    {v : ℝ → ℝ} {a b l r : ℝ} (hv : ContinuousOn v (Ioo a b))
    (hl : Tendsto v (𝓝[>] a) (𝓝 l)) (hr : Tendsto v (𝓝[<] b) (𝓝 r)) :
    IntegrableOn v (Ioo a b) := by
  have he := continuousOn_Icc_extendFrom_Ioo hv hl hr
  exact (he.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
    (extendFrom_extends hv) measurableSet_Ioo

end MeasureTheory
