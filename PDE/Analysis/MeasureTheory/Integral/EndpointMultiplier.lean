/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Order.ExtendFrom

/-!
# Integrable products with finite endpoint limits

A continuous multiplier with finite limits at both ends of an interval
extends continuously to its closure. Multiplying an integrable function by
this extension preserves integrability, regardless of the multiplier's
assigned endpoint values.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- A continuous multiplier with finite one-sided endpoint limits preserves
integrability on the open interval. -/
theorem IntegrableOn.mul_of_continuousOn_tendsto_Ioo
    {R : Type*} [NormedRing R] {f g : ℝ → R} {a b : ℝ} {la lb : R}
    {μ : Measure ℝ} (hf : IntegrableOn f (Ioo a b) μ)
    (hg : ContinuousOn g (Ioo a b))
    (ha : Tendsto g (𝓝[>] a) (𝓝 la)) (hb : Tendsto g (𝓝[<] b) (𝓝 lb)) :
    IntegrableOn (fun x ↦ f x * g x) (Ioo a b) μ := by
  have hc := continuousOn_Icc_extendFrom_Ioo hg ha hb
  apply (hf.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc
    Ioo_subset_Icc_self).congr_fun _ measurableSet_Ioo
  intro x hx
  exact congrArg (f x * ·) (extendFrom_extends hg x hx)

end MeasureTheory
