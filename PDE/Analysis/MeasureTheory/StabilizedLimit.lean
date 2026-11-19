/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Identifying a locally stabilized approximation

If an approximation converges in an `Lᵖ` seminorm and is eventually equal to a fixed function
on a measurable set, that fixed function represents the limit there. This does not require
pointwise convergence or continuity of the limit.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PDE.Analysis

/-- Eventual equality on a measurable set identifies an `Lᵖ` limit almost everywhere there.
The exponent may be any nonzero exponent, including infinity. -/
theorem ae_eq_of_tendsto_eLpNorm_of_eventually_eqOn
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {p : ℝ≥0∞} {f v : α → E} {F : ℕ → α → E}
    (hs : MeasurableSet s) (hp : p ≠ 0)
    (hlim : Tendsto (fun j ↦ eLpNorm (fun x ↦ F j x - f x) p μ) atTop (𝓝 0))
    (hstable : ∀ᶠ j in atTop, Set.EqOn (F j) v s) :
    v =ᵐ[μ.restrict s] f := by
  have hzero : eLpNorm (fun x ↦ v x - f x) p (μ.restrict s) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    filter_upwards [hstable] with j hj
    have heq : (fun x ↦ v x - f x) =ᵐ[μ.restrict s] (fun x ↦ F j x - f x) := by
      filter_upwards [ae_restrict_mem hs] with x hx
      rw [hj hx]
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hae := (eLpNorm_eq_zero_iff hp).mp hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx

end PDE.Analysis
