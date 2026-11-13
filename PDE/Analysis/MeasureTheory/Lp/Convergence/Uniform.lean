/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Uniform representatives and strong Lᵖ convergence

A finite measure concentrated on a set sees uniform convergence on that set as
strong Lᵖ convergence. Representatives may take arbitrary values outside the set.
This also applies to the essential supremum norm.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- Uniform convergence of representatives on a set of full measure implies strong
convergence of their Lᵖ classes, for any finite measure. -/
theorem tendsto_Lp_of_tendstoUniformlyOn
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {l : Filter ι} {s : Set α} {F : ι → Lp E p μ} {G : Lp E p μ}
    {f : ι → α → E} {g : α → E}
    (hs : ∀ᵐ x ∂μ, x ∈ s) (hf : ∀ i, (F i : α → E) =ᵐ[μ] f i)
    (hg : (G : α → E) =ᵐ[μ] g) (hconv : TendstoUniformlyOn f g l s) :
    Tendsto F l (𝓝 G) := by
  let C : ℝ := (measureUnivNNReal μ : ℝ) ^ p.toReal⁻¹
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv _ hδ] with i hi
  have hbound : ∀ᵐ x ∂μ, ‖(F i - G) x‖ ≤ ε / (C + 1) := by
    filter_upwards [hs, hf i, hg, Lp.coeFn_sub (F i) G] with x hx hfx hgx hsub
    rw [hsub, Pi.sub_apply, hfx, hgx, ← dist_eq_norm, dist_comm]
    exact (hi x hx).le
  rw [dist_eq_norm]
  refine (Lp.norm_le_of_ae_bound hδ.le hbound).trans_lt ?_
  change C * (ε / (C + 1)) < ε
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

end MeasureTheory
