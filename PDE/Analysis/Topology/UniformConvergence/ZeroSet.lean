/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Order.Compact
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Positivity on moving zero sets

Uniform perturbations preserve positivity on the zero set of a continuous map
on a compact set. The zero sets may move, and the perturbed maps need not be
continuous. This is useful when a derivative is positive only where a limiting
field vanishes, rather than everywhere on the compact set.
-/

public section

open Filter Set

/-- Positivity on a compact zero set persists under uniform convergence of both
maps. The approximating maps need not be continuous, and the zero set may be empty. -/
theorem IsCompact.eventually_pos_on_zeros_of_tendstoUniformlyOn
    {α E ι : Type*} [TopologicalSpace α] [MetricSpace E] [Zero E]
    {s : Set α} {f : α → E} {g : α → ℝ} {F : ι → α → E} {G : ι → α → ℝ}
    {l : Filter ι} (hs : IsCompact s) (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hpos : ∀ x ∈ s, f x = 0 → 0 < g x)
    (hF : TendstoUniformlyOn F f l s) (hG : TendstoUniformlyOn G g l s) :
    ∀ᶠ i in l, ∀ x ∈ s, F i x = 0 → 0 < G i x := by
  have hd : ContinuousOn (fun x ↦ dist (f x) 0) s :=
    fun x hx ↦ Filter.Tendsto.dist (hf x hx) continuousWithinAt_const
  have hc : ContinuousOn (fun x ↦ max (dist (f x) 0) (g x)) s :=
    fun x hx ↦ Filter.Tendsto.max (hd x hx) (hg x hx)
  -- Away from the zero set, distance supplies the positive margin instead of g.
  obtain ⟨ε, hε, hbound⟩ := hs.exists_forall_le'
    hc (a := (0 : ℝ)) (by
      intro x hx
      by_cases hzero : f x = 0
      · exact (hpos x hx hzero).trans_le (le_max_right _ _)
      · exact (dist_pos.mpr hzero).trans_le (le_max_left _ _))
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) (half_pos hε),
    Metric.tendstoUniformlyOn_iff.mp hG (ε / 2) (half_pos hε)] with i hFi hGi
  intro x hx hzero
  have hsmall : dist (f x) 0 < ε / 2 := by
    simpa only [hzero] using hFi x hx
  have hlarge : ε ≤ g x := by
    rcases le_max_iff.mp (hbound x hx) with h | h
    · linarith
    · exact h
  have hclose : |g x - G i x| < ε / 2 := by
    simpa only [Real.dist_eq] using hGi x hx
  linarith [(abs_lt.mp hclose).2]
