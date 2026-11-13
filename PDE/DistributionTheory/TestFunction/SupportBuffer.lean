/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Smooth cutoffs with a uniform support buffer

Compactness turns a neighborhood of a support into a uniform radius. A
smooth cutoff can therefore equal one both on the support and on all its
translates by vectors smaller than that radius. The radius and the cutoff
depend only on the compact set and its surrounding open set.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace TestFunction

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Smooth separation with a uniform closed translation buffer, also for an
empty compact set. No function to be localized enters the construction. -/
theorem exists_eq_one_on_compact_with_buffer {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (ρ : ℝ) (χ : 𝓓((⊤ : Opens E), ℝ)), 0 < ρ ∧
      tsupport χ.toFun ⊆ U ∧
      (∀ x ∈ K, χ.toFun =ᶠ[𝓝 x] 1) ∧
      (∀ x ∈ K, ∀ v : E, ‖v‖ ≤ ρ → χ.toFun (x + v) = 1) ∧
      (∀ x, χ.toFun x ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hbuffer : Metric.cthickening (δ / 2) K ⊆ U :=
    (Metric.cthickening_subset_thickening' hδ (by linarith) K).trans hδU
  obtain ⟨χ, hχU, hχone, hχnhds, hχrange⟩ :=
    exists_eq_one_on_compact_finiteDimensional hU hK.cthickening hbuffer
  refine ⟨δ / 2, χ, by positivity, hχU, ?_, ?_, hχrange⟩
  · intro x hx
    apply hχnhds
    exact Metric.mem_cthickening_of_dist_le x x (δ / 2) K hx
      (by simpa only [dist_self] using (half_pos hδ).le)
  · intro x hx v hv
    apply hχone
    apply Metric.mem_cthickening_of_dist_le (x + v) x (δ / 2) K hx
    simpa only [dist_eq_norm, add_sub_cancel_left] using hv

end TestFunction
