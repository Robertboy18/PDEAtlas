/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension

/-!
# Local representatives supported inside their original domain

A second cutoff confines the existing compact representative to the prescribed
open neighborhood. The original finite regularity and germ are preserved.
-/

@[expose] public section

open Filter Function Metric Set
open scoped Topology

/-- A classical germ on an open set has a compact representative whose entire
closed support lies in that set. No regularity outside the set is required. -/
theorem ContDiffOn.exists_contDiff_tsupport_subset_eventuallyEq
    {n : ℕ} {k : ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ^n → F} {Ω : Set (ℝ^n)} {x : ℝ^n}
    (hf : ContDiffOn ℝ k f Ω) (hopen : IsOpen Ω) (hx : x ∈ Ω) :
    ∃ g : ℝ^n → F, ContDiff ℝ k g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ω ∧ f =ᶠ[𝓝 x] g := by
  obtain ⟨G, hG, _, hnear⟩ := hf.exists_contDiff_compactSupport_eventuallyEq hopen hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨fun y ↦ b y • G y, b.contDiff.smul hG, b.hasCompactSupport.smul_right, ?_, ?_⟩
  · intro y hy
    have hyb : y ∈ tsupport b := tsupport_smul_subset_left b G hy
    rw [b.tsupport_eq] at hyb
    exact hball (Metric.closedBall_subset_ball (half_lt_self hr) hyb)
  · filter_upwards [hnear, b.eventuallyEq_one] with y hy hby
    change b y = (1 : ℝ) at hby
    simp only [hby, one_smul, hy]
