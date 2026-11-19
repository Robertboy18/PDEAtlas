/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension

/-!
# Compact extension from an interior closed ball

A smooth cutoff equal to one on the smaller ball extends a function that is
classical only on its original open domain. Its support stays inside a larger
interior closed ball. This preserves the whole smaller ball, rather than only
the germ at its centre, when applying compact-test integral identities.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

/-- A function classical on an open domain has a compact classical extension
agreeing on any closed ball with room for a larger interior closed ball. -/
theorem ContDiffOn.exists_contDiff_tsupport_subset_eqOn_closedBall
    {n : ℕ} {k : ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ^n → F} {Ω : Set ℝ^n} (hu : ContDiffOn ℝ k u Ω) (hΩ : IsOpen Ω)
    {x : ℝ^n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : closedBall x R ⊆ Ω) :
    ∃ a : ℝ^n → F, ContDiff ℝ k a ∧ HasCompactSupport a ∧
      tsupport a ⊆ Ω ∧ EqOn a u (closedBall x r) := by
  let b : ContDiffBump x :=
    { rIn := r, rOut := R, rIn_pos := hr, rIn_lt_rOut := hrR }
  refine ⟨fun y ↦ b y • u y, ?_, b.hasCompactSupport.smul_right, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport b
    · have hyΩ : y ∈ Ω := hball (by simpa only [b.tsupport_eq] using hy)
      exact b.contDiffAt.smul (hu.contDiffAt (hΩ.mem_nhds hyΩ))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hy] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · intro y hy
    have hyb := tsupport_smul_subset_left b u hy
    exact hball (by simpa only [b.tsupport_eq] using hyb)
  · intro y hy
    change b y • u y = u y
    rw [b.one_of_mem_closedBall hy, one_smul]
