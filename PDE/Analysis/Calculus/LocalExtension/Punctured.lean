/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension

/-!
# Regularizing a kernel inside a prescribed ball

A kernel smooth away from zero can be replaced by a globally smooth compact
function without changing its germ on the bounded region outside a prescribed
ball about its pole. The existing annular extension supplies the replacement.
This makes smooth Sobolev liftings of singular boundary data available without
requiring any regularity of the boundary itself.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

/-- On a bounded region, a translated punctured kernel has a global compact
regularization agreeing in a neighbourhood of every point outside the prescribed
ball. The ball radius and the regularity order are arbitrary positive and finite
or infinite, respectively. -/
theorem ContDiffOn.exists_contDiff_compactSupport_eq_away_pole
    {n : ℕ} {k : ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : ℝ^n → F} (hK : ContDiffOn ℝ k K {0}ᶜ)
    {Ω : Set ℝ^n} (hbounded : Bornology.IsBounded Ω)
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ^n → F, ContDiff ℝ k A ∧ HasCompactSupport A ∧
      ∀ y ∈ closure Ω, r ≤ ‖y - x‖ →
        A =ᶠ[𝓝 y] (fun z ↦ K (z - x)) := by
  obtain ⟨M, hM, hbound⟩ := hbounded.isCompact_closure.isBounded.subset_ball_lt 0 x
  obtain ⟨G, hG, hGc, heq⟩ := hK.exists_contDiff_compactSupport_eqOn_annulus
    (half_pos hr) (by linarith : 0 < M + 1)
  refine ⟨fun z ↦ G (z - x), hG.comp (contDiff_id.sub contDiff_const),
    hGc.comp_homeomorph (Homeomorph.subRight x), ?_⟩
  intro y hy hnear
  have hupper : ‖y - x‖ < M + 1 := by
    have h := hbound hy
    rw [mem_ball, dist_eq_norm] at h
    linarith
  have hopen : IsOpen {z : ℝ^n | r / 2 < ‖z - x‖ ∧ ‖z - x‖ < M + 1} :=
    isOpen_Ioo.preimage ((continuous_id.sub continuous_const).norm)
  filter_upwards [hopen.mem_nhds ⟨lt_of_lt_of_le (half_lt_self hr) hnear, hupper⟩] with z hz
  exact heq (z - x) hz.1.le hz.2.le
