/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.RegularLevel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The side of a regular level graph

A positive derivative in the last variable orients the implicit graph: nearby,
the strict superlevel set is its epigraph. Continuity of this derivative supplies
one product neighborhood on which every vertical slice is strictly increasing.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology ContDiff

/-- A positive transverse derivative identifies a strict superlevel set locally
with the epigraph of one `C^m` graph, including at infinite order. -/
theorem ContDiffOn.exists_implicit_superlevel_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : ℕ∞} {f : E × ℝ → ℝ} {U : Set (E × ℝ)} {x : E × ℝ}
    (hf : ContDiffOn ℝ m f U) (hU : IsOpen U) (hm : 1 ≤ m) (hx : x ∈ U)
    (hpartial : 0 < fderiv ℝ f x (0, 1)) :
    ∃ g : E → ℝ, ∃ s : Set E,
      IsOpen s ∧ x.1 ∈ s ∧ ContDiffOn ℝ m g s ∧ g x.1 = x.2 ∧
        ∀ᶠ y in 𝓝 x, f x < f y ↔ g y.1 < y.2 := by
  obtain ⟨g, s, hs, hxs, hg, hgx, hgraph, _⟩ :=
    hf.exists_implicitFunction_of_fderiv_snd_ne_zero hU hm hx hpartial.ne'
  have hf1 : ContDiffAt ℝ 1 f x :=
    (hf.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hm)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ 0 < fderiv ℝ f y (0, 1) :=
    inter_mem (hU.mem_nhds hx)
      (((hf1.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const)
        (Ioi_mem_nhds hpartial))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hmem {q : E} {t : ℝ} (hq : q ∈ ball x.1 δ) (ht : t ∈ ball x.2 δ) :
      (q, t) ∈ ball x δ := by
    rw [← Prod.eta x, ← ball_prod_same]
    exact ⟨hq, ht⟩
  have hderiv {q : E} {t : ℝ} (hq : q ∈ ball x.1 δ) (ht : t ∈ ball x.2 δ) :
      HasDerivAt (fun r ↦ f (q, r)) (fderiv ℝ f (q, t) (0, 1)) t := by
    have hd := ((hf.contDiffAt (hU.mem_nhds (hball (hmem hq ht)).1)).of_le
      (show (1 : ℕ∞ω) ≤ m by exact_mod_cast hm)).differentiableAt one_ne_zero
    simpa only [Function.comp_def, id_eq] using hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t q).prodMk (hasDerivAt_id t))
  have hmono {q : E} (hq : q ∈ ball x.1 δ) :
      StrictMonoOn (fun t ↦ f (q, t)) (ball x.2 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_ball x.2 δ)
    · exact fun t ht ↦ (hderiv hq ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hderiv hq (interior_subset ht)).deriv]
      exact (hball (hmem hq (interior_subset ht))).2
  have hgcont := (hg.contDiffAt (hs.mem_nhds hxs)).continuousAt
  have hgnear : ∀ᶠ q in 𝓝 x.1, g q ∈ ball x.2 δ := by
    apply hgcont
    simpa only [hgx] using ball_mem_nhds x.2 hδ
  refine ⟨g, s, hs, hxs, hg, hgx, ?_⟩
  filter_upwards [continuousAt_fst (hs.mem_nhds hxs),
    continuousAt_fst (ball_mem_nhds x.1 hδ), continuousAt_fst hgnear,
    continuousAt_snd (ball_mem_nhds x.2 hδ)] with y hys hyq hyg hyt
  rw [← (hgraph y.1 hys).2]
  exact (hmono hyq).lt_iff_lt hyg hyt
