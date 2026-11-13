/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Smoothness of integral curves on open time intervals

A classical integral curve inherits the smoothness of its vector field. Around
any interior time, choose a compact interval and apply Mathlib's regularity
result for the Picard integral equation. This gives a local smooth germ without
assuming temporal derivatives of the curve beyond its defining ODE.
-/

@[expose] public section

open Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A classical solution inherits the finite or smooth regularity of its vector
field on any open time set. No global extension of the curve is required. -/
theorem contDiffOn_of_hasDerivAt {n : ℕ∞} {s : Set ℝ} {u : ℝ → E} {f : ℝ → E → E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n (Function.uncurry f) (s ×ˢ univ))
    (hu : ∀ t ∈ s, HasDerivAt u (f t (u t)) t) : ContDiffOn ℝ n u s := by
  intro t ht
  obtain ⟨a, b, ht', hab, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hs.mem_nhds ht)
  have hlocal : ContDiffOn ℝ n u (Icc a b) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (hf.mono (prod_subset_prod_left hsub))
      (fun r hr ↦ (hu r (hsub hr)).hasDerivWithinAt) (fun _ _ ↦ mem_univ _)
  exact (hlocal t ht').contDiffAt hab |>.contDiffWithinAt

end PDE.Analysis.Evolution
