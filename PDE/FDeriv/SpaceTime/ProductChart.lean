/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime

/-!
# Smoothness through the product chart of spacetime

A field on canonical spacetime `ℝ^(n+1)` is smooth at a point when its pullback
`(t, x) ↦ f (t, x)` to `ℝ × ℝⁿ` is smooth on an open neighbourhood of the corresponding pair:
the pair map `z ↦ (z₀, spatialPart z)` is a continuous linear map and `timeSpaceCons` inverts it.
-/

@[expose] public section

noncomputable section

open PDE.Common
open scoped Topology

namespace PDE.Common

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pair map `z ↦ (z₀, spatialPart z)` from spacetime to `ℝ × ℝⁿ` is smooth. -/
theorem contDiff_timeSpacePair {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun z : ℝ^(n + 1) ↦ (z 0, spatialPart z)) := by
  refine (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).contDiff.prodMk ?_
  have he : (spatialPart : ℝ^(n + 1) → ℝ^n) = ⇑(spatialPartCLM n) :=
    funext fun z ↦ PiLp.ext fun i ↦ by rw [spatialPartCLM_apply, spatialPart_apply]
  rw [he]
  exact (spatialPartCLM n).contDiff

/-- A spacetime field whose pullback to `ℝ × ℝⁿ` is smooth on an open set is smooth at every
spacetime point whose pair lies in the set. -/
theorem contDiffAt_of_contDiffOn_timeSpaceCons {m : WithTop ℕ∞} {f : ℝ^(n + 1) → E}
    {s : Set (ℝ × ℝ^n)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ m (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons p.1 p.2)) s)
    {z : ℝ^(n + 1)} (hz : (z 0, spatialPart z) ∈ s) : ContDiffAt ℝ m f z := by
  have h := (hf.contDiffAt (hs.mem_nhds hz)).comp z contDiff_timeSpacePair.contDiffAt
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' ↦ ?_)
  simp only [Function.comp_apply]
  rw [timeSpaceCons_spatialPart]

end PDE.Common
