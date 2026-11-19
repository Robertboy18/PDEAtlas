/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.FDeriv.SpaceTime

/-!
# Classical representatives before a terminal time

Time reflection reduces an upper time boundary to the forward
localization theorem. Every smaller closed strip has an ambient classical
representative with the same germs. No regularity at the terminal time is used.
-/

@[expose] public noncomputable section

open PDE.Common Set Filter
open scoped Topology

namespace WaveEquation

/-- A field classical strictly before `T` has a global classical representative
with the same germs at all times at most `S < T`. -/
theorem exists_contDiff_eventuallyEq_before {m : ℕ∞} {u : ℝ^2 → ℝ} {S T : ℝ}
    (hu : ContDiffOn ℝ m u {p | p 0 < T}) (hST : S < T) :
    ∃ v : ℝ^2 → ℝ, ContDiff ℝ m v ∧ ∀ p : ℝ^2, p 0 ≤ S → v =ᶠ[𝓝 p] u := by
  let P : ℝ^2 → ℝ^2 := fun p ↦ timeSpaceCons (T - p 0) (spatialPart p)
  have hP : ContDiff ℝ m P := (contDiff_timeSpaceCons_uncurry 1).comp
      ((contDiff_const.sub (EuclideanSpace.proj 0).contDiff).prodMk (spatialPartCLM 1).contDiff)
  have hPP (p : ℝ^2) : P (P p) = p := by
    simp [P]
  have hU : ContDiffOn ℝ m (u ∘ P) {p : ℝ^2 | 0 < p 0} := by
    refine hu.comp hP.contDiffOn fun p hp ↦ ?_
    change T - p 0 < T
    exact sub_lt_self T hp
  obtain ⟨v, hv, he⟩ := exists_contDiff_eqOn_forward hU (half_pos (sub_pos.mpr hST))
  refine ⟨v ∘ P, hv.comp hP, fun p hp ↦ ?_⟩
  have hlt : (T - S) / 2 < P p 0 := by
    change (T - S) / 2 < T - p 0
    linarith
  have hgerm := (eventuallyEq_of_eqOn_forward he hlt).comp_tendsto hP.continuous.continuousAt
  simpa only [Function.comp_def, hPP] using hgerm

end WaveEquation
