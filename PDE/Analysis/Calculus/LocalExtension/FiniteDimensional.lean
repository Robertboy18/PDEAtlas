/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension

/-!
# Compact smooth extension in finite dimensions

A smooth germ on a finite-dimensional real normed space admits a compactly supported global
extension of the same order.
-/

@[expose] public noncomputable section

section

open Filter Set
open scoped Topology ContDiff

/-- A function of finite or infinite order on an open neighborhood in a finite-dimensional
space has a compact global representative with the same germ and order. -/
theorem ContDiffOn.exists_contDiff_compactSupport_eventuallyEq_finiteDimensional
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ∞} {f : E → G} {s : Set E} {x : E}
    (hf : ContDiffOn ℝ m f s) (hs : IsOpen s) (hx : x ∈ s) :
    ∃ g : E → G, ContDiff ℝ m g ∧ HasCompactSupport g ∧ f =ᶠ[𝓝 x] g := by
  classical
  let e : E ≃L[ℝ] ℝ^(Module.finrank ℝ E) :=
    (Module.finBasis ℝ E).equivFunL.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  have hlocal : ContDiffOn ℝ m (fun y ↦ f (e.symm y)) (e.symm ⁻¹' s) :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ hy ↦ hy)
  have hx' : e x ∈ e.symm ⁻¹' s := by simpa using hx
  obtain ⟨g, hg, hcompact, heq⟩ :=
    hlocal.exists_contDiff_compactSupport_eventuallyEq
      (hs.preimage e.symm.continuous) hx'
  refine ⟨g ∘ e, hg.comp e.contDiff, hcompact.comp_homeomorph e.toHomeomorph, ?_⟩
  have h := heq.comp_tendsto e.continuous.continuousAt
  simpa only [Function.comp_def, e.symm_apply_apply] using h

end
