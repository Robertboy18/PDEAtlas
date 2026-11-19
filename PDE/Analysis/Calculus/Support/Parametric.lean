/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Support of spatial slices and their derivatives

The parameter need not be a vector: only the spatial variable is differentiated.
Locality of the Fréchet derivative preserves the joint support, so compactness
and uniform bounds can be reused for parameter-dependent PDE data.
-/

@[expose] public section

open Function Set Filter Topology

variable {T 𝕜 E F : Type*} [TopologicalSpace T] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace PDE

/-- Differentiating a spatial slice does not enlarge joint support, even when the
parameter space has no vector space structure. -/
theorem tsupport_fderiv_snd_subset (f : T × E → F) :
    tsupport (fun p : T × E ↦ fderiv 𝕜 (fun x ↦ f (p.1, x)) p.2) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro p hp
  by_contra h
  have hf : f =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp h
  have hslice : (fun x ↦ f (p.1, x)) =ᶠ[𝓝 p.2] 0 :=
    hf.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto p.2)
  exact hp (by simpa using hslice.fderiv_eq (𝕜 := 𝕜))

end PDE

/-- A compactly supported family has compactly supported spatial derivatives
jointly in its parameter and spatial variables. -/
protected theorem HasCompactSupport.fderiv_snd {f : T × E → F}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : T × E ↦ fderiv 𝕜 (fun x ↦ f (p.1, x)) p.2) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (PDE.tsupport_fderiv_snd_subset f)

/-- A fixed spatial direction preserves compact support of the whole parameter family. -/
protected theorem HasCompactSupport.fderiv_snd_apply {f : T × E → F}
    (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fun p : T × E ↦ fderiv 𝕜 (fun x ↦ f (p.1, x)) p.2 v) :=
  (hf.fderiv_snd (𝕜 := 𝕜)).comp_left (g := fun L : E →L[𝕜] F ↦ L v) (by simp)

/-- Fixing a parameter leaves a compactly supported spatial slice. -/
protected theorem HasCompactSupport.slice_snd {f : T × E → F}
    (hf : HasCompactSupport f) (t : T) :
    HasCompactSupport (fun x : E ↦ f (t, x)) := by
  refine HasCompactSupport.intro (hf.isCompact.image continuous_snd) ?_
  intro x hx
  by_contra hne
  exact hx ⟨(t, x), subset_closure hne, rfl⟩
