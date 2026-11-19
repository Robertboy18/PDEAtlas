/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Iterated derivatives along affine slices

Restricting a Taylor series to an affine slice identifies the actual derivatives
of the restriction, even when the slice lies in the boundary of the original
domain. A continuously indexed family of parallel slices therefore has jointly
continuous spatial jets without differentiating its index.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Affine restriction pulls back each iterated derivative by its linear part. -/
theorem ContinuousAffineMap.iteratedFDerivWithin_comp_right
    {n : ℕ∞ω} {f : E → F} {s : Set E} (g : G →ᴬ[𝕜] E)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hgs : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G} (hx : g x ∈ s)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap
        (fun _ ↦ g.contLinear) :=
  ((((hf.of_le hi).ftaylorSeriesWithin hs).comp_continuousAffineMap
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hgs hx).symm

namespace PDE

/-- Parallel affine slices contained in a domain inherit continuous actual jets.
The indexing space needs only a topology. -/
theorem continuous_iteratedFDeriv_affine_family
    {T : Type*} [TopologicalSpace T] {n : ℕ∞ω} {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (g : T → G →ᴬ[𝕜] E) (L : G →L[𝕜] E)
    (hL : ∀ t, (g t).contLinear = L)
    (hg : Continuous (fun p : T × G ↦ g p.1 p.2))
    (hmem : ∀ t x, g t x ∈ s) {i : ℕ} (hi : i ≤ n) :
    Continuous (fun p : T × G ↦ iteratedFDeriv 𝕜 i (f ∘ g p.1) p.2) := by
  have heq (t : T) (x : G) :
      iteratedFDeriv 𝕜 i (f ∘ g t) x =
        (iteratedFDerivWithin 𝕜 i f s (g t x)).compContinuousLinearMap
          (fun _ ↦ L) := by
    have hpre : (g t) ⁻¹' s = univ := eq_univ_of_forall (hmem t)
    simpa only [hpre, iteratedFDerivWithin_univ, hL t] using
      (g t).iteratedFDerivWithin_comp_right hf hs
        (hpre ▸ uniqueDiffOn_univ) (hmem t x) hi
  simp_rw [heq]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin i ↦ L)).continuous.comp
      ((hf.continuousOn_iteratedFDerivWithin hi hs).comp_continuous hg
        (fun p ↦ hmem p.1 p.2))

/-- The actual derivative along an affine line evaluates the spatial jet on
copies of its direction. The direction may be zero. -/
theorem iteratedDeriv_comp_affine_line
    {m : ℕ∞ω} {f : E → F} (hf : ContDiff 𝕜 m f)
    (x e : E) (t : 𝕜) {r : ℕ} (hr : r ≤ m) :
    iteratedDeriv r (fun s ↦ f (x + s • e)) t =
      iteratedFDeriv 𝕜 r f (x + t • e) (fun _ ↦ e) := by
  have h := (ContinuousLinearMap.toSpanSingleton 𝕜 e).iteratedFDeriv_comp_right
    (hf.comp ((contDiff_const (c := x)).add contDiff_id)) t hr
  simpa only [iteratedDeriv, Function.comp_def, id_eq,
    ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left, one_smul] using
    congrArg (fun A ↦ A (fun _ ↦ (1 : 𝕜))) h

end PDE
