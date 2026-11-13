/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual derivatives of continuously indexed families

The indexing space needs only a topology. Currying and continuous linear
composition preserve joint continuity of the actual spatial jets.
-/

@[expose] public noncomputable section

variable {𝕜 T E F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A continuous family has a continuous zeroth spatial jet. -/
theorem Continuous.iteratedFDeriv_zero_family
    {f : T → E → F} (hf : Continuous (fun p : T × E ↦ f p.1 p.2)) :
    Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 0 (f p.1) p.2) := by
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
    (continuousMultilinearCurryFin0 𝕜 E F).symm.continuous.comp hf

namespace PDE

/-- Continuity of the zeroth spatial jet is continuity of the family itself. -/
theorem continuous_of_continuous_iteratedFDeriv_zero_family
    {f : T → E → F}
    (hf : Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 0 (f p.1) p.2)) :
    Continuous (fun p : T × E ↦ f p.1 p.2) := by
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using
    (continuousMultilinearCurryFin0 𝕜 E F).continuous.comp hf

/-- A continuous jet of the derivative gives the next continuous jet of the family. -/
theorem continuous_iteratedFDeriv_succ_family
    {f : T → E → F} {j : ℕ}
    (hf : Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 j (fderiv 𝕜 (f p.1)) p.2)) :
    Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 (j + 1) (f p.1) p.2) := by
  simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def] using
    (continuousMultilinearCurryRightEquiv' 𝕜 j E F).symm.continuous.comp hf

/-- Removing one spatial derivative preserves joint continuity of the remaining jets. -/
theorem continuous_iteratedFDeriv_fderiv_family
    {f : T → E → F} {j : ℕ}
    (hf : Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 (j + 1) (f p.1) p.2)) :
    Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 j (fderiv 𝕜 (f p.1)) p.2) := by
  simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using
    (continuousMultilinearCurryRightEquiv' 𝕜 j E F).continuous.comp hf

/-- A fixed linear map on the values preserves continuous spatial jets. -/
theorem _root_.ContinuousLinearMap.continuous_iteratedFDeriv_comp_family
    (L : F →L[𝕜] G) {f : T → E → F} {j : ℕ}
    (hf : ∀ t, ContDiff 𝕜 j (f t))
    (hjet : Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 j (f p.1) p.2)) :
    Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 j (L ∘ f p.1) p.2) := by
  simp_rw [L.iteratedFDeriv_comp_left (hf _).contDiffAt le_rfl]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL
    𝕜 (fun _ : Fin j ↦ E) F G L).continuous.comp hjet

/-- A fixed directional derivative removes one order from a continuous jet family. -/
theorem continuous_iteratedFDeriv_fderiv_apply_family
    {f : T → E → F} {j : ℕ} (hf : ∀ t, ContDiff 𝕜 (j + 1) (f t))
    (hjet : Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 (j + 1) (f p.1) p.2))
    (v : E) :
    Continuous (fun p : T × E ↦
      iteratedFDeriv 𝕜 j (fun x ↦ fderiv 𝕜 (f p.1) x v) p.2) := by
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
    (ContinuousLinearMap.apply 𝕜 F v).continuous_iteratedFDeriv_comp_family
      (fun t ↦ (hf t).fderiv_right (by simp))
      (continuous_iteratedFDeriv_fderiv_family hjet)

/-- A continuously varying linear spatial substitution preserves continuous jets. -/
theorem continuous_iteratedFDeriv_comp_linear_family
    {f : T → E → F} {L : T → G →L[𝕜] E} {j : ℕ}
    (hf : ∀ t, ContDiff 𝕜 j (f t))
    (hjet : Continuous (fun p : T × E ↦ iteratedFDeriv 𝕜 j (f p.1) p.2))
    (hL : Continuous L) :
    Continuous (fun p : T × G ↦ iteratedFDeriv 𝕜 j (f p.1 ∘ L p.1) p.2) := by
  simp_rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (hf _) _ le_rfl]
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : Fin j ↦ G) (fun _ : Fin j ↦ E) F).cont.comp
      (continuous_pi (fun _ ↦ hL.comp continuous_fst))).clm_apply
        (hjet.comp (continuous_fst.prodMk
          ((hL.comp continuous_fst).clm_apply continuous_snd)))

end PDE
