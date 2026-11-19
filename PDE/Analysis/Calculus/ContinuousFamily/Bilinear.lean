/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.ContinuousFamily.IteratedDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Bilinear operations on continuous spatial jets

The product rule preserves joint continuity in an arbitrary topological index.
The induction differentiates only in the normed spatial variable.
-/

@[expose] public noncomputable section

universe u uD uE uF uG

variable {𝕜 T : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace T]
  {D : Type u} [NormedAddCommGroup D] [NormedSpace 𝕜 D]

/-- The induction uses a common universe for the spaces and their derivatives. -/
private theorem continuous_iteratedFDeriv_bilinear_family_aux
    {E F G : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G) {f : T → D → E} {g : T → D → F} {k : ℕ}
    (hf : ∀ t, ContDiff 𝕜 k (f t)) (hg : ∀ t, ContDiff 𝕜 k (g t))
    (hfj : ∀ j ≤ k, Continuous
      (fun p : T × D ↦ iteratedFDeriv 𝕜 j (f p.1) p.2))
    (hgj : ∀ j ≤ k, Continuous
      (fun p : T × D ↦ iteratedFDeriv 𝕜 j (g p.1) p.2)) :
    Continuous (fun p : T × D ↦
      iteratedFDeriv 𝕜 k (fun x ↦ B (f p.1 x) (g p.1 x)) p.2) := by
  induction k generalizing E F G with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 𝕜 D G).symm.continuous.comp
      ((B.continuous.comp
        (PDE.continuous_of_continuous_iteratedFDeriv_zero_family (hfj 0 le_rfl))).clm_apply
          (PDE.continuous_of_continuous_iteratedFDeriv_zero_family (hgj 0 le_rfl)))
  | succ k ih =>
    have hfk (t : T) : ContDiff 𝕜 k (f t) := (hf t).of_le (by simp)
    have hgk (t : T) : ContDiff 𝕜 k (g t) := (hg t).of_le (by simp)
    have hfD (t : T) : ContDiff 𝕜 k (fderiv 𝕜 (f t)) :=
      (hf t).fderiv_right (by simp)
    have hgD (t : T) : ContDiff 𝕜 k (fderiv 𝕜 (g t)) :=
      (hg t).fderiv_right (by simp)
    have hfjD (j : ℕ) (hj : j ≤ k) :=
      PDE.continuous_iteratedFDeriv_fderiv_family (hfj (j + 1) (Nat.succ_le_succ hj))
    have hgjD (j : ℕ) (hj : j ≤ k) :=
      PDE.continuous_iteratedFDeriv_fderiv_family (hgj (j + 1) (Nat.succ_le_succ hj))
    have hA := ih (B.precompR D) hfk hgD
      (fun j hj ↦ hfj j (hj.trans (Nat.le_succ k))) hgjD
    have hB := ih (B.precompL D) hfD hgk hfjD
      (fun j hj ↦ hgj j (hj.trans (Nat.le_succ k)))
    have hAc (t : T) : ContDiff 𝕜 k
        (fun x ↦ B.precompR D (f t x) (fderiv 𝕜 (g t) x)) :=
      (B.precompR D).isBoundedBilinearMap.contDiff.comp₂ (hfk t) (hgD t)
    have hBc (t : T) : ContDiff 𝕜 k
        (fun x ↦ B.precompL D (fderiv 𝕜 (f t) x) (g t x)) :=
      (B.precompL D).isBoundedBilinearMap.contDiff.comp₂ (hfD t) (hgk t)
    convert (continuousMultilinearCurryRightEquiv' 𝕜 k D G).symm.continuous.comp
      (hA.add hB) using 1
    ext p
    rw [iteratedFDeriv_succ_eq_comp_right]
    have heq : fderiv 𝕜 (fun x ↦ B (f p.1 x) (g p.1 x)) =
        fun x ↦ B.precompR D (f p.1 x) (fderiv 𝕜 (g p.1) x) +
          B.precompL D (fderiv 𝕜 (f p.1) x) (g p.1 x) := by
      funext x
      exact B.fderiv_of_bilinear
        ((hf p.1).differentiable (by simp) x) ((hg p.1).differentiable (by simp) x)
    simp only [Function.comp_apply, Pi.add_apply, heq,
      fun_iteratedFDeriv_add_apply (hAc p.1).contDiffAt (hBc p.1).contDiffAt]

/-- Bilinear combinations preserve jointly continuous finite spatial jets. -/
theorem ContinuousLinearMap.continuous_iteratedFDeriv_bilinear_family
    {D : Type uD} {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G) {f : T → D → E} {g : T → D → F} {k : ℕ}
    (hf : ∀ t, ContDiff 𝕜 k (f t)) (hg : ∀ t, ContDiff 𝕜 k (g t))
    (hfj : ∀ j ≤ k, Continuous
      (fun p : T × D ↦ iteratedFDeriv 𝕜 j (f p.1) p.2))
    (hgj : ∀ j ≤ k, Continuous
      (fun p : T × D ↦ iteratedFDeriv 𝕜 j (g p.1) p.2)) :
    Continuous (fun p : T × D ↦
      iteratedFDeriv 𝕜 k (fun x ↦ B (f p.1 x) (g p.1 x)) p.2) := by
  -- As in Mathlib's bilinear derivative bounds, lift the spaces to a common universe.
  let Du : Type max uD uE uF uG := ULift.{max uE uF uG, uD} D
  let Eu : Type max uD uE uF uG := ULift.{max uD uF uG, uE} E
  let Fu : Type max uD uE uF uG := ULift.{max uD uE uG, uF} F
  let Gu : Type max uD uE uF uG := ULift.{max uD uE uF, uG} G
  let isoD : Du ≃ₗᵢ[𝕜] D := LinearIsometryEquiv.ulift 𝕜 D
  let isoE : Eu ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.ulift 𝕜 E
  let isoF : Fu ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  let isoG : Gu ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  let fu (t : T) : Du → Eu := isoE.symm ∘ f t ∘ isoD
  let gu (t : T) : Du → Fu := isoF.symm ∘ g t ∘ isoD
  let Bu₀ : Eu →L[𝕜] Fu →L[𝕜] G :=
    ((B.comp (isoE : Eu →L[𝕜] E)).flip.comp (isoF : Fu →L[𝕜] F)).flip
  let Bu : Eu →L[𝕜] Fu →L[𝕜] Gu :=
    ContinuousLinearMap.compL 𝕜 Eu (Fu →L[𝕜] G) (Fu →L[𝕜] Gu)
      (ContinuousLinearMap.compL 𝕜 Fu G Gu (isoG.symm : G →L[𝕜] Gu)) Bu₀
  have hfu (t : T) : ContDiff 𝕜 k (fu t) :=
    isoE.symm.contDiff.comp ((hf t).comp isoD.contDiff)
  have hgu (t : T) : ContDiff 𝕜 k (gu t) :=
    isoF.symm.contDiff.comp ((hg t).comp isoD.contDiff)
  have hfuj (j : ℕ) (hj : j ≤ k) : Continuous
      (fun p : T × Du ↦ iteratedFDeriv 𝕜 j (fu p.1) p.2) :=
    (isoE.symm : E →L[𝕜] Eu).continuous_iteratedFDeriv_comp_family
      (fun t ↦ ((hf t).of_le (by exact_mod_cast hj)).comp isoD.contDiff)
      (PDE.continuous_iteratedFDeriv_comp_linear_family
        (L := fun _ : T ↦ (isoD : Du →L[𝕜] D))
        (fun t ↦ (hf t).of_le (by exact_mod_cast hj)) (hfj j hj) continuous_const)
  have hguj (j : ℕ) (hj : j ≤ k) : Continuous
      (fun p : T × Du ↦ iteratedFDeriv 𝕜 j (gu p.1) p.2) :=
    (isoF.symm : F →L[𝕜] Fu).continuous_iteratedFDeriv_comp_family
      (fun t ↦ ((hg t).of_le (by exact_mod_cast hj)).comp isoD.contDiff)
      (PDE.continuous_iteratedFDeriv_comp_linear_family
        (L := fun _ : T ↦ (isoD : Du →L[𝕜] D))
        (fun t ↦ (hg t).of_le (by exact_mod_cast hj)) (hgj j hj) continuous_const)
  have hproduct := continuous_iteratedFDeriv_bilinear_family_aux Bu hfu hgu hfuj hguj
  have hproduct_diff (t : T) : ContDiff 𝕜 k (fun x ↦ Bu (fu t x) (gu t x)) :=
    Bu.isBoundedBilinearMap.contDiff.comp₂ (hfu t) (hgu t)
  have h := (isoG : Gu →L[𝕜] G).continuous_iteratedFDeriv_comp_family
    (fun t ↦ (hproduct_diff t).comp isoD.symm.contDiff)
    (PDE.continuous_iteratedFDeriv_comp_linear_family
      (L := fun _ : T ↦ (isoD.symm : D →L[𝕜] Du)) hproduct_diff hproduct continuous_const)
  simpa only [Function.comp_def, Bu, Bu₀, fu, gu, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply] using h
