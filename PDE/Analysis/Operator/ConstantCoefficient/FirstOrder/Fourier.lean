/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier transformation of compactly supported first-order systems

The spatial derivatives of a compactly supported `C¹` field transform
into the full signed symbol. Integrability is derived from compact support,
and integration by parts is Mathlib's Fourier derivative theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis

variable {V E F ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Fintype ι]

/-- The Fourier transform of the full constant first-order operator on a
compactly supported `C¹` field, with the native `2π` normalization. -/
theorem fourier_firstOrder_of_contDiff_hasCompactSupport
    (v : ι → V) (A : ι → E →L[ℂ] F) {u : V → E}
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) (ξ : V) :
    𝓕 (fun x ↦ ∑ j, A j (fderiv ℝ u x (v j))) ξ =
      (2 * Real.pi * Complex.I) • ∑ j, ⟪v j, ξ⟫ • A j (𝓕 u ξ) := by
  have hui : Integrable u := hu.continuous.integrable_of_hasCompactSupport hs
  have hdi : Integrable (fderiv ℝ u) :=
    (hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hs.fderiv ℝ)
  have hAi (j : ι) : Integrable (fun x ↦ A j (fderiv ℝ u x (v j))) :=
    (A j).integrable_comp (hdi.apply_continuousLinearMap (v j))
  have hj (j : ι) :
      𝓕 (fun x ↦ A j (fderiv ℝ u x (v j))) ξ =
        (2 * Real.pi * Complex.I) • ⟪v j, ξ⟫ • A j (𝓕 u ξ) := by
    have hmap :
        𝓕 (fun x ↦ A j (fderiv ℝ u x (v j))) ξ =
          A j (𝓕 (fun x ↦ fderiv ℝ u x (v j)) ξ) := by
      simp only [Real.fourier_eq, Circle.smul_def]
      simp_rw [← map_smul]
      have hi := (Real.fourierIntegral_convergent_iff
        (f := fun x ↦ fderiv ℝ u x (v j)) ξ).2
          (hdi.apply_continuousLinearMap (v j))
      exact (A j).integral_comp_comm
        (by simpa only [Circle.smul_def] using hi)
    rw [hmap, ← Real.fourier_continuousLinearMap_apply hdi,
      Real.fourier_fderiv hui (hu.differentiable one_ne_zero) hdi]
    simp only [VectorFourier.fourierSMulRight_apply, neg_apply,
      innerSL_apply_apply ℝ, neg_smul, smul_neg, neg_neg, map_smul,
      ContinuousLinearMap.map_smul_of_tower, real_inner_comm ξ (v j)]
  calc
    _ = ∑ j, 𝓕 (fun x ↦ A j (fderiv ℝ u x (v j))) ξ := by
      simp only [Real.fourier_eq, Finset.smul_sum]
      exact integral_finsetSum _ (fun j _ ↦
        (Real.fourierIntegral_convergent_iff ξ).2 (hAi j))
    _ = _ := by simp only [hj, Finset.smul_sum]

end PDE.Analysis
