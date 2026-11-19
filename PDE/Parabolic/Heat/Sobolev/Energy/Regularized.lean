/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Construction.Regularization
public import PDE.Spaces.Sobolev.Approximation.Mollification.HilbertPairing

/-!
# Scale-independent energy estimates for mollified heat evolution

The physical diffusivity `ε` is positive and fixed. The estimates do not depend
on the smoothing scale `δ`. Forcing is measured in L², using integration by parts
to absorb its spatial derivative into the dissipated Hessian energy.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ}

/-- The bounded heat regularization is dissipative in H¹. -/
theorem inner_regularizedLaplacianCLM_one_nonpos {δ : ℝ} (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) :
    ⟪U, regularizedLaplacianCLM 1 hδ U⟫_ℝ ≤ 0 := by
  rw [inner_regularizedLaplacianCLM]
  exact neg_nonpos.mpr
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Pairing the smoothed L² forcing against an arbitrary H¹ state costs only
its L² norm and an absorbable part of the ordered Hessian energy. -/
theorem two_inner_mollifierSmoothingCLM_one_le
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) (F : DerivLp n 2 Set.univ) :
    2 * ⟪U, mollifierSmoothingCLM 1 (standardMollifier n) hδ F⟫_ℝ ≤
      ‖U‖ ^ 2 + (1 + (n : ℝ) / ε) * ‖F‖ ^ 2 +
        ε * ∑ i : Fin n, ∑ j : Fin n,
          ‖(mollifierSmoothingCLM 2 (standardMollifier n) hδ
              (wkpBaseCoordinateCLM U) : WkpAmbientOn n 2 2 Set.univ)
            (pairDerivIndex n i j)‖ ^ 2 := by
  classical
  let V := mollifierSmoothingCLM 2 (standardMollifier n) hδ
    (wkpBaseCoordinateCLM U)
  have hb : ‖wkpBaseCoordinateCLM V‖ ≤ ‖U‖ := by
    rw [mollifierSmoothingCLM_base]
    exact (norm_mollifierRowCLM_apply_le _ _ _).trans (wkpBaseCoordinateCLM_norm_le U)
  have hbpair :
      2 * ⟪wkpBaseCoordinateCLM V, F⟫_ℝ ≤ ‖U‖ ^ 2 + ‖F‖ ^ 2 := by
    have hnorm := real_inner_le_norm (wkpBaseCoordinateCLM V) F
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb
    nlinarith [sq_nonneg (‖wkpBaseCoordinateCLM V‖ - ‖F‖)]
  have hdiag (i : Fin n) :
      -2 * ⟪V.val (pairDerivIndex n i i), F⟫_ℝ ≤
        ε * ‖V.val (pairDerivIndex n i i)‖ ^ 2 + ε⁻¹ * ‖F‖ ^ 2 := by
    have hi := real_inner_le_norm (-V.val (pairDerivIndex n i i)) F
    rw [inner_neg_left, norm_neg] at hi
    have hy := two_mul_le_add_mul_sq
      (a := ‖V.val (pairDerivIndex n i i)‖) (b := ‖F‖) hε
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hdiag i
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hdiagfull :
      (∑ i : Fin n, ‖V.val (pairDerivIndex n i i)‖ ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, ‖V.val (pairDerivIndex n i j)‖ ^ 2 := by
    exact Finset.sum_le_sum fun i _ ↦
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg ‖V.val (pairDerivIndex n i j)‖) (Finset.mem_univ i)
  rw [inner_mollifierSmoothingCLM_one]
  change 2 * ⟪identitySubLaplacianCLM n V, F⟫_ℝ ≤ _
  have heval : identitySubLaplacianCLM n V =
      wkpBaseCoordinateCLM V - ∑ i : Fin n, V.val (pairDerivIndex n i i) := by
    simp [identitySubLaplacianCLM, sub_apply, sum_apply]
  rw [heval, inner_sub_left, sum_inner]
  change _ ≤ ‖U‖ ^ 2 + (1 + (n : ℝ) / ε) * ‖F‖ ^ 2 +
    ε * ∑ i : Fin n, ∑ j : Fin n, ‖V.val (pairDerivIndex n i j)‖ ^ 2
  rw [div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_left hdiagfull hε.le]

/-- The regularized heat equation has an H¹ energy inequality with an L²
forcing budget and an explicit positive diffusion dissipation. -/
theorem regularized_heat_energy_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) (F : DerivLp n 2 Set.univ) :
    2 * ⟪U, ε • regularizedLaplacianCLM 1 hδ U +
        mollifierSmoothingCLM 1 (standardMollifier n) hδ F⟫_ℝ -
        ε * ⟪U, regularizedLaplacianCLM 1 hδ U⟫_ℝ ≤
      ‖U‖ ^ 2 + (1 + (n : ℝ) / ε) * ‖F‖ ^ 2 := by
  have hf := two_inner_mollifierSmoothingCLM_one_le hε hδ U F
  rw [inner_add_right,
    real_inner_smul_right U (regularizedLaplacianCLM 1 hδ U) ε]
  rw [inner_regularizedLaplacianCLM_one]
  have hg : 0 ≤ ∑ i : Fin n,
      ‖(mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U) : WkpAmbientOn n 2 2 Set.univ)
        (firstDerivIndex n 2 (by omega) i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith [mul_nonneg hε.le hg]

/-- Discarding dissipation gives the scale-independent differential bound. -/
theorem two_inner_regularized_heat_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) (F : DerivLp n 2 Set.univ) :
    2 * ⟪U, ε • regularizedLaplacianCLM 1 hδ U +
        mollifierSmoothingCLM 1 (standardMollifier n) hδ F⟫_ℝ ≤
      ‖U‖ ^ 2 + (1 + (n : ℝ) / ε) * ‖F‖ ^ 2 := by
  have h := regularized_heat_energy_le hε hδ U F
  have hd := inner_regularizedLaplacianCLM_one_nonpos hδ U
  nlinarith

end PDE.Parabolic.Heat
