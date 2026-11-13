/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Energy
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.WholeSpace

/-!
# Spatial energy of diffusion and matrix transport

The weak Laplacian dissipates the H¹ energy, including the full
ordered Hessian. The symmetric transport and forcing terms have bounds
independent of the diffusion coefficient.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

variable {n m : ℕ}

/-- The H¹ energy inequality for the full diffusion-transport right-hand
side. The coefficient bound is purely spatial; no solution estimate is assumed. -/
theorem transport_diffusion_spatial_energy_le (ε : ℝ)
    (A : Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ j p q, wkpBaseCoordinateCLM (A j p q) = wkpBaseCoordinateCLM (A j q p))
    (K : ℝ)
    (hK : transportDerivativeSum A ≤ K)
    (U : Fin m → W^{3,2}(ℝ^n)) (F : Fin m → W^{1,2}(ℝ^n)) :
    2 * (∑ p, ⟪lowerOrderCLM (by decide : 1 ≤ 3) (U p),
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p) + F p +
        vectorTransportH1CLM isOpen_univ A
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U q)) p⟫_ℝ) -
      2 * ε * (∑ p, ⟪lowerOrderCLM (by decide : 1 ≤ 3) (U p),
        higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p)⟫_ℝ) ≤
    (K + 1) * (∑ p, ‖lowerOrderCLM (by decide : 1 ≤ 3) (U p)‖ ^ 2) +
      ∑ p, ‖F p‖ ^ 2 := by
  let W (p : Fin m) := lowerOrderCLM (by decide : 1 ≤ 3) (U p)
  let V (p : Fin m) := lowerOrderCLM (by decide : 2 ≤ 3) (U p)
  have hT := vectorTransportH1CLM_energy_le A hA V
  simp only [V, lowerOrderCLM_trans_apply] at hT
  have hT' : 2 * (∑ p, ⟪W p, vectorTransportH1CLM isOpen_univ A V p⟫_ℝ) ≤
      K * ∑ p, ‖W p‖ ^ 2 := by
    have hc : (∑ p, ⟪W p, vectorTransportH1CLM isOpen_univ A V p⟫_ℝ) =
        ∑ p, ⟪vectorTransportH1CLM isOpen_univ A V p, W p⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro p _
      exact real_inner_comm _ _
    rw [hc]
    exact hT.trans (mul_le_mul_of_nonneg_right hK
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  have hF : 2 * (∑ p, ⟪W p, F p⟫_ℝ) ≤ (∑ p, ‖W p‖ ^ 2) + ∑ p, ‖F p‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _
    have h := real_inner_le_norm (W p) (F p)
    nlinarith [sq_nonneg (‖W p‖ - ‖F p‖)]
  change 2 * (∑ p, ⟪W p,
    ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p) + F p +
      vectorTransportH1CLM isOpen_univ A V p⟫_ℝ) -
    2 * ε * (∑ p, ⟪W p, higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p)⟫_ℝ) ≤
    (K + 1) * (∑ p, ‖W p‖ ^ 2) + ∑ p, ‖F p‖ ^ 2
  have hs (p : Fin m) :
      ⟪W p, ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p)⟫_ℝ =
        ε * ⟪W p, higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p)⟫_ℝ :=
    real_inner_smul_right (W p) (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p)) ε
  simp only [inner_add_right, hs, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith only [hT', hF]

/-- The H¹ Laplacian dissipation of every finite family is nonnegative,
including in zero spatial or target dimension. -/
theorem neg_sum_inner_hOne_laplacian_nonneg (U : Fin m → W^{3,2}(ℝ^n)) :
    0 ≤ -(∑ p, ⟪lowerOrderCLM (by decide : 1 ≤ 3) (U p),
      higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p)⟫_ℝ) := by
  simp only [inner_hOne_laplacian_eq_neg_gradient_hessian, Finset.sum_neg_distrib, neg_neg]
  exact Finset.sum_nonneg fun _ _ ↦ add_nonneg
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

end PDE.Parabolic.Systems
