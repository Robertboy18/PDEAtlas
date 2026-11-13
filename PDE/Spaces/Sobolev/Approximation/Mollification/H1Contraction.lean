/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.ProductH1
public import PDE.Spaces.Sobolev.Approximation.SpatialTestDensity

/-!
# Uniform H¹ bounds for spatial mollification

Mollification is a contraction on H¹, uniformly over every positive scale. Its weak
spatial derivatives are mollifications of the original derivative rows, so the L²
contraction applies to every graph coordinate. The same argument applies to any finite
component product, including an empty product.

The product convergence theorem reuses the scalar H¹ approximate identity. These bounds
allow dominated convergence with moving H¹ tests, without using the scale-dependent
operator bound from L² into H¹.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n : ℕ}

/-- Applying the L²-to-H¹ mollifier to the base of an H¹ function does not
increase its H¹ norm. The bound is independent of the positive scale. -/
theorem norm_mollifierH1CLM_base_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : W^{1,2}(ℝ^n)) :
    ‖mollifierH1CLM μ hε (wkpCoordinateCLM (baseIndex n 1) U)‖ ≤ ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(mollifierH1CLM μ hε (wkpCoordinateCLM (baseIndex n 1) U) :
    WkpAmbientOn n 1 2 univ)‖ ^ 2 ≤ ‖(U : WkpAmbientOn n 1 2 univ)‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro d _
  change ‖wkpCoordinateCLM d
    (mollifierH1CLM μ hε (wkpCoordinateCLM (baseIndex n 1) U))‖ ^ 2 ≤
    ‖wkpCoordinateCLM d U‖ ^ 2
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  rcases d.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨j, rfl⟩
  · rw [mollifierH1CLM_base]
    exact norm_mollifierRowCLM_apply_le μ hε _
  · rw [mollifierH1CLM_derivative, mollifierDerivativeRowCLM_base]
    exact norm_mollifierRowCLM_apply_le μ hε _

/-- Componentwise spatial mollification is a contraction on the finite product H¹
norm. Each input component is supplied through its base coordinate. -/
theorem norm_mollifierProductH1CLM_base_le {ι : Type*} [Fintype ι]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (U : PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n))) :
    ‖mollifierProductH1CLM μ hε
      (WithLp.toLp 2 (fun p ↦ wkpCoordinateCLM (baseIndex n 1) (U p)))‖ ≤ ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro p _
  change ‖mollifierH1CLM μ hε (wkpCoordinateCLM (baseIndex n 1) (U p))‖ ^ 2 ≤ ‖U p‖ ^ 2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_mollifierH1CLM_base_le μ hε (U p))

/-- The componentwise mollifiers of the base coordinates converge to the original
finite H¹ product as their positive scales tend to zero. -/
theorem tendsto_mollifierProductH1CLM_base {ι : Type*} [Finite ι]
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (U : PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n))) :
    Tendsto (fun k ↦ mollifierProductH1CLM μ (hε k)
      (WithLp.toLp 2 (fun p ↦ wkpCoordinateCLM (baseIndex n 1) (U p))))
        atTop (𝓝 U) := by
  let : Fintype ι := Fintype.ofFinite ι
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ W^{1,2}(ℝ^n))
  have hcoords : Tendsto (fun k p ↦ mollifierH1CLM μ (hε k)
      (wkpCoordinateCLM (baseIndex n 1) (U p))) atTop (𝓝 (fun p ↦ U p)) :=
    tendsto_pi_nhds.mpr fun p ↦ tendsto_mollifierH1CLM_base μ ε hε hε0 (U p)
  exact e.symm.continuous.continuousAt.tendsto.comp hcoords

end SobolevSpace.Approximation
