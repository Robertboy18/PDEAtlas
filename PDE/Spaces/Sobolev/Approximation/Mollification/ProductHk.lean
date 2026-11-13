/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.HigherOrderOperator
public import PDE.Analysis.Normed.Operator.FiniteProduct

/-!
# Mollification in finite Sobolev Hilbert products

Coordinatewise graph mollification contracts the exact finite-Hilbert
Sobolev norm. Its base coordinates are the literal scaled-kernel
convolutions on one common exceptional set, including an empty product.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory GraphSpace
open scoped ENNReal Sobolev

/-- Real scalar multiplication on finite products of Sobolev graphs. -/
local instance mollifierProductHkNormedSpace {n k : ℕ} {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (PiLp 2 (fun _ : ι ↦ W^{k,2}(ℝ^n))) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι ↦ W^{k,2}(ℝ^n))

variable {n k : ℕ} {ι : Type*}

/-- Componentwise mollification is contractive in the finite-Hilbert Hᵏ norm. -/
theorem norm_piLpMap_mollifierHkCLM_le [Fintype ι]
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (u : PiLp 2 (fun _ : ι ↦ W^{k,2}(ℝ^n))) :
    ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι ↦ mollifierHkCLM μ hδ) u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, ContinuousLinearMap.piLpMap_apply]
  exact Finset.sum_le_sum fun i _ ↦
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_mollifierHkCLM_apply_le μ hδ (u i))

/-- All components of a countable family of mollified graphs represent the
convolutions of their Sobolev base functions on a common almost-everywhere set. -/
theorem piLpMap_mollifierHkCLM_base_ae [Countable ι]
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (u : PiLp 2 (fun _ : ι ↦ W^{k,2}(ℝ^n))) :
    ∀ᵐ x ∂volume, ∀ i,
      wkpBaseCoordinateCLM
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι ↦ mollifierHkCLM μ hδ) u i) x =
      mollify μ δ (wkpBaseCoordinateCLM (u i)) x := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [mollifierHkCLM_base_ae μ hδ (u i)] with x hx
  simpa only [ContinuousLinearMap.piLpMap_apply, baseRepresentative,
    wkpBaseCoordinateCLM_apply, domainMeasure, Measure.restrict_univ] using hx

end SobolevSpace.Approximation
