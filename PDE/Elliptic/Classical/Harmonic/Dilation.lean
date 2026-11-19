/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Analysis.Calculus.Laplacian.Dilation
public import PDE.FDeriv.PartialDeriv.DilationFamily

/-!
# Dilation of harmonic functions

Harmonicity is preserved on the preimage of a domain under scalar multiplication. No extension
of the harmonic function across its boundary is used.
-/

@[expose] public section

namespace LaplacianEquation

/-- A dilated harmonic function is harmonic on the preimage of its domain. -/
theorem IsHarmonicPDE.comp_const_smul
    {n : ℕ} {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (c : ℝ) :
    IsHarmonicPDE n (fun y ↦ u (c • y)) ((fun y : ℝ^n ↦ c • y) ⁻¹' U) := by
  have hsmul : ContDiffOn ℝ 2 (fun y : ℝ^n ↦ c • y)
      ((fun y : ℝ^n ↦ c • y) ⁻¹' U) := by
    exact (c • ContinuousLinearMap.id ℝ (ℝ^n)).contDiff.contDiffOn
  have hreg : ContDiffOn ℝ 2 (fun y ↦ u (c • y)) ((fun y : ℝ^n ↦ c • y) ⁻¹' U) :=
    hu.contDiffOn.comp hsmul (fun _ hx ↦ hx)
  refine ⟨hreg, ?_⟩
  intro x hx
  rw [PDE.laplacian_comp_smul u c x, hu.laplacian_eq_zero hx, smul_zero]

end LaplacianEquation
