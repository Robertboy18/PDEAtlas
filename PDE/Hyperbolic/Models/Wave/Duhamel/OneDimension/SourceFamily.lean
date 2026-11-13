/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SpaceTime.ForwardSpatialJet
public import PDE.Hyperbolic.Models.Wave.DAlembert.ClassicalSolution
public import PDE.Hyperbolic.Models.Wave.DAlembert.ContinuousFamily

/-!
# D'Alembert waves of forward forcing slices

Each spatial slice of a forward `C¹` source is the initial velocity of a
homogeneous wave with zero displacement. The characteristic integral gains
one derivative, giving a `C²` wave and continuous jets through order two.
Clipping the source index lets us include time zero without differentiating
the clipped source in time.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- A forward source slice is `C¹` in the scalar coordinate used by d'Alembert's formula. -/
theorem contDiff_dAlembert_forward_velocity
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) (s : ℝ) :
    ContDiff ℝ 1 (fun r : ℝ ↦
      f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) r))) := by
  let L : ℝ →L[ℝ] ℝ^1 := ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 1)
  have hL (r : ℝ) : L r = EuclideanSpace.single 0 r := by
    ext i
    fin_cases i
    simp [L]
  simpa [Function.comp_def, hL] using
    (hf.contDiff_forward_spatialSlice (n := 1) (le_max_left 0 s)).comp L.contDiff

/-- The homogeneous wave of a forward `C¹` source slice is jointly `C²` in space and age. -/
theorem contDiff_two_dAlembertSolution1D_forward
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) (s : ℝ) :
    ContDiff ℝ 2 (dAlembertSolution1D (fun _ ↦ 0) (fun x ↦ f (timeSpaceCons (max 0 s) x))) :=
  contDiff_two_dAlembertSolution1D _ _ contDiff_const (contDiff_dAlembert_forward_velocity hf s)

/-- Two wave jets vary continuously with the source index using only one source derivative. -/
theorem continuous_iteratedFDeriv_dAlembertSolution1D_forward
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun p : ℝ × ℝ^2 ↦ iteratedFDeriv ℝ j (dAlembertSolution1D (fun _ ↦ 0)
      (fun x ↦ f (timeSpaceCons (max 0 p.1) x))) p.2) := by
  let h (s r : ℝ) := f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) r))
  let L : ℝ →L[ℝ] ℝ^1 := ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 1)
  have hL (r : ℝ) : L r = EuclideanSpace.single 0 r := by
    ext i
    fin_cases i
    simp [L]
  have hjet (i : ℕ) (hi : i ≤ 1) :
      Continuous (fun p : ℝ × ℝ ↦ iteratedFDeriv ℝ i (h p.1) p.2) := by
    simpa only [Function.comp_def, hL] using (PDE.continuous_iteratedFDeriv_comp_linear_family
        (f := fun s x ↦ f (timeSpaceCons (max 0 s) x)) (L := fun _ ↦ L)
        (fun s ↦ (hf.contDiff_forward_spatialSlice (n := 1)
          (le_max_left 0 s)).of_le (by exact_mod_cast hi))
        (hf.continuous_iteratedFDeriv_forward_spatialSlice (n := 1)
          (by exact_mod_cast hi)) continuous_const)
  have hcont : Continuous (fun p : ℝ × ℝ ↦ h p.1 p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family (hjet 0 (by omega))
  have hD : Continuous (fun p : ℝ × ℝ ↦ fderiv ℝ (h p.1) p.2) :=
    PDE.continuous_of_continuous_iteratedFDeriv_zero_family (f := fun s ↦ fderiv ℝ (h s))
      (PDE.continuous_iteratedFDeriv_fderiv_family (f := h) (j := 0) (hjet 1 le_rfl))
  exact continuous_iteratedFDeriv_dAlembert_zero_displacement_family
    (fun s ↦ contDiff_dAlembert_forward_velocity hf s) hcont (hD.clm_apply continuous_const) hj

end WaveEquation
