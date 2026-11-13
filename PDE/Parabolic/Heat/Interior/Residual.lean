/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Localization
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.Calculus.SpaceTime.Regularity

/-!
# Continuity and localization of the cutoff heat residual

The residual of a spatially localized classical heat field is continuous
and supported in the cutoff annulus. Both conclusions follow from its
derivatives and the heat equation; no source regularity or support is assumed.
-/

@[expose] public section

open PDE (partialDeriv laplacian)

open Filter Metric Set
open scoped Topology

namespace HeatEquation

variable {n : ℕ}

/-- Continuous spatial and temporal derivative fields give a continuous
heat residual after spatial localization, on the original arbitrary time set. -/
theorem continuousOn_spatialCutoff_heatResidual
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ} {χ : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hu : ContinuousOn u.uncurry (Ω ×ˢ I))
    (hDx : ContinuousOn Dx (Ω ×ˢ I)) (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hDt : ContinuousOn Dt (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (hχ : ContDiff ℝ 2 χ) (hχΩ : tsupport χ ⊆ Ω) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      χ p.1 * Dt p - laplacian (fun y ↦ χ y * u y p.2) p.1) (univ ×ˢ I) := by
  have hD : ContinuousOn (fun p : ℝ^n × ℝ ↦ χ p.1 * Dt p) (univ ×ˢ I) := by
    simpa only [smul_eq_mul] using
      PDE.Analysis.continuousOn_spatial_cutoff_smul hΩ hχ.continuous hχΩ hDt
  have hL : ContinuousOn (fun p : ℝ^n × ℝ ↦
      laplacian (fun y ↦ χ y * u y p.2) p.1) (univ ×ˢ I) :=
    PDE.FDeriv.continuousOn_laplacian_spatial_cutoff hΩ hχ hχΩ hu
      (PDE.continuousOn_partialDeriv_spatial_of_hasFDerivAt hDx hspace)
      (PDE.continuousOn_laplacian_spatial_of_hasFDerivAt hΩ hDxx hspace hhessian)
      (fun _ ht ↦
        PDE.Analysis.contDiffOn_two_slice_of_space_derivatives hΩ hDxx hspace hhessian ht)
  exact hD.sub hL

/-- Adding a `C¹` time cutoff preserves continuity of the localized
residual, including both endpoints of any original time set. -/
theorem continuousOn_spaceTimeCutoff_heatResidual
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ} {χ : ℝ^n → ℝ} {η : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hu : ContinuousOn u.uncurry (Ω ×ˢ I))
    (hDx : ContinuousOn Dx (Ω ×ˢ I)) (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hDt : ContinuousOn Dt (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ I,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (hχ : ContDiff ℝ 2 χ) (hχΩ : tsupport χ ⊆ Ω) (hη : ContDiff ℝ 1 η) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      deriv η p.2 * (χ p.1 * u p.1 p.2) +
        η p.2 * (χ p.1 * Dt p - laplacian (fun y ↦ χ y * u y p.2) p.1))
      (univ ×ˢ I) := by
  have hχu : ContinuousOn (fun p : ℝ^n × ℝ ↦ χ p.1 * u p.1 p.2) (univ ×ˢ I) := by
    simpa only [smul_eq_mul, Function.uncurry_def] using
      PDE.Analysis.continuousOn_spatial_cutoff_smul hΩ hχ.continuous hχΩ hu
  exact ((hη.continuous_deriv_one.comp continuous_snd).continuousOn.mul hχu).add
    ((hη.continuous.comp continuous_snd).continuousOn.mul
      (continuousOn_spatialCutoff_heatResidual hΩ hu hDx hDxx hDt hspace hhessian hχ hχΩ))

/-- Outside the closed spatial support of a cutoff, its heat residual
is zero. No regularity of the unlocalized field is needed at that point. -/
theorem spatialCutoff_heatResidual_eq_zero_of_notMem_tsupport
    {u χ : ℝ^n → ℝ} (D : ℝ) {x : ℝ^n} (hx : x ∉ tsupport χ) :
    χ x * D - laplacian (fun y ↦ χ y * u y) x = 0 := by
  have heq : (fun y ↦ χ y * u y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hL : laplacian (fun y ↦ χ y * u y) x = 0 := by
    simpa [laplacian, partialDeriv] using
      EuclideanLaplacian.laplacian_congr_nhds heq
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, hL, sub_self]

/-- The residual of a localized heat solution vanishes outside the
cutoff annulus. Its inner radius is positive, so the source stays away from
the center. -/
theorem spatialCutoff_heatResidual_support
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dt : ℝ^n × ℝ → ℝ} {x : ℝ^n} (χ : ContDiffBump x)
    (hχΩ : tsupport χ ⊆ Ω)
    (hheat : ∀ p ∈ Ω ×ˢ I, Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0)
    {s : ℝ} (hs : s ∈ I) {y : ℝ^n}
    (hy : y ∉ tsupport χ \ ball x (χ.rIn / 2)) :
    χ y * Dt (y, s) - laplacian (fun z ↦ χ z * u z s) y = 0 := by
  by_cases hys : y ∈ tsupport χ
  · have hyball : y ∈ ball x (χ.rIn / 2) := by
      by_contra h
      exact hy ⟨hys, h⟩
    apply spatialCutoff_heatResidual_eq_zero
      (χ.eventuallyEq_one_of_mem_ball
        (ball_subset_ball (half_le_self χ.rIn_pos.le) hyball))
    exact hheat (y, s) ⟨hχΩ hys, hs⟩
  · exact spatialCutoff_heatResidual_eq_zero_of_notMem_tsupport (Dt (y, s)) hys

end HeatEquation
