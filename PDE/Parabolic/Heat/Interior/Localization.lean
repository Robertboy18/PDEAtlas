/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Representation.CompactSupport
public import PDE.FDeriv.SpaceTime.Localization
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.Calculus.SpaceTime.Regularity

/-!
# Localizing a classical heat field

Duhamel's identity applies to a spatial cutoff of a local `C^{2,1}`
field. Its global spatial regularity, continuous Laplacian, time
derivative, and compact support are derived from the local derivative fields.
The identity is valid at the closed terminal time.
-/

@[expose] public section

open PDE (laplacian)

open Filter MeasureTheory Set
open scoped Topology Interval

namespace HeatEquation

variable {n : ℕ}

/-- Duhamel's identity for a spatial cutoff of a local `C^{2,1}` field.
There is no global regularity or growth assumption on the unlocalized field. -/
theorem spatialCutoff_eq_initialValueSolution_add_integral
    {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ} {χ : ℝ^n → ℝ}
    (hab : a ≤ b) (hΩ : IsOpen Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Icc a b))
    (hDx : ContinuousOn Dx (Ω ×ˢ Icc a b))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Icc a b))
    (hDt : ContinuousOn Dt (Ω ×ˢ Icc a b))
    (hspace : ∀ p ∈ Ω ×ˢ Icc a b,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Icc a b,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Icc a b,
      HasDerivWithinAt (u p.1) (Dt p) (Icc a b) p.2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (x : ℝ^n) :
    χ x * u x b =
      initialValueSolution (fun y ↦ χ y * u y a) x (b - a) +
        ∫ s in a..b,
          initialValueSolution (fun y ↦
            χ y * Dt (y, s) - laplacian (fun z ↦ χ z * u z s) y) x (b - s) := by
  have hslices (s : ℝ) (hs : s ∈ Icc a b) :
      ContDiffOn ℝ 2 (fun y ↦ u y s) Ω :=
    PDE.Analysis.contDiffOn_two_slice_of_space_derivatives hΩ hDxx hspace hhessian hs
  have hv : ContinuousOn (fun p : ℝ^n × ℝ ↦ χ p.1 * u p.1 p.2)
      (univ ×ˢ Icc a b) := by
    simpa only [smul_eq_mul, Function.uncurry_def] using
      PDE.Analysis.continuousOn_spatial_cutoff_smul hΩ hχ.continuous hχΩ hu
  have hD : ContinuousOn (fun p : ℝ^n × ℝ ↦ χ p.1 * Dt p)
      (univ ×ˢ Icc a b) := by
    simpa only [smul_eq_mul] using
      PDE.Analysis.continuousOn_spatial_cutoff_smul hΩ hχ.continuous hχΩ hDt
  have hL : ContinuousOn (fun p : ℝ^n × ℝ ↦
      laplacian (fun y ↦ χ y * u y p.2) p.1) (univ ×ˢ Icc a b) :=
    PDE.FDeriv.continuousOn_laplacian_spatial_cutoff hΩ hχ hχΩ hu
      (PDE.continuousOn_partialDeriv_spatial_of_hasFDerivAt hDx hspace)
      (PDE.continuousOn_laplacian_spatial_of_hasFDerivAt hΩ hDxx hspace hhessian) hslices
  refine eq_initialValueSolution_add_integral_heatResidual
    (u := fun s y ↦ χ y * u y s) (D := fun s y ↦ χ y * Dt (y, s))
    (K := tsupport χ) hab hχc ?_ ?_ ?_ ?_ ?_ ?_ x
  · exact hv.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩)
  · exact hD.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩)
  · intro p hp
    exact (hL (p.2, p.1) ⟨hp.2, hp.1⟩).comp (f := Prod.swap)
      continuous_swap.continuousWithinAt (fun q hq ↦ ⟨hq.2, hq.1⟩)
  · intro s hs y
    exact PDE.FDeriv.hasDerivWithinAt_spatial_cutoff hχΩ htime y hs
  · intro s _ y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · intro s hs
    simpa only [smul_eq_mul] using
      PDE.Analysis.contDiff_spatial_cutoff_smul hΩ hχ hχΩ (hslices s hs)

/-- Where a cutoff is identically one near a spatial point, its heat
residual vanishes if the original field solves the heat equation there. -/
theorem spatialCutoff_heatResidual_eq_zero
    {u : ℝ^n → ℝ} {χ : ℝ^n → ℝ} {D : ℝ} {x : ℝ^n}
    (hχ : χ =ᶠ[𝓝 x] fun _ ↦ 1)
    (hheat : D - laplacian u x = 0) :
    χ x * D - laplacian (fun y ↦ χ y * u y) x = 0 := by
  have heq : (fun y ↦ χ y * u y) =ᶠ[𝓝 x] u := by
    filter_upwards [hχ] with y hy
    simp only [hy, one_mul]
  have hL : laplacian (fun y ↦ χ y * u y) x = laplacian u x := by
    exact EuclideanLaplacian.laplacian_congr_nhds heq
  simpa only [hχ.eq_of_nhds, one_mul, hL] using hheat

end HeatEquation
