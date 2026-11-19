/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Localization
public import PDE.Parabolic.Heat.Duhamel.Representation.TimeCutoff
import PDE.Analysis.Calculus.SpaceTime.Regularity

/-!
# Spacetime localization of a classical heat field

A spatial cutoff and an initial time cutoff give a Duhamel identity
without an initial-slice term. The field remains local in space and its time
derivative is taken within the closed interval. For a heat solution, the source
is a cutoff commutator, to which spatial integration by parts applies.
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory Set
open scoped Interval

namespace HeatEquation

variable {n : ℕ}

/-- The spacetime cutoff of a local classical field is the heat potential
of its cutoff heat residual. No regularity is required outside the spatial
domain, and the cutoff products supply the common compact spatial support. -/
theorem spaceTimeCutoff_eq_integral_heatResidual
    {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ} {χ : ℝ^n → ℝ} {η : ℝ → ℝ}
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
    (hχΩ : tsupport χ ⊆ Ω) (hη : ContDiff ℝ 1 η) (hηa : η a = 0)
    (x : ℝ^n) :
    η b * (χ x * u x b) =
      ∫ s in a..b, initialValueSolution (fun y ↦
        deriv η s * (χ y * u y s) +
          η s * (χ y * Dt (y, s) -
            laplacian (fun z ↦ χ z * u z s) y)) x (b - s) := by
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
  exact timeCutoff_eq_integral_heatResidual
    (u := fun s y ↦ χ y * u y s) (D := fun s y ↦ χ y * Dt (y, s))
    (K := tsupport χ) hab hχc
    (hv.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩))
    (hD.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩))
    (fun p hp ↦ (hL (p.2, p.1) ⟨hp.2, hp.1⟩).comp (f := Prod.swap)
      continuous_swap.continuousWithinAt (fun q hq ↦ ⟨hq.2, hq.1⟩))
    (fun s hs y ↦ PDE.FDeriv.hasDerivWithinAt_spatial_cutoff hχΩ htime y hs)
    (fun _ _ y hy ↦ by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    (fun s hs ↦ by
      simpa only [smul_eq_mul] using
        PDE.Analysis.contDiff_spatial_cutoff_smul hΩ hχ hχΩ (hslices s hs))
    hη hηa x
end HeatEquation
