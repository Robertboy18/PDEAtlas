/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Calculus

/-!
# Normalized velocity from the Hilbert principal value

Integrating the continuous principal value from zero constructs a classical
velocity with the prescribed derivative. Odd input gives even velocity gradient
and odd velocity, with the normalization fixed at the origin.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory
open scoped ContDiff NNReal

noncomputable section

/-- Velocity normalized to vanish at zero, obtained by integrating the
Hilbert principal value along the oriented interval from zero. -/
def hilbertPVVelocity (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, hilbertPV f y

/-- The normalization fixes the velocity at the origin. -/
theorem hilbertPVVelocity_zero (f : ℝ → ℝ) : hilbertPVVelocity f 0 = 0 := by
  simp only [hilbertPVVelocity, intervalIntegral.integral_same]

/-- For compactly supported Lipschitz input, the constructed velocity has the
principal value as its classical derivative at every point. -/
theorem hasDerivAt_hilbertPVVelocity_of_lipschitzWith_compactSupport {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (hilbertPVVelocity f) (hilbertPV f x) x :=
  ((continuous_hilbertPV_of_lipschitzWith_compactSupport hf hsupp).integral_hasStrictDerivAt
    0 x).hasDerivAt

/-- Compact `C¹` input therefore produces a classical velocity with derivative
equal to its principal value. -/
theorem hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (hilbertPVVelocity f) (hilbertPV f x) x :=
  ((continuous_hilbertPV_of_contDiff_one_compactSupport hf hsupp).integral_hasStrictDerivAt
    0 x).hasDerivAt

/-- The normalized velocity is `C¹` already for compactly supported Lipschitz input. -/
theorem contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) :
    ContDiff ℝ 1 (hilbertPVVelocity f) := by
  have hd := hasDerivAt_hilbertPVVelocity_of_lipschitzWith_compactSupport hf hsupp
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
  rw [show deriv (hilbertPVVelocity f) = hilbertPV f from funext fun x ↦ (hd x).deriv]
  exact continuous_hilbertPV_of_lipschitzWith_compactSupport hf hsupp

/-- Smooth compactly supported input gives a smooth normalized classical velocity. -/
theorem contDiff_hilbertPVVelocity_of_contDiff_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) :
    ContDiff ℝ ∞ (hilbertPVVelocity f) := by
  have hC1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hd := hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport hC1 hsupp
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
  rw [show deriv (hilbertPVVelocity f) = hilbertPV f from funext fun x ↦ (hd x).deriv]
  exact contDiff_hilbertPV_of_contDiff_compactSupport hf hsupp

/-- Odd input gives odd normalized velocity by reflection of the oriented integral. -/
theorem hilbertPVVelocity_odd_of_odd {f : ℝ → ℝ} (hf : Function.Odd f) :
    Function.Odd (hilbertPVVelocity f) := by
  intro x
  have heven := hilbertPV_even_of_odd hf
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) (hilbertPV f)
  rw [show (fun y ↦ hilbertPV f (-y)) = hilbertPV f from funext heven, neg_zero,
    intervalIntegral.integral_symm (a := 0) (b := -x)] at h
  change (∫ y in (0 : ℝ)..-x, hilbertPV f y) = -(∫ y in (0 : ℝ)..x, hilbertPV f y)
  linarith

/-- The classical velocity gradient is even for odd, compactly supported Lipschitz input. -/
theorem even_deriv_hilbertPVVelocity_of_odd {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) (hodd : Function.Odd f) :
    Function.Even (deriv (hilbertPVVelocity f)) := by
  rw [show deriv (hilbertPVVelocity f) = hilbertPV f from funext fun x ↦
    (hasDerivAt_hilbertPVVelocity_of_lipschitzWith_compactSupport hf hsupp x).deriv]
  exact hilbertPV_even_of_odd hodd

end

end PDE.Analysis
