/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.EnergyIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Contraction for absolutely continuous Hilbert trajectories

An almost-everywhere dissipative pairing makes the squared distance nonincreasing.
Absolute continuity is essential: the scalar fundamental theorem, rather than only
pointwise differentiation almost everywhere, controls the endpoint difference.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Dissipation of the relative velocity controls the distance between the
endpoint values of two absolutely continuous curves. -/
theorem norm_sub_le_of_ae_dissipative_derivatives
    {a b : ℝ} (hab : a ≤ b) {u v g h : ℝ → H}
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt u (g t) t)
    (hdv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt v (h t) t)
    (hdiss : ∀ᵐ t ∂volume.restrict (Ioo a b),
      inner ℝ (g t - h t) (u t - v t) ≤ 0) :
    ‖u b - v b‖ ≤ ‖u a - v a‖ := by
  let energy := fun t ↦ (1 / 2 : ℝ) * ‖u t - v t‖ ^ 2
  have hAC : AbsolutelyContinuousOnInterval energy a b :=
    (absolutelyContinuousOnInterval_norm_sq (hu.sub hv)).const_mul (1 / 2)
  have hnonpos : ∀ᵐ t ∂volume.restrict (Ioo a b), deriv energy t ≤ 0 := by
    filter_upwards [hdu, hdv, hdiss] with t hut hvt ht
    have hd := hasDerivAt_half_norm_sq (hut.sub hvt)
    change HasDerivAt energy _ t at hd
    rw [hd.deriv]
    exact ht
  have hint : ∫ t in a..b, deriv energy t ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_nonpos_of_ae
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [hAC.integral_deriv_eq_sub] at hint
  dsimp only [energy] at hint
  nlinarith [norm_nonneg (u b - v b), norm_nonneg (u a - v a)]

end PDE.Analysis.Evolution
