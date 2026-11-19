/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integrated dissipation of an absolutely continuous energy

Let `e ≥ 0` be absolutely continuous on `[a, b]` with `e' + d ≤ K e + g` almost
everywhere, where `K ≥ 0` and the dissipation `d` and source `g` are integrable
and nonnegative almost everywhere. Grönwall bounds `e` by
`(e(a) + ∫ₐᵇ g) e^{K(b-a)}`, and integrating the inequality gives
`∫ₐᵇ d ≤ (1 + K(b-a) e^{K(b-a)}) (e(a) + ∫ₐᵇ g)`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution

open MeasureTheory Set

/-- Integrated dissipation bound
`∫ₐᵇ d ≤ (1 + K(b-a) e^{K(b-a)}) (e(a) + ∫ₐᵇ g)` for an absolutely continuous
energy `e ≥ 0` with `e' + d ≤ K e + g` almost everywhere. -/
theorem integral_dissipation_le_of_deriv_add_le
    {e d g : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (he : AbsolutelyContinuousOnInterval e a b)
    (he_nonneg : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hd : IntervalIntegrable d volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hd_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ d t)
    (hg_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ g t)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), deriv e t + d t ≤ K * e t + g t) :
    (∫ t in a..b, d t) ≤
      (1 + K * (b - a) * Real.exp (K * (b - a))) * (e a + ∫ t in a..b, g t) := by
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b), deriv e t ≤ K * e t + g t := by
    filter_upwards [hderiv, hd_nonneg] with t ht hdt
    linarith
  have hbound := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le
    hab he hg hg_nonneg hK hdiff
  have hcont : ContinuousOn e (Icc a b) := by
    simpa only [uIcc_of_le hab] using he.continuousOn
  have heint : IntervalIntegrable e volume a b := hcont.intervalIntegrable_of_Icc hab
  have hsource : 0 ≤ ∫ t in a..b, g t := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_nonneg_of_ae hg_nonneg
  have hbudget : 0 ≤ e a + ∫ t in a..b, g t :=
    add_nonneg (he_nonneg a ⟨le_rfl, hab⟩) hsource
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      e t ≤ (e a + ∫ s in a..b, g s) * Real.exp (K * (b - a)) := by
    apply (hbound t ht).trans
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_right ht.2 a) hK)) hbudget
  have heupper := intervalIntegral.integral_mono_on hab heint
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ ↦
        (e a + ∫ s in a..b, g s) * Real.exp (K * (b - a))) volume a b) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at heupper
  have hderivIcc : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv e t + d t ≤ K * e t + g t := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hderiv
  have hint := intervalIntegral.integral_mono_ae_restrict hab
    (he.intervalIntegrable_deriv.add hd) ((heint.const_mul K).add hg) hderivIcc
  rw [intervalIntegral.integral_add he.intervalIntegrable_deriv hd,
    he.integral_deriv_eq_sub, intervalIntegral.integral_add (heint.const_mul K) hg,
    intervalIntegral.integral_const_mul] at hint
  have hkbound := mul_le_mul_of_nonneg_left heupper hK
  nlinarith [he_nonneg b ⟨hab, le_rfl⟩]

end PDE.Analysis.Evolution
