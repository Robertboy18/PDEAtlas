/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Integer powers of real Lp norms

For a positive integer `n` and an almost everywhere strongly measurable `f`,
`∫ ‖f‖ ^ n = (lpNorm f n) ^ n`. When `f` is not in `Lⁿ` both sides are zero by the
totalization conventions. Mathlib states the formula with the reciprocal exponent.
The lower Lebesgue integral form `∫⁻ ‖f‖ ^ n = (eLpNorm f n) ^ n` holds in `ℝ≥0∞` with no
integrability assumption.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory

/-- The integral of a positive integer power of the norm is the corresponding Lp norm power. -/
theorem integral_norm_pow_eq_lpNorm_pow {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {n : ℕ} (hn : 0 < n) :
    ∫ x, ‖f x‖ ^ n ∂μ = lpNorm f n μ ^ n := by
  have h := congrArg ENNReal.toReal
    (eLpNorm_norm_rpow (p := 1) f hf (Nat.cast_pos.mpr hn))
  simp only [ENNReal.ofReal_natCast, one_mul, Real.rpow_natCast,
    ENNReal.rpow_natCast, ENNReal.toReal_pow, toReal_eLpNorm] at h
  rw [lpNorm_one_eq_integral_norm (f := fun x ↦ ‖f x‖ ^ n) (hf.norm.pow n)] at h
  simpa only [norm_pow, norm_norm] using h

/-- The lower Lebesgue integral of a positive integer power of the norm is the same power of
the extended Lp seminorm. -/
theorem lintegral_ofReal_norm_pow_eq_eLpNorm_pow {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ n) ∂μ = eLpNorm f n μ ^ n := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (n : ℝ≥0)) (by exact_mod_cast hn) hf
  simp only [NNReal.coe_natCast, ENNReal.coe_natCast] at h
  rw [← ENNReal.rpow_natCast, h]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.rpow_natCast]

end MeasureTheory
