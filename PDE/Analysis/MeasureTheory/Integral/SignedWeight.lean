/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Comparison of signed moments with ordered weights

If `0 ≤ φ ≤ w` almost everywhere, the signed moment `∫ φ v` lies between
`-∫ w v⁻` and `∫ w v + ∫ w v⁻`, where `v⁻ = max (-v) 0` is the negative part of `v`.
-/

@[expose] public noncomputable section

open Set

namespace MeasureTheory

/-- A smaller nonnegative weight has its signed moment between minus the full
negative moment and the full signed moment plus that negative moment. -/
theorem integral_mul_mem_Icc_of_le_weight
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w φ v : α → ℝ}
    (hφ : Integrable (fun x ↦ φ x * v x) μ)
    (hw : Integrable (fun x ↦ w x * v x) μ)
    (hn : Integrable (fun x ↦ w x * max (-v x) 0) μ)
    (hbound : ∀ᵐ x ∂μ, 0 ≤ φ x ∧ φ x ≤ w x) :
    (∫ x, φ x * v x ∂μ) ∈ Icc (-(∫ x, w x * max (-v x) 0 ∂μ))
      ((∫ x, w x * v x ∂μ) + ∫ x, w x * max (-v x) 0 ∂μ) := by
  have hp : ∀ᵐ x ∂μ, -(w x * max (-v x) 0) ≤ φ x * v x ∧
      φ x * v x ≤ w x * v x + w x * max (-v x) 0 := by
    filter_upwards [hbound] with x hx
    by_cases hv : 0 ≤ v x
    · rw [max_eq_right (neg_nonpos.mpr hv)]
      constructor <;> nlinarith [mul_nonneg hx.1 hv,
        mul_le_mul_of_nonneg_right hx.2 hv]
    · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge hv))]
      constructor <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos hx.1 (le_of_not_ge hv),
        mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hv)]
  constructor
  · simpa only [Pi.neg_apply, integral_neg] using
      integral_mono_ae hn.neg hφ (hp.mono fun _ hx ↦ hx.1)
  · simpa only [Pi.add_apply, integral_add hw hn] using
      integral_mono_ae hφ (hw.add hn) (hp.mono fun _ hx ↦ hx.2)

end MeasureTheory
