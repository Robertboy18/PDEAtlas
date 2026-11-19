/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# From finite nonnegative energy to Bochner integrals

Finiteness of the lower integral of a sum of two nonnegative measurable densities
implies integrability of each density. The resulting Bochner integrals obey the
same strict upper bound when the second density has coefficient at most one.
All statements allow an arbitrary measure, including restrictions to open intervals. For a
continuous function nonnegative on an open interval, the lower integral over the interval is the
interval integral (`setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

/-- A finite lower integral of a nonnegative sum controls each Bochner summand. -/
theorem integrable_left_of_lintegral_ofReal_add_ne_top
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hfinite : (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ) ≠ ∞) :
    Integrable f μ := by
  have hsum0 : 0 ≤ᵐ[μ] fun x ↦ f x + g x :=
    hf0.mp (hg0.mono fun _ hb ha ↦ add_nonneg ha hb)
  have hsum : Integrable (fun x ↦ f x + g x) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.add hg) hsum0).mp hfinite
  exact hsum.mono_nonneg hf hf0 (hg0.mono fun _ hx ↦ le_add_of_nonneg_right hx)

/-- The second summand is integrable under the same finite energy hypothesis. -/
theorem integrable_right_of_lintegral_ofReal_add_ne_top
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hfinite : (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ) ≠ ∞) :
    Integrable g μ := by
  apply integrable_left_of_lintegral_ofReal_add_ne_top hg hf hg0 hf0
  simpa only [add_comm] using hfinite

/-- Lower-integral smallness implies smallness of the Bochner energy.
Integrability is derived from the finite bound, rather than assumed. -/
theorem integral_add_mul_lt_of_lintegral_ofReal_add_lt
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) {θ ε : ℝ} (hθ : θ ≤ 1)
    (hsmall : (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ) < ENNReal.ofReal ε) :
    (∫ x, f x ∂μ) + θ * (∫ x, g x ∂μ) < ε := by
  have hfinite := (hsmall.trans_le le_top).ne
  have hfi := integrable_left_of_lintegral_ofReal_add_ne_top hf hg hf0 hg0 hfinite
  have hgi := integrable_right_of_lintegral_ofReal_add_ne_top hf hg hf0 hg0 hfinite
  have hsum0 : 0 ≤ᵐ[μ] fun x ↦ f x + g x :=
    hf0.mp (hg0.mono fun _ hb ha ↦ add_nonneg ha hb)
  have hsumint : Integrable (fun x ↦ f x + g x) μ := hfi.add hgi
  rw [← ofReal_integral_eq_lintegral_ofReal hsumint hsum0] at hsmall
  have hsum : (∫ x, f x + g x ∂μ) < ε := by
    by_contra h
    exact hsmall.not_ge (ENNReal.ofReal_le_ofReal (not_lt.mp h))
  rw [integral_add hfi hgi] at hsum
  exact lt_of_le_of_lt
    (add_le_add le_rfl (mul_le_of_le_one_left (integral_nonneg_of_ae hg0) hθ)) hsum

/-- For a function continuous on `[a, b]` and nonnegative on `(a, b)`, the lower integral of
`ofReal f` over `(a, b)` is `ofReal` of the interval integral. -/
theorem setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hnn : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hnn))]

end MeasureTheory
