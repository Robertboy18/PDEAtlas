/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Domains of weighted quadratic energies

An integrable nonnegative weighted square gives a weighted L² function.
Bounded coefficient and reserve factors preserve this energy domain. These lemmas
allow weights that are nonnegative only almost everywhere for the chosen measure.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An almost everywhere nonnegative weight turns integrability of its quadratic
density into weighted `L²` membership. The weight need not be nonnegative off the
measure's support. -/
theorem memLp_mul_sqrt_of_integrable_weighted_sq_ae
    {a w : α → ℝ} (ha : AEStronglyMeasurable a μ)
    (hw : AEStronglyMeasurable w μ) (hw0 : 0 ≤ᵐ[μ] w)
    (henergy : Integrable (fun x ↦ a x ^ 2 * w x) μ) :
    MemLp (fun x ↦ a x * √(w x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (ha.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hw))).mpr
  apply henergy.congr
  filter_upwards [hw0] with x hx
  change a x ^ 2 * w x = (a x * √(w x)) ^ 2
  simp only [mul_pow, Real.sq_sqrt hx]

/-- A pointwise coefficient certificate `a² w ≤ C` makes the nonlocal factor
`a w q` square integrable whenever the energy density `q² w` is integrable. -/
theorem memLp_mul_weight_of_integrable_weighted_sq
    {a w q : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ)
    (hq : AEStronglyMeasurable q μ) (hw0 : 0 ≤ᵐ[μ] w)
    (hbound : ∀ᵐ x ∂μ, a x ^ 2 * w x ≤ C)
    (henergy : Integrable (fun x ↦ q x ^ 2 * w x) μ) :
    MemLp (fun x ↦ a x * w x * q x) 2 μ := by
  -- `a w q = a (q² w) q⁻¹` pointwise (both sides vanish where `q = 0`), so no measurability
  -- of `w` itself is needed.
  have hm : AEStronglyMeasurable (fun x ↦ a x * w x * q x) μ := by
    refine ((ha.mul henergy.aestronglyMeasurable).mul
      hq.aemeasurable.inv.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases h : q x = 0
    · simp [h]
    · simp only [Pi.mul_apply, Pi.inv_apply]
      field_simp
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (henergy.const_mul C).mono_nonneg (hm.pow 2)
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  filter_upwards [hw0, hbound] with x hx hax
  calc
    (a x * w x * q x) ^ 2 = (a x ^ 2 * w x) * (q x ^ 2 * w x) := by ring
    _ ≤ C * (q x ^ 2 * w x) :=
      mul_le_mul_of_nonneg_right hax (mul_nonneg (sq_nonneg _) hx)

/-- Multiplication of a weight by an almost everywhere bounded nonnegative reserve
preserves the weighted `L²` energy domain. -/
theorem memLp_mul_sqrt_reserve_of_integrable_weighted_sq
    {r w q : α → ℝ} {C : ℝ}
    (hr : AEStronglyMeasurable r μ) (hw : AEStronglyMeasurable w μ)
    (hq : AEStronglyMeasurable q μ) (hw0 : 0 ≤ᵐ[μ] w)
    (hr0 : 0 ≤ᵐ[μ] r) (hbound : ∀ᵐ x ∂μ, r x ≤ C)
    (henergy : Integrable (fun x ↦ q x ^ 2 * w x) μ) :
    MemLp (fun x ↦ q x * √(r x * w x)) 2 μ := by
  have hrw0 : 0 ≤ᵐ[μ] fun x ↦ r x * w x :=
    hr0.mp (hw0.mono fun _ hx hrx ↦ mul_nonneg hrx hx)
  apply memLp_mul_sqrt_of_integrable_weighted_sq_ae hq (hr.mul hw) hrw0
  apply (henergy.const_mul C).mono_nonneg ((hq.pow 2).mul (hr.mul hw))
    (hrw0.mono fun _ hx ↦ mul_nonneg (sq_nonneg _) hx)
  filter_upwards [hw0, hbound] with x hx hrx
  calc
    q x ^ 2 * (r x * w x) = r x * (q x ^ 2 * w x) := by ring
    _ ≤ C * (q x ^ 2 * w x) :=
      mul_le_mul_of_nonneg_right hrx (mul_nonneg (sq_nonneg _) hx)

end MeasureTheory
