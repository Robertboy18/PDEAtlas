/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.Domain

/-!
# Coefficient factors controlled by finite weighted energy

Let `∫ q² w < ∞`. If `0 ≤ a ≤ C w`, then `a q²` is integrable. If `a² ≤ C w`, then
`a q ∈ L²`. A mixed term `a b c` with `|c| ≤ C √p √q` is integrable when `a √p` and
`b √q` are in `L²`, and a bounded nonnegative factor preserves an integrable quadratic
density. All coefficient inequalities need hold only almost everywhere.
-/

@[expose] public section

open Filter

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A nonnegative density dominated by the energy weight has finite integral
against the squared perturbation. -/
theorem integrable_mul_weighted_sq_of_le
    {a w q : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hq : AEStronglyMeasurable q μ)
    (ha0 : 0 ≤ᵐ[μ] a) (hbound : ∀ᵐ x ∂μ, a x ≤ C * w x)
    (henergy : Integrable (fun x ↦ q x ^ 2 * w x) μ) :
    Integrable (fun x ↦ a x * q x ^ 2) μ := by
  apply (henergy.const_mul C).mono_nonneg (ha.mul (hq.pow 2))
    (ha0.mono fun _ hx ↦ mul_nonneg hx (sq_nonneg _))
  filter_upwards [hbound] with x hx
  simpa only [Pi.mul_apply, Pi.pow_apply, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hx (sq_nonneg (q x))

/-- A coefficient square bounded by the energy weight gives an `L²` factor. -/
theorem memLp_mul_of_sq_le_weight
    {a w q : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hq : AEStronglyMeasurable q μ)
    (hbound : ∀ᵐ x ∂μ, a x ^ 2 ≤ C * w x)
    (henergy : Integrable (fun x ↦ q x ^ 2 * w x) μ) :
    MemLp (fun x ↦ a x * q x) 2 μ := by
  apply (memLp_two_iff_integrable_sq (ha.mul hq)).mpr
  simpa only [Pi.mul_apply, Pi.pow_apply, mul_pow] using
    integrable_mul_weighted_sq_of_le (ha.pow 2) hq
    (Eventually.of_forall fun _ ↦ sq_nonneg _) hbound henergy

/-- The pointwise geometric-mean comparison used for a mixed energy term also
proves integrability of that term. -/
theorem integrable_cross_of_weighted_bound
    {a b p q c : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ)
    (hp : MemLp (fun x ↦ a x * √(p x)) 2 μ)
    (hq : MemLp (fun x ↦ b x * √(q x)) 2 μ)
    (hbound : ∀ᵐ x ∂μ, |c x| ≤ C * √(p x) * √(q x)) :
    Integrable (fun x ↦ a x * b x * c x) μ := by
  have hmajor := (hp.integrable_mul hq).norm.const_mul C
  apply hmajor.mono' ((ha.mul hb).mul hc)
  filter_upwards [hbound] with x hx
  have h := mul_le_mul_of_nonneg_left hx (abs_nonneg (a x * b x))
  simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_assoc, mul_left_comm, mul_comm] using h

/-- An almost everywhere bounded measurable factor preserves an integrable
nonnegative quadratic density. -/
theorem integrable_mul_weighted_sq_of_bounded
    {Q q φ : α → ℝ} {C : ℝ}
    (hQ : AEStronglyMeasurable Q μ) (hQ0 : ∀ᵐ x ∂μ, 0 ≤ Q x)
    (hbound : ∀ᵐ x ∂μ, Q x ≤ C) (hφ : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (henergy : Integrable (fun x ↦ q x ^ 2 * φ x) μ) :
    Integrable (fun x ↦ Q x * q x ^ 2 * φ x) μ := by
  apply (henergy.const_mul C).mono_nonneg
    ((hQ.mul henergy.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun _ ↦ (mul_assoc _ _ _).symm))
  · filter_upwards [hQ0, hφ] with x hx hφx
    exact mul_nonneg (mul_nonneg hx (sq_nonneg _)) hφx
  · filter_upwards [hbound, hφ] with x hx hφx
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hx (mul_nonneg (sq_nonneg _) hφx)

end MeasureTheory
