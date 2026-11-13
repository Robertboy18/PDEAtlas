/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import CAS.ExactTactic

/-!
# Singular quotient energies

A lower bound `c / x² ≤ w(x)` controls the square integral of `f(x) / x`
by the weighted energy of `f`. The same comparison proves membership in
`L²`, so finiteness of the unweighted quotient is a conclusion.
Origin and reflected endpoint weights split into their quotient
square integrals, with integrability established before using linearity.
-/

@[expose] public section

open Filter

namespace MeasureTheory

/-- A positive inverse-square lower bound on the weight supplies both
square integrability of the quotient and its quantitative energy bound. -/
theorem memLp_div_and_integral_sq_le_of_weight_lower_bound
    {μ : Measure ℝ} {f w : ℝ → ℝ} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hc : 0 < c)
    (hfloor : ∀ᵐ x ∂μ, c / x ^ 2 ≤ w x)
    (henergy : Integrable (fun x ↦ f x ^ 2 * w x) μ) :
    MemLp (fun x ↦ f x / x) 2 μ ∧
      (∫ x, (f x / x) ^ 2 ∂μ) ≤ c⁻¹ * ∫ x, f x ^ 2 * w x ∂μ := by
  have hmeas : AEStronglyMeasurable (fun x ↦ f x / x) μ :=
    hf.div₀ measurable_id.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ, (f x / x) ^ 2 ≤ c⁻¹ * (f x ^ 2 * w x) := by
    filter_upwards [hfloor] with x hx
    have h := mul_le_mul_of_nonneg_left hx (sq_nonneg (f x))
    have heq : f x ^ 2 * (c / x ^ 2) = c * (f x / x) ^ 2 := by
      rw [div_pow]
      ring
    rw [heq] at h
    have hscaled := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hscaled
  have hint : Integrable (fun x ↦ (f x / x) ^ 2) μ :=
    (henergy.const_mul c⁻¹).mono' (hmeas.pow 2)
      (hpoint.mono fun x hx ↦ by simpa only
        [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x / x))]
        using hx)
  refine ⟨(memLp_two_iff_integrable_sq hmeas).2 hint, ?_⟩
  calc
    (∫ x, (f x / x) ^ 2 ∂μ) ≤ ∫ x, c⁻¹ * (f x ^ 2 * w x) ∂μ :=
      integral_mono_ae hint (henergy.const_mul c⁻¹) hpoint
    _ = c⁻¹ * ∫ x, f x ^ 2 * w x ∂μ := integral_const_mul _ _

/-- Two square-integrable origin quotients give integrability against any
linear combination of the inverse fourth and second powers. -/
theorem integrable_sq_mul_origin_weight {f : ℝ → ℝ} {μ : Measure ℝ}
    (hsecond : MemLp (fun x ↦ f x / x ^ 2) 2 μ)
    (hfirst : MemLp (fun x ↦ f x / x) 2 μ) (a b : ℝ) :
    Integrable (fun x ↦ f x ^ 2 * (a / x ^ 4 + b / x ^ 2)) μ := by
  apply ((hsecond.integrable_sq.const_mul a).add
    (hfirst.integrable_sq.const_mul b)).congr
  exact Eventually.of_forall fun x ↦ by
    dsimp only [Pi.add_apply]
    by_cases hx : x = 0
    · simp [hx]
    · generalize f x = z
      cas using hx


/-- The origin weighted integral splits into its two quotient norms. Both
terms are integrable, so integral linearity has its analytic hypotheses. -/
theorem integral_sq_mul_origin_weight {f : ℝ → ℝ} {μ : Measure ℝ}
    (hsecond : MemLp (fun x ↦ f x / x ^ 2) 2 μ)
    (hfirst : MemLp (fun x ↦ f x / x) 2 μ) (a b : ℝ) :
    (∫ x, f x ^ 2 * (a / x ^ 4 + b / x ^ 2) ∂μ) =
      a * (∫ x, (f x / x ^ 2) ^ 2 ∂μ) + b * ∫ x, (f x / x) ^ 2 ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hsecond.integrable_sq.const_mul a) (hfirst.integrable_sq.const_mul b)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x = 0
    · simp [hx]
    · generalize f x = z
      cas using hx


/-- Square integrability of a function and its coordinate quotient gives
integrability against an inverse-square weight with a constant term. -/
theorem integrable_sq_mul_inv_square_add {f : ℝ → ℝ} {μ : Measure ℝ}
    (hq : MemLp (fun x ↦ f x / x) 2 μ) (hf : MemLp f 2 μ) (a b : ℝ) :
    Integrable (fun x ↦ f x ^ 2 * (a / x ^ 2 + b)) μ := by
  apply ((hq.integrable_sq.const_mul a).add (hf.integrable_sq.const_mul b)).congr
  exact Eventually.of_forall fun x ↦ by
    dsimp only [Pi.add_apply]
    rw [div_pow]
    ring

/-- An inverse-square weighted norm splits into the quotient norm and the
ordinary norm, with integrability supplied by their `L²` memberships. -/
theorem integral_sq_mul_inv_square_add {f : ℝ → ℝ} {μ : Measure ℝ}
    (hq : MemLp (fun x ↦ f x / x) 2 μ) (hf : MemLp f 2 μ) (a b : ℝ) :
    (∫ x, f x ^ 2 * (a / x ^ 2 + b) ∂μ) =
      a * (∫ x, (f x / x) ^ 2 ∂μ) + b * ∫ x, f x ^ 2 ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hq.integrable_sq.const_mul a) (hf.integrable_sq.const_mul b)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    dsimp only
    rw [div_pow]
    ring


/-- A pair of endpoint quotients gives integrability against the reflected
inverse-square weight, without any sign condition on its scalar coefficient. -/
theorem integrable_sq_mul_endpoint_weight {f : ℝ → ℝ} {μ : Measure ℝ} {L : ℝ}
    (hleft : MemLp (fun x ↦ f x / (x - L)) 2 μ)
    (hright : MemLp (fun x ↦ f x / (x + L)) 2 μ) (a : ℝ) :
    Integrable (fun x ↦ f x ^ 2 * (a / (x - L) ^ 2 + a / (x + L) ^ 2)) μ := by
  apply ((hleft.integrable_sq.const_mul a).add
    (hright.integrable_sq.const_mul a)).congr
  exact Eventually.of_forall fun x ↦ by
    dsimp only [Pi.add_apply]
    simp only [div_pow]
    simp only [div_eq_mul_inv]
    generalize f x = z, ((x - L) ^ 2)⁻¹ = r, ((x + L) ^ 2)⁻¹ = s
    cas


/-- The reflected endpoint weight is the sum of two quotient norms. -/
theorem integral_sq_mul_endpoint_weight {f : ℝ → ℝ} {μ : Measure ℝ} {L : ℝ}
    (hleft : MemLp (fun x ↦ f x / (x - L)) 2 μ)
    (hright : MemLp (fun x ↦ f x / (x + L)) 2 μ) (a : ℝ) :
    (∫ x, f x ^ 2 * (a / (x - L) ^ 2 + a / (x + L) ^ 2) ∂μ) =
      a * ∫ x, (f x / (x - L)) ^ 2 + (f x / (x + L)) ^ 2 ∂μ := by
  rw [integral_add hleft.integrable_sq hright.integrable_sq, mul_add,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hleft.integrable_sq.const_mul a) (hright.integrable_sq.const_mul a)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    simp only [div_pow]
    simp only [div_eq_mul_inv]
    generalize f x = z, ((x - L) ^ 2)⁻¹ = r, ((x + L) ^ 2)⁻¹ = s
    cas


/-- Reflection of an even function transports its right endpoint quotient
to the other endpoint without changing its `L²` domain. -/
theorem memLp_div_add_of_even {f : ℝ → ℝ} {L : ℝ} (heven : Function.Even f)
    (hmem : MemLp (fun x ↦ f x / (x - L)) 2 volume) :
    MemLp (fun x ↦ f x / (x + L)) 2 volume := by
  apply (hmem.comp_measurePreserving (Measure.measurePreserving_neg volume)).neg.ae_eq
  exact Eventually.of_forall fun x ↦ by
    simp only [Function.comp_def, Pi.neg_apply, heven x,
      show -x - L = -(x + L) by cas, div_neg, neg_neg]

end MeasureTheory
