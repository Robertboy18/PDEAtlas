/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiating a weighted integral energy

The weight is fixed in time. Multiplying by its square root reduces the
calculation to the unweighted L² theorem, for an arbitrary spatial measure.
Two common local majorants justify differentiation under the integral.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- Weighted `L²` majorants differentiate a weighted square, with a fixed
nonnegative weight. Measurability is only required for the weighted states; the weighted
derivative is measurable as an almost-everywhere limit of difference quotients. -/
theorem hasDerivAt_integral_weighted_sq_of_memLp_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w A B : α → ℝ} {q r : ℝ → α → ℝ}
    {t₀ : ℝ} {times : Set ℝ}
    (htimes : times ∈ 𝓝 t₀) (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hq : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun x ↦ q t x * √(w x)) μ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ times,
      |q t x * √(w x)| ≤ A x ∧ |r t x * √(w x)| ≤ B x)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ times,
      HasDerivAt (fun s ↦ q s x) (r t x) t) :
    HasDerivAt (fun t ↦ ∫ x, q t x ^ 2 * w x ∂μ)
      (2 * ∫ x, q t₀ x * r t₀ x * w x ∂μ) t₀ := by
  have hr : AEStronglyMeasurable (fun x ↦ r t₀ x * √(w x)) μ := by
    have hs : Tendsto (fun n : ℕ ↦ t₀ + 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] t₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n h ↦ ?_⟩
      · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t₀
      · have h' : t₀ + 1 / ((n : ℝ) + 1) = t₀ := h
        have := Nat.one_div_pos_of_nat (α := ℝ) (n := n)
        linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hs.mono_right nhdsWithin_le_nhds).eventually hq)
    have hq₀ : AEStronglyMeasurable (fun x ↦ q t₀ x * √(w x)) μ := hq.self_of_nhds
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x ↦ slope (fun s ↦ q s x * √(w x)) t₀ (t₀ + 1 / (((n + N : ℕ) : ℝ) + 1)))
      (fun n ↦ ?_) ?_
    · simp only [slope_def_field, div_eq_mul_inv]
      exact ((hN (n + N) (Nat.le_add_left N n)).sub hq₀).mul_const _
    · filter_upwards [hderiv] with x hx
      exact (hasDerivAt_iff_tendsto_slope.mp ((hx t₀ (mem_of_mem_nhds htimes)).mul_const
        (√(w x)))).comp (hs.comp (tendsto_add_atTop_nat N))
  have h := hasDerivAt_integral_sq_of_memLp_bounds
    htimes hq hr hA hB hbound (by
      filter_upwards [hderiv] with x hx
      exact fun t ht ↦ (hx t ht).mul_const (√(w x)))
  have heq (t : ℝ) :
      (∫ x, (q t x * √(w x)) ^ 2 ∂μ) = ∫ x, q t x ^ 2 * w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [mul_pow, Real.sq_sqrt hx]
  have hpair :
      (∫ x, q t₀ x * √(w x) * (r t₀ x * √(w x)) ∂μ) =
        ∫ x, q t₀ x * r t₀ x * w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    calc
      _ = q t₀ x * r t₀ x * (√(w x)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx]
  simpa only [heq, hpair] using h

end MeasureTheory
