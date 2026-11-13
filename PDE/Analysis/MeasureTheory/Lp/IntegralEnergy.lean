/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Squared integral energy

Young's inequality transfers a squared integral bound while retaining the
squared difference as an explicit error term.

Pointwise time derivatives and two locally uniform L² bounds suffice to
differentiate the squared L² energy. The measure is arbitrary, so a fixed
singular spatial weight can be incorporated in the measure without
differentiating that weight in time.
-/

@[expose] public section

namespace MeasureTheory

open Filter Set
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrate Young's inequality with the exact difference retained as the error term. -/
theorem integral_sq_le_of_difference
    {f g : α → ℝ} {q ε η : ℝ} (hη : 0 < η)
    (hf : Integrable (fun x ↦ f x ^ 2) μ)
    (hg : Integrable (fun x ↦ g x ^ 2) μ)
    (hd : Integrable (fun x ↦ (f x - g x) ^ 2) μ)
    (hq : (∫ x, g x ^ 2 ∂μ) ≤ q)
    (hε : (∫ x, (f x - g x) ^ 2 ∂μ) ≤ ε) :
    (∫ x, f x ^ 2 ∂μ) ≤ (1 + η) * q + (1 + η⁻¹) * ε := by
  have hgc := hg.const_mul (1 + η)
  have hdc := hd.const_mul (1 + η⁻¹)
  calc
    _ ≤ ∫ x, ((1 + η) * g x ^ 2 + (1 + η⁻¹) * (f x - g x) ^ 2) ∂μ := by
      apply integral_mono hf (hgc.add hdc)
      intro x
      simp only [Pi.add_apply]
      have h := two_mul_le_add_mul_sq (a := g x) (b := f x - g x) hη
      nlinarith only [h]
    _ = (1 + η) * (∫ x, g x ^ 2 ∂μ) +
        (1 + η⁻¹) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
      rw [integral_add hgc hdc, integral_const_mul, integral_const_mul]
    _ ≤ (1 + η) * q + (1 + η⁻¹) * ε := by gcongr

/-- L² bounds for a trajectory and its time derivative justify differentiation
of its integral energy. The bounds hold on one time neighborhood outside one
fixed null set; no continuity of the pointwise derivative is required. -/
theorem hasDerivAt_integral_sq_of_memLp_bounds
    {u v : ℝ → α → ℝ} {A B : α → ℝ} {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀)
    (hu : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (u t) μ)
    (hv : AEStronglyMeasurable (v t₀) μ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, |u t x| ≤ A x ∧ |v t x| ≤ B x)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun τ ↦ u τ x) (v t x) t) :
    HasDerivAt (fun t ↦ ∫ x, u t x ^ 2 ∂μ)
      (2 * ∫ x, u t₀ x * v t₀ x ∂μ) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  have hu₀ : AEStronglyMeasurable (u t₀) μ := hu.self_of_nhds
  have huLp : MemLp (u t₀) 2 μ := hA.of_le hu₀ <| by
    filter_upwards [hbound] with x hx
    exact (hx t₀ ht₀).1.trans (le_abs_self (A x))
  have hbase : Integrable (fun x ↦ u t₀ x ^ 2) μ := by
    refine (huLp.integrable_mul huLp).congr ?_
    filter_upwards with x
    simp only [pow_two, Pi.mul_apply]
  have hmajorant : Integrable (fun x ↦ 2 * (A x * B x)) μ :=
    (hA.integrable_mul hB).const_mul 2
  have hbound' : ∀ᵐ x ∂μ, ∀ t ∈ s,
      ‖2 * u t x * v t x‖ ≤ 2 * (A x * B x) := by
    filter_upwards [hbound] with x hx
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hA₀ : 0 ≤ A x := (abs_nonneg _).trans (hx t ht).1
    nlinarith [mul_le_mul (hx t ht).1 (hx t ht).2 (abs_nonneg (v t x)) hA₀]
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ s,
      HasDerivAt (fun τ ↦ u τ x ^ 2) (2 * u t x * v t x) t := by
    filter_upwards [hderiv] with x hx
    intro t ht
    have hsq := (hx t ht).pow 2
    have hsq' := hsq.congr_of_eventuallyEq
      (Eventually.of_forall fun τ ↦ (Pi.pow_apply (fun τ ↦ u τ x) 2 τ).symm)
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hsq'
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (hu.mono fun _ ht ↦ ht.pow 2) hbase ((hu₀.const_mul 2).mul hv)
    hbound' hmajorant hdiff
  simpa only [Pi.pow_apply, mul_assoc, integral_const_mul] using h.2

end MeasureTheory
