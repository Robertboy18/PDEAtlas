/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Passing nonnegative energy bounds to almost-everywhere limits

Fatou's lemma both proves integrability and preserves a convergent sequence of
upper bounds. Allowing arbitrary measure spaces is needed for the Hardy weight
on Euclidean balls; allowing varying bounds retains the separate function and
gradient energies when smooth Sobolev approximants converge.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

/-- A convergent bound on nonnegative integrals proves integrability of an a.e. limit
and bounds its integral. No integrability hypothesis on the limit is required. -/
theorem integrable_and_integral_le_of_ae_limit_nonneg_of_tendsto_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → ℝ} {f : X → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (hu : ∀ k, Integrable (u k) μ)
    (hnonneg : ∀ k, ∀ᵐ x ∂μ, 0 ≤ u k x)
    (hbound : ∀ k, (∫ x, u k x ∂μ) ≤ b k)
    (hb : Tendsto b atTop (𝓝 C))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ u k x) atTop (𝓝 (f x))) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hC : 0 ≤ C := ge_of_tendsto' hb fun k ↦
    (integral_nonneg_of_ae (hnonneg k)).trans (hbound k)
  have hlin (k : ℕ) : (∫⁻ x, ‖u k x‖ₑ ∂μ) ≤ ENNReal.ofReal (b k) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hu k)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ x, ‖u k x‖ ∂μ) = ∫ x, u k x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hnonneg k] with x hx
        exact Real.norm_of_nonneg hx
      _ ≤ b k := hbound k
  have hinf : liminf (fun k ↦ ∫⁻ x, ‖u k x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    calc
      _ ≤ liminf (fun k ↦ ENNReal.ofReal (b k)) atTop :=
        liminf_le_liminf (Eventually.of_forall hlin)
      _ = _ := (ENNReal.continuous_ofReal.tendsto C |>.comp hb).liminf_eq
  have hfatou : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, liminf (fun k ↦ ‖u k x‖ₑ) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ liminf (fun k ↦ ∫⁻ x, ‖u k x‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' fun k ↦ (hu k).aestronglyMeasurable.enorm
      _ ≤ _ := hinf
  have hint : Integrable f μ :=
    ⟨aestronglyMeasurable_of_tendsto_ae _ (fun k ↦ (hu k).aestronglyMeasurable) hlim,
      lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint] at hfatou
  have hnorm : (∫ x, ‖f x‖ ∂μ) ≤ C := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
      ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou
  exact ⟨hint, (le_abs_self _).trans ((norm_integral_le_integral_norm _).trans hnorm)⟩

end MeasureTheory
