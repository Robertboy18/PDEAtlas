/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted energy bounds under unweighted L² convergence

An almost-everywhere convergent subsequence and Fatou's lemma preserve a
uniform bound on a nonnegative weighted energy. Finiteness of the limiting
energy is proved, so the conclusion does not rely on the totalized value of
an integral outside its integrability domain.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

/-- A uniform integral bound for nonnegative integrable functions passes to
an almost-everywhere limit, and proves that the limit is integrable. -/
theorem integrable_and_integral_le_of_ae_limit_nonneg
    {μ : Measure ℝ} {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hu : ∀ n, Integrable (u n) μ)
    (hnonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x)
    (hbound : ∀ n, (∫ x, u n x ∂μ) ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (f x))) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hC : 0 ≤ C := (integral_nonneg_of_ae (hnonneg 0)).trans (hbound 0)
  have hnorm (n : ℕ) : (∫ x, ‖u n x‖ ∂μ) = ∫ x, u n x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hnonneg n] with x hx
    exact Real.norm_of_nonneg hx
  have hlin (n : ℕ) : (∫⁻ x, ‖u n x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hu n), hnorm n]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hinf : liminf (fun n ↦ ∫⁻ x, ‖u n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le (Eventually.of_forall hlin).frequently
  have hint : Integrable f μ :=
    integrable_of_tendsto hlim (fun n ↦ (hu n).aestronglyMeasurable)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinf)
  have hfatou := (lintegral_enorm_le_liminf_of_tendsto hlim
    (fun n ↦ (hu n).aestronglyMeasurable.enorm)).trans hinf
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint] at hfatou
  have hnormf : (∫ x, ‖f x‖ ∂μ) ≤ C := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
      ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou
  exact ⟨hint, (le_abs_self _).trans ((norm_integral_le_integral_norm _).trans hnormf)⟩

/-- Unweighted `L²` convergence preserves any uniformly bounded nonnegative
weighted error energy on a smaller measure. The proof extracts an a.e.
subsequence and applies Fatou; weighted convergence is not assumed. -/
theorem integrable_weighted_sq_sub_and_integral_le_of_tendsto_L2
    {μ ν : Measure ℝ} (hν : ν ≤ μ)
    {u : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {b w : ℝ → ℝ} {C : ℝ}
    (hlim : Tendsto u atTop (𝓝 v))
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (henergy : ∀ n, Integrable (fun x ↦ (u n x - b x) ^ 2 * w x) ν)
    (hbound : ∀ n, (∫ x, (u n x - b x) ^ 2 * w x ∂ν) ≤ C) :
    Integrable (fun x ↦ (v x - b x) ^ 2 * w x) ν ∧
      (∫ x, (v x - b x) ^ 2 * w x ∂ν) ≤ C := by
  obtain ⟨s, _hs, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine integrable_and_integral_le_of_ae_limit_nonneg
    (fun n ↦ henergy (s n)) ?_ (fun n ↦ hbound (s n)) ?_
  · intro n
    filter_upwards [hw] with x hx
    exact mul_nonneg (sq_nonneg _) hx
  · filter_upwards [hsub.filter_mono (ae_mono hν)] with x hx
    exact ((hx.sub_const (b x)).pow 2).mul_const (w x)

end MeasureTheory
