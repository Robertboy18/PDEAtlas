/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.RealL2

/-!
# A positive weight controls the unweighted L² norm

A positive constant lower bound on the weight turns a finite weighted square
integral into unweighted `MemLp` membership. Thus vanishing weighted
energy implies convergence of the unweighted L² classes. Every square integral
used for comparison is proved integrable.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A finite weighted square integral and a positive lower bound for the
weight supply unweighted square integrability. -/
theorem memLp_two_of_integrable_sq_mul_of_weight_lower_bound
    {f w : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : AEStronglyMeasurable f μ) (hw : ∀ᵐ x ∂μ, c ≤ w x)
    (hint : Integrable (fun x ↦ f x ^ 2 * w x) μ) :
    MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq hf).2
  apply (hint.div_const c).mono' (hf.pow 2)
  filter_upwards [hw] with x hx
  simp only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
  exact (le_div_iff₀ hc).2 (mul_le_mul_of_nonneg_left hx (sq_nonneg _))

/-- The square of the L² norm is controlled by weighted energy divided
by the positive lower bound for the weight. -/
theorem norm_toLp_sq_le_integral_sq_mul_div
    {f w : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : MemLp f 2 μ) (hw : ∀ᵐ x ∂μ, c ≤ w x)
    (hint : Integrable (fun x ↦ f x ^ 2 * w x) μ) :
    ‖hf.toLp f‖ ^ 2 ≤ (∫ x, f x ^ 2 * w x ∂μ) / c := by
  rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq hf, ← integral_div]
  apply integral_mono_ae hf.integrable_sq (hint.div_const c)
  filter_upwards [hw] with x hx
  exact (le_div_iff₀ hc).2 (mul_le_mul_of_nonneg_left hx (sq_nonneg _))

/-- Vanishing weighted energy forces the unweighted L² classes to vanish.
The filter and spatial measure are arbitrary. -/
theorem tendsto_toLp_zero_of_weighted_energy
    {ι : Type*} {l : Filter ι} {f : ι → X → ℝ} {w : X → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ i, MemLp (f i) 2 μ)
    (hw : ∀ᵐ x ∂μ, c ≤ w x)
    (hint : ∀ i, Integrable (fun x ↦ f i x ^ 2 * w x) μ)
    (henergy : Tendsto (fun i ↦ ∫ x, f i x ^ 2 * w x ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ (hf i).toLp (f i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hroot : Tendsto (fun i ↦ √((∫ x, f i x ^ 2 * w x ∂μ) / c))
      l (𝓝 0) := by
    simpa only [zero_div, Real.sqrt_zero] using (henergy.div_const c).sqrt
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) hroot
  have hsq := norm_toLp_sq_le_integral_sq_mul_div hc (hf i) hw (hint i)
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hsq)).2 hsq

end MeasureTheory
