/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# `L²` bound for a forcing with a bounded operator term

If `f = f₀ + A(t) u(t)` for almost every `t`, where `u ∈ L²(μ; V)`, `f, f₀ ∈ L²(μ; H)` and
`‖A(t)‖ ≤ K` almost everywhere, then `‖f‖_{L²} ≤ ‖f₀‖_{L²} + K ‖u‖_{L²}`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory

namespace PDE.Analysis.Evolution

variable {α V H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- If `f = f₀ + A(t) u(t)` and `‖A(t)‖ ≤ K` almost everywhere, then
`‖f‖ ≤ ‖f₀‖ + K ‖u‖` in `L²`. -/
theorem norm_le_add_mul_of_ae_eq_add_clm
    (u : Lp V 2 μ) (f f₀ : Lp H 2 μ) (A : α → V →L[ℝ] H)
    {K : ℝ} (hA : ∀ᵐ t ∂μ, ‖A t‖ ≤ K)
    (hf : ∀ᵐ t ∂μ, f t = f₀ t + A t (u t)) :
    ‖f‖ ≤ ‖f₀‖ + K * ‖u‖ := by
  have hd : ‖f - f₀‖ ≤ K * ‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub f f₀, hA, hf] with t ht hAt hft
    rw [ht, Pi.sub_apply, hft, add_sub_cancel_left]
    exact ((A t).le_opNorm (u t)).trans
      (mul_le_mul_of_nonneg_right hAt (norm_nonneg _))
  calc
    ‖f‖ ≤ ‖f - f₀‖ + ‖f₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f - f₀) f₀
    _ ≤ K * ‖u‖ + ‖f₀‖ := add_le_add hd (le_refl _)
    _ = ‖f₀‖ + K * ‖u‖ := add_comm _ _

end PDE.Analysis.Evolution
