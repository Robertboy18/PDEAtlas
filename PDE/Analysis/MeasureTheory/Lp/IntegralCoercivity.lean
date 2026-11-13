/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Comparing Lp powers with extended integrals

Integrating an Lp norm power gives a lower bound for a possibly infinite
energy. No measurability or integrability of the larger density is needed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Lp

/-- An integrable gradient power can be compared with an extended energy without
assuming that the energy density is integrable or even measurable. -/
theorem ofReal_mul_norm_rpow_le_lintegral
    {α H : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    {μ : Measure α} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (g : Lp H p μ) {e : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᵐ x ∂μ, c * ‖g x‖ ^ p.toReal ≤ e x) :
    ENNReal.ofReal (c * ‖g‖ ^ p.toReal) ≤ ∫⁻ x, ENNReal.ofReal (e x) ∂μ := by
  have hint : Integrable (fun x ↦ c * ‖g x‖ ^ p.toReal) μ :=
    ((Lp.memLp g).integrable_norm_rpow hp_zero hp_top).const_mul c
  calc
    ENNReal.ofReal (c * ‖g‖ ^ p.toReal) =
        ENNReal.ofReal (∫ x, c * ‖g x‖ ^ p.toReal ∂μ) := by
      rw [integral_const_mul, Lp.norm_rpow_eq_integral hp_zero hp_top g]
    _ = ∫⁻ x, ENNReal.ofReal (c * ‖g x‖ ^ p.toReal) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun x ↦ mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))
    _ ≤ ∫⁻ x, ENNReal.ofReal (e x) ∂μ :=
      lintegral_mono_ae (hbound.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

end MeasureTheory.Lp
