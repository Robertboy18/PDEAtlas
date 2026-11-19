/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Weighted difference bounds for superposition

A pointwise Lipschitz coefficient in a Hölder factor space controls the
difference of two superposition values. The coefficient may depend on both
inputs; neither a finite measure nor a uniform pointwise bound is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ : Measure α} {p q t : ℝ≥0∞} [Fact (1 ≤ p)] [ENNReal.HolderTriple t p q]

/-- A weighted pointwise difference bound gives the corresponding Hölder norm
bound for superposition, with a possibly input-dependent coefficient. -/
theorem norm_superposition_sub_le_of_weighted_bound
    (G : α → ℝ → F)
    (hmem : ∀ u : Lp ℝ p μ, MemLp (fun x ↦ G x (u x)) q μ)
    (u v : Lp ℝ p μ) (a : Lp ℝ t μ)
    (hbound : ∀ᵐ x ∂μ, ‖G x (u x) - G x (v x)‖ ≤ ‖a x‖ * ‖u x - v x‖) :
    ‖superposition G hmem u - superposition G hmem v‖ ≤ ‖a‖ * ‖u - v‖ := by
  let W : Lp ℝ q μ := (ContinuousLinearMap.mul ℝ ℝ).holder q a (u - v)
  have hW : ‖superposition G hmem u - superposition G hmem v‖ ≤ ‖W‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hbound, Lp.coeFn_sub (superposition G hmem u) (superposition G hmem v),
      coeFn_superposition G hmem u, coeFn_superposition G hmem v,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := q) a (u - v),
      Lp.coeFn_sub u v] with x hx hs hu hv hw hd
    simpa only [hs, Pi.sub_apply, hu, hv, W, hw, ContinuousLinearMap.mul_apply',
      hd, norm_mul] using hx
  calc
    _ ≤ ‖W‖ := hW
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖a‖ * ‖u - v‖ :=
      (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le _ _
    _ ≤ 1 * ‖a‖ * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
          (show 0 ≤ ‖a‖ from ENNReal.toReal_nonneg)) (norm_nonneg _)
    _ = ‖a‖ * ‖u - v‖ := by rw [one_mul]

end MeasureTheory.Lp
