/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrating a coercive pairing with an error

A pointwise coercivity inequality with a product error gives an `L²` pairing estimate.
The error is integrated using the scalar norm functions, so cancellation cannot weaken
its majorant. This is useful when a spatially varying nonlinear flux is differenced.
-/

@[expose] public noncomputable section

namespace MeasureTheory.Lp

open Filter
open scoped RealInnerProductSpace

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]

/-- Integrate pointwise coercivity and estimate its product error by Cauchy--Schwarz. -/
theorem mul_norm_sq_le_inner_add_of_ae_le
    (u v : Lp E 2 μ) (r : Lp F 2 μ) (c : ℝ)
    (h : ∀ᵐ x ∂μ, c * ‖u x‖ ^ 2 ≤ ⟪v x, u x⟫ + ‖r x‖ * ‖u x‖) :
    c * ‖u‖ ^ 2 ≤ ⟪v, u⟫ + ‖r‖ * ‖u‖ := by
  let R := lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) r
  let U := lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : E)‖ = 0) u
  have hR : (R : X → ℝ) =ᵐ[μ] fun x ↦ ‖r x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) r
  have hU : (U : X → ℝ) =ᵐ[μ] fun x ↦ ‖u x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : E)‖ = 0) u
  have hpoint : ∀ᵐ x ∂μ,
      c * ⟪u x, u x⟫ ≤ ⟪v x, u x⟫ + ⟪R x, U x⟫ := by
    filter_upwards [h, hR, hU] with x hx hr hu
    simpa only [real_inner_self_eq_norm_sq, Real.inner_apply, hr, hu] using hx
  have hint := integral_mono_ae
    ((L2.integrable_inner (𝕜 := ℝ) u u).const_mul c)
    ((L2.integrable_inner (𝕜 := ℝ) v u).add (L2.integrable_inner (𝕜 := ℝ) R U))
    hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_const_mul, integral_add
    (L2.integrable_inner (𝕜 := ℝ) v u) (L2.integrable_inner (𝕜 := ℝ) R U),
    ← L2.inner_def, ← L2.inner_def, ← L2.inner_def,
    real_inner_self_eq_norm_sq] at hint
  refine hint.trans (add_le_add le_rfl ((real_inner_le_norm R U).trans ?_))
  apply mul_le_mul
  · simpa only [NNReal.coe_one, one_mul] using
      lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : F)‖ = 0) r
  · simpa only [NNReal.coe_one, one_mul] using
      lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : E)‖ = 0) u
  · exact norm_nonneg _
  · exact norm_nonneg _

end MeasureTheory.Lp
