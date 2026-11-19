/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pairings of real `L²` classes as integrals

For a real inner product space `E`, the squared `L²` norm of a class is the integral of the
squared pointwise norm (`L2.integral_norm_sq_eq_norm_sq`), and the pairing of the class of a
square-integrable function `ψ` with a class `U` is `∫ ⟪U, ψ⟫` (`L2.inner_toLp_eq_integral`).
-/

@[expose] public section

namespace MeasureTheory.L2

open scoped RealInnerProductSpace

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
theorem integral_norm_sq_eq_norm_sq (f : Lp E 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The pairing of the class of a square-integrable function `ψ` with `U` is `∫ ⟪U, ψ⟫`. -/
theorem inner_toLp_eq_integral {ψ : α → E} (hψ : MemLp ψ 2 μ) (U : Lp E 2 μ) :
    ⟪hψ.toLp ψ, U⟫ = ∫ x, ⟪U x, ψ x⟫ ∂μ := by
  rw [inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hψ.coeFn_toLp] with x hx
  rw [hx, real_inner_comm]

end MeasureTheory.L2
