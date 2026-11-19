/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import CAS.ExactTactic

/-!
# The square of an integral over a finite measure

On a finite measure space the Cauchy–Schwarz inequality against the constant function `1`
bounds the square of an integral by the mass of the measure times the integral of the square.
The results are standard and follow no particular source.

## Main results

* `MeasureTheory.sq_integral_le_measureReal_mul_integral_sq`: `(∫ q dμ)² ≤ μ (univ) ∫ q² dμ`
  for every finite measure `μ` and every real `q` in `L² (μ)`. It is
  `MeasureTheory.integral_abs_mul_le_sqrt_integral_sq` for the functions `q` and `1`.
* `MeasureTheory.sq_norm_integral_le_measureReal_mul_integral_sq_norm`:
  `‖∫ f dμ‖² ≤ μ (univ) ∫ ‖f‖² dμ` for every `f` in `L² (μ)` with values in a real normed
  space.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- The Cauchy–Schwarz inequality for a finite measure: `(∫ q dμ)² ≤ μ (univ) ∫ q² dμ` for `q`
in `L² (μ)`. -/
theorem sq_integral_le_measureReal_mul_integral_sq {q : α → ℝ} (hq : MemLp q 2 μ) :
    (∫ x, q x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, q x ^ 2 ∂μ := by
  have hcs := integral_abs_mul_le_sqrt_integral_sq hq (memLp_const (1 : ℝ))
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at hcs
  have hA : 0 ≤ ∫ x, q x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  have hs := pow_le_pow_left₀ (abs_nonneg _) (abs_integral_le_integral_abs.trans hcs) 2
  cas using [hs, sq_abs (∫ x, q x ∂μ), Real.sq_sqrt hA,
    Real.sq_sqrt (measureReal_nonneg (μ := μ) (s := univ))]

/-- The Cauchy–Schwarz inequality for a finite measure and values in a normed space:
`‖∫ f dμ‖² ≤ μ (univ) ∫ ‖f‖² dμ` for `f` in `L² (μ)`. -/
theorem sq_norm_integral_le_measureReal_mul_integral_sq_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm f) 2).trans
    (sq_integral_le_measureReal_mul_integral_sq hf.norm)

end MeasureTheory
