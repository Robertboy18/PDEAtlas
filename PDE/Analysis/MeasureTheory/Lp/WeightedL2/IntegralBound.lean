/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.Moment

/-!
# An integral bound from weighted square integrability

Split the integrand into `f √w` and `1 / √w`. Their squared integrals give
the two factors in Cauchy–Schwarz. This is the shared
estimate behind classical and weak weighted fundamental theorems of calculus.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A finite reciprocal-weight integral and finite weighted square integral
control the integral of a function. Positivity is needed only almost everywhere. -/
theorem abs_integral_le_weighted_sqrt
    {f w : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hw : AEStronglyMeasurable w μ)
    (hpos : ∀ᵐ x ∂μ, 0 < w x)
    (hinverse : Integrable (fun x ↦ 1 / w x) μ)
    (henergy : Integrable (fun x ↦ f x ^ 2 * w x) μ) :
    |∫ x, f x ∂μ| ≤ √(∫ x, 1 / w x ∂μ) * √(∫ x, f x ^ 2 * w x ∂μ) := by
  have hn : MemLp (fun x ↦ (1 : ℝ) / √(w x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (aestronglyMeasurable_const.div₀
        (Real.continuous_sqrt.comp_aestronglyMeasurable hw))).mpr
    refine hinverse.congr ?_
    filter_upwards [hpos] with x hx
    change 1 / w x = (1 / √(w x)) ^ 2
    simp only [div_pow, one_pow, Real.sq_sqrt hx.le]
  have hfw := memLp_mul_sqrt_of_integrable_weighted_sq_ae
    hf hw (hpos.mono fun _ hx ↦ hx.le) henergy
  simpa only [one_mul, one_pow] using abs_integral_mul_le_weighted_sqrt hpos hn hfw

end MeasureTheory
