/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHigherTailDerivatives

/-!
# Separated Newtonian derivatives from source L¹

A source separated from the evaluation point has no kernel singularity there.
The explicit kernel derivative bound therefore controls each derivative
integral by the source's L¹ norm. Keeping all derivatives on the kernel gives
the distance power needed when comparing different source and output annuli.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter

namespace PotentialTheory

/-- A positive separation distance bounds every mixed kernel integral by the
source L¹ norm. Its absolute convergence follows from the same estimate. -/
theorem integrable_and_norm_integral_fundamentalSolution_five_derivative_le_of_separated
    (g : ℝ^5 → ℝ) (hg : Integrable g) (indices : List (Fin 5))
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0) :
    Integrable (fun Y : ℝ^5 ↦
      iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y) * g Y) ∧
      ‖∫ Y : ℝ^5,
        iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y) * g Y‖ ≤
        (fiveDimensionalHigherKernelConstant indices.length / r ^ (indices.length + 3)) *
          ∫ Y : ℝ^5, ‖g Y‖ := by
  let F : ℝ^5 → ℝ := fun Y ↦
    iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y) * g Y
  let C := fiveDimensionalHigherKernelConstant indices.length / r ^ (indices.length + 3)
  have hmeas : AEStronglyMeasurable F volume :=
    (((measurable_iteratedPartialDeriv_fiveDimensionalGamma indices).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
        hg.aestronglyMeasurable
  have hbound (Y : ℝ^5) : ‖F Y‖ ≤ C * ‖g Y‖ := by
    by_cases hY : g Y = 0
    · simp only [F, hY, mul_zero, norm_zero, le_refl]
    have haway : r ≤ ‖X - Y‖ := by
      by_contra h
      apply hY
      apply hzero Y
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev Y X] using lt_of_not_ge h
    have hpos : 0 < ‖X - Y‖ := hr.trans_le haway
    have hkernel :
        |iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y)| ≤ C := by
      calc
        _ ≤ fiveDimensionalHigherKernelConstant indices.length /
            ‖X - Y‖ ^ (indices.length + 3) :=
          abs_iteratedPartialDeriv_fundamentalSolution_five_le indices (X - Y)
            (norm_ne_zero_iff.mp hpos.ne')
        _ ≤ C := by
          have hC := fiveDimensionalHigherKernelConstant_pos indices.length
          dsimp only [C]
          gcongr
    calc
      ‖F Y‖ =
          |iteratedPartialDeriv indices (fundamentalSolution 5) (X - Y)| * ‖g Y‖ := by
        simp only [F, norm_mul, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_right hkernel (norm_nonneg _)
  have hF : Integrable F :=
    (hg.norm.const_mul C).mono' hmeas (Eventually.of_forall hbound)
  refine ⟨hF, ?_⟩
  calc
    ‖∫ Y : ℝ^5, F Y‖ ≤ ∫ Y : ℝ^5, ‖F Y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ Y : ℝ^5, C * ‖g Y‖ :=
      integral_mono hF.norm (hg.norm.const_mul C) hbound
    _ = _ := integral_const_mul _ _

end PotentialTheory
