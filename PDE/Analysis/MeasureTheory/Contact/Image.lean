/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure controlled by a contact image

A measurable source set with bounded Jacobian cannot cover a vertex set of
larger measure than its Jacobian bound times the source measure. Mathlib's
noninjective image inequality applies directly; neither injectivity nor
measurability of the image is an input.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory MeasureTheory.Measure Set

/-- A derivative bound converts coverage by an image into a lower bound on the
source measure. The measure of the image is its outer measure. -/
theorem measure_le_mul_measure_of_subset_differentiable_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    {F : E → E} {F' : E → E →L[ℝ] E} {S Y : Set E} {D : ℝ}
    (hS : MeasurableSet S) (hF : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    (hcover : Y ⊆ F '' S) (hdet : ∀ x ∈ S, |(F' x).det| ≤ D) :
    μ Y ≤ ENNReal.ofReal D * μ S := by
  calc
    μ Y ≤ μ (F '' S) := measure_mono hcover
    _ ≤ ∫⁻ x in S, ENNReal.ofReal |(F' x).det| ∂μ :=
      addHaar_image_le_lintegral_abs_det_fderiv μ hS hF
    _ ≤ ∫⁻ _ in S, ENNReal.ofReal D ∂μ :=
      setLIntegral_mono' hS (fun x hx ↦ ENNReal.ofReal_le_ofReal (hdet x hx))
    _ = ENNReal.ofReal D * μ S := by rw [setLIntegral_const]

end PDE.Analysis
