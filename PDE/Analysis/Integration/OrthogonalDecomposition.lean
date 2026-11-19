/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Integration along orthogonal subspaces

Writing a vector as the sum of its components in `K` and `Kᗮ` preserves
Lebesgue measure. Fubini's theorem therefore expresses an ambient integral as
an iterated integral over these two subspaces, each with its induced Euclidean
volume.

The ordinary product carries the supremum norm. Mathlib's orthogonal
decomposition instead takes values in the `L²` product, where it is an
isometry. The measure-preserving identification between these products lets
Mathlib's product integration lemmas apply without changing the volume.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def orthogonalSum (K : Submodule ℝ E) : K × Kᗮ ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 (K × Kᗮ)).trans
    K.orthogonalDecomposition.symm.toMeasurableEquiv

private theorem orthogonalSum_apply (K : Submodule ℝ E) (p : K × Kᗮ) :
    orthogonalSum K p = (p.1 : E) + (p.2 : E) := by
  simp [orthogonalSum, Submodule.orthogonalDecomposition_symm_apply]

private theorem orthogonalSum_measurePreserving (K : Submodule ℝ E) :
    MeasurePreserving (orthogonalSum K) :=
  (WithLp.volume_preserving_toLp K Kᗮ).trans
    K.orthogonalDecomposition.symm.measurePreserving

variable [NormedAddCommGroup F]

/-- An integrable function remains integrable after writing its argument
as the sum of two orthogonal components. -/
theorem integrable_add_orthogonal (K : Submodule ℝ E) {f : E → F}
    (hf : Integrable f) :
    Integrable (fun p : K × Kᗮ ↦ f ((p.1 : E) + (p.2 : E))) := by
  simpa only [Function.comp_def, orthogonalSum_apply] using
    (orthogonalSum_measurePreserving K).integrable_comp_of_integrable hf

variable [NormedSpace ℝ F]

/-- Fubini's theorem for any orthogonal decomposition of a finite-dimensional
real inner product space. There is no Jacobian factor. -/
theorem integral_add_orthogonal (K : Submodule ℝ E) {f : E → F}
    (hf : Integrable f) :
    (∫ x, f x) = ∫ x : K, ∫ y : Kᗮ, f ((x : E) + (y : E)) := by
  calc
    (∫ x, f x) = ∫ p : K × Kᗮ, f ((p.1 : E) + (p.2 : E)) := by
      simpa only [orthogonalSum_apply] using
        ((orthogonalSum_measurePreserving K).integral_comp' f).symm
    _ = _ := integral_prod _ (integrable_add_orthogonal K hf)

end PDE.Analysis
