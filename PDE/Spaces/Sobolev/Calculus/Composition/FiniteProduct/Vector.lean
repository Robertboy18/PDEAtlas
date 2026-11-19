/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Domain

/-!
# Vector-valued Sobolev composition

Apply the scalar chain rule to each coordinate of a map between Euclidean
spaces. The resulting field is still a finite family of scalar Sobolev
fields; its value and derivative columns assemble into the usual vector chain
rule.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n m l : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
  [IsFiniteMeasure (domainMeasure n Ω)] {G : ℝ^m → ℝ^l} {C : ℝ≥0}

private theorem coordinate_fderiv (hG : ContDiff ℝ 1 G) (j : Fin l) (z : ℝ^m) :
    fderiv ℝ (fun x ↦ G x j) z =
      (EuclideanSpace.proj j).comp (fderiv ℝ G z) :=
  (((EuclideanSpace.proj j : ℝ^l →L[ℝ] ℝ).hasFDerivAt).comp z
    ((hG.differentiable one_ne_zero).differentiableAt.hasFDerivAt)).fderiv

/-- A bound for a vector derivative bounds each scalar coordinate derivative.
The coordinate projection contributes its operator norm. -/
theorem norm_fderiv_coordinate_le (hG : ContDiff ℝ 1 G)
    (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C) (j : Fin l) (z : ℝ^m) :
    ‖fderiv ℝ (fun x ↦ G x j) z‖ ≤
      (‖(EuclideanSpace.proj j : ℝ^l →L[ℝ] ℝ)‖₊ * C : ℝ≥0) := by
  rw [coordinate_fderiv hG j z]
  exact ((EuclideanSpace.proj j : ℝ^l →L[ℝ] ℝ).opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _))

/-- Compose a finite Sobolev family with a vector-valued `C¹` map whose
derivative is bounded. The open domain has finite measure and an extension
operator. -/
def vectorCompositionOnOfExtension (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) : Fin l → W^{1,p}(Ω) :=
  fun j ↦ compositionOnOfExtension hΩ E hp
    ((EuclideanSpace.proj j : ℝ^l →L[ℝ] ℝ).contDiff.comp hG)
    (norm_fderiv_coordinate_le hG hbound j) U

/-- Vector composition has the expected value almost everywhere. -/
theorem vectorCompositionOnOfExtension_values_ae (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) :
    values (vectorCompositionOnOfExtension hΩ E hp hG hbound U)
      =ᵐ[domainMeasure n Ω] fun x ↦ G (values U x) := by
  have h := ae_all_iff.mpr fun j ↦ compositionOnOfExtension_base_ae hΩ E hp
    ((EuclideanSpace.proj j : ℝ^l →L[ℝ] ℝ).contDiff.comp hG)
    (norm_fderiv_coordinate_le hG hbound j) U
  filter_upwards [h] with x hx
  ext j
  exact hx j

/-- Each weak derivative column satisfies the vector chain rule. -/
theorem vectorCompositionOnOfExtension_derivatives_ae (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) (i : Fin n) :
    derivatives (vectorCompositionOnOfExtension hΩ E hp hG hbound U) i
      =ᵐ[domainMeasure n Ω] fun x ↦ fderiv ℝ G (values U x) (derivatives U i x) := by
  have h := ae_all_iff.mpr fun j ↦ compositionOnOfExtension_derivative_ae hΩ E hp
    ((EuclideanSpace.proj j : ℝ^l →L[ℝ] ℝ).contDiff.comp hG)
    (norm_fderiv_coordinate_le hG hbound j) U i
  filter_upwards [h] with x hx
  ext j
  exact (hx j).trans (congrArg (fun T : ℝ^m →L[ℝ] ℝ ↦ T (derivatives U i x))
    (coordinate_fderiv hG j (values U x)))

end SobolevSpace.GraphSpace.FiniteProductComposition
