/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Radial integrals under an injective linear parametrization

An injective map into a larger inner product space preserves radial integrals after weighting
by its metric determinant. Orthonormal coordinates on its range reduce the claim to the
ordinary square change-of-variables formula; the map need not be an isometry.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An injective map has a square coordinate representation with the same norms and
absolute determinant equal to the original metric determinant. -/
theorem exists_linearEquiv_norm_eq_norm (T : E →ₗ[ℝ] F) (hT : Function.Injective T) :
    ∃ B : E ≃ₗ[ℝ] E, (∀ v, ‖B v‖ = ‖T v‖) ∧ |B.toLinearMap.det| = T.normDet := by
  have hker : T.ker = ⊥ := ker_eq_bot.mpr hT
  have hrank : Module.finrank ℝ T.range = Module.finrank ℝ E :=
    (T.normDet_ne_zero_tfae.out 2 3).mp hker
  obtain ⟨bv⟩ := (T.normDet_ne_zero_tfae.out 2 4).mp hker
  let g : E ≃ₗᵢ[ℝ] T.range := (stdOrthonormalBasis ℝ E).equiv bv (Equiv.refl _)
  let B : E ≃ₗ[ℝ] E := (LinearEquiv.ofInjective T hT).trans g.symm.toLinearEquiv
  refine ⟨B, ?_, ?_⟩
  · intro v
    exact g.symm.norm_map (T.rangeRestrict v)
  · rw [← normDet_eq_abs_det]
    change (g.symm.toLinearIsometry.toLinearMap.comp T.rangeRestrict).normDet = _
    rw [normDet_comp_of_finrank_eq _ _ hrank.symm,
      g.symm.toLinearIsometry.normDet_eq_one, one_mul]
    exact normDet_codRestrict _

variable [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]

/-- Radial integrals use the metric determinant for an injective parametrization into a
larger inner product space. No orthogonality of the chosen coordinates is required. -/
theorem integral_normDet_mul_comp_norm (T : E →ₗ[ℝ] F) (hT : Function.Injective T)
    (f : ℝ → ℝ) :
    (∫ v : E, T.normDet * f ‖T v‖) = ∫ v : E, f ‖v‖ := by
  obtain ⟨B, hnorm, hdet⟩ := exists_linearEquiv_norm_eq_norm T hT
  let C := B.toContinuousLinearEquiv
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    MeasurableSet.univ (fun x _ ↦ C.hasFDerivAt.hasFDerivWithinAt)
    C.injective.injOn (fun v : E ↦ f ‖v‖)
  have himage : C '' Set.univ = Set.univ := Set.image_univ_of_surjective C.surjective
  rw [himage, Measure.restrict_univ] at h
  change (∫ v : E, f ‖v‖) = ∫ v : E, |B.toLinearMap.det| * f ‖B v‖ at h
  simpa only [hdet, hnorm] using h.symm

end LinearMap
