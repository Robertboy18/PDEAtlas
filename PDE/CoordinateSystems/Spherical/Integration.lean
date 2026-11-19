/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import PDE.CoordinateSystems.RadialCompactification
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Spherical integration and radial compactification

The angular measure is the sphere measure induced by Euclidean volume.
Mathlib's measure-preserving sphere–radius homeomorphism gives the full
three-dimensional integration formula. Compactifying its radial variable
then gives an exact squared-norm identity with the physical scale cubed.
No regularity at the excluded origin or radial endpoint is required.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Metric
open scoped ENNReal

/-- Euclidean volume decomposes as sphere measure times `r² dr`.
This nonnegative integral formula includes infinite integrals. -/
theorem lintegral_spherical {f : ℝ^3 → ℝ≥0∞} (hf : AEMeasurable f volume) :
    (∫⁻ x, f x) = ∫⁻ ω : sphere (0 : ℝ^3) 1,
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * f (r • (ω : ℝ^3))
        ∂volume ∂(volume : Measure (ℝ^3)).toSphere := by
  let e := homeomorphUnitSphereProd (ℝ^3)
  have hp := (volume : Measure (ℝ^3)).measurePreserving_homeomorphUnitSphereProd
  have hps := hp.symm e.toMeasurableEquiv
  have hfsub : AEMeasurable (fun x : ({(0 : ℝ^3)}ᶜ : Set (ℝ^3)) ↦ f x)
      (volume.comap Subtype.val) :=
    (aemeasurable_restrict_iff_comap_subtype (measurableSet_singleton _).compl).mp hf.restrict
  have hG : AEMeasurable (fun p ↦ f (e.symm p))
      ((volume : Measure (ℝ^3)).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa [e, Function.comp_def] using
      (hps.aemeasurable_comp_iff e.symm.measurableEmbedding).mpr hfsub
  calc
    (∫⁻ x, f x) = ∫⁻ x : ({(0 : ℝ^3)}ᶜ : Set (ℝ^3)), f x
        ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0 : ℝ^3) 1 × Ioi (0 : ℝ), f (e.symm p)
        ∂((volume : Measure (ℝ^3)).toSphere.prod (Measure.volumeIoiPow 2)) := by
      simpa [e] using
        (hps.lintegral_comp_emb e.symm.measurableEmbedding (fun x ↦ f x)).symm
    _ = ∫⁻ ω : sphere (0 : ℝ^3) 1, ∫⁻ r : Ioi (0 : ℝ), f (r.val • ω.val)
        ∂Measure.volumeIoiPow 2 ∂(volume : Measure (ℝ^3)).toSphere := by
      rw [lintegral_prod _ hG]
      simp only [e, homeomorphUnitSphereProd_symm_apply_coe]
    _ = _ := by
      apply lintegral_congr
      intro ω
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul_non_measurable]
      · exact lintegral_subtype_comap measurableSet_Ioi
          (fun r ↦ ENNReal.ofReal (r ^ 2) * f (r • (ω : ℝ^3)))
      · fun_prop
      · exact Filter.Eventually.of_forall fun r ↦ ENNReal.ofReal_lt_top

/-- Physical-space squared norm in compactified sphere–radius coordinates.
The full angular measure is retained, so no quadrant normalization is implicit. -/
theorem lintegral_sq_norm_comp_scaled_tan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {κ : ℝ} (hκ : 0 < κ) {f : ℝ^3 → E}
    (hf : AEStronglyMeasurable f volume) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) =
      ENNReal.ofReal (κ ^ 3) *
        ∫⁻ ω : sphere (0 : ℝ^3) 1, ∫⁻ β in Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal
            (‖(Real.sin β / Real.cos β ^ 2) • f ((κ * Real.tan β) • (ω : ℝ^3))‖ ^ 2)
          ∂volume ∂(volume : Measure (ℝ^3)).toSphere := by
  rw [lintegral_spherical (hf.norm.aemeasurable.pow_const 2).ennreal_ofReal]
  calc
    _ = ∫⁻ ω : sphere (0 : ℝ^3) 1, ∫⁻ β in Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (κ ^ 3 *
          ‖(Real.sin β / Real.cos β ^ 2) • f ((κ * Real.tan β) • (ω : ℝ^3))‖ ^ 2)
        ∂volume ∂(volume : Measure (ℝ^3)).toSphere := by
      apply lintegral_congr
      intro ω
      simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      exact lintegral_radial_sq_norm_comp_scaled_tan hκ (fun r ↦ f (r • (ω : ℝ^3)))
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (pow_nonneg hκ.le 3),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end PDE.CoordinateSystems.Spherical
