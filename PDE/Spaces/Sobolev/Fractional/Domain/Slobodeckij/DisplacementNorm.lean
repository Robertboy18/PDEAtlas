/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Displacement
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Energy
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The fractional seminorm through translation increments

For finite positive `p`, the fractional energy is the weighted integral of the
`Lᵖ` norms of `u(· - h) - u`. This form lets a bound on each translation increment
be integrated without making any regularity assumption on the displacement.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
private theorem eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → F} (hf : AEStronglyMeasurable f ν) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm f p ν ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_pos hp0 hp).ne', ENNReal.rpow_one]

/-- The fractional energy is the weighted integral of the translation-increment
`Lᵖ` energies. The formula also holds when either side is infinite. -/
theorem eLpNorm_diffQuot_rpow_eq_lintegral_displacement {u : ℝ^n → F}
    (hu : AEStronglyMeasurable u volume) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm (diffQuot n s u (p := p)) p (gagliardoProductMeasure n Set.univ) ^
        p.toReal =
      ∫⁻ h : ℝ^n, ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + s * p.toReal))) *
        eLpNorm (fun x ↦ u (x - h) - u x) p volume ^ p.toReal := by
  have humeas : AEStronglyMeasurable u (volume.restrict Set.univ) := by
    simpa only [Measure.restrict_univ] using hu
  rw [eLpNorm_rpow_eq (aestronglyMeasurable_diffQuot humeas) hp0 hp]
  simp_rw [enorm_diffQuot_rpow u _ hp0 hp]
  simp only [gagliardoProductMeasure, Measure.restrict_univ]
  rw [lintegral_enorm_sub_div_eq_weighted_displacement hu (ENNReal.toReal_pos hp0 hp)]
  apply lintegral_congr
  intro h
  have hshift : AEStronglyMeasurable (fun x ↦ u (x - h)) volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hu.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (-h)).quasiMeasurePreserving
  have hdiff : AEStronglyMeasurable (fun x ↦ u (x - h) - u x) volume :=
    hshift.sub hu
  rw [eLpNorm_rpow_eq hdiff hp0 hp]
  simp_rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
    (ENNReal.toReal_nonneg)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [NormedSpace ℝ F] in
/-- The increment energy is measurable as a function of the displacement,
even when the original function is only a.e. strongly measurable. -/
theorem aemeasurable_eLpNorm_sub_translate_rpow {u : ℝ^n → F}
    (hu : AEStronglyMeasurable u volume) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    AEMeasurable (fun h : ℝ^n ↦
      eLpNorm (fun x ↦ u (x - h) - u x) p volume ^ p.toReal) volume := by
  have heq (h : ℝ^n) :
      eLpNorm (fun x ↦ u (x - h) - u x) p volume ^ p.toReal =
        ∫⁻ x : ℝ^n, ‖u (x - h) - u x‖ₑ ^ p.toReal := by
    apply eLpNorm_rpow_eq _ hp0 hp
    have hshift : AEStronglyMeasurable (fun x ↦ u (x - h)) volume := by
      simpa only [sub_eq_add_neg, Function.comp_def] using
        hu.comp_quasiMeasurePreserving
          (measurePreserving_add_right volume (-h)).quasiMeasurePreserving
    exact hshift.sub hu
  simp_rw [heq]
  have hshift := hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
  exact (hshift.sub hu.comp_fst).enorm.pow_const p.toReal |>.lintegral_prod_left'

end SobolevSpace.Fractional
