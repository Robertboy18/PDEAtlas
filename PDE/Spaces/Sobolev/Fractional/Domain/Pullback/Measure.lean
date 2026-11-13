/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure distortion for fractional chart pullbacks

An upper bound `D` for the absolute determinant of the inverse chart bounds the
pushforward of restricted volume by `D` times target volume. Applying the estimate
to both variables gives `D²` for the intrinsic Gagliardo double integral.
The estimate is derived from Mathlib's Jacobian theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SobolevSpace.Fractional.Pullback

variable {n : ℕ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {D : ℝ≥0}

/-- An inverse Jacobian majorant controls the volume distortion of a chart. -/
theorem map_restrict_le_of_det_le
    (hE : Measurable (fun x ↦ E x))
    (hSymm : Differentiable ℝ (fun x ↦ E.symm x))
    (hD : ∀ y ∈ E.target, |(fderiv ℝ (fun z ↦ E.symm z) y).det| ≤ D) :
    Measure.map E (volume.restrict E.source) ≤
      (D : ℝ≥0∞) • volume.restrict E.target := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hE hA, Measure.restrict_apply (hA.preimage hE),
    Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  have hset : E ⁻¹' A ∩ E.source = E.symm '' (A ∩ E.target) := by
    ext x
    constructor
    · rintro ⟨hxA, hxS⟩
      exact ⟨E x, ⟨hxA, E.map_source hxS⟩, E.left_inv hxS⟩
    · rintro ⟨y, ⟨hyA, hyT⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, E.right_inv hyT] using hyA, E.map_target hyT⟩
  rw [hset]
  calc
    volume (E.symm '' (A ∩ E.target)) ≤
        ∫⁻ y in A ∩ E.target, ENNReal.ofReal
          |(fderiv ℝ (fun z ↦ E.symm z) y).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume
        (hA.inter E.open_target.measurableSet)
        (fun _ _ ↦ hSymm.differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _ in A ∩ E.target, (D : ℝ≥0∞) := by
      apply setLIntegral_mono' (hA.inter E.open_target.measurableSet)
      intro y hy
      exact (ENNReal.ofReal_le_ofReal (hD y hy.2)).trans_eq (by simp)
    _ = (D : ℝ≥0∞) * volume (A ∩ E.target) := by simp

/-- Product pullback incurs the volume distortion once for each variable. -/
theorem map_gagliardoProductMeasure_le
    (hE : Measurable (fun x ↦ E x))
    (hD : Measure.map E (volume.restrict E.source) ≤
      (D : ℝ≥0∞) • volume.restrict E.target) :
    Measure.map (Prod.map E E) (gagliardoProductMeasure n E.source) ≤
      (D : ℝ≥0∞) ^ 2 • gagliardoProductMeasure n E.target := by
  unfold gagliardoProductMeasure
  rw [← Measure.map_prod_map _ _ hE hE]
  calc
    _ ≤ ((D : ℝ≥0∞) • volume.restrict E.target).prod
        ((D : ℝ≥0∞) • volume.restrict E.target) := Measure.prod_mono hD hD
    _ = _ := by rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_two]

/-- Integrating a pullback costs at most the pushforward measure majorant. -/
theorem lintegral_comp_le_of_map_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} {C : ℝ≥0∞}
    (hf : Measurable f) (hC : Measure.map f μ ≤ C • ν)
    {g : β → ℝ≥0∞} (hg : AEMeasurable g ν) :
    ∫⁻ x, g (f x) ∂μ ≤ C * ∫⁻ y, g y ∂ν := by
  have hgm := hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hC)
  rw [← lintegral_map' hgm hf.aemeasurable]
  exact (lintegral_mono' hC le_rfl).trans_eq (lintegral_smul_measure C g)

end SobolevSpace.Fractional.Pullback
