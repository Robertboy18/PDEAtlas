/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core

/-!
# Translations and mollification

Translation commutes with convolution by a fixed mollifier. Subtracting the original
function gives the corresponding identity for increments. This lets fractional
Sobolev estimates use the same `Lᵖ` convolution bounds as integer-order derivatives.
-/

@[expose] public section

open MeasureTheory

namespace SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Translating the input translates its mollification by the same vector. -/
theorem mollifyVector_comp_sub_right (μ : Mollifier n) (ε : ℝ)
    (f : ℝ^n → F) (h : ℝ^n) :
    mollifyVector μ ε (fun x ↦ f (x - h)) =
      fun x ↦ mollifyVector μ ε f (x - h) := by
  funext x
  simp only [mollifyVector, convolution_def, sub_right_comm]

/-- Mollification commutes with increments of a locally integrable function. -/
theorem mollifyVector_sub_translate (μ : Mollifier n) {ε : ℝ}
    {f : ℝ^n → F} (hf : LocallyIntegrable f) (h : ℝ^n) :
    mollifyVector μ ε (fun x ↦ f (x - h) - f x) =
      fun x ↦ mollifyVector μ ε f (x - h) - mollifyVector μ ε f x := by
  have hshift : LocallyIntegrable (fun x ↦ f (x - h)) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hKint := hf.integrableOn_isCompact (hK.image (continuous_id.add_const (-h)))
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_right volume (-h)).integrableOn_image
        (MeasurableEquiv.addRight (-h)).measurableEmbedding |>.mp hKint
  change mollifyVector μ ε ((fun x ↦ f (x - h)) - f) = _
  rw [mollifyVector_sub_of_pos μ _ _ hshift hf, mollifyVector_comp_sub_right]
  rfl

end SobolevSpace.Approximation
