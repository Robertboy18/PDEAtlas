/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import CAS.ExactTactic

/-!
# Reflection of the time axis

Reflection across a time `c` is the affine involution `t ↦ 2c - t`.
It preserves Lebesgue measure and transports local Bochner integrability.
These facts support endpoint extensions for weak evolutions on finite
intervals.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X]

/-- Reflection of the time axis across `c`.  This affine involution is the
standard extension device used to recover endpoint traces from an
open-interval weak evolution. -/
def reflectTime (c t : ℝ) : ℝ := 2 * c - t

/-- The centre of reflection is fixed. -/
@[simp]
theorem reflectTime_self (c : ℝ) : reflectTime c c = c := by
  simp only [reflectTime]
  ring

/-- Reflecting twice across the same time is the identity. -/
@[simp]
theorem reflectTime_involutive (c t : ℝ) :
    reflectTime c (reflectTime c t) = t := by
  simp [reflectTime]

/-- Reflection as a homeomorphism. -/
def reflectTimeHomeomorph (c : ℝ) : ℝ ≃ₜ ℝ :=
  Homeomorph.subLeft (2 * c)

/-- The homeomorphism `reflectTimeHomeomorph c` acts as `t ↦ 2c - t`. -/
@[simp]
theorem reflectTimeHomeomorph_apply (c t : ℝ) :
    reflectTimeHomeomorph c t = reflectTime c t := rfl

/-- Time reflection preserves Lebesgue measure. -/
theorem measurePreserving_reflectTime (c : ℝ) :
    MeasurePreserving (reflectTime c)
      (volume : Measure ℝ) (volume : Measure ℝ) := by
  change MeasurePreserving (fun t : ℝ ↦ 2 * c - t)
    (volume : Measure ℝ) (volume : Measure ℝ)
  exact volume.measurePreserving_sub_left (2 * c)

/-- Time reflection is smooth. -/
theorem contDiff_reflectTime (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (reflectTime c) := by
  exact contDiff_const.sub contDiff_id

/-- The derivative of time reflection is `-1`. -/
@[simp]
theorem deriv_reflectTime (c t : ℝ) : deriv (reflectTime c) t = -1 := by
  cas

/-- Pullback by time reflection transports local Bochner integrability to
the reflected open set. -/
theorem LocallyIntegrableOn.comp_reflectTime
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → X}
    (hf : LocallyIntegrableOn f U (volume : Measure ℝ)) (c : ℝ) :
    LocallyIntegrableOn (f ∘ reflectTime c) ((reflectTime c) ⁻¹' U)
      (volume : Measure ℝ) := by
  change LocallyIntegrableOn (f ∘ ⇑(reflectTimeHomeomorph c))
    ((reflectTimeHomeomorph c) ⁻¹' U) (volume : Measure ℝ)
  rw [MeasureTheory.locallyIntegrableOn_iff
    (hU.preimage (reflectTimeHomeomorph c).continuous).isLocallyClosed]
  intro K hKU hK
  let e := reflectTimeHomeomorph c
  have heK : e '' K ⊆ U := by
    intro y hy
    obtain ⟨x, hxK, rfl⟩ := hy
    exact hKU hxK
  have hfK : IntegrableOn f (e '' K) (volume : Measure ℝ) :=
    hf.integrableOn_compact_subset heK (hK.image e.continuous)
  have hpull := (measurePreserving_reflectTime c).integrableOn_comp_preimage
    e.toMeasurableEquiv.measurableEmbedding (f := f) (s := e '' K)
  have hpre : e ⁻¹' (e '' K) = K := e.toEquiv.preimage_image K
  have he : (e : ℝ → ℝ) = reflectTime c := rfl
  have hpull' : IntegrableOn (f ∘ e) (e ⁻¹' (e '' K))
      (volume : Measure ℝ) := by
    rw [he]
    exact hpull.2 hfK
  rwa [hpre] at hpull'

end PDE.Analysis.Evolution
