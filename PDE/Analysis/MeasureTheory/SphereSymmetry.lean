/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Symmetry of the polar sphere measure

Lebesgue measure on a finite-dimensional real inner product space `E` is
invariant under linear isometries. The invariance lifts to the
angular measure `(volume : Measure E).toSphere` on the unit sphere used in polar
coordinates: every linear isometry
`e : E ≃ₗᵢ[ℝ] E` restricts to a measure-preserving map of the unit sphere.

The proof goes through the definition of `Measure.toSphere`: the measure of a
set `s` on the sphere is a fixed multiple of the volume of the radial cone
`(0,1) • s`, and `e` carries the cone over `e⁻¹ s` onto the cone over `s`.

## Main results

* `measurableSet_radialCone`: the cone `(0,1) • s` over a measurable subset
  `s` of the unit sphere is measurable.
* `sphereLinearIsometryEquiv`: restriction of `e` to the unit sphere as a
  measurable equivalence.
* `LinearIsometryEquiv.measurePreserving_toSphere`: this restriction preserves
  `volume.toSphere`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped Pointwise

noncomputable section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- A measurable subset of the unit sphere generates a measurable radial cone
with radii in `(0,1)`. -/
theorem measurableSet_radialCone
    {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
  let h := homeomorphUnitSphereProd E
  let R : Set (Ioi (0 : ℝ)) := Iio ⟨1, by norm_num⟩
  have hprod : MeasurableSet (s ×ˢ R) := hs.prod measurableSet_Iio
  have hpre : MeasurableSet (h ⁻¹' (s ×ˢ R)) := h.measurable hprod
  have hcoe : MeasurableEmbedding
      (Subtype.val : (({0}ᶜ : Set E)) → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  have himage : MeasurableSet
      ((Subtype.val : (({0}ᶜ : Set E)) → E) '' (h ⁻¹' (s ×ˢ R))) :=
    hcoe.measurableSet_image' hpre
  rw [show ((Subtype.val : (({0}ᶜ : Set E)) → E) '' (h ⁻¹' (s ×ˢ R))) =
      Ioo (0 : ℝ) 1 • ((↑) '' s : Set E) by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      let ω := (h y).1
      let r := (h y).2
      have hω : ω ∈ s := hy.1
      have hr : (r : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨r.property, hy.2⟩
      refine ⟨r, hr, (ω : E), ⟨ω, hω, rfl⟩, ?_⟩
      simpa [h, r, ω] using
        (homeomorphUnitSphereProd_symm_apply_coe E (h y)).symm
    · rintro ⟨r, hr, _x, ⟨ω, hω, rfl⟩, rfl⟩
      have hr0 : r • (ω : E) ≠ 0 :=
        smul_ne_zero hr.1.ne' (ne_zero_of_mem_sphere one_ne_zero ω)
      let y : (({0}ᶜ : Set E)) := ⟨r • (ω : E), hr0⟩
      refine ⟨y, ?_, rfl⟩
      have hhy : h y = (ω, ⟨r, hr.1⟩) := by
        apply h.symm.injective
        rw [h.symm_apply_apply]
        apply Subtype.ext
        exact
          (homeomorphUnitSphereProd_symm_apply_coe E (ω, ⟨r, hr.1⟩)).symm
      change h y ∈ s ×ˢ R
      rw [hhy]
      exact ⟨hω, hr.2⟩] at himage
  exact himage

/-- Restriction of a linear isometry to the unit sphere as a measurable
equivalence. -/
def sphereLinearIsometryEquiv (e : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 where
  toEquiv :=
    { toFun := fun ω ↦
        ⟨e ω, by simp⟩
      invFun := fun ω ↦
        ⟨e.symm ω, by simp⟩
      left_inv := fun ω ↦ by apply Subtype.ext; simp
      right_inv := fun ω ↦ by apply Subtype.ext; simp }
  measurable_toFun := by
    apply Continuous.measurable
    apply Continuous.subtype_mk
    exact e.continuous.comp continuous_subtype_val
  measurable_invFun := by
    apply Continuous.measurable
    apply Continuous.subtype_mk
    exact e.symm.continuous.comp continuous_subtype_val

omit [FiniteDimensional ℝ E] in
/-- The restricted isometry acts on points of the sphere by the underlying map `e`. -/
@[simp]
theorem sphereLinearIsometryEquiv_coe
    (e : E ≃ₗᵢ[ℝ] E) (ω : sphere (0 : E) 1) :
    ((sphereLinearIsometryEquiv e ω : sphere (0 : E) 1) : E) = e ω := rfl

/-- Every linear isometry preserves the angular measure induced from
Lebesgue volume by `Measure.toSphere`. -/
theorem LinearIsometryEquiv.measurePreserving_toSphere (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereLinearIsometryEquiv e)
      (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨(sphereLinearIsometryEquiv e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereLinearIsometryEquiv e).measurable hs]
  rw [Measure.toSphere_apply' _ ((sphereLinearIsometryEquiv e).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone :
      Ioo (0 : ℝ) 1 •
          ((↑) '' ((sphereLinearIsometryEquiv e) ⁻¹' s) : Set E) =
        e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
    ext x
    constructor
    · rintro ⟨r, hr, _w, ⟨ω, hω, rfl⟩, rfl⟩
      change sphereLinearIsometryEquiv e ω ∈ s at hω
      refine ⟨r, hr, e ω,
        ⟨sphereLinearIsometryEquiv e ω, hω, rfl⟩, ?_⟩
      simp
    · intro hx
      rcases hx with ⟨r, hr, _w, ⟨ω, hω, rfl⟩, heq⟩
      have hx : x = r • e.symm (ω : E) := by
        apply e.injective
        simpa using heq.symm
      rw [hx]
      let η : sphere (0 : E) 1 :=
        ⟨e.symm ω, by simp⟩
      refine ⟨r, hr, (η : E), ⟨η, ?_, rfl⟩, rfl⟩
      change sphereLinearIsometryEquiv e η ∈ s
      simpa [η, sphereLinearIsometryEquiv] using hω
  rw [hcone]
  exact e.measurePreserving.measure_preimage
    (measurableSet_radialCone hs).nullMeasurableSet

end MeasureTheory
