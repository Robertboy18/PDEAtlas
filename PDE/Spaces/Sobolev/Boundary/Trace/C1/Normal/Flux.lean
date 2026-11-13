/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.AtlasIndependence

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Continuity

/-!
# Signed normal flux and surface integrability

The normal flux is the inner product with the intrinsic outward unit normal,
extended by zero away from the boundary. Continuity on the compact boundary
and finiteness of its surface measure prove signed integrability.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open Set MeasureTheory Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Signed outward flux, extended by zero away from the boundary. -/
def normalFlux (F : ℝ^(m + 1) → ℝ^(m + 1)) (x : ℝ^(m + 1)) : ℝ :=
  open Classical in
  if hx : x ∈ frontier Ω then inner ℝ (F x) (outwardUnitNormal ⟨x, hx⟩) else 0

/-- On the boundary the flux uses the outward unit normal. -/
theorem normalFlux_eq_inner (F : ℝ^(m + 1) → ℝ^(m + 1))
    {x : ℝ^(m + 1)} (hx : x ∈ frontier Ω) :
    normalFlux (Ω := Ω) F x = inner ℝ (F x) (outwardUnitNormal ⟨x, hx⟩) := by
  simp [normalFlux, hx]

omit hΩ in
/-- The entire signed flux function is independent of the operational atlas.
Consequently its surface integral is independent of that choice too. -/
theorem normalFlux_eq_of_atlases
    (A B : Boundary.C1ExtensionAtlas (m + 1) Ω) (F : ℝ^(m + 1) → ℝ^(m + 1)) :
    normalFlux (hΩ := A) F = normalFlux (hΩ := B) F := by
  funext x
  by_cases hx : x ∈ frontier Ω
  · rw [normalFlux_eq_inner (hΩ := A) _ hx, normalFlux_eq_inner (hΩ := B) _ hx,
      outwardUnitNormal_eq_of_atlases A B]
  · simp only [normalFlux, dite_eq_right hx]

/-- A continuous vector field has continuous normal flux along the boundary. -/
theorem continuousOn_normalFlux {F : ℝ^(m + 1) → ℝ^(m + 1)}
    (hF : ContinuousOn F (frontier Ω)) :
    ContinuousOn (normalFlux (Ω := Ω) F) (frontier Ω) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h := hF.domRestrict.inner (𝕜 := ℝ)
    (continuous_outwardUnitNormal (Ω := Ω))
  apply h.congr
  intro x
  exact (normalFlux_eq_inner F x.property).symm

/-- A continuous boundary vector field has integrable signed flux for
Hausdorff surface measure. Integrability is a conclusion, not supplied data. -/
theorem integrable_normalFlux {F : ℝ^(m + 1) → ℝ^(m + 1)}
    (hF : ContinuousOn F (frontier Ω)) :
    Integrable (normalFlux (Ω := Ω) F) (surfaceMeasure Ω) := by
  have hcompact : IsCompact (frontier Ω) :=
    hΩ.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have h := (continuousOn_normalFlux hF).integrableOn_compact
    (μ := surfaceMeasure Ω) hcompact
  simpa only [IntegrableOn, surfaceMeasure,
    Measure.restrict_restrict isClosed_frontier.measurableSet, Set.inter_self] using h

/-- Flux is additive in the vector field. -/
theorem normalFlux_add (F G : ℝ^(m + 1) → ℝ^(m + 1)) :
    normalFlux (Ω := Ω) (fun x ↦ F x + G x) =
      fun x ↦ normalFlux (Ω := Ω) F x + normalFlux (Ω := Ω) G x := by
  funext x
  by_cases hx : x ∈ frontier Ω <;> simp [normalFlux, hx, inner_add_left]

/-- A scalar cutoff multiplies the signed flux by its boundary value. -/
theorem normalFlux_smul (a : ℝ^(m + 1) → ℝ) (F : ℝ^(m + 1) → ℝ^(m + 1)) :
    normalFlux (Ω := Ω) (fun x ↦ a x • F x) =
      fun x ↦ a x * normalFlux (Ω := Ω) F x := by
  funext x
  by_cases hx : x ∈ frontier Ω <;> simp [normalFlux, hx, inner_smul_left]

/-- The normal flux commutes with finite sums of vector fields. -/
theorem normalFlux_sum {ι : Type*} [Fintype ι]
    (F : ι → ℝ^(m + 1) → ℝ^(m + 1)) :
    normalFlux (Ω := Ω) (fun x ↦ ∑ i, F i x) =
      fun x ↦ ∑ i, normalFlux (Ω := Ω) (F i) x := by
  funext x
  by_cases hx : x ∈ frontier Ω <;> simp [normalFlux, hx, sum_inner]

end SobolevSpace.Trace.C1
