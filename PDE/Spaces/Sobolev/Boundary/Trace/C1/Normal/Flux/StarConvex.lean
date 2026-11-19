/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Flux
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.StarConvex

/-!
# Nonnegative radial flux on star-shaped closures

The outward-normal inequality gives the sign for any nonnegative
boundary weight. The center may be a boundary point and the normal component
may vanish. No strict star-shapedness is needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set MeasureTheory Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A nonnegative weight times the radial field has nonnegative outward flux
on a star-shaped closure. Off the boundary the totalized flux is zero. -/
theorem normalFlux_smul_sub_nonneg_of_starConvex_closure
    {c : ℝ^(m + 1)} (hstar : StarConvex ℝ c (closure Ω))
    {w : ℝ^(m + 1) → ℝ} (hw : ∀ x ∈ frontier Ω, 0 ≤ w x) (x : ℝ^(m + 1)) :
    0 ≤ normalFlux (Ω := Ω) (fun y ↦ w y • (y - c)) x := by
  by_cases hx : x ∈ frontier Ω
  · rw [normalFlux_eq_inner _ hx]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    exact mul_nonneg (hw x hx)
      (inner_sub_outwardUnitNormal_nonneg_of_starConvex_closure hstar ⟨x, hx⟩)
  · simp only [normalFlux, dite_eq_right hx, le_refl]

/-- The signed boundary integral of the weighted radial field is nonnegative. -/
theorem integral_normalFlux_smul_sub_nonneg_of_starConvex_closure
    {c : ℝ^(m + 1)} (hstar : StarConvex ℝ c (closure Ω))
    {w : ℝ^(m + 1) → ℝ} (hw : ∀ x ∈ frontier Ω, 0 ≤ w x) :
    0 ≤ ∫ x, normalFlux (Ω := Ω) (fun y ↦ w y • (y - c)) x ∂surfaceMeasure Ω :=
  integral_nonneg (normalFlux_smul_sub_nonneg_of_starConvex_closure hstar hw)

end SobolevSpace.Trace.C1
