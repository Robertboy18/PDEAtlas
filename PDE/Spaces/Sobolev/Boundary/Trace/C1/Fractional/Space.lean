/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Coordinates
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation

/-!
# Chartwise half-order boundary space

Boundary data consist of a surface `L²` value and real `H^{1/2}` coordinates for
each partition piece. Compatibility requires the physical representative of each
coordinate to equal the localized pullback of the boundary value. These constraints
form a closed subspace of a Hilbert product.

This definition uses only boundary data, the atlas, and the real Bessel
space. It makes no reference to an interior extension or to the range of a trace.
The norm squared is the surface `L²` norm squared plus the sum of the squared
fractional coordinate norms.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The Hilbert product of a surface value and its candidate fractional chart coordinates. -/
abbrev BoundaryChartData :=
  WithLp 2 (Lp ℝ 2 (surfaceMeasure Ω) ×
    PiLp 2 (fun _ : Fin hΩ.N ↦ H^{1 / 2}(ℝ^m; ℝ)))

/-- The discrepancy between a fractional coordinate and the localized surface value. -/
def coordinateCompatibility (i : Fin hΩ.N) :
    BoundaryChartData (Ω := Ω) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ^m)) :=
  (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)).comp
    ((PiLp.proj 2 (fun _ : Fin hΩ.N ↦ H^{1 / 2}(ℝ^m; ℝ)) i).comp
      (WithLp.sndL 2 ℝ _ _)) -
    (localizedBoundaryCoordinates 2 i).comp (WithLp.fstL 2 ℝ _ _)

/-- The closed graph of the boundary-coordinate compatibility conditions. -/
def halfOrderBoundarySubmodule : ClosedSubmodule ℝ (BoundaryChartData (Ω := Ω)) where
  toSubmodule := (ContinuousLinearMap.pi (coordinateCompatibility (Ω := Ω))).ker
  isClosed' := (ContinuousLinearMap.pi (coordinateCompatibility (Ω := Ω))).isClosed_ker

/-- Real chartwise `H^{1/2}` boundary data, equipped with the Hilbert graph norm. -/
abbrev HalfOrderBoundarySpace : Type :=
  ↥(halfOrderBoundarySubmodule (Ω := Ω))

/-- The inherited real inner product, with the scalar and ambient space specified explicitly. -/
instance instInnerProductSpaceHalfOrderBoundarySpace :
    InnerProductSpace ℝ (HalfOrderBoundarySpace (Ω := Ω)) := by
  letI : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin hΩ.N ↦ H^{1 / 2}(ℝ^m; ℝ))) :=
    PiLp.innerProductSpace (𝕜 := ℝ) _
  letI : InnerProductSpace ℝ (BoundaryChartData (Ω := Ω)) :=
    WithLp.instProdInnerProductSpace (𝕜 := ℝ)
  exact ClosedSubmodule.innerProductSpace (𝕜 := ℝ) (E := BoundaryChartData (Ω := Ω))
    (halfOrderBoundarySubmodule (Ω := Ω))

/-- The physical surface value of independent fractional boundary data. -/
def boundaryValue :
    HalfOrderBoundarySpace (Ω := Ω) →L[ℝ] Lp ℝ 2 (surfaceMeasure Ω) :=
  (WithLp.fstL 2 ℝ _ _).comp (halfOrderBoundarySubmodule (Ω := Ω)).toSubmodule.subtypeL

/-- The fractional coordinate of a boundary datum in one chart. -/
def chartValue (i : Fin hΩ.N) :
    HalfOrderBoundarySpace (Ω := Ω) →L[ℝ] H^{1 / 2}(ℝ^m; ℝ) :=
  (PiLp.proj 2 (fun _ : Fin hΩ.N ↦ H^{1 / 2}(ℝ^m; ℝ)) i).comp
    ((WithLp.sndL 2 ℝ _ _).comp (halfOrderBoundarySubmodule (Ω := Ω)).toSubmodule.subtypeL)

/-- A fractional chart coordinate represents exactly the localized surface value. -/
theorem physical_chartValue (i : Fin hΩ.N) (g : HalfOrderBoundarySpace (Ω := Ω)) :
    HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2) (chartValue i g) =
      localizedBoundaryCoordinates 2 i (boundaryValue g) := by
  have h := congrFun g.property i
  change HsSpaceReal.toL2FunCLM m _ (chartValue i g) -
    localizedBoundaryCoordinates 2 i (boundaryValue g) = 0 at h
  exact sub_eq_zero.mp h

/-- The surface value uniquely determines all fractional chart coordinates. -/
theorem boundaryValue_injective :
    Function.Injective (boundaryValue (Ω := Ω)) := by
  intro g h heq
  have hsnd : g.val.snd = h.val.snd := by
    apply PiLp.ext
    intro i
    apply HsSpaceReal.toL2FunCLM_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
    change HsSpaceReal.toL2FunCLM m _ (chartValue i g) =
      HsSpaceReal.toL2FunCLM m _ (chartValue i h)
    rw [physical_chartValue, physical_chartValue, heq]
  apply Subtype.ext
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective (Prod.ext heq hsnd)

/-- The graph norm has the prescribed surface-plus-fractional Hilbert form. -/
theorem norm_sq_halfOrderBoundarySpace (g : HalfOrderBoundarySpace (Ω := Ω)) :
    ‖g‖ ^ 2 = ‖boundaryValue g‖ ^ 2 + ∑ i : Fin hΩ.N, ‖chartValue i g‖ ^ 2 := by
  change ‖g.val‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rfl

/-- Membership of the physical image is exactly chartwise real Bessel regularity. -/
theorem mem_range_boundaryValue_iff (g : Lp ℝ 2 (surfaceMeasure Ω)) :
    g ∈ Set.range (boundaryValue (Ω := Ω)) ↔
      ∀ i : Fin hΩ.N, localizedBoundaryCoordinates 2 i g ∈
        Set.range (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)) := by
  constructor
  · rintro ⟨v, rfl⟩ i
    exact ⟨chartValue i v, physical_chartValue i v⟩
  · intro hg
    let v : PiLp 2 (fun _ : Fin hΩ.N ↦ H^{1 / 2}(ℝ^m; ℝ)) :=
      WithLp.toLp 2 (fun i ↦ (hg i).choose)
    let data : BoundaryChartData (Ω := Ω) := WithLp.toLp 2 (g, v)
    have hdata : data ∈ halfOrderBoundarySubmodule (Ω := Ω) := by
      change ContinuousLinearMap.pi (coordinateCompatibility (Ω := Ω)) data = 0
      funext i
      change HsSpaceReal.toL2FunCLM m _ ((hg i).choose) -
        localizedBoundaryCoordinates 2 i g = 0
      exact sub_eq_zero.mpr (hg i).choose_spec
    exact ⟨⟨data, hdata⟩, rfl⟩

end SobolevSpace.Trace.C1.Fractional
