/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal
import PDE.Analysis.InnerProductSpace.CodimensionOne

/-!
# Surface Jacobian and the outward normal

For a general C¹ boundary chart, the tangential Jacobian is the absolute
Jacobian of the inverse chart times the conormal length. Multiplying by
the outward unit normal cancels that length and retains the outward sign.
The coordinate frame need not be orthogonal.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open Set Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The flat embedding sends the standard basis to the first ambient basis vectors. -/
theorem flatEmbedding_basisFun (i : Fin m) :
    flatEmbedding (EuclideanSpace.basisFun (Fin m) ℝ i) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j <;>
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single]

/-- The chart surface Jacobian is the inverse volume Jacobian times the
length of the physical conormal. -/
theorem chartBoundaryJacobian_eq_abs_det_mul_norm_conormal
    (i : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryParameterDomain (m := m) (Ω := Ω) i) :
    chartBoundaryJacobian (Ω := Ω) i y =
      |(fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (flatEmbedding y)).toLinearMap.det| *
        ‖chartConormal (Ω := Ω) i (chartBoundaryParametrization (Ω := Ω) i y)‖ := by
  let e := hΩ.chart i
  let x := chartBoundaryParametrization (Ω := Ω) i y
  have hx : x ∈ e.source := e.map_target hy
  have hex : e x = flatEmbedding y := e.right_inv hy
  apply ContinuousLinearMap.normDet_eq_abs_det_mul_norm_of_normal_covector
    (fderiv ℝ (fun z ↦ e.symm z) (flatEmbedding y))
    (fderiv ℝ (fun z ↦ e z) x)
  · have hinv := fderiv_chart_symm_comp_fderiv_chart i hx
    change (fderiv ℝ (fun z ↦ e.symm z) (e x)).comp
      (fderiv ℝ (fun z ↦ e z) x) = _ at hinv
    rwa [hex] at hinv
  · intro j
    change fderiv ℝ (fun z ↦ e.symm z) (flatEmbedding y)
      (flatEmbedding (EuclideanSpace.basisFun (Fin m) ℝ j)) = _
    rw [flatEmbedding_basisFun]
  · intro v
    simp only [chartConormal, InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.comp_apply]
    rfl

/-- Multiplying the outward normal by the surface Jacobian yields the
negative, unnormalized physical conormal weighted by the volume Jacobian. -/
theorem chartBoundaryJacobian_smul_outwardUnitNormal
    (i : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryParameterDomain (m := m) (Ω := Ω) i) :
    chartBoundaryJacobian (Ω := Ω) i y •
        chartOutwardUnitNormal (Ω := Ω) i
          (chartBoundaryParametrization (Ω := Ω) i y) =
      -|(fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (flatEmbedding y)).toLinearMap.det| •
        chartConormal (Ω := Ω) i (chartBoundaryParametrization (Ω := Ω) i y) := by
  have hc := norm_ne_zero_iff.mpr
    (chartConormal_ne_zero i ((hΩ.chart i).map_target hy))
  rw [chartBoundaryJacobian_eq_abs_det_mul_norm_conormal i hy,
    chartOutwardUnitNormal, smul_smul]
  congr 1
  dsimp only [chartBoundaryParametrization]
  field_simp [hc]

end SobolevSpace.Trace.C1
