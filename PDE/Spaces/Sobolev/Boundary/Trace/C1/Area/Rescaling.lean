/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.Normal

/-!
# Rescaling a C¹ boundary chart at a boundary point

The physical boundary parametrization converges after rescaling to its tangential derivative.
The surface Jacobian converges to the area factor of that derivative, which need not be one:
flattening coordinates need not be orthogonal. The intrinsic normal is orthogonal to this
actual tangent map, so the two limiting normal-offset denominators do not vanish.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set Boundary.Geometry.SurfaceMeasure
open scoped Topology InnerProductSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A boundary chart blown up at a parameter converges along each ray to its tangent map. -/
theorem tendsto_rescale_chartBoundaryParametrization (i : Fin hΩ.N) (a v : ℝ^m) :
    Tendsto (fun t : ℝ ↦ t⁻¹ •
      (chartBoundaryParametrization (Ω := Ω) i (a + t • v) -
        chartBoundaryParametrization (Ω := Ω) i a))
      (𝓝[>] 0) (𝓝 (chartBoundaryTangentialDerivative (Ω := Ω) i a v)) := by
  have hp : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (x := (0 : ℝ))).smul_const v).const_add a
  have hP := ((contDiff_chartBoundaryParametrization (Ω := Ω) i).differentiable
    one_ne_zero a).hasFDerivAt
  rw [fderiv_chartBoundaryParametrization] at hP
  have hline := hP.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
  simpa only [zero_add, zero_smul, add_zero, Function.comp_apply] using
    hline.tendsto_slope_zero_right

/-- Each fixed rescaled parameter stays in the actual open parameter domain for small scales. -/
theorem eventually_rescale_mem_chartBoundaryParameterDomain (i : Fin hΩ.N) {a : ℝ^m}
    (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i) (v : ℝ^m) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      a + t • v ∈ chartBoundaryParameterDomain (Ω := Ω) i := by
  have hp : Tendsto (fun t : ℝ ↦ a + t • v) (𝓝 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).smul_const v)
  exact hp.eventually ((isOpen_chartBoundaryParameterDomain (Ω := Ω) i).mem_nhds ha)

/-- The rescaled area density tends to the actual tangent Jacobian. -/
theorem tendsto_chartBoundaryJacobian_rescale (i : Fin hΩ.N) (a v : ℝ^m) :
    Tendsto (fun t : ℝ ↦ chartBoundaryJacobian (Ω := Ω) i (a + t • v))
      (𝓝 0) (𝓝 (chartBoundaryJacobian (Ω := Ω) i a)) := by
  have hp : Tendsto (fun t : ℝ ↦ a + t • v) (𝓝 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).smul_const v)
  exact (continuous_chartBoundaryJacobian (Ω := Ω) i).continuousAt.tendsto.comp hp

/-- The intrinsic normal annihilates the physical tangent map of any chart at the point. -/
theorem inner_outwardUnitNormal_chartBoundaryTangentialDerivative
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    (v : ℝ^m) :
    inner ℝ (outwardUnitNormal (Ω := Ω) x)
      (chartBoundaryTangentialDerivative (Ω := Ω) i a v) = 0 := by
  have hxsource : (x : ℝ^(m + 1)) ∈ (hΩ.chart i).source := by
    rw [← hx]
    exact (hΩ.chart i).map_target ha
  have hex : hΩ.chart i x = flatEmbedding a := by
    rw [← hx]
    exact (hΩ.chart i).right_inv ha
  have hinv := congrArg (fun L : ℝ^(m + 1) →L[ℝ] ℝ^(m + 1) ↦ L (flatEmbedding v))
    (fderiv_chart_comp_fderiv_chart_symm i hxsource)
  rw [hex] at hinv
  have htangent : fderiv ℝ (fun y ↦ hΩ.chart i y) x
      (chartBoundaryTangentialDerivative (Ω := Ω) i a v) = flatEmbedding v := hinv
  rw [outwardUnitNormal_eq_chart x i hxsource, chartOutwardUnitNormal,
    real_inner_smul_left, chartConormal, InnerProductSpace.toDual_symm_apply]
  change -‖chartConormal (Ω := Ω) i x‖⁻¹ *
    (fderiv ℝ (fun y ↦ hΩ.chart i y) x
      (chartBoundaryTangentialDerivative (Ω := Ω) i a v)) PDE.Common.lastIndex = 0
  rw [htangent]
  have hlast : PDE.Common.lastIndex (n := m + 1) = Fin.last m := by
    ext
    simp [PDE.Common.lastIndex]
  rw [hlast, flatEmbedding_apply_last, mul_zero]

/-- Normal-offset vectors in a rescaled chart converge to their tangent-plane counterparts.
The offset vector is arbitrary, allowing both signs of the intrinsic unit normal. -/
theorem tendsto_rescale_normal_sub_chartBoundaryParametrization
    (i : Fin hΩ.N) (a v : ℝ^m) (w : ℝ^(m + 1)) :
    Tendsto (fun t : ℝ ↦ t⁻¹ •
      (chartBoundaryParametrization (Ω := Ω) i a + t • w -
        chartBoundaryParametrization (Ω := Ω) i (a + t • v)))
      (𝓝[>] 0) (𝓝 (w - chartBoundaryTangentialDerivative (Ω := Ω) i a v)) := by
  refine (tendsto_const_nhds.sub
    (tendsto_rescale_chartBoundaryParametrization (Ω := Ω) i a v)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have heq : chartBoundaryParametrization (Ω := Ω) i a + t • w -
      chartBoundaryParametrization (Ω := Ω) i (a + t • v) =
      t • w - (chartBoundaryParametrization (Ω := Ω) i (a + t • v) -
        chartBoundaryParametrization (Ω := Ω) i a) := by abel
  simp only [heq, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]

/-- The squared tangent-plane denominator is the sum of the squared normal height and
squared physical tangent length, even for nonorthogonal chart coordinates. -/
theorem norm_normal_sub_chartBoundaryTangentialDerivative_sq
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    (s : ℝ) (v : ℝ^m) :
    ‖s • outwardUnitNormal (Ω := Ω) x -
      chartBoundaryTangentialDerivative (Ω := Ω) i a v‖ ^ 2 =
      s ^ 2 + ‖chartBoundaryTangentialDerivative (Ω := Ω) i a v‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_left,
    inner_outwardUnitNormal_chartBoundaryTangentialDerivative i ha x hx v,
    norm_smul, norm_outwardUnitNormal, mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- A nonzero normal height keeps every tangent-plane denominator nonzero. -/
theorem normal_sub_chartBoundaryTangentialDerivative_ne_zero
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    {s : ℝ} (hs : s ≠ 0) (v : ℝ^m) :
    s • outwardUnitNormal (Ω := Ω) x -
      chartBoundaryTangentialDerivative (Ω := Ω) i a v ≠ 0 := by
  intro heq
  have hsq := norm_normal_sub_chartBoundaryTangentialDerivative_sq i ha x hx s v
  rw [heq, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hsq
  nlinarith [sq_pos_of_ne_zero hs,
    sq_nonneg ‖chartBoundaryTangentialDerivative (Ω := Ω) i a v‖]

end SobolevSpace.Trace.C1
