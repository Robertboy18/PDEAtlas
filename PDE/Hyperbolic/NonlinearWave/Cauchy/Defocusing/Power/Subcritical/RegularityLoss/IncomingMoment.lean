/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RegularityLoss.Moment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Strict positivity of an incoming nodal moment

A nonnegative full-cone nodal derivative and an exact positive zero patch give a strictly
positive retarded nodal moment.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

private def incomingPoint (z : NodalParameter) : ℝ × ℝ^3 :=
  ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3))

private theorem continuous_incomingPoint : Continuous incomingPoint :=
  (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd))

private theorem incomingPoint_on_cone (z : NodalParameter) :
    (incomingPoint z).1 + ‖(incomingPoint z).2‖ = 1 := by
  have hω : ‖(z.2 : ℝ^3)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2.property
  simp only [incomingPoint, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr z.1.property.2),
    hω, mul_one, add_sub_cancel]

private theorem incomingPoint_mem_band (z : NodalParameter) :
    incomingPoint z ∈ {p : ℝ × ℝ^3 | |p.1| < 3} := by
  change |(z.1 : ℝ)| < 3
  rw [abs_of_nonneg z.1.property.1]
  exact z.1.property.2.trans_lt (by norm_num)

private theorem nodalRay_eq_incomingPoint (z : NodalParameter) :
    timeSpaceContinuousLinearEquiv 3 (nodalRay z) = incomingPoint z := by
  simp only [nodalRay, mkOfCompact_apply, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, incomingPoint]

/-- The ordinary ray derivative in the retarded moment is the full cone-direction
Fréchet derivative, including the initial face and cone vertex. -/
theorem nodalMoment_unit_eq_integral_fderiv {p : ℝ} {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {q | |q.1| < 3}) :
    nodalMoment p (u ∘ timeSpaceContinuousLinearEquiv 3) 0 1 =
      ∫ z : NodalParameter,
        if u ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3)) = 0 then
          |fderiv ℝ u ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3))
            ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3))| ^ (p - 1) *
            (nodalWeight z * fderiv ℝ u
              ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3))
              ((z.1 : ℝ), (1 - (z.1 : ℝ)) • (z.2 : ℝ^3)))
        else 0 ∂nodalMeasure := by
  have hbase : timeSpaceCons 0 (0 : ℝ^3) = (0 : ℝ^4) := by
    apply (timeSpaceContinuousLinearEquiv 3).injective
    simp only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons, map_zero, Prod.mk_zero_zero]
  have hderiv (z : NodalParameter) : deriv (fun t : ℝ ↦ (u ∘ timeSpaceContinuousLinearEquiv 3)
        (timeSpaceCons 0 0 + (1 + t) • nodalRay z)) 0 =
          fderiv ℝ u (incomingPoint z) (incomingPoint z) := by
    have hud := (hu.contDiffAt ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds
        (incomingPoint_mem_band z))).differentiableAt one_ne_zero
    have hud' : HasFDerivAt u (fderiv ℝ u (incomingPoint z))
        ((1 + (0 : ℝ)) • incomingPoint z) := by
      simpa only [add_zero, one_smul] using hud.hasFDerivAt
    have hd := hud'.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const (incomingPoint z))
    simpa only [Function.comp_def, hbase, zero_add, map_smul,
      nodalRay_eq_incomingPoint, add_zero, one_smul, id_eq] using hd.deriv
  unfold nodalMoment
  apply integral_congr_ae
  filter_upwards [] with z
  rw [hderiv z]
  simp only [Function.comp_def, hbase, zero_add, one_smul, nodalRay_eq_incomingPoint, incomingPoint]

/-- A positive incoming nodal patch has a positive total retarded nodal moment
when the cone derivative is nonnegative at every zero on the complete cone. -/
theorem nodalMoment_pos_of_incoming_zero_patch {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1)
    {u : ℝ × ℝ^3 → ℝ} (hu : ContDiffOn ℝ 1 u {q | |q.1| < 3})
    (hsign : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ^3, t + ‖x‖ = 1 → u (t, x) = 0 → 0 ≤
      fderiv ℝ u (t, x) (t, x))
    (hpatch : ∀ t ∈ Ioo (0 : ℝ) δ, ∀ x : ℝ^3, t + ‖x‖ = 1 → u (t, x) = 0 ∧ 0 <
      fderiv ℝ u (t, x) (t, x)) :
    0 < nodalMoment p (u ∘ timeSpaceContinuousLinearEquiv 3) 0 1 := by
  let U : NodalParameter → ℝ := fun z ↦ u (incomingPoint z)
  let D : NodalParameter → ℝ := fun z ↦ fderiv ℝ u (incomingPoint z) (incomingPoint z)
  have hU : Continuous U := hu.continuousOn.comp_continuous
    continuous_incomingPoint incomingPoint_mem_band
  have hD : Continuous D := ((hu.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_fst.abs continuous_const) le_rfl).comp_continuous
        continuous_incomingPoint incomingPoint_mem_band).clm_apply continuous_incomingPoint
  let f : NodalParameter → ℝ := fun z ↦
    if U z = 0 then |D z| ^ (p - 1) * (nodalWeight z * D z) else 0
  have hc : Continuous (fun z ↦ |D z| ^ (p - 1) * (nodalWeight z * D z)) :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).comp hD.abs).mul
      (nodalWeight.continuous.mul hD)
  have hi : Integrable f nodalMeasure := by
    exact (mkOfCompact ⟨_, hc⟩).integrable nodalMeasure |>.indicator
      (isClosed_singleton.preimage hU).measurableSet
  have hweight (z : NodalParameter) : 0 ≤ nodalWeight z :=
    div_nonneg (sub_nonneg.mpr z.1.property.2) unitSphereArea_pos.le
  have hf : 0 ≤ f := by
    intro z
    dsimp only [f]
    split_ifs with hz
    · exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (mul_nonneg (hweight z)
          (hsign _ z.1.property _ (incomingPoint_on_cone z) hz))
    · exact le_rfl
  rw [nodalMoment_unit_eq_integral_fderiv hu]
  change 0 < ∫ z, f z ∂nodalMeasure
  apply (integral_pos_iff_support_of_nonneg hf hi).mpr
  let b : I := ⟨δ / 2, ⟨(half_pos hδ).le, by linarith⟩⟩
  have hrect : 0 < nodalMeasure (Ioo (0 : I) b ×ˢ (univ : Set Direction)) := by
    rw [nodalMeasure, Measure.prod_prod, unitInterval.volume_Ioo]
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (by change 0 < δ / 2 - 0; linarith)).ne'
    · exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
  apply hrect.trans_le (measure_mono ?_)
  intro z hz
  have ht : (z.1 : ℝ) ∈ Ioo (0 : ℝ) δ := by
    constructor
    · exact hz.1.1
    · have hb : (z.1 : ℝ) < δ / 2 := hz.1.2
      linarith
  have hpz := hpatch _ ht _ (incomingPoint_on_cone z)
  change f z ≠ 0
  apply ne_of_gt
  dsimp only [f]
  have hzU : U z = 0 := hpz.1
  rw [ite_eq_left hzU]
  exact mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr hpz.2.ne') _)
    (mul_pos (div_pos (by have := ht.2.trans hδ1; linarith) unitSphereArea_pos) hpz.2)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end
