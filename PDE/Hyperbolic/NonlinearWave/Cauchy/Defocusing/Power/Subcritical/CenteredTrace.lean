/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedTrace
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator

/-!
# Centering a retarded Sobolev trace

Translation places a cone trace on a ball centered at zero, as used in the
inverse-distance potential estimate. The weak chart pullback gives
its base and derivative coordinates. Lebesgue invariance preserves both L²
norms exactly.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.WeakChangeOfVariables
open scoped Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Centering the retarded trace preserves its base and gradient norms;
no boundary condition is introduced by the Sobolev pullback. -/
theorem exists_centered_retardedTrace {u : ℝ^4 → ℝ} {c : ℝ^3} {T : ℝ} (U : H¹(ball c T))
    (hbase : baseRepresentative U =ᵐ[domainMeasure 3 (ball c T)] retardedTrace u c T) :
    ∃ V : H¹(ball (0 : ℝ^3) T),
      baseRepresentative V =ᵐ[domainMeasure 3 (ball 0 T)] (fun x ↦ u (timeSpaceCons (T - ‖x‖) (c +
      x))) ∧
      ‖wkpBaseCoordinateCLM V‖ = ‖wkpBaseCoordinateCLM U‖ ∧ ‖∇ V‖ = ‖∇ U‖ := by
  have himage : (Homeomorph.addLeft c) '' ball (0 : ℝ^3) T = ball c T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change c + x ∈ ball c T
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
    · intro hy
      refine ⟨y - c, ?_, by simp⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hy
  let e := (Homeomorph.addLeft c).toOpenPartialHomeomorphOfImageEq
    (ball 0 T) isOpen_ball (ball c T) himage
  have he : ContDiff ℝ 1 (fun x ↦ e x) := contDiff_const.add contDiff_id
  have hi : ContDiff ℝ 1 (fun y ↦ e.symm y) := contDiff_const.neg.add contDiff_id
  have hb : Bornology.IsBounded e.target := isBounded_ball
  let V : H¹(ball (0 : ℝ^3) T) := boundedW1pPullbackCLM he hi hb U
  have hpre : (fun x : ℝ^3 ↦ c + x) ⁻¹' ball c T = ball 0 T := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hm : MeasurePreserving (fun x : ℝ^3 ↦ c + x)
      (domainMeasure 3 (ball 0 T)) (domainMeasure 3 (ball c T)) := by
    have h := (measurePreserving_add_left (volume : Measure (ℝ^3)) c).restrict_preimage
      (s := ball c T) measurableSet_ball
    rwa [hpre] at h
  have hv : baseRepresentative V =ᵐ[domainMeasure 3 (ball 0 T)]
      fun x ↦ baseRepresentative U (c + x) := boundedW1pPullbackCLM_base_ae he hi hb U
  have hgrad : (∇ V : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 (ball 0 T)]
      fun x ↦ ∇ U (c + x) := by
    have hrows := ae_all_iff.mpr fun i : Fin 3 ↦ boundedW1pPullbackCLM_derivative_ae he hi hb U i
    have hU := hm.quasiMeasurePreserving.ae (wkpGradientCLM_apply_ae U)
    filter_upwards [wkpGradientCLM_apply_ae V, hrows, hU] with x hx hd hu
    refine PiLp.ext fun i ↦ ?_
    have hdi := hd i
    change (V.val (singleDerivIndex 3 i) : ℝ^3 → ℝ) x = _ at hdi
    rw [hx i, hdi, hu i]
    have hder : fderiv ℝ (fun z ↦ e z) x = ContinuousLinearMap.id ℝ (ℝ^3) :=
      ((hasFDerivAt_id x).const_add c).fderiv
    simp only [partialDeriv, hder, ContinuousLinearMap.id_apply, PiLp.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rfl
  refine ⟨V, ?_, ?_, ?_⟩
  · have h := hv.trans (hm.quasiMeasurePreserving.ae_eq_comp hbase)
    simpa only [retardedTrace, Function.comp_def, backwardConeGraph, add_sub_cancel_left] using h
  · rw [Lp.norm_def, Lp.norm_def]
    change (eLpNorm (baseRepresentative V) 2 _).toReal = (eLpNorm (baseRepresentative U) 2 _).toReal
    rw [eLpNorm_congr_ae hv]
    exact congrArg ENNReal.toReal
      (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable (wkpBaseCoordinateCLM U)) hm)
  · rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hgrad]
    exact congrArg ENNReal.toReal
      (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable (∇ U)) hm)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
