/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.Primitive
public import PDE.Analysis.Calculus.DivergenceTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Divergence of a moving-endpoint flux integral

Taking the trace of the differential of the parameter primitive gives the endpoint
pairing and the integral of the slice divergences. Finite-dimensional continuity
of the trace justifies commuting it with the interval integral. When the slice divergence is
the derivative in the parameter of a function, the integral is the increment of that function
(`divergence_parameterPrimitive_of_hasDerivAt`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis

variable {n : ℕ}

private def spatialTrace : (ℝ^n →L[ℝ] ℝ^n) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ (ℝ^n)).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

private theorem spatialTrace_fderiv {H : ℝ^n × ℝ → ℝ^n} {x : ℝ^n} {t : ℝ}
    (hH : DifferentiableAt ℝ H (x, t)) :
    spatialTrace ((fderiv ℝ H (x, t)).comp (ContinuousLinearMap.inl ℝ (ℝ^n) ℝ)) =
      ∇· (fun y ↦ H (y, t)) x := by
  have hd := hH.hasFDerivAt.comp (f := fun y : ℝ^n ↦ (y, t)) x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  dsimp only [Function.comp_def] at hd
  rw [divergence_eq_trace_fderiv hd.differentiableAt, hd.fderiv]
  rfl

/-- Joint `C¹` regularity makes the spatial slice divergence continuous in the parameter. -/
theorem continuousOn_divergence_slices {H : ℝ^n × ℝ → ℝ^n} {x : ℝ^n} {J : Set ℝ}
    (hH : ∀ t ∈ J, ContDiffAt ℝ 1 H (x, t)) :
    ContinuousOn (fun t ↦ ∇· (fun y ↦ H (y, t)) x) J := by
  have hc : ContinuousOn (fun t ↦ spatialTrace
      ((fderiv ℝ H (x, t)).comp (ContinuousLinearMap.inl ℝ (ℝ^n) ℝ))) J := by
    intro t ht
    exact (spatialTrace.continuous.continuousAt.comp
      ((((hH t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).clm_comp
          continuousAt_const)).continuousWithinAt
  apply hc.congr
  intro t ht
  exact (spatialTrace_fderiv ((hH t ht).differentiableAt (by norm_num))).symm

/-- The divergence of a primitive with variable upper endpoint is the endpoint
pairing plus the integral of the spatial divergence. The parameter interval may
extend in either direction from zero. -/
theorem divergence_parameterPrimitive
    {H : ℝ^n × ℝ → ℝ^n} {θ : ℝ^n → ℝ} {x : ℝ^n} {J : Set ℝ}
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J) (hθJ : θ x ∈ J)
    (hH : ∀ t ∈ J, ContDiffAt ℝ 1 H (x, t))
    (hθ : DifferentiableAt ℝ θ x) :
    ∇· (parameterPrimitive H θ) x = fderiv ℝ θ x (H (x, θ x)) +
      ∫ t in (0 : ℝ)..θ x, ∇· (fun y ↦ H (y, t)) x := by
  let D (t : ℝ) := (fderiv ℝ H (x, t)).comp (ContinuousLinearMap.inl ℝ (ℝ^n) ℝ)
  have hseg : uIcc (0 : ℝ) (θ x) ⊆ J := hJc.uIcc_subset h0 hθJ
  have hDC : ContinuousOn D J := by
    intro t ht
    exact ((((hH t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).clm_comp
        continuousAt_const).continuousWithinAt
  have hDI : IntervalIntegrable D volume 0 (θ x) := (hDC.mono hseg).intervalIntegrable
  have hd := hasFDerivAt_parameterPrimitive hJ hJc h0 hθJ hH hθ
  rw [divergence_eq_trace_fderiv hd.differentiableAt, hd.fderiv]
  change spatialTrace ((fderiv ℝ θ x).smulRight (H (x, θ x)) + ∫ t in 0..θ x, D t) = _
  rw [map_add, ← spatialTrace.intervalIntegral_comp_comm hDI]
  have hrank : spatialTrace ((fderiv ℝ θ x).smulRight (H (x, θ x))) =
      fderiv ℝ θ x (H (x, θ x)) := LinearMap.trace_smulRight _ _
  rw [hrank]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact spatialTrace_fderiv ((hH t (hseg ht)).differentiableAt (by norm_num))

/-- If the spatial divergence of the flux at `x` is the derivative in the parameter of a
function `c`, the divergence of the primitive is the endpoint pairing plus the increment of `c`
from `0` to the endpoint. For the flux of a family of extremals, `c` is the density of the
family at `x` (`divergence_extremalFamilyPrimitive`). -/
theorem divergence_parameterPrimitive_of_hasDerivAt
    {H : ℝ^n × ℝ → ℝ^n} {θ : ℝ^n → ℝ} {x : ℝ^n} {J : Set ℝ} {c : ℝ → ℝ}
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J) (hθJ : θ x ∈ J)
    (hH : ∀ t ∈ J, ContDiffAt ℝ 1 H (x, t))
    (hθ : DifferentiableAt ℝ θ x)
    (hc : ∀ t ∈ J, HasDerivAt c (∇· (fun y ↦ H (y, t)) x) t) :
    ∇· (parameterPrimitive H θ) x = fderiv ℝ θ x (H (x, θ x)) + (c (θ x) - c 0) := by
  rw [divergence_parameterPrimitive hJ hJc h0 hθJ hH hθ]
  congr 1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hc t (hJc.uIcc_subset h0 hθJ ht)) ?_
  exact ((continuousOn_divergence_slices hH).mono (hJc.uIcc_subset h0 hθJ)).intervalIntegrable

end PDE.CalculusOfVariations.ExtremalFamily
