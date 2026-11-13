/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Approximation.Basic
public import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Finite-interval velocities of the constructed approximations

On every interval `[0, T]`, the velocity `-A_λ u_λ` of a Yosida flow and its
resolvent state `J_λ u_λ` are continuous, hence in `L²(0, T; H)`, and
`u_λ(t) = x₀ + ∫₀ᵗ (-A_λ u_λ)` for `t ∈ [0, T]`, with the integral of the `L²`
class of the velocity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis.Convex

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal} (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
  (hlsc : LowerSemicontinuous I) {lambda : ℝ} (hlambda : 0 < lambda) (x₀ : H)

/-- The Yosida velocity belongs to L² on each finite time interval. -/
theorem memLp_yosidaFlow_velocity (T : ℝ) :
    MemLp (fun t ↦ -yosidaApproximation I hproper hconvex hlsc lambda hlambda
      (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t))
      2 (volume.restrict (Ioc 0 T)) := by
  have hc := (lipschitzWith_yosidaApproximation hproper hconvex hlsc hlambda).continuous.neg
    |>.comp_continuousOn (isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hlambda x₀).continuousOn
  exact (hc.mono Icc_subset_Ici_self).memLp_of_subset_isCompact
    isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self

/-- The resolvent state of the constructed curve belongs to L² on a finite interval. -/
theorem memLp_resolvent_yosidaFlow (T : ℝ) :
    MemLp (fun t ↦ resolvent I hproper hconvex hlsc lambda hlambda
      (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t))
      2 (volume.restrict (Ioc 0 T)) := by
  have hc := (lipschitzWith_resolvent hproper hconvex hlsc hlambda).continuous
    |>.comp_continuousOn (isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hlambda x₀).continuousOn
  exact (hc.mono Icc_subset_Ici_self).memLp_of_subset_isCompact
    isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self

/-- `u_λ(t) = x₀ + ∫₀ᵗ g` for every `t ∈ [0, T]`, where `g` is the `L²(0, T)` class of
the velocity `-A_λ u_λ`. -/
theorem yosidaFlow_eq_initial_add_integral {T t : ℝ} (ht : t ∈ Icc 0 T) :
    yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t = x₀ +
      ∫ r in 0..t, (memLp_yosidaFlow_velocity hproper hconvex hlsc hlambda x₀ T).toLp
        (fun s ↦ -yosidaApproximation I hproper hconvex hlsc lambda hlambda
          (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ s)) r := by
  let u := yosidaFlow I hproper hconvex hlsc lambda hlambda x₀
  let g := fun s ↦ -yosidaApproximation I hproper hconvex hlsc lambda hlambda (u s)
  have hu := isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hlambda x₀
  have hg := (lipschitzWith_yosidaApproximation hproper hconvex hlsc hlambda).continuous.neg
    |>.comp_continuousOn hu.continuousOn
  have hFTC : ∫ r in 0..t, g r = u t - x₀ := by
    rw [← yosidaFlow_zero hproper hconvex hlsc hlambda x₀]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hu.continuousOn.mono Icc_subset_Ici_self)
      (fun r hr ↦ (hu r hr.1.le).hasDerivAt (Ici_mem_nhds hr.1))
      (ContinuousOn.intervalIntegrable (by
        simpa only [uIcc_of_le ht.1, g, u, Function.comp_def, Pi.neg_apply] using
          (hg.mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0))))
  have heq :
      ∫ r in 0..t, (memLp_yosidaFlow_velocity hproper hconvex hlsc hlambda x₀ T).toLp g r =
        ∫ r in 0..t, g r := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    exact (memLp_yosidaFlow_velocity hproper hconvex hlsc hlambda x₀ T).coeFn_toLp.filter_mono
      (ae_mono (volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2)))
  change u t = x₀ + _
  rw [heq, hFTC]
  abel

end PDE.Analysis.Evolution
