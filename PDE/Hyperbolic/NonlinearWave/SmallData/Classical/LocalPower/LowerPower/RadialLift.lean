/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.RadialCutoff
public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
public import PDE.Hyperbolic.Models.Wave.OddDimensions.AnalyticBridge
public import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Lifting a one-dimensional wave to three dimensions

At positive radii, `w(t,r)/r` has wave operator `(w_tt-w_rr)/r`.
The smooth cutoff radius gives a globally C² lift. The formula applies where
the cutoff has become the identity; finite propagation will handle its inner region.
-/

@[expose] public noncomputable section

open Filter PDE.Common
open PDE (laplacian)
open PDE.CoordinateSystems
open scoped Topology

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The radial lift uses a positive radius on the inner ball. -/
def radialLift (c : ℝ) (w : ℝ^2 → ℝ) (q : ℝ^4) : ℝ :=
  w (timeSpaceCons (q 0) (EuclideanSpace.single (0 : Fin 1)
    (cutoffRadius c ‖spatialPartCLM 3 q‖))) / cutoffRadius c ‖spatialPartCLM 3 q‖

/-- Evaluation of the radial lift on a time slice. -/
theorem radialLift_timeSpaceCons (c : ℝ) (w : ℝ^2 → ℝ) (t : ℝ) (x : ℝ^3) :
    radialLift c w (timeSpaceCons t x) = w (timeSpaceCons t
      (EuclideanSpace.single (0 : Fin 1) (cutoffRadius c ‖x‖))) / cutoffRadius c ‖x‖ := by
  simp only [radialLift, timeSpaceCons_zero, spatialPartCLM_timeSpaceCons]

/-- The cutoff makes the lift jointly C² on all of spacetime. -/
theorem contDiff_radialLift {c : ℝ} (hc : 0 < c) {w : ℝ^2 → ℝ}
    (hw : ContDiff ℝ 2 w) : ContDiff ℝ 2 (radialLift c w) := by
  have hR : ContDiff ℝ 2 (fun q : ℝ^4 ↦ cutoffRadius c ‖spatialPartCLM 3 q‖) :=
    (contDiff_cutoffRadius_norm hc).comp (spatialPartCLM 3).contDiff
  have hmap : ContDiff ℝ 2 (fun q : ℝ^4 ↦ timeSpaceCons (q 0)
      (EuclideanSpace.single (0 : Fin 1) (cutoffRadius c ‖spatialPartCLM 3 q‖))) := by
    refine (contDiff_piLp 2).mpr fun i ↦ ?_
    fin_cases i
    · change ContDiff ℝ 2 (fun q : ℝ^4 ↦ q 0)
      exact (EuclideanSpace.proj (0 : Fin 4) : ℝ^4 →L[ℝ] ℝ).contDiff
    · exact hR
  exact (hw.comp hmap).div hR
    (fun q ↦ (hc.trans_le (cutoffRadius_bounds hc ‖spatialPartCLM 3 q‖).1).ne')

/-- Outside the cutoff ball, the wave operator of the lift is the divided
one-dimensional wave operator. -/
theorem waveOperator_radialLift {c : ℝ} (hc : 0 < c) {w : ℝ^2 → ℝ}
    (hw : ContDiff ℝ 2 w) (t : ℝ) {x : ℝ^3} (hx : 2 * c < ‖x‖) :
    waveOperator (radialLift c w) (timeSpaceCons t x) =
      waveOperator w (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) ‖x‖)) / ‖x‖ := by
  have hr : 0 < ‖x‖ := by linarith
  have hR := cutoffRadius_eq_self hc hx.le
  let f : ℝ → ℝ := fun r ↦ w (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r))
  have hf : ContDiff ℝ 2 f := by
    apply hw.comp
    refine (contDiff_piLp 2).mpr fun i ↦ ?_
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id
  have hslice : (fun y ↦ radialLift c w (timeSpaceCons t y)) =ᶠ[𝓝 x]
      (fun y : ℝ^3 ↦ f ‖y‖ / ‖y‖) := by
    filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
    rw [radialLift_timeSpaceCons, cutoffRadius_eq_self hc hy.le]
  have htime : deriv (deriv (fun s ↦ radialLift c w (timeSpaceCons s x))) t = deriv (deriv (fun s ↦
        w (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) ‖x‖)))) t / ‖x‖ := by
    simp_rw [radialLift_timeSpaceCons, hR]
    rw [show deriv (fun s ↦ w (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) ‖x‖)) / ‖x‖) =
        (fun s ↦ deriv (fun s ↦
          w (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) ‖x‖))) s / ‖x‖) from
      funext (fun _ ↦ deriv_div_const _), deriv_div_const]
  rw [waveOperator_timeSpaceCons (contDiff_radialLift hc hw)]
  have hlap : laplacian (fun y : ℝ^3 ↦ f ‖y‖ / ‖y‖) x =
      radialLaplacian 3 (fun r ↦ f r / r) ‖x‖ := by
    simpa only [Function.comp_def] using
      EuclideanLaplacian.laplacian_radial (fun r ↦ f r / r) x (norm_pos_iff.mp hr)
        (hf.contDiffAt.div contDiffAt_id hr.ne')
  rw [htime, EuclideanLaplacian.laplacian_congr_nhds hslice, hlap,
    radialLaplacian_three_div hf.contDiffAt hr.ne', waveOperator_one_timeSpaceCons_single w hw]
  change _ - deriv (deriv f) ‖x‖ / ‖x‖ = (_ - deriv (deriv f) ‖x‖) / ‖x‖
  cas

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
