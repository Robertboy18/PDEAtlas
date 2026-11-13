/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import PDE.FDeriv.Calculus

/-!
# The wave operator from an interior spacetime germ

The coordinate wave operator agrees with the second time-trace derivative
minus the spatial Laplacian under C² regularity only near the evaluation point.
This permits direct use of forward classical solutions on finite lifespans.
-/

@[expose] public noncomputable section

open Filter PDE PDE.Common Set
open scoped Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

/-- C² regularity near one spacetime point suffices for the time-slice formula. -/
theorem waveOperator_timeSpaceCons_of_contDiffAt {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    {t : ℝ} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u (timeSpaceCons t x)) :
    waveOperator u (timeSpaceCons t x) =
      deriv (deriv (fun s ↦ u (timeSpaceCons s x))) t - Δ (fun y ↦ u (timeSpaceCons t y)) x := by
  have hc : ContinuousAt (fun s : ℝ ↦ timeSpaceCons s x) t :=
    ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousAt
  have htrace : (fun s ↦ (∂[0] u) (timeSpaceCons s x)) =ᶠ[𝓝 t]
      deriv (fun s ↦ u (timeSpaceCons s x)) := by
    filter_upwards [hc.preimage_mem_nhds (hu.eventually (by simp))] with s hs
    change ContDiffAt ℝ 2 u (timeSpaceCons s x) at hs
    exact partialDeriv_timeSpaceCons_eq_deriv u x s
      (hs.differentiableAt (by norm_num))
  have hslice : ContDiffAt ℝ 2 (fun y ↦ u (timeSpaceCons t y)) x :=
    hu.comp x (contDiff_timeSpaceCons_spatial n t).contDiffAt
  rw [waveOperator, ← laplacian_timeSlice_of_contDiffAt u t x hu,
    hslice.coordinate_laplacian_eq_laplacian, partialDeriv_timeSpaceCons_eq_deriv (∂[0] u) x t
      ((contDiffAt_partialDeriv 1 hu 0).differentiableAt one_ne_zero), htrace.deriv_eq]

end PDE.Hyperbolic.NonlinearWave.Cauchy
