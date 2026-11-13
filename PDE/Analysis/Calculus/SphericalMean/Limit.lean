/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean.Regularity
import Mathlib.Topology.TietzeExtension

/-!
# The small-radius limit of a spherical mean

Continuity on a neighborhood of the center suffices for convergence of the
fixed-sphere average in positive dimension. A continuous extension on a closed ball
reduces this local assertion to compact parametric integration. No derivative,
support condition, or behavior away from that ball is required.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology

variable {n : ℕ}

/-- In positive dimension, spherical means converge to the center value for
data continuous on a closed ball of positive radius. The averaging radius
may have either sign. The dimension hypothesis is essential: the sphere in
dimension zero is empty and its totalized average is zero. -/
theorem tendsto_unitSphereAverage_of_continuousOn [Fact (0 < n)]
    {u : ℝ^n → ℝ} {x : ℝ^n} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (Metric.closedBall x R)) :
    Tendsto (unitSphereAverage n u x) (𝓝 0) (𝓝 (u x)) := by
  let f : C(Metric.closedBall x R, ℝ) := ⟨fun y ↦ u y, hu.domRestrict⟩
  obtain ⟨v, hv⟩ := f.exists_restrict_eq Metric.isClosed_closedBall
  have heq : EqOn v u (Metric.closedBall x R) := by
    intro y hy
    exact congrArg (fun g : C(Metric.closedBall x R, ℝ) ↦ g ⟨y, hy⟩) hv
  have hv₀ : ContDiff ℝ 0 (v : ℝ^n → ℝ) := contDiff_zero.mpr v.continuous
  have hc : Continuous (unitSphereAverage n v x) :=
    (contDiff_unitSphereAverage hv₀).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hnear : unitSphereAverage n u x =ᶠ[𝓝 0] unitSphereAverage n v x := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hR] with r hr
    have hrabs : |r| < R := by simpa [Real.dist_eq] using hr
    unfold unitSphereAverage
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    apply (heq ?_).symm
    rw [Metric.mem_closedBall]
    simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp ω.property] using
      hrabs.le
  apply Tendsto.congr' hnear.symm
  simpa [heq (Metric.mem_closedBall_self hR.le)] using
    (hc.continuousAt : ContinuousAt (unitSphereAverage n v x) 0).tendsto

end PDE.Analysis
