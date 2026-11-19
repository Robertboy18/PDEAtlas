/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Transport
public import PDE.Analysis.Integration.Cone.Truncated

/-!
# Divergence on closed truncated backward cones

For arbitrary C¹ density P and spatial flux Q, integration of ∂t P − div Q
on a truncated backward cone gives the top density integral minus the bottom
integral, plus the lateral flux P − Q·ν. The lateral surface is closed and uses
normalized Euclidean Hausdorff measure with factor 1/√2. The upper time may
equal the vertex time: continuity
and shrinking volume imply that the top integral tends to zero.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped RealInnerProductSpace Topology

namespace PDE.Analysis

variable {n : ℕ}

/-- The shrinking-ball integral of a continuous density tends to zero at the cone vertex. -/
theorem tendsto_ballIntegral_shrinking_vertex [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} (hP : Continuous P) (c : ℝ^n) (T : ℝ) :
    Filter.Tendsto (fun t ↦ ∫ x in Metric.ball c (T - t), P (timeSpaceCons t x))
      (𝓝[≤] T) (𝓝 0) := by
  have hc := continuousOn_ballIntegral_shrinking hP c T T le_rfl
  simpa only [ContinuousWithinAt, ballIntegral, sub_self, Metric.ball_zero,
    setIntegral_empty] using hc

/-- Divergence theorem on a closed truncated backward cone. Both rim times
are included in the Hausdorff surface, and the upper rim may collapse to the
vertex. The volume integrand uses actual time and spatial derivatives. -/
theorem integral_divergence_truncatedCone [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} {Q : ℝ^(n + 1) → ℝ^n}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) (c : ℝ^n)
    {s τ T : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ T) :
    (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x) =
      (∫ x in Metric.ball c (T - τ), P (timeSpaceCons τ x)) -
        (∫ x in Metric.ball c (T - s), P (timeSpaceCons s x)) +
          (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
            (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
              ∂Measure.euclideanHausdorffMeasure n) := by
  have h := integral_ballIntegral_current_divergence hP hQ c hsτ hτ
  rw [← normalized_integral_truncatedConeLateralSurface
    (continuous_coneCurrentNormalFlux hP.continuous hQ.continuous) c hsτ hτ] at h
  simpa only [ballIntegral, coneCurrentDivergence_timeSpaceCons P hQ,
    coneNormalTrace, coneCurrentNormalFlux] using h

/-- The full backward-cone divergence identity. Continuity of the density
supplies the zero top limit; no endpoint limit or integrability premise is needed. -/
theorem integral_divergence_backwardCone [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} {Q : ℝ^(n + 1) → ℝ^n}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) (c : ℝ^n)
    {s T : ℝ} (hsT : s ≤ T) :
    (∫ t in s..T, ∫ x in Metric.ball c (T - t),
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x) =
      -(∫ x in Metric.ball c (T - s), P (timeSpaceCons s x)) +
        (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s T,
          (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
            ∂Measure.euclideanHausdorffMeasure n) := by
  simpa only [sub_self, Metric.ball_zero, setIntegral_empty, zero_sub] using
    integral_divergence_truncatedCone hP hQ c hsT le_rfl

end PDE.Analysis
