/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.NormalTrace
import CAS.ExactTactic

/-!
# Closed truncated cone surfaces

The graph parametrization identifies a truncated lateral cone with a spatial
annulus. Both rims are included; their images are Hausdorff null. Radial coarea
then gives the time integral of spherical sections, with the cone factor 1/√2.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common WaveEquation

namespace PDE.Analysis

variable {n : ℕ}

/-- The closed lateral surface between two times on a backward cone. -/
def truncatedConeLateralSurface (c : ℝ^n) (T s τ : ℝ) : Set (ℝ^(n + 1)) :=
  {p | s ≤ p 0 ∧ p 0 ≤ τ ∧ ‖spatialPart p - c‖ = T - p 0}

/-- A closed spatial annulus parametrizes the closed truncated cone. -/
theorem truncatedConeLateralSurface_eq_image (c : ℝ^n) (T s τ : ℝ) :
    truncatedConeLateralSurface c T s τ = backwardConeGraph c T ''
      (Metric.closedBall c (T - s) \ Metric.ball c (T - τ)) := by
  ext p
  constructor
  · rintro ⟨hs, hτ, hx⟩
    refine ⟨spatialPart p, ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, hx]
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, hx]
      linarith
    · unfold backwardConeGraph
      rw [hx, sub_sub_cancel, timeSpaceCons_spatialPart]
  · rintro ⟨x, ⟨hs, hτ⟩, rfl⟩
    simp only [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, not_lt] at hs hτ
    change s ≤ T - ‖x - c‖ ∧ T - ‖x - c‖ ≤ τ ∧
      ‖x - c‖ = T - (T - ‖x - c‖)
    exact ⟨by linarith, by linarith, (sub_sub_cancel T _).symm⟩

/-- Truncated lateral cones are compact, including their rims and possible vertex. -/
theorem isCompact_truncatedConeLateralSurface (c : ℝ^n) (T s τ : ℝ) :
    IsCompact (truncatedConeLateralSurface c T s τ) := by
  rw [truncatedConeLateralSurface_eq_image]
  obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
  exact ((isCompact_closedBall c (T - s)).inter_right
    Metric.isOpen_ball.isClosed_compl).image hK.continuous

/-- The closed truncated surface has the same area formula as its open annulus. -/
theorem integral_truncatedConeLateralSurface [Fact (0 < n)]
    (c : ℝ^n) {T s τ : ℝ} (hτ : τ ≤ T) (g : ℝ^(n + 1) → ℝ)
    (hg : Measurable g) :
    (∫ p in truncatedConeLateralSurface c T s τ, g p ∂Measure.euclideanHausdorffMeasure n) =
      Real.sqrt 2 * ∫ x in Metric.ball c (T - s) \ Metric.ball c (T - τ),
        g (backwardConeGraph c T x) := by
  let U := Metric.ball c (T - s) \ Metric.closedBall c (T - τ)
  have hball (r : ℝ) : Metric.closedBall c r =ᵐ[volume] Metric.ball c r := by
    let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
      (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
    exact (closedBall_ae_eq_coneGraph_domain c r).trans
      (sdiff_null_ae_eq_self (measure_singleton c))
  have heq : Metric.closedBall c (T - s) \ Metric.ball c (T - τ) =ᵐ[volume] U :=
    by
      filter_upwards [hball (T - s), hball (T - τ)] with x hs hx
      simp only [U, mem_sdiff, hs, hx]
  rw [truncatedConeLateralSurface_eq_image,
    setIntegral_congr_set (backwardConeGraph_image_ae_eq c T heq)]
  rw [integral_backwardConeGraph_image c T
    (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall) (by
      intro hc
      exact hc.2 (Metric.mem_closedBall_self (sub_nonneg.mpr hτ))) g
    hg.aestronglyMeasurable]
  congr 1
  apply setIntegral_congr_set
  filter_upwards [hball (T - τ)] with x hx
  simp only [mem_sdiff, hx]

/-- Normalized integration over the closed truncated cone equals integration
of its spherical sections. Continuity of the normal-dependent flux supplies
all integrability assumptions, including at the vertex. -/
theorem normalized_integral_truncatedConeLateralSurface [Fact (0 < n)]
    {H : ℝ^(n + 1) × ℝ^n → ℝ} (hH : Continuous H) (c : ℝ^n)
    {s τ T : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ T) :
    (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
      coneNormalTrace H c p ∂Measure.euclideanHausdorffMeasure n) =
      ∫ t in s..τ, sphereIntegral n
        (fun x ↦ coneNormalTrace H c (timeSpaceCons t x)) c (T - t) := by
  rw [integral_truncatedConeLateralSurface c hτ _ (measurable_coneNormalTrace hH c),
    ← mul_assoc]
  have hscale : (1 / Real.sqrt 2) * Real.sqrt 2 = 1 := by cas
  rw [hscale, one_mul, coarea_formula_annulus _ c (T - τ) (T - s)
    (sub_nonneg.mpr hτ) (by linarith)
    (integrableOn_coneNormalTrace_graph hH c T (T - s))
    (integrableOn_sphereIntegral_coneNormalTrace_graph hH c T (by linarith))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : T - τ ≤ T - s)]
  let F (t : ℝ) := sphereIntegral n
    (fun x ↦ coneNormalTrace H c (timeSpaceCons t x)) c (T - t)
  have hchange := intervalIntegral.integral_comp_sub_left (a := T - τ) (b := T - s) F T
  simp only [sub_sub_cancel] at hchange
  rw [← hchange]
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  rw [uIoo_of_le (by linarith : T - τ ≤ T - s)] at hr
  have hrpos : 0 < r := lt_of_le_of_lt (sub_nonneg.mpr hτ) hr.1
  dsimp only [F]
  rw [sub_sub_cancel]
  apply sphereIntegral_congr_on_sphere hrpos
  intro x hx
  have hx' : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  simp only [backwardConeGraph, hx']

end PDE.Analysis
