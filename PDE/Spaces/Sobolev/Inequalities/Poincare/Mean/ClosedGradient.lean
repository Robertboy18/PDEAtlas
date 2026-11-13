/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Ball

/-!
# Closedness of the weak-gradient range

Mean Poincaré controls the full Sobolev norm on the closed subspace of functions
with integral zero. Its gradient is therefore bounded below and has closed
range. Subtracting the mean shows that this is also the range of the unrestricted
gradient. On balls the required estimate is already proved from their geometry.

This permits passage to an Lᵖ limit of weak gradients without assuming a
potential for the limit. The argument works at every exponent from one to
infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- A mean-subtracted Poincaré estimate implies that the gradient range
is closed. The estimate controls the value coordinate; the graph norm estimate
then controls the full integral-zero Sobolev space. -/
theorem isClosed_range_wkpGradientCLM_of_poincare
    [IsFiniteMeasure (domainMeasure n Ω)] (C : ℝ≥0)
    (hP : ∀ U : W^{1,p}(Ω),
      ‖wkpBaseCoordinateCLM (subtractMean U)‖ ≤ C * ‖∇ U‖) :
    IsClosed (Set.range (fun u : W^{1,p}(Ω) ↦ ∇ u)) := by
  let K := (wkpIntegralCLM (n := n) (p := p) (Ω := Ω)).ker
  have hK : IsClosed (K : Set (W^{1,p}(Ω))) :=
    (wkpIntegralCLM (n := n) (p := p) (Ω := Ω)).isClosed_ker
  have : CompleteSpace K := hK.completeSpace_coe
  let G : K →L[ℝ] Lp (ℝ^n) p (domainMeasure n Ω) :=
    wkpGradientCLM.comp K.subtypeL
  have hbase (U : K) :
      ‖wkpBaseCoordinateCLM U.val‖ ≤ C * ‖∇ U.val‖ := by
    have hint : wkpIntegralCLM U.val = 0 := U.property
    have havg : (⨍ x, wkpBaseCoordinateCLM U.val x ∂domainMeasure n Ω) = 0 := by
      rw [average_eq, ← wkpIntegralCLM_apply, hint, smul_zero]
    have heq : wkpBaseCoordinateCLM (subtractMean U.val) =
        wkpBaseCoordinateCLM U.val := by
      apply Lp.ext
      filter_upwards [subtractMean_base_ae U.val] with x hx
      simpa only [havg, sub_zero] using hx
    simpa only [heq] using hP U.val
  have hbound (U : K) : ‖U‖ ≤ ((C + (n : ℝ≥0) : ℝ≥0) : ℝ) * ‖G U‖ := by
    change ‖U.val‖ ≤ ((C : ℝ) + n) * ‖∇ U.val‖
    calc
      _ ≤ ‖wkpBaseCoordinateCLM U.val‖ + n * ‖∇ U.val‖ :=
        norm_le_base_add_gradient U.val
      _ ≤ C * ‖∇ U.val‖ + n * ‖∇ U.val‖ :=
        add_le_add (hbase U) le_rfl
      _ = _ := (add_mul _ _ _).symm
  have hclosed := (G.antilipschitz_of_bound hbound).isClosed_range G.uniformContinuous
  have hrange : Set.range G =
      Set.range (fun u : W^{1,p}(Ω) ↦ ∇ u) := by
    ext f
    constructor
    · rintro ⟨U, rfl⟩
      exact ⟨U.val, rfl⟩
    · rintro ⟨U, rfl⟩
      exact ⟨⟨subtractMean U, wkpIntegralCLM_subtractMean U⟩,
        wkpGradientCLM_subtractMean U⟩
  rwa [hrange] at hclosed

/-- On a ball of positive radius, limits in Lᵖ of weak gradients are
weak gradients. The Poincaré estimate is derived from the ball itself. -/
theorem isClosed_range_wkpGradientCLM_ball [Fact (0 < n)]
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) :
    IsClosed (Set.range (fun u : W^{1,p}(ball x r) ↦ ∇ u)) := by
  have : IsFiniteMeasure (domainMeasure n (ball x r)) := by
    simpa only [domainMeasure, isFiniteMeasure_restrict] using
      (measure_ball_lt_top : volume (ball x r) < ∞).ne
  obtain ⟨C, hC, hP⟩ := exists_poincare_mean_ball (n := n) (p := p)
  apply isClosed_range_wkpGradientCLM_of_poincare ⟨C * r, mul_nonneg hC.le hr.le⟩
  intro U
  rw [Lp.norm_def, eLpNorm_congr_ae (subtractMean_base_ae U)]
  exact hP x r hr U

end SobolevSpace.GraphSpace
