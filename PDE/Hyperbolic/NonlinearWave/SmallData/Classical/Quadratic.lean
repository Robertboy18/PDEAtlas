/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.SmoothReaction
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.StraussLifespan

/-!
# Local and finite maximal quadratic power waves

The smooth cutoff of `-z²` agrees with the original focusing reaction while the
constructed displacement remains in `[-1,1]`. Thus the local existence input is
proved for the quadratic power. Compact velocity with positive
integral in three dimensions then gives a finite maximal classical solution.

This argument uses smoothness of the polynomial square.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set
open scoped NNReal

namespace WaveEquation.SmallData.Classical

private theorem exists_smooth_quadratic_cutoff :
    ∃ (f : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ (⊤ : ℕ∞) f ∧ LipschitzWith K f ∧
      f 0 = 0 ∧ ∀ z, |z| ≤ 1 → f z = -|z| ^ (2 : ℝ) := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 2
      rOut := 3
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let f : ℝ → ℝ := fun z ↦ b z * (-(z ^ 2))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.mul (contDiff_id.pow 2).neg
  have hc : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)
  refine ⟨f, K, hf, hK, by simp [f], fun z hz ↦ ?_⟩
  have hb : z ∈ Metric.closedBall 0 b.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hz.trans (by norm_num [b])
  change b z * (-(z ^ 2)) = -|z| ^ (2 : ℝ)
  rw [b.one_of_mem_closedBall hb, one_mul, Real.rpow_two, sq_abs]

/-- Local existence for the quadratic focusing wave, in every positive
dimension, with zero displacement and arbitrary smooth compact velocity.
The solution has joint C² regularity across its ordinary initial traces. -/
theorem exists_solutionBefore_quadratic_zero {n : ℕ} [NeZero n] (h : ℝ^n → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^(n + 1) → ℝ, IsSolutionBefore (fun z ↦ -|z| ^ (2 : ℝ)) (fun _ ↦ 0) h T u := by
  obtain ⟨f, K, hs, hf, hf0, heq⟩ := exists_smooth_quadratic_cutoff
  obtain ⟨T, u, hu, hb⟩ := exists_solutionBefore_smoothReaction_zero hs hf hf0 h hh hhc
  refine ⟨T, u, hu.time_pos, hu.regular, ?_, hu.position, hu.velocity⟩
  intro p hp
  rw [hu.equation p hp, heq]
  simpa only [timeSpaceCons_spatialPart] using hb (p 0) ⟨hp.1, hp.2.le⟩ (spatialPart p)

/-- In three dimensions, smooth compact velocity of positive
integral and zero displacement produce a finite maximal classical quadratic
wave. Maximality is in the classical Cauchy solution class. -/
theorem exists_finite_maximalSolution_quadratic_three {h : ℝ^3 → ℝ} {R : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (hs : ∀ x, R < ‖x‖ → h x = 0)
    (hR : 0 < R) (hpositive : 0 < ∫ x, h x) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, IsMaximalSolutionBefore (fun z ↦ -|z| ^ (2 : ℝ)) (fun _ ↦ 0) h T u := by
  obtain ⟨a, u₀, h₀⟩ := exists_solutionBefore_quadratic_zero h hh hhc
  have hcrit : (2 : ℝ) < 1 + Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  obtain ⟨T, u, hu, _⟩ := exists_maximalSolution_three_of_lt_strauss
    contDiff_const (hh.of_le (by simp)) (fun _ _ ↦ rfl) hs hR
    (by norm_num) hcrit (by simp) hpositive h₀
  exact ⟨T, u, hu⟩

end WaveEquation.SmallData.Classical
